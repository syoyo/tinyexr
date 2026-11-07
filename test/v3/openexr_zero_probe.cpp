/*
 * Independent OpenEXR full-decode oracle for zero-valued Lean fixtures.
 * All levels and parts are read; deep sample counts must match the argument.
 * This deliberately bounded fixture probe is not a general image comparator.
 * Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
 * SPDX-License-Identifier: BSD-3-Clause
 */
#include <OpenEXR/ImfChannelList.h>
#include <OpenEXR/ImfDeepFrameBuffer.h>
#include <OpenEXR/ImfDeepScanLineInputPart.h>
#include <OpenEXR/ImfDeepTiledInputPart.h>
#include <OpenEXR/ImfFrameBuffer.h>
#include <OpenEXR/ImfHeader.h>
#include <OpenEXR/ImfInputPart.h>
#include <OpenEXR/ImfMultiPartInputFile.h>
#include <OpenEXR/ImfPartType.h>
#include <OpenEXR/ImfTiledInputPart.h>
#include <cstdio>
#include <stdexcept>
#include <vector>

static size_t pixels(const Imath::Box2i &box) {
    const int64_t w = int64_t(box.max.x) - box.min.x + 1;
    const int64_t h = int64_t(box.max.y) - box.min.y + 1;
    if (w < 1 || h < 1 || w > 128 || h > 128)
        throw std::runtime_error("fixture extent outside probe limits");
    return size_t(w) * size_t(h);
}

static void require_zero(const std::vector<std::vector<float>> &values) {
    for (const auto &channel : values)
        for (float value : channel)
            if (value != 0.0f) throw std::runtime_error("nonzero fixture sample");
}

template <class Part, class Read>
static void read_flat(Part &part, const Imath::Box2i &box, Read read) {
    const size_t n = pixels(box);
    std::vector<std::vector<float>> values;
    Imf::FrameBuffer fb;
    for (auto c = part.header().channels().begin(); c != part.header().channels().end(); ++c) {
        if (c.channel().xSampling != 1 || c.channel().ySampling != 1)
            throw std::runtime_error("fixture probe requires unit sampling");
        values.emplace_back(n, -1.0f);
        fb.insert(c.name(), Imf::Slice::Make(Imf::FLOAT, values.back().data(), box));
    }
    part.setFrameBuffer(fb);
    read();
    require_zero(values);
}

template <class Part, class Counts, class Samples>
static void read_deep(Part &part, const Imath::Box2i &box, unsigned expected,
                      Counts read_counts, Samples read_samples) {
    const size_t n = pixels(box);
    const size_t width = size_t(int64_t(box.max.x) - box.min.x + 1);
    std::vector<unsigned> counts(n, 0xffffffffu);
    std::vector<std::vector<float *>> pointers;
    std::vector<std::vector<float>> values;
    Imf::DeepFrameBuffer fb;
    fb.insertSampleCountSlice(Imf::Slice::Make(Imf::UINT, counts.data(), box));
    for (auto c = part.header().channels().begin(); c != part.header().channels().end(); ++c) {
        pointers.emplace_back(n, nullptr);
        const auto origin = Imf::Slice::Make(Imf::FLOAT, pointers.back().data(), box,
                                             sizeof(float *), width * sizeof(float *));
        fb.insert(c.name(), Imf::DeepSlice(Imf::FLOAT, origin.base,
                    sizeof(float *), width * sizeof(float *), sizeof(float)));
    }
    part.setFrameBuffer(fb);
    read_counts();
    for (unsigned count : counts)
        if (count != expected) throw std::runtime_error("deep fixture sample-count mismatch");
    values.resize(pointers.size());
    for (size_t c = 0; c < values.size(); ++c) {
        values[c].assign(n * expected, -1.0f);
        for (size_t p = 0; p < n; ++p)
            pointers[c][p] = expected ? values[c].data() + p * expected : nullptr;
    }
    read_samples();
    require_zero(values);
}

int main(int argc, char **argv) {
    if (argc != 3 || (argv[2][0] != '0' && argv[2][0] != '1') || argv[2][1] != '\0') {
        std::fprintf(stderr, "usage: openexr_zero_probe <fixture.exr> <deep-count:0|1>\n");
        return 2;
    }
    try {
        const unsigned expected = unsigned(argv[2][0] - '0');
        Imf::MultiPartInputFile file(argv[1]);
        for (int p = 0; p < file.parts(); ++p) {
            const auto &header = file.header(p);
            const bool tiled = Imf::isTiled(header.type());
            const bool deep = Imf::isDeepData(header.type());
            if (tiled && deep) {
                Imf::DeepTiledInputPart part(file, p);
                for (int ly = 0; ly < part.numYLevels(); ++ly)
                    for (int lx = 0; lx < part.numXLevels(); ++lx) {
                        if (!part.isValidLevel(lx, ly)) continue;
                        const int nx = part.numXTiles(lx), ny = part.numYTiles(ly);
                        read_deep(part, part.dataWindowForLevel(lx, ly), expected,
                            [&] { part.readPixelSampleCounts(0, nx - 1, 0, ny - 1, lx, ly); },
                            [&] { part.readTiles(0, nx - 1, 0, ny - 1, lx, ly); });
                    }
            } else if (tiled) {
                Imf::TiledInputPart part(file, p);
                for (int ly = 0; ly < part.numYLevels(); ++ly)
                    for (int lx = 0; lx < part.numXLevels(); ++lx) {
                        if (!part.isValidLevel(lx, ly)) continue;
                        read_flat(part, part.dataWindowForLevel(lx, ly), [&] {
                            part.readTiles(0, part.numXTiles(lx) - 1,
                                           0, part.numYTiles(ly) - 1, lx, ly);
                        });
                    }
            } else if (deep) {
                Imf::DeepScanLineInputPart part(file, p);
                const auto box = header.dataWindow();
                read_deep(part, box, expected,
                    [&] { part.readPixelSampleCounts(box.min.y, box.max.y); },
                    [&] { part.readPixels(box.min.y, box.max.y); });
            } else {
                Imf::InputPart part(file, p);
                const auto box = header.dataWindow();
                read_flat(part, box, [&] { part.readPixels(box.min.y, box.max.y); });
            }
        }
        std::printf("OpenEXR full-decode: %d parts, all samples zero\n", file.parts());
        return 0;
    } catch (const std::exception &error) {
        std::fprintf(stderr, "OpenEXR fixture error: %s\n", error.what());
        return 1;
    }
}
