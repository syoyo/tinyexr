// Copyright (c) 2026 Syoyo Fujita and TinyEXR authors
// SPDX-License-Identifier: BSD-3-Clause
//
// Read a deep-scanline part (sample counts + sample data) with OpenEXR 3.x.
//
//   g++ -std=c++17 read_deep.cpp $(pkg-config --cflags --libs OpenEXR) -o read_deep
//   ./read_deep deep_no_maxsamples.exr
//
#include <OpenEXR/ImfDeepFrameBuffer.h>
#include <OpenEXR/ImfDeepScanLineInputPart.h>
#include <OpenEXR/ImfHeader.h>
#include <OpenEXR/ImfMultiPartInputFile.h>
#include <half.h>

#include <cstdio>
#include <vector>

int main(int argc, char **argv) {
    if (argc != 2) {
        std::fprintf(stderr, "usage: %s <deep.exr>\n", argv[0]);
        return 2;
    }
    try {
        Imf::MultiPartInputFile in(argv[1]);
        Imf::DeepScanLineInputPart part(in, 0);
        Imath::Box2i dw = part.header().dataWindow();
        const int w = dw.max.x - dw.min.x + 1, h = dw.max.y - dw.min.y + 1;
        const size_t n = (size_t)w * (size_t)h;

        std::vector<unsigned int> counts(n, 0);
        std::vector<half *> aptr(n, nullptr), yptr(n, nullptr);
        std::vector<float *> zptr(n, nullptr);
        std::vector<half> abuf(1), ybuf(1);
        std::vector<float> zbuf(1);

        Imf::DeepFrameBuffer fb;
        fb.insertSampleCountSlice(Imf::Slice(
            Imf::UINT, (char *)counts.data(), sizeof(unsigned int),
            sizeof(unsigned int) * (size_t)w));
        // (only pixel 0 is populated by the fixture)
        aptr[0] = abuf.data(); yptr[0] = ybuf.data(); zptr[0] = zbuf.data();
        fb.insert("A", Imf::DeepSlice(Imf::HALF, (char *)aptr.data(),
                                           sizeof(half *), sizeof(half *) * (size_t)w,
                                           sizeof(half)));
        fb.insert("Y", Imf::DeepSlice(Imf::HALF, (char *)yptr.data(),
                                           sizeof(half *), sizeof(half *) * (size_t)w,
                                           sizeof(half)));
        fb.insert("Z", Imf::DeepSlice(Imf::FLOAT, (char *)zptr.data(),
                                           sizeof(float *), sizeof(float *) * (size_t)w,
                                           sizeof(float)));

        part.setFrameBuffer(fb);
        part.readPixelSampleCounts(dw.min.y, dw.max.y);
        part.readPixels(dw.min.y, dw.max.y);

        std::printf("read %dx%d deep pixels, sampleCount[0,0]=%u, A=%.4f Y=%.4f Z=%.4f\n",
                    w, h, counts[0], (float)abuf[0], (float)ybuf[0], zbuf[0]);
        return 0;
    } catch (const std::exception &e) {
        std::fprintf(stderr, "OpenEXR error: %s\n", e.what());
        return 1;
    }
}
