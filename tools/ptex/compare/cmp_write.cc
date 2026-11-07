// SPDX-License-Identifier: BSD-3-Clause
// Differential test: tptex writer vs upstream PtexWriter. The same faces and
// metadata are written through both; the two files are then read back with the
// UPSTREAM reader and compared (face infos incl. nbconstant flags, every face at
// every resolution, constants, border/edge modes, metadata). Compressed bytes
// legitimately differ (different deflate), decoded content must not. Also checks
// our reader opens our file with identical results.
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <string>
#include <vector>

#include "Ptexture.h"
extern "C" {
#include "tptex.h"
#include "tptex_write.h"
}

namespace {
uint32_t g_rng = 0xc0ffee11u;
uint32_t rnd() { g_rng ^= g_rng << 13; g_rng ^= g_rng >> 17; g_rng ^= g_rng << 5; return g_rng; }
uint64_t g_fail = 0, g_checks = 0;
#define CHECK(cond, ...) do { ++g_checks; if (!(cond)) { if (g_fail++ < 30) { std::printf("FAIL: " __VA_ARGS__); std::printf("\n"); } } } while (0)

struct FaceSrc { tptex_face_info fi; bool constant; std::vector<uint8_t> px; };
struct Cfg { int mt, dt, nch, alpha, nfaces; bool mips; int maxlog; bool meta; int ub, vb, em; };

void fill(std::vector<uint8_t>& buf, int dt, size_t n, int mode) {
  const size_t es = size_t(1) << (dt == 0 ? 0 : dt == 3 ? 2 : 1);
  buf.assign(n * es, 0);
  for (size_t i = 0; i < n; ++i) {
    uint32_t r = mode == 0 ? uint32_t(i * 7) : rnd();
    if (dt == 0) buf[i] = uint8_t(r);
    else if (dt == 1) { uint16_t v = uint16_t(r); std::memcpy(&buf[i * 2], &v, 2); }
    else if (dt == 2) { uint16_t v = uint16_t(0x3000 + (r & 0x0fff)); std::memcpy(&buf[i * 2], &v, 2); }
    else { float v = float(r & 0xffff) / 65535.0f; std::memcpy(&buf[i * 4], &v, 4); }
  }
}

void gen_faces(const Cfg& c, std::vector<FaceSrc>& faces) {
  const size_t es = size_t(1) << (c.dt == 0 ? 0 : c.dt == 3 ? 2 : 1);
  faces.resize(size_t(c.nfaces));
  for (int f = 0; f < c.nfaces; ++f) {
    FaceSrc& s = faces[size_t(f)];
    int ul = int(rnd() % (c.maxlog + 1)), vl = int(rnd() % (c.maxlog + 1));
    if (c.mt == 0) vl = ul;
    s.fi.res = tptex_make_res(ul, vl);
    s.fi.adjfaces[0] = (f + 1) % c.nfaces; s.fi.adjfaces[1] = (f + c.nfaces - 1) % c.nfaces;
    s.fi.adjfaces[2] = (f % 3 == 0) ? -1 : (f + 2) % c.nfaces; s.fi.adjfaces[3] = -1;
    s.fi.adjedges = uint8_t(0 | (1 << 2) | (2 << 4) | (3 << 6));
    s.fi.flags = (f % 5 == 0) ? TPTEX_FACE_SUBFACE : 0;
    const size_t npix = (size_t(1) << ul) * (size_t(1) << vl);
    const int kind = int(rnd() % 4);
    s.constant = kind == 0;
    if (s.constant) fill(s.px, c.dt, size_t(c.nch), 1);
    else fill(s.px, c.dt, npix * size_t(c.nch), kind == 1 ? 0 : 1);
    (void)es;
  }
}

bool write_upstream(const std::string& path, const Cfg& c, const std::vector<FaceSrc>& faces) {
  Ptex::String err;
  PtexWriter* w = PtexWriter::open(path.c_str(), c.mt ? Ptex::mt_quad : Ptex::mt_triangle, Ptex::DataType(c.dt), c.nch, c.alpha, c.nfaces, err, c.mips);
  if (!w) { std::printf("upstream writer open: %s\n", err.c_str()); return false; }
  w->setBorderModes(Ptex::BorderMode(c.ub), Ptex::BorderMode(c.vb));
  w->setEdgeFilterMode(Ptex::EdgeFilterMode(c.em));
  if (c.meta) {
    w->writeMeta("name", "tptex-write");
    int32_t iv[3] = {1, -2, 3}; w->writeMeta("ints", iv, 3);
    double dv[2] = {3.5, -1e10}; w->writeMeta("doubles", dv, 2);
    std::string big(5000, 'q'); for (size_t i = 0; i < big.size(); ++i) big[i] = char('a' + (i * 17) % 26);
    w->writeMeta("large", big.c_str());
    int16_t sv[2] = {-5, 7}; w->writeMeta("name", "replaced"); w->writeMeta("shorts", sv, 2);
  }
  for (int f = 0; f < c.nfaces; ++f) {
    const FaceSrc& s = faces[size_t(f)];
    Ptex::FaceInfo fi(Ptex::Res(s.fi.res.ulog2, s.fi.res.vlog2));
    fi.setadjfaces(s.fi.adjfaces[0], s.fi.adjfaces[1], s.fi.adjfaces[2], s.fi.adjfaces[3]);
    fi.adjedges = s.fi.adjedges;
    fi.flags = s.fi.flags;
    if (f % 7 == 6) continue;   // leave some faces unwritten (constant black)
    bool ok = s.constant ? w->writeConstantFace(f, fi, s.px.data()) : w->writeFace(f, fi, s.px.data(), 0);
    if (!ok) { std::printf("upstream write face %d failed\n", f); return false; }
  }
  bool ok = w->close(err);
  w->release();
  return ok;
}

bool write_tptex(const std::string& path, const Cfg& c, const std::vector<FaceSrc>& faces) {
  tptex_write_config cfg; tptex_write_config_init(&cfg);
  cfg.mesh_type = c.mt ? TPTEX_MESH_QUAD : TPTEX_MESH_TRIANGLE;
  cfg.data_type = tptex_data_type(c.dt);
  cfg.num_channels = c.nch; cfg.alpha_channel = c.alpha; cfg.num_faces = c.nfaces; cfg.gen_mipmaps = c.mips;
  tptex_writer* w = nullptr;
  if (tptex_writer_create(&cfg, &w) != TPTEX_OK) { std::printf("tptex writer create failed\n"); return false; }
  tptex_writer_set_border_modes(w, tptex_border_mode(c.ub), tptex_border_mode(c.vb));
  tptex_writer_set_edge_filter_mode(w, tptex_edge_filter_mode(c.em));
  if (c.meta) {
    tptex_writer_meta_string(w, "name", "tptex-write");
    int32_t iv[3] = {1, -2, 3}; tptex_writer_meta(w, "ints", TPTEX_META_INT32, iv, 3);
    double dv[2] = {3.5, -1e10}; tptex_writer_meta(w, "doubles", TPTEX_META_DOUBLE, dv, 2);
    std::string big(5000, 'q'); for (size_t i = 0; i < big.size(); ++i) big[i] = char('a' + (i * 17) % 26);
    tptex_writer_meta_string(w, "large", big.c_str());
    int16_t sv[2] = {-5, 7}; tptex_writer_meta_string(w, "name", "replaced"); tptex_writer_meta(w, "shorts", TPTEX_META_INT16, sv, 2);
  }
  for (int f = 0; f < c.nfaces; ++f) {
    const FaceSrc& s = faces[size_t(f)];
    if (f % 7 == 6) continue;
    tptex_status st = s.constant ? tptex_writer_write_constant_face(w, f, &s.fi, s.px.data()) : tptex_writer_write_face(w, f, &s.fi, s.px.data(), 0);
    if (st != TPTEX_OK) { std::printf("tptex write face %d: %s\n", f, tptex_status_str(st)); tptex_writer_destroy(w); return false; }
  }
  void* data = nullptr; size_t size = 0;
  tptex_status st = tptex_writer_finish_memory(w, &data, &size);
  if (st != TPTEX_OK) { std::printf("tptex finish: %s\n", tptex_status_str(st)); tptex_writer_destroy(w); return false; }
  FILE* fp = std::fopen(path.c_str(), "wb");
  std::fwrite(data, 1, size, fp); std::fclose(fp);
  tptex_free(nullptr, data, size);
  tptex_writer_destroy(w);
  return true;
}

void compare(const std::string& pa, const std::string& pb, const Cfg& c, const char* tag) {
  Ptex::String ea, eb;
  PtexTexture* a = PtexTexture::open(pa.c_str(), ea, false);
  PtexTexture* b = PtexTexture::open(pb.c_str(), eb, false);
  if (!a || !b) { std::printf("%s: open failed (%s | %s)\n", tag, ea.c_str(), eb.c_str()); ++g_fail; if (a) a->release(); if (b) b->release(); return; }
  CHECK(a->meshType() == b->meshType() && a->dataType() == b->dataType() && a->numChannels() == b->numChannels() &&
            a->alphaChannel() == b->alphaChannel() && a->numFaces() == b->numFaces(), "%s header", tag);
  CHECK(a->uBorderMode() == b->uBorderMode() && a->vBorderMode() == b->vBorderMode() && a->edgeFilterMode() == b->edgeFilterMode(), "%s modes", tag);
  CHECK(a->hasMipMaps() == b->hasMipMaps(), "%s hasMipMaps %d vs %d", tag, a->hasMipMaps(), b->hasMipMaps());
  const size_t ps = size_t(Ptex::DataSize(a->dataType()) * a->numChannels());
  for (int f = 0; f < a->numFaces() && f < b->numFaces(); ++f) {
    const Ptex::FaceInfo& fa = a->getFaceInfo(f); const Ptex::FaceInfo& fb = b->getFaceInfo(f);
    CHECK(fa.res.ulog2 == fb.res.ulog2 && fa.res.vlog2 == fb.res.vlog2 && fa.adjedges == fb.adjedges && fa.flags == fb.flags &&
              !std::memcmp(fa.adjfaces, fb.adjfaces, sizeof fa.adjfaces), "%s face %d info (flags %d vs %d)", tag, f, fa.flags, fb.flags);
    for (int ul = fa.res.ulog2; ul >= 0; --ul)
      for (int vl = fa.res.vlog2; vl >= 0; --vl) {
        if (c.mt == 0 && ul != vl) continue;
        const Ptex::Res r((int8_t)ul, (int8_t)vl);
        std::vector<uint8_t> x(ps << (ul + vl), 1), y(ps << (ul + vl), 2);
        a->getData(f, x.data(), int(ps << ul), r);
        b->getData(f, y.data(), int(ps << ul), r);
        CHECK(x == y, "%s face %d res %dx%d data", tag, f, ul, vl);
      }
  }
  PtexMetaData* ma = a->getMetaData(); PtexMetaData* mb = b->getMetaData();
  CHECK(ma->numKeys() == mb->numKeys(), "%s meta count %d vs %d", tag, ma->numKeys(), mb->numKeys());
  for (int i = 0; i < ma->numKeys() && i < mb->numKeys(); ++i) {
    const char *ka = nullptr, *kb = nullptr; Ptex::MetaDataType ta, tb;
    ma->getKey(i, ka, ta); mb->getKey(i, kb, tb);
    CHECK(ka && kb && !std::strcmp(ka, kb) && ta == tb, "%s meta key %d", tag, i);
    if (ta == Ptex::mdt_string) { const char *sa = nullptr, *sb = nullptr; ma->getValue(i, sa); mb->getValue(i, sb); CHECK(sa && sb && !std::strcmp(sa, sb), "%s meta str", tag); }
    else if (ta == Ptex::mdt_int32) { const int32_t *x, *y; int nx, ny; ma->getValue(i, x, nx); mb->getValue(i, y, ny); CHECK(nx == ny && !std::memcmp(x, y, size_t(nx) * 4), "%s meta i32", tag); }
    else if (ta == Ptex::mdt_int16) { const int16_t *x, *y; int nx, ny; ma->getValue(i, x, nx); mb->getValue(i, y, ny); CHECK(nx == ny && !std::memcmp(x, y, size_t(nx) * 2), "%s meta i16", tag); }
    else if (ta == Ptex::mdt_double) { const double *x, *y; int nx, ny; ma->getValue(i, x, nx); mb->getValue(i, y, ny); CHECK(nx == ny && !std::memcmp(x, y, size_t(nx) * 8), "%s meta f64", tag); }
  }
  ma->release(); mb->release();

  // our reader on our file must agree with upstream on the same file
  FILE* fp = std::fopen(pb.c_str(), "rb");
  std::vector<uint8_t> file; std::fseek(fp, 0, SEEK_END); file.resize(size_t(std::ftell(fp))); std::fseek(fp, 0, SEEK_SET);
  if (std::fread(file.data(), 1, file.size(), fp) != file.size()) ++g_fail;
  std::fclose(fp);
  tptex_texture* t = nullptr;
  tptex_status st = tptex_open_memory(file.data(), file.size(), nullptr, &t);
  CHECK(st == TPTEX_OK, "%s tptex reader open ours: %s", tag, tptex_status_str(st));
  if (st == TPTEX_OK) {
    for (int f = 0; f < b->numFaces(); ++f) {
      const Ptex::FaceInfo& fb = b->getFaceInfo(f);
      std::vector<uint8_t> x(ps << (fb.res.ulog2 + fb.res.vlog2)), y(x.size());
      b->getData(f, x.data(), int(ps << fb.res.ulog2), fb.res);
      tptex_get_data(t, f, tptex_make_res(fb.res.ulog2, fb.res.vlog2), y.data(), 0);
      CHECK(x == y, "%s face %d tptex-read of tptex-write", tag, f);
    }
    tptex_close(t);
  }
  a->release(); b->release();
}
}  // namespace

int main(int argc, char** argv) {
  const std::string dir = argc > 1 ? argv[1] : ".";
  int files = 0;
  for (int mt = 0; mt < 2; ++mt)
    for (int d = 0; d < 4; ++d)
      for (int nch : {1, 4})
        for (int alpha : {0, 1})
          for (int mips = 0; mips < 2; ++mips)
            for (int maxlog : {3, 7}) {
              Cfg c;
              c.mt = mt; c.dt = d; c.nch = nch; c.alpha = (alpha && nch > 1) ? nch - 1 : -1;
              c.nfaces = maxlog > 4 ? 8 : 16; c.mips = mips != 0; c.maxlog = maxlog; c.meta = (rnd() & 1) != 0;
              c.ub = int(rnd() % 3); c.vb = int(rnd() % 3); c.em = int(rnd() % 2);
              std::vector<FaceSrc> faces; gen_faces(c, faces);
              char tag[128]; std::snprintf(tag, sizeof tag, "%s dt=%d nch=%d a=%d mips=%d log=%d", mt ? "quad" : "tri", d, nch, c.alpha, mips, maxlog);
              std::string pa = dir + "/wa_" + std::to_string(files) + ".ptx", pb = dir + "/wb_" + std::to_string(files) + ".ptx";
              ++files;
              if (!write_upstream(pa, c, faces) || !write_tptex(pb, c, faces)) { ++g_fail; continue; }
              compare(pa, pb, c, tag);
              std::remove(pa.c_str()); std::remove(pb.c_str());
            }
  std::printf("cmp_write: %d fixtures, %llu checks, %llu failures\n", files, (unsigned long long)g_checks, (unsigned long long)g_fail);
  return g_fail ? 1 : 0;
}
