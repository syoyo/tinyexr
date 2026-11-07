// SPDX-License-Identifier: BSD-3-Clause
// Differential test: tptex reader vs upstream PtexReader on files written by the
// upstream PtexWriter across a matrix of mesh type, data type, channels, alpha,
// resolutions, mipmaps, premultiply, and metadata. Compared: header info, every
// FaceInfo, every face at every stored-or-lower resolution (bytes), constants,
// getPixel, and all metadata (order, type, bytes).
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <string>
#include <vector>

#include "Ptexture.h"
extern "C" {
#include "tptex.h"
}

namespace {
uint32_t g_rng = 0x1badf00du;
uint32_t rnd() { g_rng ^= g_rng << 13; g_rng ^= g_rng >> 17; g_rng ^= g_rng << 5; return g_rng; }
uint64_t g_fail = 0, g_checks = 0;
#define CHECK(cond, ...) do { ++g_checks; if (!(cond)) { if (g_fail++ < 30) { std::printf("FAIL: " __VA_ARGS__); std::printf("\n"); } } } while (0)

struct Cfg { Ptex::MeshType mt; Ptex::DataType dt; int nch, alpha; int nfaces; bool mips; bool premult; int maxlog; bool meta; };

void fill_face(std::vector<uint8_t>& buf, Ptex::DataType dt, size_t n, int mode) {
  const int es = Ptex::DataSize(dt);
  buf.assign(n * es, 0);
  for (size_t i = 0; i < n; ++i) {
    uint32_t r = mode == 0 ? uint32_t(i * 7) : rnd();   // mode 0: smooth ramp (compresses), 1: noise
    switch (dt) {
      case Ptex::dt_uint8: buf[i] = uint8_t(r); break;
      case Ptex::dt_uint16: { uint16_t v = uint16_t(r); std::memcpy(&buf[i * 2], &v, 2); break; }
      case Ptex::dt_half: { uint16_t v = uint16_t(0x3000 + (r & 0x0fff)); std::memcpy(&buf[i * 2], &v, 2); break; }
      case Ptex::dt_float: { float v = float(r & 0xffff) / 65535.0f; std::memcpy(&buf[i * 4], &v, 4); break; }
    }
  }
}

bool write_fixture(const std::string& path, const Cfg& c) {
  Ptex::String err;
  PtexWriter* w = PtexWriter::open(path.c_str(), c.mt, c.dt, c.nch, c.alpha, c.nfaces, err, c.mips);
  if (!w) { std::printf("writer open failed: %s\n", err.c_str()); return false; }
  if (c.meta) {
    w->writeMeta("name", "tptex-fixture");
    int32_t iv[3] = {1, -2, 3}; w->writeMeta("ints", iv, 3);
    int16_t sv[2] = {-5, 7}; w->writeMeta("shorts", sv, 2);
    int8_t bv[4] = {1, 2, 3, -4}; w->writeMeta("bytes", bv, 4);
    float fv[2] = {1.5f, -2.25f}; w->writeMeta("floats", fv, 2);
    double dv[2] = {3.14159, -1e10}; w->writeMeta("doubles", dv, 2);
    std::string big(20000, 'x'); for (size_t i = 0; i < big.size(); ++i) big[i] = char('a' + (i * 31) % 26);
    w->writeMeta("large", big.c_str());   // > 1KB -> large metadata
  }
  const int esz = Ptex::DataSize(c.dt);
  for (int f = 0; f < c.nfaces; ++f) {
    int ul = int(rnd() % (c.maxlog + 1)), vl = int(rnd() % (c.maxlog + 1));
    if (c.mt == Ptex::mt_triangle) vl = ul;
    const Ptex::Res fres((int8_t)ul, (int8_t)vl);
    Ptex::FaceInfo fi(fres);
    // simple adjacency ring so the info round-trips distinct values
    int32_t adj[4] = {(f + 1) % c.nfaces, (f + c.nfaces - 1) % c.nfaces, -1, -1};
    fi.setadjfaces(adj[0], adj[1], adj[2], adj[3]);
    fi.setadjedges(0, 1, 2, 3);
    std::vector<uint8_t> px;
    const size_t n = (size_t(1) << ul) * (size_t(1) << vl) * c.nch;
    int kind = int(rnd() % 4);
    if (kind == 0) {   // constant face
      px.assign(n * esz, 0);
      std::vector<uint8_t> one; fill_face(one, c.dt, c.nch, 1);
      for (size_t i = 0; i < size_t(1) << (ul + vl); ++i) std::memcpy(&px[i * c.nch * esz], one.data(), c.nch * esz);
      if (!w->writeConstantFace(f, fi, one.data())) { std::printf("writeConstantFace failed\n"); return false; }
    } else {
      fill_face(px, c.dt, n, kind == 1 ? 0 : 1);
      if (!w->writeFace(f, fi, px.data(), 0)) { std::printf("writeFace failed\n"); return false; }
    }
  }
  bool ok = w->close(err);
  if (!ok) std::printf("close failed: %s\n", err.c_str());
  w->release();
  return ok;
}

void compare(const std::string& path, const Cfg& c, const char* tag) {
  Ptex::String err;
  PtexTexture* up = PtexTexture::open(path.c_str(), err, c.premult);
  if (!up) { std::printf("%s: upstream cannot open: %s\n", tag, err.c_str()); ++g_fail; return; }
  tptex_options opt; tptex_options_init(&opt);
  if (c.premult) opt.flags |= TPTEX_OPEN_PREMULTIPLY;
  // read the file through memory
  FILE* fp = std::fopen(path.c_str(), "rb");
  std::vector<uint8_t> file;
  { std::fseek(fp, 0, SEEK_END); long n = std::ftell(fp); std::fseek(fp, 0, SEEK_SET); file.resize(size_t(n)); if (std::fread(file.data(), 1, file.size(), fp) != file.size()) { std::printf("read fail\n"); ++g_fail; } std::fclose(fp); }
  tptex_texture* t = nullptr;
  tptex_status st = tptex_open_memory(file.data(), file.size(), &opt, &t);
  if (st != TPTEX_OK) { std::printf("%s: tptex open failed: %s\n", tag, tptex_status_str(st)); ++g_fail; up->release(); return; }
  const tptex_info* ti = tptex_get_info(t);
  CHECK(ti->mesh_type == int(up->meshType()), "%s mesh type", tag);
  CHECK(ti->data_type == int(up->dataType()), "%s data type", tag);
  CHECK(ti->num_channels == up->numChannels(), "%s channels", tag);
  CHECK(ti->alpha_channel == up->alphaChannel(), "%s alpha", tag);
  CHECK(ti->num_faces == up->numFaces(), "%s nfaces", tag);
  CHECK(ti->u_border_mode == int(up->uBorderMode()) && ti->v_border_mode == int(up->vBorderMode()), "%s border", tag);
  CHECK(ti->edge_filter_mode == int(up->edgeFilterMode()), "%s edgefilter", tag);
  CHECK(ti->has_mipmaps == (up->hasMipMaps() ? 1 : 0), "%s mipmaps", tag);
  const size_t ps = tptex_pixel_size(t);
  CHECK(ps == size_t(Ptex::DataSize(up->dataType()) * up->numChannels()), "%s pixel size", tag);

  for (int f = 0; f < up->numFaces(); ++f) {
    const Ptex::FaceInfo& u = up->getFaceInfo(f);
    tptex_face_info fi;
    if (tptex_get_face_info(t, f, &fi) != TPTEX_OK) { CHECK(false, "%s face %d info", tag, f); continue; }
    CHECK(fi.res.ulog2 == u.res.ulog2 && fi.res.vlog2 == u.res.vlog2 && fi.adjedges == u.adjedges &&
              fi.flags == u.flags && !std::memcmp(fi.adjfaces, u.adjfaces, sizeof fi.adjfaces),
          "%s face %d faceinfo", tag, f);
    // every resolution from stored down to 1x1 (upstream's own reduction rules)
    for (int ul = u.res.ulog2; ul >= 0; --ul) {
      for (int vl = u.res.vlog2; vl >= 0; --vl) {
        if (c.mt == Ptex::mt_triangle && ul != vl) continue;
        const Ptex::Res r((int8_t)ul, (int8_t)vl);
        std::vector<uint8_t> a(ps << (ul + vl), 0xAA), b(ps << (ul + vl), 0x55);
        up->getData(f, a.data(), int(ps << ul), r);
        tptex_status gs = tptex_get_data(t, f, tptex_make_res(ul, vl), b.data(), 0);
        CHECK(gs == TPTEX_OK && a == b, "%s face %d res %dx%d data (%s)", tag, f, ul, vl, tptex_status_str(gs));
      }
    }
    // constant pixel
    std::vector<uint8_t> ca(ps), cb(ps);
    PtexFaceData* fd = up->getData(f, Ptex::Res(0, 0));
    if (fd) { std::memcpy(ca.data(), fd->getData(), ps); fd->release(); }
    tptex_get_constant(t, f, cb.data());
    CHECK(ca == cb, "%s face %d constant", tag, f);
    // a few pixels via getPixel
    for (int k = 0; k < 3; ++k) {
      int pu = int(rnd() % (1u << u.res.ulog2)), pv = int(rnd() % (1u << u.res.vlog2));
      float ra[8] = {0}, rb[8] = {0};
      up->getPixel(f, pu, pv, ra, 0, up->numChannels());
      tptex_get_pixel(t, f, pu, pv, rb, 0, up->numChannels());
      CHECK(!std::memcmp(ra, rb, sizeof(float) * up->numChannels()), "%s face %d pixel (%d,%d)", tag, f, pu, pv);
    }
  }

  // metadata: same keys in the same order, same types and bytes
  PtexMetaData* um = up->getMetaData();
  int cnt = 0; tptex_meta_count(t, &cnt);
  CHECK(cnt == um->numKeys(), "%s meta count %d vs %d", tag, cnt, um->numKeys());
  for (int i = 0; i < cnt && i < um->numKeys(); ++i) {
    const char* uk = nullptr; Ptex::MetaDataType ut;
    um->getKey(i, uk, ut);
    const char* tk = nullptr; tptex_meta_type tt;
    tptex_meta_key(t, i, &tk, &tt);
    CHECK(uk && tk && !std::strcmp(uk, tk) && int(ut) == int(tt), "%s meta key %d (%s vs %s)", tag, i, uk ? uk : "?", tk ? tk : "?");
    const void* td = nullptr; int tcount = 0;
    tptex_meta_value(t, i, &td, &tcount);
    if (ut == Ptex::mdt_string) {
      const char* s = nullptr; um->getValue(i, s);
      CHECK(s && td && !std::strcmp(s, (const char*)td), "%s meta %s string", tag, uk);
    } else if (ut == Ptex::mdt_int8) {
      const int8_t* p; int n; um->getValue(i, p, n); CHECK(n == tcount && !std::memcmp(p, td, size_t(n)), "%s meta %s", tag, uk);
    } else if (ut == Ptex::mdt_int16) {
      const int16_t* p; int n; um->getValue(i, p, n); CHECK(n == tcount && !std::memcmp(p, td, size_t(n) * 2), "%s meta %s", tag, uk);
    } else if (ut == Ptex::mdt_int32) {
      const int32_t* p; int n; um->getValue(i, p, n); CHECK(n == tcount && !std::memcmp(p, td, size_t(n) * 4), "%s meta %s", tag, uk);
    } else if (ut == Ptex::mdt_float) {
      const float* p; int n; um->getValue(i, p, n); CHECK(n == tcount && !std::memcmp(p, td, size_t(n) * 4), "%s meta %s", tag, uk);
    } else {
      const double* p; int n; um->getValue(i, p, n); CHECK(n == tcount && !std::memcmp(p, td, size_t(n) * 8), "%s meta %s", tag, uk);
    }
  }
  um->release();
  tptex_close(t);
  up->release();
}
}  // namespace

int main(int argc, char** argv) {
  const std::string dir = argc > 1 ? argv[1] : ".";
  const Ptex::DataType dts[] = {Ptex::dt_uint8, Ptex::dt_uint16, Ptex::dt_half, Ptex::dt_float};
  const char* dn[] = {"u8", "u16", "half", "f32"};
  int files = 0;
  for (int mt = 0; mt < 2; ++mt)
    for (int d = 0; d < 4; ++d)
      for (int nch : {1, 3, 4})
        for (int alpha : {-1, 99})   // 99 = last channel
          for (int mips = 0; mips < 2; ++mips)
            for (int maxlog : {2, 6}) {
              Cfg c;
              c.mt = mt ? Ptex::mt_triangle : Ptex::mt_quad;
              c.dt = dts[d];
              c.nch = nch;
              c.alpha = alpha == 99 ? (nch > 1 ? nch - 1 : -1) : -1;
              c.nfaces = maxlog > 4 ? 6 : 12;
              c.mips = mips != 0;
              c.premult = c.alpha >= 0 && (rnd() & 1);
              c.maxlog = maxlog;
              c.meta = (rnd() & 1) != 0;
              char tag[128];
              std::snprintf(tag, sizeof tag, "%s %s nch=%d a=%d mips=%d log=%d", mt ? "tri" : "quad", dn[d], nch, c.alpha, mips, maxlog);
              std::string path = dir + "/fx_" + std::to_string(files++) + ".ptx";
              if (!write_fixture(path, c)) { ++g_fail; continue; }
              compare(path, c, tag);
              std::remove(path.c_str());
            }
  // Hostile phase: mutate / truncate fixtures; tptex must never crash or hang
  // (run under ASan/UBSan via TPTEX_SAN=1) and must fail with a status, never UB.
  {
    Cfg c = {Ptex::mt_quad, Ptex::dt_uint8, 4, 3, 10, true, false, 5, true};
    std::string path = dir + "/fx_hostile.ptx";
    if (write_fixture(path, c)) {
      FILE* fp = std::fopen(path.c_str(), "rb");
      std::vector<uint8_t> base;
      std::fseek(fp, 0, SEEK_END); base.resize(size_t(std::ftell(fp))); std::fseek(fp, 0, SEEK_SET);
      if (std::fread(base.data(), 1, base.size(), fp) != base.size()) ++g_fail;
      std::fclose(fp);
      unsigned opened = 0, rejected = 0;
      for (int iter = 0; iter < 3000; ++iter) {
        std::vector<uint8_t> m = base;
        const int mode = iter % 3;
        if (mode == 0) m.resize(rnd() % (m.size() + 1));                      // truncate
        else if (mode == 1) { for (int k = 0; k < 1 + int(rnd() % 4); ++k) m[rnd() % std::min<size_t>(m.size(), 200)] ^= uint8_t(1u << (rnd() & 7)); } // header bit flips
        else { for (int k = 0; k < 1 + int(rnd() % 8); ++k) m[rnd() % m.size()] = uint8_t(rnd()); }                                               // anywhere
        tptex_options opt; tptex_options_init(&opt);
        opt.limits.max_block_bytes = 1u << 24;
        tptex_texture* t = nullptr;
        if (tptex_open_memory(m.data(), m.size(), &opt, &t) != TPTEX_OK) { ++rejected; continue; }
        ++opened;
        const tptex_info* ti = tptex_get_info(t);
        std::vector<uint8_t> buf(1u << 22);
        for (int f = 0; f < ti->num_faces && f < 64; ++f) {
          tptex_face_info fi;
          if (tptex_get_face_info(t, f, &fi) != TPTEX_OK) continue;
          if (fi.res.ulog2 + fi.res.vlog2 + 2 <= 22 - 0 && (size_t(tptex_pixel_size(t)) << (fi.res.ulog2 + fi.res.vlog2)) <= buf.size())
            tptex_get_data(t, f, fi.res, buf.data(), 0);
          tptex_get_data(t, f, tptex_make_res(0, 0), buf.data(), 0);
        }
        int n = 0; tptex_meta_count(t, &n);
        for (int i = 0; i < n && i < 16; ++i) { const void* d; int cnt; tptex_meta_value(t, i, &d, &cnt); }
        tptex_close(t);
      }
      std::printf("hostile: %u opened, %u rejected (no crash)\n", opened, rejected);
      std::remove(path.c_str());
    }
  }
  std::printf("cmp_reader: %d fixtures, %llu checks, %llu failures\n", files,
              (unsigned long long)g_checks, (unsigned long long)g_fail);
  return g_fail ? 1 : 0;
}
