// SPDX-License-Identifier: BSD-3-Clause
// Differential test: tptex filters vs upstream PtexFilter. Meshes (quad grids with
// mismatched face resolutions, constant faces, all border modes; closed triangle
// meshes) are written with the upstream writer, then every filter type is
// evaluated at random positions/footprints through both implementations.
// Tolerance is float rounding (tiles are applied as one block here).
#include <cmath>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <array>
#include <cstring>
#include <string>
#include <vector>

#include "Ptexture.h"
extern "C" {
#include "tptex.h"
#include "tptex_filter.h"
}

namespace {
uint32_t g_rng = 0x5eed1234u;
uint32_t rnd() { g_rng ^= g_rng << 13; g_rng ^= g_rng >> 17; g_rng ^= g_rng << 5; return g_rng; }
float frand() { return float(rnd() >> 8) * (1.0f / 16777216.0f); }
uint64_t g_fail = 0, g_checks = 0, g_errs = 0, g_worst_n = 0;
double g_worst = 0;

void fill(std::vector<uint8_t>& buf, int dt, size_t npix, int nch, int mode, uint32_t seed) {
  const size_t es = size_t(1) << (dt == 0 ? 0 : dt == 3 ? 2 : 1);
  buf.assign(npix * nch * es, 0);
  for (size_t i = 0; i < npix * nch; ++i) {
    uint32_t r = mode == 0 ? uint32_t(seed + (i * 5) % 251) : rnd();
    if (dt == 0) buf[i] = uint8_t(r);
    else if (dt == 1) { uint16_t v = uint16_t(r); std::memcpy(&buf[i * 2], &v, 2); }
    else if (dt == 2) { uint16_t v = uint16_t(0x3000 + (r & 0x0fff)); std::memcpy(&buf[i * 2], &v, 2); }
    else { float v = float(r & 0xffff) / 65535.0f; std::memcpy(&buf[i * 4], &v, 4); }
  }
}

struct Topo { std::vector<std::array<int, 4>> adj; std::vector<std::array<int, 4>> aedge; };

// quad grid W x H; edges 0=bottom 1=right 2=top 3=left, no rotations
void grid(int W, int H, Topo& t) {
  t.adj.assign(size_t(W * H), {-1, -1, -1, -1});
  t.aedge.assign(size_t(W * H), {0, 0, 0, 0});
  for (int j = 0; j < H; ++j) for (int i = 0; i < W; ++i) {
    int f = j * W + i;
    if (j > 0) { t.adj[f][0] = f - W; t.aedge[f][0] = 2; }
    if (i + 1 < W) { t.adj[f][1] = f + 1; t.aedge[f][1] = 3; }
    if (j + 1 < H) { t.adj[f][2] = f + W; t.aedge[f][2] = 0; }
    if (i > 0) { t.adj[f][3] = f - 1; t.aedge[f][3] = 1; }
  }
}

// closed triangle mesh from outward-CCW vertex triples
void tri_mesh(const std::vector<std::array<int, 3>>& tris, Topo& t) {
  const size_t n = tris.size();
  t.adj.assign(n, {-1, -1, -1, -1});
  t.aedge.assign(n, {0, 0, 0, 0});
  for (size_t f = 0; f < n; ++f) for (int e = 0; e < 3; ++e) {
    int a = tris[f][e], b = tris[f][(e + 1) % 3];
    for (size_t g = 0; g < n; ++g) for (int ge = 0; ge < 3; ++ge)
      if (g != f && tris[g][ge] == b && tris[g][(ge + 1) % 3] == a) { t.adj[f][e] = int(g); t.aedge[f][e] = ge; }
  }
}

// closed quad mesh from outward-CCW vertex quads (edge e runs v[e] -> v[e+1])
void quad_mesh(const std::vector<std::array<int, 4>>& q, Topo& t) {
  const size_t n = q.size();
  t.adj.assign(n, {-1, -1, -1, -1});
  t.aedge.assign(n, {0, 0, 0, 0});
  for (size_t f = 0; f < n; ++f) for (int e = 0; e < 4; ++e) {
    int a = q[f][e], b = q[f][(e + 1) % 4];
    for (size_t g = 0; g < n; ++g) for (int ge = 0; ge < 4; ++ge)
      if (g != f && q[g][ge] == b && q[g][(ge + 1) % 4] == a) { t.adj[f][e] = int(g); t.aedge[f][e] = ge; }
  }
}

struct Cfg { int mt, dt, nch; bool mips; int ub, vb, efm; };

bool write_mesh(const std::string& path, const Cfg& c, const Topo& t, std::vector<int>* ulogs) {
  Ptex::String err;
  const int n = int(t.adj.size());
  PtexWriter* w = PtexWriter::open(path.c_str(), c.mt ? Ptex::mt_quad : Ptex::mt_triangle, Ptex::DataType(c.dt), c.nch, -1, n, err, c.mips);
  if (!w) { std::printf("writer: %s\n", err.c_str()); return false; }
  w->setBorderModes(Ptex::BorderMode(c.ub), Ptex::BorderMode(c.vb));
  w->setEdgeFilterMode(Ptex::EdgeFilterMode(c.efm));
  for (int f = 0; f < n; ++f) {
    int ul = 1 + int(rnd() % 6), vl = c.mt ? 1 + int(rnd() % 6) : ul;
    const Ptex::Res fr((int8_t)ul, (int8_t)vl);
    Ptex::FaceInfo fi(fr);
    fi.setadjfaces(t.adj[f][0], t.adj[f][1], t.adj[f][2], t.adj[f][3]);
    fi.setadjedges(t.aedge[f][0], t.aedge[f][1], t.aedge[f][2], t.aedge[f][3]);
    std::vector<uint8_t> px;
    const int kind = int(rnd() % 5);
    if (kind == 0) {
      std::vector<uint8_t> one; fill(one, c.dt, 1, c.nch, 1, 0);
      std::vector<uint8_t> big; const size_t ps = one.size();
      big.resize(ps << (ul + vl));
      for (size_t i = 0; i < (size_t(1) << (ul + vl)); ++i) std::memcpy(&big[i * ps], one.data(), ps);
      w->writeConstantFace(f, fi, one.data());
    } else {
      fill(px, c.dt, size_t(1) << (ul + vl), c.nch, kind == 1 ? 0 : 1, uint32_t(f * 13));
      w->writeFace(f, fi, px.data(), 0);
    }
  }
  bool ok = w->close(err);
  w->release();
  (void)ulogs;
  return ok;
}

void run(const std::string& path, const Cfg& c, const char* tag, int nfaces) {
  Ptex::String err;
  PtexTexture* up = PtexTexture::open(path.c_str(), err, false);
  if (!up) { std::printf("%s: upstream open failed\n", tag); ++g_fail; return; }
  FILE* fp = std::fopen(path.c_str(), "rb");
  std::vector<uint8_t> file; std::fseek(fp, 0, SEEK_END); file.resize(size_t(std::ftell(fp))); std::fseek(fp, 0, SEEK_SET);
  if (std::fread(file.data(), 1, file.size(), fp) != file.size()) ++g_fail;
  std::fclose(fp);
  tptex_texture* t = nullptr;
  if (tptex_open_memory(file.data(), file.size(), nullptr, &t) != TPTEX_OK) { std::printf("%s: tptex open failed\n", tag); ++g_fail; up->release(); return; }

  const PtexFilter::FilterType types[] = {PtexFilter::f_point, PtexFilter::f_bilinear, PtexFilter::f_box, PtexFilter::f_gaussian, PtexFilter::f_bicubic, PtexFilter::f_bspline, PtexFilter::f_catmullrom, PtexFilter::f_mitchell};
  const char* tn[] = {"point", "bilinear", "box", "gaussian", "bicubic", "bspline", "catmullrom", "mitchell"};
  for (int ft = 0; ft < 8; ++ft) {
    if (!c.mt && ft != 0 && ft != 2) continue;   // triangle meshes: point + (any other = triangle filter)
    for (int variant = 0; variant < 4; ++variant) {
      const bool lerp = variant & 1, noedge = variant & 2;
      PtexFilter::Options uo(types[ft], lerp, 0.3f, noedge);
      PtexFilter* uf = PtexFilter::getFilter(up, uo);
      tptex_filter_options to; tptex_filter_options_init(&to);
      to.filter = tptex_filter_type(ft); to.lerp = lerp; to.sharpness = 0.3f; to.noedgeblend = noedge;
      tptex_filter* tf = nullptr;
      if (tptex_filter_create(t, &to, &tf) != TPTEX_OK) { ++g_fail; uf->release(); continue; }
      for (int it = 0; it < 60; ++it) {
        const int face = int(rnd() % nfaces);
        float u = frand(), v = frand();
        if ((rnd() & 3) == 0 && c.ub != 1 && c.vb != 1) {   // upstream is UB for a black-border kernel wholly outside a face
          u = frand() * 1.4f - 0.2f; v = frand() * 1.4f - 0.2f; }
        const float wd = std::pow(10.0f, -4.0f * frand());          // 1e-4 .. 1
        const float ang = frand() * 6.2831853f;
        float uw1 = wd * std::cos(ang), vw1 = wd * std::sin(ang);
        float uw2 = -vw1 * 0.5f * frand(), vw2 = uw1 * 0.5f * frand();
        float blur = (rnd() & 1) ? 0.0f : frand() * 0.02f;
        const int nchan = c.nch;
        float ra[8] = {0}, rb[8] = {0};
        if (std::getenv("CMP_VERBOSE")) { std::fprintf(stderr, "%s %s v%d face %d u %.9g v %.9g uw1 %.9g vw1 %.9g uw2 %.9g vw2 %.9g blur %.9g\n", tag, tn[ft], variant, face, u, v, uw1, vw1, uw2, vw2, blur); }
        uf->eval(ra, 0, nchan, face, u, v, uw1, vw1, uw2, vw2, 1.0f, blur);
        tptex_status st = tptex_filter_eval(tf, rb, 0, nchan, face, u, v, uw1, vw1, uw2, vw2, 1.0f, blur);
        ++g_checks;
        if (st != TPTEX_OK) { ++g_errs; if (g_fail++ < 30) std::printf("%s %s v%d: status %s (face %d u %.4f v %.4f w %.5f)\n", tag, tn[ft], variant, tptex_status_str(st), face, u, v, wd); continue; }
        double worst = 0;
        for (int i = 0; i < nchan; ++i) worst = std::fmax(worst, std::fabs(double(ra[i]) - double(rb[i])) / std::fmax(1.0, std::fabs(double(ra[i]))));
        if (worst > g_worst) g_worst = worst;
        if (!(worst <= 2e-5)) { if (g_fail++ < 30) std::printf("%s %s v%d: face %d u %.4f v %.4f w %.5f blur %.4f: err %.3g (up %.6f tptex %.6f)\n", tag, tn[ft], variant, face, u, v, wd, blur, worst, ra[0], rb[0]); }
      }
      tptex_filter_destroy(tf);
      uf->release();
    }
  }
  tptex_close(t);
  up->release();
}
}  // namespace

int main(int argc, char** argv) {
  const std::string dir = argc > 1 ? argv[1] : ".";
  int n = 0;
  for (int dt = 0; dt < 4; ++dt)
    for (int nch : {1, 3})
      for (int mips = 0; mips < 2; ++mips)
        for (int bm = 0; bm < 3; ++bm) {
          Cfg c{1, dt, nch, mips != 0, bm, (bm + 1) % 3, bm & 1};
          Topo t; grid(4, 3, t);
          char tag[96]; std::snprintf(tag, sizeof tag, "quad dt=%d nch=%d mips=%d border=%d", dt, nch, mips, bm);
          std::string p = dir + "/cf_" + std::to_string(n++) + ".ptx";
          if (!write_mesh(p, c, t, nullptr)) { ++g_fail; continue; }
          run(p, c, tag, 12);
          std::remove(p.c_str());
        }
  for (int dt = 0; dt < 4; dt += 1)
    for (int mips = 0; mips < 2; ++mips) {   // cube: rotated adjacency + valence-3 corners
      Cfg c{1, dt, 3, mips != 0, 0, 0, dt & 1};
      Topo t; quad_mesh({{0, 3, 2, 1}, {4, 5, 6, 7}, {0, 1, 5, 4}, {1, 2, 6, 5}, {2, 3, 7, 6}, {3, 0, 4, 7}}, t);
      char tag[96]; std::snprintf(tag, sizeof tag, "cube dt=%d mips=%d", dt, mips);
      std::string p = dir + "/cf_" + std::to_string(n++) + ".ptx";
      if (!write_mesh(p, c, t, nullptr)) { ++g_fail; continue; }
      run(p, c, tag, 6);
      std::remove(p.c_str());
    }
  for (int dt = 0; dt < 4; ++dt)
    for (int mips = 0; mips < 2; ++mips) {
      Cfg c{0, dt, 3, mips != 0, 0, 0, 0};
      Topo t; tri_mesh({{0, 1, 2}, {0, 3, 1}, {1, 3, 2}, {0, 2, 3}}, t);   // tetrahedron
      char tag[96]; std::snprintf(tag, sizeof tag, "tri dt=%d mips=%d", dt, mips);
      std::string p = dir + "/cf_" + std::to_string(n++) + ".ptx";
      if (!write_mesh(p, c, t, nullptr)) { ++g_fail; continue; }
      run(p, c, tag, 4);
      std::remove(p.c_str());
    }
  std::printf("cmp_filter: %d meshes, %llu evals, %llu failures (%llu errors), worst rel err %.3g\n", n,
              (unsigned long long)g_checks, (unsigned long long)g_fail, (unsigned long long)g_errs, g_worst);
  return g_fail ? 1 : 0;
}
