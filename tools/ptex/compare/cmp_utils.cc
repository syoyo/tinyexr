// SPDX-License-Identifier: BSD-3-Clause
// Differential test: tptex utils vs upstream PtexUtils, byte-for-byte, on random
// data (finite values only, so NaN payload propagation cannot differ by operand
// order) across all data types, channel counts, sizes and padded strides.
#include <cstdint>
#include <cstdio>
#include <cstring>
#include <vector>

#include "PtexUtils.h"
extern "C" {
#include "tptex_utils.h"
#include "tptex_half.h"
}

namespace {
uint32_t g_rng = 0x2545f491u;
uint32_t rnd() { g_rng ^= g_rng << 13; g_rng ^= g_rng >> 17; g_rng ^= g_rng << 5; return g_rng; }
float frand() { return float(rnd() >> 8) * (1.0f / 16777216.0f); }

Ptex::DataType up(tptex_data_type t) { return static_cast<Ptex::DataType>(t); }
const tptex_data_type kTypes[] = {TPTEX_UINT8, TPTEX_UINT16, TPTEX_HALF, TPTEX_FLOAT};
const char* kNames[] = {"u8", "u16", "half", "float"};

uint64_t g_fail = 0, g_cases = 0;
void report(const char* what, tptex_data_type dt, int nc, int u, int v, size_t off) {
  if (g_fail++ < 20)
    std::printf("MISMATCH %s dt=%s nchan=%d %dx%d first diff at byte %zu\n", what,
                kNames[dt], nc, u, v, off);
}
bool same(const std::vector<uint8_t>& a, const std::vector<uint8_t>& b, size_t* at) {
  for (size_t i = 0; i < a.size(); ++i) if (a[i] != b[i]) { *at = i; return false; }
  return true;
}

// finite random pixels of a type, `n` elements
void fill_random(std::vector<uint8_t>& buf, tptex_data_type dt, size_t n) {
  const size_t es = tptex_data_type_size(dt);
  buf.assign(n * es, 0);
  for (size_t i = 0; i < n; ++i) {
    uint8_t* p = &buf[i * es];
    switch (dt) {
      case TPTEX_UINT8: *p = uint8_t(rnd()); break;
      case TPTEX_UINT16: { uint16_t v = uint16_t(rnd()); std::memcpy(p, &v, 2); break; }
      case TPTEX_HALF: { uint16_t v; do v = uint16_t(rnd()); while (((v >> 10) & 31) == 31); std::memcpy(p, &v, 2); break; }
      case TPTEX_FLOAT: { float f = (frand() - 0.5f) * 2000.0f; if ((rnd() & 15) == 0) f = 0.0f; std::memcpy(p, &f, 4); break; }
    }
  }
}
}  // namespace

int main() {
  const int sizes[] = {2, 4, 8, 16, 32};
  const int nchans[] = {1, 2, 3, 4, 5, 8};
  for (int ti = 0; ti < 4; ++ti) {
    const tptex_data_type dt = kTypes[ti];
    const size_t es = tptex_data_type_size(dt);
    for (int nc : nchans)
      for (int u : sizes)
        for (int v : sizes)
          for (int pad = 0; pad < 2; ++pad) {
            const size_t rowbytes = size_t(u) * nc * es;
            const size_t stride = rowbytes + (pad ? 2 * es * 3 : 0);
            std::vector<uint8_t> src;
            fill_random(src, dt, (stride / es) * size_t(v));
            size_t at = 0;
            ++g_cases;

            // reduce / reduceu / reducev
            {
              const int ou = u / 2, ov = v / 2;
              std::vector<uint8_t> a(size_t(ou) * ov * nc * es, 0xAA), b = a;
              Ptex::PtexUtils::reduce(src.data(), int(stride), u, v, a.data(), int(ou * nc * es), up(dt), nc);
              tptex_reduce(src.data(), stride, u, v, b.data(), size_t(ou) * nc * es, dt, nc);
              if (!same(a, b, &at)) report("reduce", dt, nc, u, v, at);
              std::vector<uint8_t> a2(size_t(ou) * v * nc * es, 0xAA), b2 = a2;
              Ptex::PtexUtils::reduceu(src.data(), int(stride), u, v, a2.data(), int(ou * nc * es), up(dt), nc);
              tptex_reduce_u(src.data(), stride, u, v, b2.data(), size_t(ou) * nc * es, dt, nc);
              if (!same(a2, b2, &at)) report("reduceu", dt, nc, u, v, at);
              std::vector<uint8_t> a3(size_t(u) * ov * nc * es, 0xAA), b3 = a3;
              Ptex::PtexUtils::reducev(src.data(), int(stride), u, v, a3.data(), int(u * nc * es), up(dt), nc);
              tptex_reduce_v(src.data(), stride, u, v, b3.data(), size_t(u) * nc * es, dt, nc);
              if (!same(a3, b3, &at)) report("reducev", dt, nc, u, v, at);
            }
            // reduceTri needs a square face
            if (u == v) {
              const int o = u / 2;
              std::vector<uint8_t> a(size_t(o) * o * nc * es, 0xAA), b = a;
              Ptex::PtexUtils::reduceTri(src.data(), int(stride), u, v, a.data(), int(o * nc * es), up(dt), nc);
              tptex_reduce_tri(src.data(), stride, u, b.data(), size_t(o) * nc * es, dt, nc);
              if (!same(a, b, &at)) report("reduceTri", dt, nc, u, v, at);
            }
            // average
            {
              std::vector<uint8_t> a(nc * es, 0xAA), b = a;
              Ptex::PtexUtils::average(src.data(), int(stride), u, v, a.data(), up(dt), nc);
              tptex_average(src.data(), stride, u, v, b.data(), dt, nc);
              if (!same(a, b, &at)) report("average", dt, nc, u, v, at);
            }
            // blend (weights in [0,1] so integer narrowing stays defined), both flips
            for (int flip = 0; flip < 2; ++flip) {
              std::vector<uint8_t> a, b;
              fill_random(a, dt, size_t(u) * nc);
              b = a;
              const float w = frand();
              Ptex::PtexUtils::blend(src.data(), w, a.data(), flip != 0, u, up(dt), nc);
              tptex_blend(src.data(), w, b.data(), flip, u, dt, nc);
              if (!same(a, b, &at)) report(flip ? "blendflip" : "blend", dt, nc, u, v, at);
            }
            // interleave / deinterleave (planar<->interleaved)
            {
              std::vector<uint8_t> planar;
              fill_random(planar, dt, size_t(nc) * u * v);
              std::vector<uint8_t> a(size_t(u) * v * nc * es, 0xAA), b = a;
              Ptex::PtexUtils::interleave(planar.data(), int(u * es), u, v, a.data(), int(u * nc * es), up(dt), nc);
              tptex_interleave(planar.data(), size_t(u) * es, u, v, b.data(), size_t(u) * nc * es, dt, nc);
              if (!same(a, b, &at)) report("interleave", dt, nc, u, v, at);
              std::vector<uint8_t> c(planar.size(), 0xAA), d = c;
              Ptex::PtexUtils::deinterleave(a.data(), int(u * nc * es), u, v, c.data(), int(u * es), up(dt), nc);
              tptex_deinterleave(a.data(), size_t(u) * nc * es, u, v, d.data(), size_t(u) * es, dt, nc);
              if (!same(c, d, &at)) report("deinterleave", dt, nc, u, v, at);
            }
            // difference codec
            {
              std::vector<uint8_t> a, b;
              fill_random(a, dt, size_t(u) * v * nc);
              b = a;
              Ptex::PtexUtils::encodeDifference(a.data(), int(a.size()), up(dt));
              tptex_encode_difference(b.data(), b.size(), dt);
              if (!same(a, b, &at)) report("encodeDifference", dt, nc, u, v, at);
              Ptex::PtexUtils::decodeDifference(a.data(), int(a.size()), up(dt));
              tptex_decode_difference(b.data(), b.size(), dt);
              if (!same(a, b, &at)) report("decodeDifference", dt, nc, u, v, at);
            }
            // alpha: for integer types keep colour <= alpha so un-premultiply stays in range
            if (nc >= 2) {
              for (int ac : {0, nc - 1}) {
                std::vector<uint8_t> a;
                fill_random(a, dt, size_t(u) * nc);
                if (dt == TPTEX_UINT8)
                  for (int p = 0; p < u; ++p)
                    for (int c = 0; c < nc; ++c)
                      if (c != ac && a[size_t(p) * nc + c] > a[size_t(p) * nc + ac]) a[size_t(p) * nc + c] = a[size_t(p) * nc + ac];
                std::vector<uint8_t> b = a;
                Ptex::PtexUtils::multalpha(a.data(), u, up(dt), nc, ac);
                tptex_multalpha(b.data(), u, dt, nc, ac);
                if (!same(a, b, &at)) report("multalpha", dt, nc, u, v, at);
                if (dt == TPTEX_FLOAT || dt == TPTEX_HALF) {  // premultiplied -> divide back
                  Ptex::PtexUtils::divalpha(a.data(), u, up(dt), nc, ac);
                  tptex_divalpha(b.data(), u, dt, nc, ac);
                  if (!same(a, b, &at)) report("divalpha", dt, nc, u, v, at);
                }
              }
            }
            // apply const + conversions
            {
              std::vector<uint8_t> px;
              fill_random(px, dt, size_t(nc));
              std::vector<float> fa(nc, 1.5f), fb(nc, 1.5f);
              const float w = frand();
              Ptex::PtexUtils::applyConst(w, fa.data(), px.data(), up(dt), nc);
              tptex_apply_const(w, fb.data(), px.data(), dt, nc);
              if (std::memcmp(fa.data(), fb.data(), nc * 4) != 0) report("applyConst", dt, nc, u, v, 0);
              std::vector<float> ta(nc), tb(nc);
              Ptex::ConvertToFloat(ta.data(), px.data(), up(dt), nc);
              tptex_convert_to_float(tb.data(), px.data(), dt, nc);
              if (std::memcmp(ta.data(), tb.data(), nc * 4) != 0) report("convertToFloat", dt, nc, u, v, 0);
              std::vector<float> fv(nc);
              for (int i = 0; i < nc; ++i) fv[i] = (frand() - 0.25f) * 1.8f;
              std::vector<uint8_t> ca(nc * es, 0xAA), cb = ca;
              Ptex::ConvertFromFloat(ca.data(), fv.data(), up(dt), nc);
              tptex_convert_from_float(cb.data(), fv.data(), dt, nc);
              if (!same(ca, cb, &at)) report("convertFromFloat", dt, nc, u, v, at);
            }
          }
  }

  // genRfaceids: random face infos incl. constant flags and ties
  for (int trial = 0; trial < 200; ++trial) {
    const int n = 1 + int(rnd() % 300);
    std::vector<Ptex::FaceInfo> uf(n);
    std::vector<tptex_face_info> tf(n);
    for (int i = 0; i < n; ++i) {
      const int ul = int(rnd() % 11), vl = int(rnd() % 11);
      uf[i] = Ptex::FaceInfo(Ptex::Res(int8_t(ul), int8_t(vl)));
      if ((rnd() & 7) == 0) uf[i].flags |= Ptex::FaceInfo::flag_constant;
      tf[i].res = tptex_make_res(ul, vl);
      tf[i].adjedges = 0;
      tf[i].flags = uf[i].flags;
      for (int e = 0; e < 4; ++e) tf[i].adjfaces[e] = -1;
    }
    std::vector<uint32_t> ur(n), ui(n), tr(n), ti2(n);
    Ptex::PtexUtils::genRfaceids(uf.data(), n, ur.data(), ui.data());
    tptex_gen_rfaceids(tf.data(), uint32_t(n), tr.data(), ti2.data());
    ++g_cases;
    if (ur != tr || ui != ti2) { if (g_fail++ < 20) std::printf("MISMATCH genRfaceids n=%d\n", n); }
  }

  std::printf("cmp_utils: %llu cases, %llu mismatches\n", (unsigned long long)g_cases,
              (unsigned long long)g_fail);
  return g_fail ? 1 : 0;
}
