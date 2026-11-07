// SPDX-License-Identifier: BSD-3-Clause
// Exhaustive half <-> float identity of tptex against the real upstream PtexHalf.
// Sweeps all 65536 half values and all 2^32 float bit patterns.
#include <cstdint>
#include <cstdio>
#include <cstring>

#include "PtexHalf.h"
extern "C" {
#include "tptex_half.h"
}

int main() {
  uint64_t bad = 0;
  for (uint32_t h = 0; h < 65536u; ++h) {
    const float up = Ptex::PtexHalf::toFloat(static_cast<uint16_t>(h));
    uint32_t upbits;
    std::memcpy(&upbits, &up, sizeof upbits);
    if (upbits != tptex_half_to_float_bits(static_cast<uint16_t>(h))) {
      if (bad++ < 8) std::printf("h2f mismatch 0x%04x\n", h);
    }
  }
  uint32_t bits = 0;
  do {
    float f;
    std::memcpy(&f, &bits, sizeof f);
    if (Ptex::PtexHalf::fromFloat(f) != tptex_float_bits_to_half(bits)) {
      if (bad++ < 8) std::printf("f2h mismatch 0x%08x\n", bits);
    }
    ++bits;
  } while (bits != 0u);
  std::printf("cmp_half: %llu mismatches\n", static_cast<unsigned long long>(bad));
  return bad ? 1 : 0;
}
