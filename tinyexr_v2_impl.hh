// SPDX-License-Identifier: BSD-3-Clause
// Copyright (c) 2025, Syoyo Fujita and many contributors.
// All rights reserved.
//
// TinyEXR V2 Implementation

#ifndef TINYEXR_V2_IMPL_HH_
#define TINYEXR_V2_IMPL_HH_

#include "tinyexr_v2.hh"
#include <cstring>
#include <cstdio>
#include <cmath>
#include <algorithm>

// Include compression library
#if defined(TINYEXR_USE_MINIZ) && TINYEXR_USE_MINIZ
#if __has_include("miniz.h")
#include "miniz.h"
#elif __has_include("deps/miniz/miniz.h")
#include "deps/miniz/miniz.h"
#endif
#elif defined(TINYEXR_USE_ZLIB) && TINYEXR_USE_ZLIB
#include <zlib.h>
#endif

// ============================================================================
// Decompression backend configuration
// ============================================================================
//
// V2 API decompression backend priority:
//   1. TINYEXR_V2_USE_CUSTOM_DEFLATE (default=1) - Custom SIMD-optimized deflate
//   2. TINYEXR_USE_ZLIB - System zlib
//   3. TINYEXR_USE_MINIZ - Miniz (bundled)
//
// To use system zlib instead of custom deflate:
//   #define TINYEXR_V2_USE_CUSTOM_DEFLATE 0
//   #define TINYEXR_USE_ZLIB 1
//
// To use miniz instead of custom deflate:
//   #define TINYEXR_V2_USE_CUSTOM_DEFLATE 0
//   #define TINYEXR_USE_MINIZ 1

// Default: use custom SIMD-optimized deflate
#ifndef TINYEXR_V2_USE_CUSTOM_DEFLATE
#define TINYEXR_V2_USE_CUSTOM_DEFLATE 1
#endif

// Custom deflate uses tinyexr_huffman.hh
#if TINYEXR_V2_USE_CUSTOM_DEFLATE
#include "tinyexr_huffman.hh"
#include "tinyexr_piz.hh"
#endif

// Fallback: miniz or zlib for when custom deflate is disabled
#if !TINYEXR_V2_USE_CUSTOM_DEFLATE
#if !defined(TINYEXR_USE_MINIZ) && !defined(TINYEXR_USE_ZLIB)
// Default to zlib if available, otherwise miniz
#if defined(__has_include)
#if __has_include(<zlib.h>)
#define TINYEXR_USE_ZLIB 1
#define TINYEXR_USE_MINIZ 0
#else
#define TINYEXR_USE_ZLIB 0
#define TINYEXR_USE_MINIZ 1
#endif
#else
#define TINYEXR_USE_ZLIB 1
#define TINYEXR_USE_MINIZ 0
#endif
#endif

#if TINYEXR_USE_MINIZ
#include "miniz.h"
#elif TINYEXR_USE_ZLIB
#include <zlib.h>
#endif
#endif

namespace tinyexr {
namespace v2 {

// ============================================================================
// Tile level mode constants
// ============================================================================

enum TileLevelMode {
  TILE_ONE_LEVEL = 0,
  TILE_MIPMAP_LEVELS = 1,
  TILE_RIPMAP_LEVELS = 2
};

enum TileRoundingMode {
  TILE_ROUND_DOWN = 0,
  TILE_ROUND_UP = 1
};

// ============================================================================
// Compression constants
// ============================================================================

enum CompressionType {
  COMPRESSION_NONE = 0,
  COMPRESSION_RLE = 1,
  COMPRESSION_ZIPS = 2,  // ZIP single scanline
  COMPRESSION_ZIP = 3,   // ZIP 16 scanlines
  COMPRESSION_PIZ = 4,
  COMPRESSION_PXR24 = 5,
  COMPRESSION_B44 = 6,
  COMPRESSION_B44A = 7,
  COMPRESSION_DWAA = 8,
  COMPRESSION_DWAB = 9
  COMPRESSION_HTJ2K256 = 10
  COMPRESSION_HTJ2K32 = 11
  COMPRESSION_ZSTD = 12
};

// Pixel types
enum PixelType {
  PIXEL_TYPE_UINT = 0,
  PIXEL_TYPE_HALF = 1,
  PIXEL_TYPE_FLOAT = 2
};

// ============================================================================
// Helper: RLE decompression (from OpenEXR)
// ============================================================================

static int rleUncompress(int inLength, int maxLength,
                         const signed char* in, char* out) {
  char* outStart = out;
  const char* outEnd = out + maxLength;
  const signed char* inEnd = in + inLength;

  while (in < inEnd) {
    if (*in < 0) {
      int count = -static_cast<int>(*in++);
      if (out + count > outEnd) return 0;
      if (in + count > inEnd) return 0;
      std::memcpy(out, in, static_cast<size_t>(count));
      out += count;
      in += count;
    } else {
      int count = static_cast<int>(*in++) + 1;
      if (out + count > outEnd) return 0;
      if (in >= inEnd) return 0;
      std::memset(out, *in++, static_cast<size_t>(count));
      out += count;
    }
  }
  return static_cast<int>(out - outStart);
}

// ============================================================================
// Helper: Decompression functions
// ============================================================================

static bool DecompressZipV2(uint8_t* dst, size_t* uncompressed_size,
                            const uint8_t* src, size_t src_size,
                            ScratchPool& pool) {
  if (*uncompressed_size == src_size) {
    // Not compressed
    std::memcpy(dst, src, src_size);
    return true;
  }

  uint8_t* tmpBuf = pool.get_buffer(*uncompressed_size);

#if TINYEXR_V2_USE_CUSTOM_DEFLATE
  // Use custom SIMD-optimized deflate decoder
  tinyexr::huffman::dfl::DeflateOptions opts;
  opts.max_output_size = *uncompressed_size;
  auto result = tinyexr::huffman::dfl::inflate_zlib_safe(
      src, src_size, tmpBuf, *uncompressed_size, opts);
  if (!result.success) {
    return false;
  }
  *uncompressed_size = result.bytes_written;
#elif TINYEXR_USE_MINIZ
  mz_ulong dest_len = static_cast<mz_ulong>(*uncompressed_size);
  int ret = mz_uncompress(tmpBuf, &dest_len, src, static_cast<mz_ulong>(src_size));
  if (ret != MZ_OK) {
    return false;
  }
  *uncompressed_size = static_cast<size_t>(dest_len);
#elif TINYEXR_USE_ZLIB
  uLongf dest_len = static_cast<uLongf>(*uncompressed_size);
  int ret = uncompress(tmpBuf, &dest_len, src, static_cast<uLong>(src_size));
  if (ret != Z_OK) {
    return false;
  }
  *uncompressed_size = static_cast<size_t>(dest_len);
#else
  // Fallback - no decompression backend available
  (void)tmpBuf; (void)src; (void)src_size;
  return false;
#endif

  // Predictor (using optimized version if available)
#if defined(TINYEXR_ENABLE_SIMD) && TINYEXR_ENABLE_SIMD
  tinyexr::simd::apply_delta_predictor_fast(tmpBuf, *uncompressed_size);
#else
  if (*uncompressed_size > 1) {
    uint8_t* t = tmpBuf + 1;
    uint8_t* stop = tmpBuf + *uncompressed_size;
    while (t < stop) {
      int d = static_cast<int>(t[-1]) + static_cast<int>(t[0]) - 128;
      t[0] = static_cast<uint8_t>(d);
      ++t;
    }
  }
#endif

  // Reorder (using optimized version if available)
#if defined(TINYEXR_ENABLE_SIMD) && TINYEXR_ENABLE_SIMD
  tinyexr::simd::unreorder_bytes_after_decompression(tmpBuf, dst, *uncompressed_size);
#else
  {
    const uint8_t* t1 = tmpBuf;
    const uint8_t* t2 = tmpBuf + (*uncompressed_size + 1) / 2;
    uint8_t* s = dst;
    uint8_t* stop = s + *uncompressed_size;
    while (s < stop) {
      if (s < stop) *s++ = *t1++;
      if (s < stop) *s++ = *t2++;
    }
  }
#endif

  return true;
}

static bool DecompressRleV2(uint8_t* dst, size_t uncompressed_size,
                            const uint8_t* src, size_t src_size,
                            ScratchPool& pool) {
  if (uncompressed_size == src_size) {
    std::memcpy(dst, src, src_size);
    return true;
  }

  if (src_size <= 2) {
    return false;
  }

  uint8_t* tmpBuf = pool.get_buffer(uncompressed_size);

  int ret = rleUncompress(static_cast<int>(src_size),
                          static_cast<int>(uncompressed_size),
                          reinterpret_cast<const signed char*>(src),
                          reinterpret_cast<char*>(tmpBuf));
  if (ret != static_cast<int>(uncompressed_size)) {
    return false;
  }

  // Predictor
#if defined(TINYEXR_ENABLE_SIMD) && TINYEXR_ENABLE_SIMD
  tinyexr::simd::apply_delta_predictor_fast(tmpBuf, uncompressed_size);
#else
  if (uncompressed_size > 1) {
    uint8_t* t = tmpBuf + 1;
    uint8_t* stop = tmpBuf + uncompressed_size;
    while (t < stop) {
      int d = static_cast<int>(t[-1]) + static_cast<int>(t[0]) - 128;
      t[0] = static_cast<uint8_t>(d);
      ++t;
    }
  }
#endif

  // Reorder
#if defined(TINYEXR_ENABLE_SIMD) && TINYEXR_ENABLE_SIMD
  tinyexr::simd::unreorder_bytes_after_decompression(tmpBuf, dst, uncompressed_size);
#else
  {
    const uint8_t* t1 = tmpBuf;
    const uint8_t* t2 = tmpBuf + (uncompressed_size + 1) / 2;
    uint8_t* s = dst;
    uint8_t* stop = s + uncompressed_size;
    while (s < stop) {
      if (s < stop) *s++ = *t1++;
      if (s < stop) *s++ = *t2++;
    }
  }
#endif

  return true;
}

// ============================================================================
// Helper: FP16 to FP32 conversion
// ============================================================================

static float HalfToFloat(uint16_t h) {
#if defined(TINYEXR_ENABLE_SIMD) && TINYEXR_ENABLE_SIMD
  return tinyexr::simd::half_to_float_scalar(h);
#else
  union { uint32_t u; float f; } o;
  static const union { uint32_t u; float f; } magic = {113U << 23};
  static const uint32_t shifted_exp = 0x7c00U << 13;

  o.u = (h & 0x7fffU) << 13;
  uint32_t exp_ = shifted_exp & o.u;
  o.u += (127 - 15) << 23;

  if (exp_ == shifted_exp) {
    o.u += (128 - 16) << 23;
  } else if (exp_ == 0) {
    o.u += 1 << 23;
    o.f -= magic.f;
  }

  o.u |= (h & 0x8000U) << 16;
  return o.f;
#endif
}

// ============================================================================
// PXR24 decompression
// ============================================================================

// PXR24 stores 32-bit floats as 24-bit values (truncates 8 mantissa bits)
// Then applies zlib compression
static bool DecompressPxr24V2(uint8_t* dst, size_t expected_size,
                              const uint8_t* src, size_t src_size,
                              int width, int num_lines,
                              int num_channels, const Channel* channels,
                              ScratchPool& pool) {
  // First, calculate the compressed data size (before zlib expansion)
  // PXR24 stores HALF as 2 bytes, UINT as 4 bytes, FLOAT as 3 bytes
  size_t pxr24_size = 0;
  for (int c = 0; c < num_channels; c++) {
    int ch_width = width / channels[c].x_sampling;
    int ch_height = num_lines / channels[c].y_sampling;
    int ch_pixels = ch_width * ch_height;

    switch (channels[c].pixel_type) {
      case PIXEL_TYPE_UINT:  pxr24_size += static_cast<size_t>(ch_pixels) * 4; break;
      case PIXEL_TYPE_HALF:  pxr24_size += static_cast<size_t>(ch_pixels) * 2; break;
      case PIXEL_TYPE_FLOAT: pxr24_size += static_cast<size_t>(ch_pixels) * 3; break;
    }
  }

  // Allocate buffer for zlib-decompressed PXR24 data
  std::vector<uint8_t> pxr24_buf(pxr24_size);
  size_t uncomp_size = pxr24_size;

  // Note: PXR24 uses raw zlib compression without predictor/reorder
  // So we use direct zlib decompression instead of DecompressZipV2
  // (which applies predictor and reorder for standard ZIP format)
  if (pxr24_size == src_size) {
    // Uncompressed - copy directly
    std::memcpy(pxr24_buf.data(), src, src_size);
  } else {
#if TINYEXR_USE_MINIZ
    mz_ulong dest_len = static_cast<mz_ulong>(pxr24_size);
    int ret = mz_uncompress(pxr24_buf.data(), &dest_len, src, static_cast<mz_ulong>(src_size));
    if (ret != MZ_OK) {
      return false;
    }
    uncomp_size = static_cast<size_t>(dest_len);
#elif TINYEXR_USE_ZLIB
    uLongf dest_len = static_cast<uLongf>(pxr24_size);
    int ret = uncompress(pxr24_buf.data(), &dest_len, src, static_cast<uLong>(src_size));
    if (ret != Z_OK) {
      return false;
    }
    uncomp_size = static_cast<size_t>(dest_len);
#else
    (void)pool;
    return false;
#endif
  }

  if (uncomp_size != pxr24_size) {
    return false;
  }

  // Now convert PXR24 format to standard EXR format
  // PXR24 organizes data by scanline, then by channel
  const uint8_t* in_ptr = pxr24_buf.data();
  uint8_t* out_ptr = dst;

  for (int line = 0; line < num_lines; line++) {
    for (int c = 0; c < num_channels; c++) {
      int ch_width = width / channels[c].x_sampling;

      // Check if this line contains data for this channel (accounting for y_sampling)
      if ((line % channels[c].y_sampling) != 0) continue;

      switch (channels[c].pixel_type) {
        case PIXEL_TYPE_UINT:
          // UINT stored as 4 bytes, copy directly
          for (int x = 0; x < ch_width; x++) {
            uint32_t val;
            std::memcpy(&val, in_ptr, 4);
            std::memcpy(out_ptr, &val, 4);
            in_ptr += 4;
            out_ptr += 4;
          }
          break;

        case PIXEL_TYPE_HALF:
          // HALF stored as 2 bytes, copy directly
          for (int x = 0; x < ch_width; x++) {
            uint16_t val;
            std::memcpy(&val, in_ptr, 2);
            std::memcpy(out_ptr, &val, 2);
            in_ptr += 2;
            out_ptr += 2;
          }
          break;

        case PIXEL_TYPE_FLOAT:
          // FLOAT stored as 24-bit (3 bytes), expand to 32-bit
          for (int x = 0; x < ch_width; x++) {
            // PXR24 stores the upper 24 bits of the float
            // (1 sign + 8 exponent + 15 mantissa)
            // We need to pad the lower 8 mantissa bits with zeros
            uint32_t val = 0;
            val |= (static_cast<uint32_t>(in_ptr[0]) << 24);
            val |= (static_cast<uint32_t>(in_ptr[1]) << 16);
            val |= (static_cast<uint32_t>(in_ptr[2]) << 8);
            // Lower 8 bits remain 0
            std::memcpy(out_ptr, &val, 4);
            in_ptr += 3;
            out_ptr += 4;
          }
          break;
      }
    }
  }

  return true;
}
// ============================================================================
// B44/B44A decompression
// ============================================================================

// B44 compresses 4x4 blocks of HALF values to 14 bytes
// B44A is similar but can compress flat regions to 3 bytes

// B44 Exp/Log Tables
// These tables convert between half-float and a 14-bit logarithmic representation
// where small integer differences correspond to small floating-point differences.
// This makes 6-bit delta encoding effective for typical image data.

// Half-float to 14-bit log table (generated at runtime, cached)
static uint16_t g_b44_exp_table[65536];
// 14-bit log to half-float table
static uint16_t g_b44_log_table[16384];
static bool g_b44_tables_initialized = false;

// Initialize B44 exp/log lookup tables
// Uses linear magnitude mapping: 15-bit magnitude -> 13-bit log per sign half
// This ensures proper range fitting and preserves sign information.
static void InitB44Tables() {
  if (g_b44_tables_initialized) return;

  // Generate expTable: half-float -> 14-bit log
  // Log space: 0-8191 for negative, 8192-16383 for positive
  // 15-bit magnitude (0-32767) maps to 13-bit range (0-8191) per half
  for (int i = 0; i < 65536; i++) {
    uint16_t h = static_cast<uint16_t>(i);

    if ((h & 0x7FFF) == 0) {
      // +0 or -0 -> center point
      g_b44_exp_table[i] = (h & 0x8000) ? 8191 : 8192;
    } else if ((h & 0x7C00) == 0x7C00) {
      // Inf or NaN - clamp to max/min
      g_b44_exp_table[i] = (h & 0x8000) ? 0 : 16383;
    } else {
      // Normal or denormal
      uint16_t magnitude = h & 0x7FFF;  // 15-bit magnitude (0-32767)

      // Map 15-bit magnitude to 13-bit range (0-8191) using >> 2
      uint16_t log_offset = magnitude >> 2;  // Now 0-8191

      if (h & 0x8000) {
        // Negative: map to 0-8191 (lower half, reversed)
        // Larger magnitude = smaller log value
        int log_val = 8191 - static_cast<int>(log_offset);
        if (log_val < 0) log_val = 0;
        g_b44_exp_table[i] = static_cast<uint16_t>(log_val);
      } else {
        // Positive: map to 8192-16383 (upper half)
        int log_val = 8192 + static_cast<int>(log_offset);
        if (log_val > 16383) log_val = 16383;
        g_b44_exp_table[i] = static_cast<uint16_t>(log_val);
      }
    }
  }

  // Generate logTable: 14-bit log -> half-float (inverse of above)
  for (int i = 0; i < 16384; i++) {
    if (i == 8192) {
      g_b44_log_table[i] = 0x0000;  // +0
    } else if (i == 8191) {
      g_b44_log_table[i] = 0x8000;  // -0
    } else if (i > 8192) {
      // Positive: log range 8193-16383 -> magnitude
      uint16_t log_offset = static_cast<uint16_t>(i - 8192);  // 1-8191
      uint16_t magnitude = log_offset << 2;  // Reverse the >> 2
      if (magnitude > 0x7BFF) magnitude = 0x7BFF;  // Clamp below inf
      g_b44_log_table[i] = magnitude;
    } else {
      // Negative: log range 0-8190 -> magnitude
      uint16_t log_offset = static_cast<uint16_t>(8191 - i);  // 1-8191
      uint16_t magnitude = log_offset << 2;
      if (magnitude > 0x7BFF) magnitude = 0x7BFF;
      g_b44_log_table[i] = 0x8000 | magnitude;
    }
  }

  g_b44_tables_initialized = true;
}

// Convert half-float to 14-bit log value
static inline uint16_t HalfToLog(uint16_t h) {
  return g_b44_exp_table[h];
}

// Convert 14-bit log value to half-float
static inline uint16_t LogToHalf(uint16_t log_val) {
  return g_b44_log_table[log_val & 0x3FFF];
}

// Unpack one 4x4 block from B44 compressed data
static void UnpackB44Block(uint16_t dst[16], const uint8_t src[14]) {
  // B44 packs 16 half values into 14 bytes using log-space delta encoding
  // Format: 2 bytes base (14-bit log) + 12 bytes for 15 6-bit deltas (90 bits)

  InitB44Tables();

  // Read 14-bit base value (big-endian, packed into 2 bytes)
  uint16_t base_log = (static_cast<uint16_t>(src[0]) << 8) | src[1];
  base_log &= 0x3FFF;  // 14-bit mask

  // First pixel uses base directly
  dst[0] = LogToHalf(base_log);

  // Decode the 15 6-bit deltas from remaining 12 bytes
  const uint8_t* delta_ptr = src + 2;
  int bit_pos = 0;

  for (int i = 1; i < 16; i++) {
    int byte_idx = bit_pos / 8;
    int bit_offset = bit_pos % 8;

    // Read 6 bits spanning potentially 2 bytes
    uint32_t bits = delta_ptr[byte_idx];
    if (byte_idx + 1 < 12) {
      bits |= (static_cast<uint32_t>(delta_ptr[byte_idx + 1]) << 8);
    }
    bits >>= bit_offset;
    bits &= 0x3F;  // 6 bits

    // Convert 6-bit unsigned to signed delta (-31 to +32)
    int delta = static_cast<int>(bits) - 31;

    // Apply delta in log space
    int result_log = static_cast<int>(base_log) + delta;
    if (result_log < 0) result_log = 0;
    if (result_log > 16383) result_log = 16383;

    // Convert back to half-float
    dst[i] = LogToHalf(static_cast<uint16_t>(result_log));

    bit_pos += 6;
  }
}

static bool DecompressB44V2(uint8_t* dst, size_t expected_size,
                            const uint8_t* src, size_t src_size,
                            int width, int num_lines,
                            int num_channels, const Channel* channels,
                            bool is_b44a, ScratchPool& pool) {
  (void)pool;

  // B44 only works with HALF pixel types
  // Each 4x4 block of HALF values compresses to:
  // - 14 bytes for regular blocks
  // - 3 bytes for flat blocks (B44A only)

  // Output layout: per-scanline interleaved
  // [Scanline0: Ch0_pixels | Ch1_pixels | ...][Scanline1: ...]

  const uint8_t* in_ptr = src;
  const uint8_t* in_end = src + src_size;

  // Calculate bytes per scanline for output layout
  size_t bytes_per_scanline = 0;
  for (int c = 0; c < num_channels; c++) {
    int ch_width = width / channels[c].x_sampling;
    bytes_per_scanline += static_cast<size_t>(ch_width) *
                          ((channels[c].pixel_type == PIXEL_TYPE_FLOAT) ? 4 :
                           (channels[c].pixel_type == PIXEL_TYPE_UINT) ? 4 : 2);
  }

  // Initialize output buffer
  std::memset(dst, 0, expected_size);

  // Process each channel
  for (int c = 0; c < num_channels; c++) {
    int ch_width = width / channels[c].x_sampling;
    int ch_height = num_lines / channels[c].y_sampling;

    // Calculate channel offset within each scanline
    size_t ch_offset = 0;
    for (int i = 0; i < c; i++) {
      int ch_w = width / channels[i].x_sampling;
      ch_offset += static_cast<size_t>(ch_w) *
                   ((channels[i].pixel_type == PIXEL_TYPE_FLOAT) ? 4 :
                    (channels[i].pixel_type == PIXEL_TYPE_UINT) ? 4 : 2);
    }

    if (channels[c].pixel_type != PIXEL_TYPE_HALF) {
      // Non-HALF channels are stored uncompressed
      size_t ch_size = static_cast<size_t>(ch_width) * ch_height *
                       (channels[c].pixel_type == PIXEL_TYPE_FLOAT ? 4 : 4);
      if (in_ptr + ch_size > in_end) return false;

      // Copy to per-scanline layout
      size_t pixel_size = (channels[c].pixel_type == PIXEL_TYPE_FLOAT) ? 4 : 4;
      for (int line = 0; line < num_lines; line++) {
        if ((line % channels[c].y_sampling) != 0) continue;

        uint8_t* line_ptr = dst + static_cast<size_t>(line) * bytes_per_scanline + ch_offset;
        std::memcpy(line_ptr, in_ptr, static_cast<size_t>(ch_width) * pixel_size);
        in_ptr += static_cast<size_t>(ch_width) * pixel_size;
      }
      continue;
    }

    // Process HALF channel in 4x4 blocks
    int num_blocks_x = (ch_width + 3) / 4;
    int num_blocks_y = (ch_height + 3) / 4;

    // Decompress into temporary channel buffer
    std::vector<uint16_t> ch_data(static_cast<size_t>(ch_width) * ch_height);

    for (int by = 0; by < num_blocks_y; by++) {
      for (int bx = 0; bx < num_blocks_x; bx++) {
        uint16_t block[16];

        if (is_b44a && in_ptr + 3 <= in_end) {
          // Check for flat block (3 bytes: 1 flag + 2 value)
          // If flag byte has high bit set, it's a flat block
          if (in_ptr[0] & 0x80) {
            uint16_t flat_val = (static_cast<uint16_t>(in_ptr[1]) << 8) | in_ptr[2];
            for (int i = 0; i < 16; i++) {
              block[i] = flat_val;
            }
            in_ptr += 3;
          } else if (in_ptr + 14 <= in_end) {
            UnpackB44Block(block, in_ptr);
            in_ptr += 14;
          } else {
            return false;
          }
        } else if (in_ptr + 14 <= in_end) {
          UnpackB44Block(block, in_ptr);
          in_ptr += 14;
        } else {
          return false;
        }

        // Copy block to temp buffer (with bounds checking for edge blocks)
        for (int py = 0; py < 4; py++) {
          int y = by * 4 + py;
          if (y >= ch_height) break;

          for (int px = 0; px < 4; px++) {
            int x = bx * 4 + px;
            if (x >= ch_width) break;

            ch_data[y * ch_width + x] = block[py * 4 + px];
          }
        }
      }
    }

    // Copy channel data to output in per-scanline layout
    for (int line = 0; line < num_lines; line++) {
      if ((line % channels[c].y_sampling) != 0) continue;

      int ch_line = line / channels[c].y_sampling;
      uint8_t* line_ptr = dst + static_cast<size_t>(line) * bytes_per_scanline + ch_offset;

      for (int x = 0; x < ch_width; x++) {
        uint16_t val = ch_data[ch_line * ch_width + x];
        line_ptr[x * 2] = static_cast<uint8_t>(val & 0xFF);
        line_ptr[x * 2 + 1] = static_cast<uint8_t>(val >> 8);
      }
    }
  }

  return true;
}

// Pack 16 half values into a 14-byte B44 block using log-space encoding
static void PackB44Block(uint8_t dst[14], const uint16_t src[16]) {
  // B44 format:
  // - 2 bytes: base value in log-space (big-endian, 14-bit)
  // - 12 bytes: 15 6-bit deltas (90 bits packed) in log-space

  InitB44Tables();

  // Convert first value to log space and use as base
  uint16_t base_log = HalfToLog(src[0]);
  dst[0] = static_cast<uint8_t>(base_log >> 8);
  dst[1] = static_cast<uint8_t>(base_log & 0xFF);

  // Initialize delta bytes to zero
  for (int i = 2; i < 14; i++) {
    dst[i] = 0;
  }

  // Pack 15 6-bit deltas in log space
  uint8_t* delta_ptr = dst + 2;
  int bit_pos = 0;

  for (int i = 1; i < 16; i++) {
    // Calculate delta in log space (clamped to 6-bit range: -31 to +32)
    uint16_t val_log = HalfToLog(src[i]);
    int delta = static_cast<int>(val_log) - static_cast<int>(base_log);

    // Clamp to representable range
    if (delta < -31) delta = -31;
    if (delta > 32) delta = 32;

    // Convert signed delta to unsigned 6-bit value (bias by 31)
    uint32_t bits = static_cast<uint32_t>(delta + 31) & 0x3F;

    // Write 6 bits at current bit position
    int byte_idx = bit_pos / 8;
    int bit_offset = bit_pos % 8;

    delta_ptr[byte_idx] |= static_cast<uint8_t>(bits << bit_offset);
    if (bit_offset > 2 && byte_idx + 1 < 12) {
      // Bits overflow into next byte
      delta_ptr[byte_idx + 1] |= static_cast<uint8_t>(bits >> (8 - bit_offset));
    }

    bit_pos += 6;
  }
}

// Check if a 4x4 block has all identical values (for B44A optimization)
static bool IsB44FlatBlock(const uint16_t src[16]) {
  uint16_t val = src[0];
  for (int i = 1; i < 16; i++) {
    if (src[i] != val) return false;
  }
  return true;
}

// Compress data using B44/B44A algorithm
static bool CompressB44V2(const uint8_t* src, size_t src_size,
                          std::vector<uint8_t>& dst,
                          int width, int num_lines,
                          int num_channels, const Channel* channels,
                          bool is_b44a) {
  (void)src_size;  // Not needed - we calculate from layout

  // B44 only works with HALF pixel types
  // Each 4x4 block of HALF values compresses to:
  // - 14 bytes for regular blocks
  // - 3 bytes for flat blocks (B44A only)

  // Input data layout (from SaveToMemory):
  // For each scanline: [Ch0_x0..Ch0_xN][Ch1_x0..Ch1_xN]...[ChM_x0..ChM_xN]
  // All channels are HALF (2 bytes each)

  // Calculate bytes per scanline (all channels)
  size_t bytes_per_pixel = 0;
  for (int c = 0; c < num_channels; c++) {
    bytes_per_pixel += (channels[c].pixel_type == PIXEL_TYPE_FLOAT) ? 4 :
                       (channels[c].pixel_type == PIXEL_TYPE_UINT) ? 4 : 2;
  }
  size_t bytes_per_scanline = bytes_per_pixel * static_cast<size_t>(width);

  // Reserve estimated output size
  dst.clear();
  dst.reserve(src_size);

  // Process each channel
  for (int c = 0; c < num_channels; c++) {
    int ch_width = width / channels[c].x_sampling;
    int ch_height = num_lines / channels[c].y_sampling;

    // Calculate channel offset within each scanline
    size_t ch_offset = 0;
    for (int i = 0; i < c; i++) {
      int ch_w = width / channels[i].x_sampling;
      ch_offset += static_cast<size_t>(ch_w) *
                   ((channels[i].pixel_type == PIXEL_TYPE_FLOAT) ? 4 :
                    (channels[i].pixel_type == PIXEL_TYPE_UINT) ? 4 : 2);
    }

    if (channels[c].pixel_type != PIXEL_TYPE_HALF) {
      // Non-HALF channels: copy uncompressed from per-scanline layout
      for (int line = 0; line < num_lines; line++) {
        if ((line % channels[c].y_sampling) != 0) continue;

        const uint8_t* line_data = src + static_cast<size_t>(line) * bytes_per_scanline + ch_offset;
        size_t ch_line_bytes = static_cast<size_t>(ch_width) *
                               ((channels[c].pixel_type == PIXEL_TYPE_FLOAT) ? 4 : 4);
        dst.insert(dst.end(), line_data, line_data + ch_line_bytes);
      }
      continue;
    }

    // Extract channel data from per-scanline layout into contiguous buffer
    std::vector<uint16_t> ch_data(static_cast<size_t>(ch_width) * ch_height);
    for (int line = 0; line < num_lines; line++) {
      if ((line % channels[c].y_sampling) != 0) continue;

      int ch_line = line / channels[c].y_sampling;
      const uint8_t* line_ptr = src + static_cast<size_t>(line) * bytes_per_scanline + ch_offset;

      for (int x = 0; x < ch_width; x++) {
        // Data is stored little-endian
        uint16_t val = static_cast<uint16_t>(line_ptr[x * 2]) |
                       (static_cast<uint16_t>(line_ptr[x * 2 + 1]) << 8);
        ch_data[ch_line * ch_width + x] = val;
      }
    }

    // Process HALF channel in 4x4 blocks
    int num_blocks_x = (ch_width + 3) / 4;
    int num_blocks_y = (ch_height + 3) / 4;

    for (int by = 0; by < num_blocks_y; by++) {
      for (int bx = 0; bx < num_blocks_x; bx++) {
        uint16_t block[16];

        // Extract 4x4 block (with padding for edge blocks)
        for (int py = 0; py < 4; py++) {
          int y = by * 4 + py;
          if (y >= ch_height) y = ch_height - 1;  // Clamp to edge

          for (int px = 0; px < 4; px++) {
            int x = bx * 4 + px;
            if (x >= ch_width) x = ch_width - 1;  // Clamp to edge

            block[py * 4 + px] = ch_data[y * ch_width + x];
          }
        }

        // Check for flat block optimization (B44A only)
        if (is_b44a && IsB44FlatBlock(block)) {
          // Write 3-byte flat block: 0x80 flag + 2 bytes value
          dst.push_back(0x80);
          dst.push_back(static_cast<uint8_t>(block[0] >> 8));
          dst.push_back(static_cast<uint8_t>(block[0] & 0xFF));
        } else {
          // Write 14-byte regular block
          uint8_t packed[14];
          PackB44Block(packed, block);
          dst.insert(dst.end(), packed, packed + 14);
        }
      }
    }
  }

  return true;
}

// ============================================================================
// Helper functions for tiled EXR format
// ============================================================================

static unsigned int FloorLog2(unsigned int x) {
  if (x == 0) return 0;
  unsigned int y = 0;
  while (x > 1) {
    y++;
    x >>= 1;
  }
  return y;
}

static unsigned int CeilLog2(unsigned int x) {
  if (x <= 1) return 0;
  unsigned int y = FloorLog2(x);
  if ((1u << y) < x) y++;
  return y;
}

static int RoundLog2(int x, int tile_rounding_mode) {
  return (tile_rounding_mode == TILE_ROUND_DOWN)
             ? static_cast<int>(FloorLog2(static_cast<unsigned>(x)))
             : static_cast<int>(CeilLog2(static_cast<unsigned>(x)));
}

static int LevelSize(int toplevel_size, int level, int tile_rounding_mode) {
  if (level < 0) return -1;
  int b = static_cast<int>(1u << static_cast<unsigned int>(level));
  int level_size = toplevel_size / b;
  if (tile_rounding_mode == TILE_ROUND_UP && level_size * b < toplevel_size)
    level_size += 1;
  return std::max(level_size, 1);
}

static int CalculateNumXLevels(const Header& hdr) {
  int w = hdr.data_window.width();
  int h = hdr.data_window.height();

  switch (hdr.tile_level_mode) {
    case TILE_ONE_LEVEL:
      return 1;
    case TILE_MIPMAP_LEVELS:
      return RoundLog2(std::max(w, h), hdr.tile_rounding_mode) + 1;
    case TILE_RIPMAP_LEVELS:
      return RoundLog2(w, hdr.tile_rounding_mode) + 1;
    default:
      return 1;
  }
}

static int CalculateNumYLevels(const Header& hdr) {
  int w = hdr.data_window.width();
  int h = hdr.data_window.height();

  switch (hdr.tile_level_mode) {
    case TILE_ONE_LEVEL:
      return 1;
    case TILE_MIPMAP_LEVELS:
      return RoundLog2(std::max(w, h), hdr.tile_rounding_mode) + 1;
    case TILE_RIPMAP_LEVELS:
      return RoundLog2(h, hdr.tile_rounding_mode) + 1;
    default:
      return 1;
  }
}

static bool CalculateNumTiles(std::vector<int>& numTiles,
                              int toplevel_size,
                              int tile_size,
                              int tile_rounding_mode) {
  for (unsigned i = 0; i < numTiles.size(); i++) {
    int level_sz = LevelSize(toplevel_size, static_cast<int>(i), tile_rounding_mode);
    if (level_sz < 0) return false;
    numTiles[i] = (level_sz + tile_size - 1) / tile_size;
  }
  return true;
}

// Tile offset structure for V2 API
struct TileOffsetData {
  // offsets[level][tile_y][tile_x] for ONE_LEVEL/MIPMAP
  // offsets[ly * num_x_levels + lx][tile_y][tile_x] for RIPMAP
  std::vector<std::vector<std::vector<uint64_t>>> offsets;
  int num_x_levels;
  int num_y_levels;

  TileOffsetData() : num_x_levels(0), num_y_levels(0) {}
};

static bool PrecalculateTileInfo(std::vector<int>& num_x_tiles,
                                 std::vector<int>& num_y_tiles,
                                 const Header& hdr) {
  int w = hdr.data_window.width();
  int h = hdr.data_window.height();

  int num_x_levels = CalculateNumXLevels(hdr);
  int num_y_levels = CalculateNumYLevels(hdr);

  if (num_x_levels < 0 || num_y_levels < 0) return false;

  num_x_tiles.resize(static_cast<size_t>(num_x_levels));
  num_y_tiles.resize(static_cast<size_t>(num_y_levels));

  if (!CalculateNumTiles(num_x_tiles, w, hdr.tile_size_x, hdr.tile_rounding_mode)) {
    return false;
  }
  if (!CalculateNumTiles(num_y_tiles, h, hdr.tile_size_y, hdr.tile_rounding_mode)) {
    return false;
  }

  return true;
}

static int InitTileOffsets(TileOffsetData& offset_data,
                           const Header& hdr,
                           const std::vector<int>& num_x_tiles,
                           const std::vector<int>& num_y_tiles) {
  int num_tile_blocks = 0;
  offset_data.num_x_levels = static_cast<int>(num_x_tiles.size());
  offset_data.num_y_levels = static_cast<int>(num_y_tiles.size());

  switch (hdr.tile_level_mode) {
    case TILE_ONE_LEVEL:
    case TILE_MIPMAP_LEVELS:
      if (offset_data.num_x_levels != offset_data.num_y_levels) return 0;
      offset_data.offsets.resize(static_cast<size_t>(offset_data.num_x_levels));

      for (int l = 0; l < offset_data.num_x_levels; ++l) {
        offset_data.offsets[l].resize(static_cast<size_t>(num_y_tiles[l]));
        for (int dy = 0; dy < num_y_tiles[l]; ++dy) {
          offset_data.offsets[l][dy].resize(static_cast<size_t>(num_x_tiles[l]));
          num_tile_blocks += num_x_tiles[l];
        }
      }
      break;

    case TILE_RIPMAP_LEVELS:
      offset_data.offsets.resize(
          static_cast<size_t>(offset_data.num_x_levels) *
          static_cast<size_t>(offset_data.num_y_levels));

      for (int ly = 0; ly < offset_data.num_y_levels; ++ly) {
        for (int lx = 0; lx < offset_data.num_x_levels; ++lx) {
          size_t l = static_cast<size_t>(ly * offset_data.num_x_levels + lx);
          offset_data.offsets[l].resize(static_cast<size_t>(num_y_tiles[ly]));
          for (size_t dy = 0; dy < offset_data.offsets[l].size(); ++dy) {
            offset_data.offsets[l][dy].resize(static_cast<size_t>(num_x_tiles[lx]));
            num_tile_blocks += num_x_tiles[lx];
          }
        }
      }
      break;

    default:
      return 0;
  }

  return num_tile_blocks;
}

static int LevelIndex(int level_x, int level_y, int tile_level_mode, int num_x_levels) {
  switch (tile_level_mode) {
    case TILE_ONE_LEVEL:
    case TILE_MIPMAP_LEVELS:
      return level_x;  // level_x == level_y for mipmap
    case TILE_RIPMAP_LEVELS:
      return level_y * num_x_levels + level_x;
    default:
      return 0;
  }
}

// ============================================================================
// Helper: Get scanlines per block for compression type
// ============================================================================

static int GetScanlinesPerBlock(int compression) {
  switch (compression) {
    case COMPRESSION_NONE:
    case COMPRESSION_RLE:
    case COMPRESSION_ZIPS:
      return 1;
    case COMPRESSION_ZIP:
      return 16;
    case COMPRESSION_PIZ:
      return 32;
    case COMPRESSION_PXR24:
      return 16;
    case COMPRESSION_B44:
    case COMPRESSION_B44A:
      return 32;
    case COMPRESSION_DWAA:
      return 32;
    case COMPRESSION_DWAB:
      return 256;
    case COMPRESSION_HTJ2K256:
      return 256;
    case COMPRESSION_HTJ2K32:
      return 32;
    case COMPRESSION_ZSTD:
    default:
      return 1;
  }
}

// ============================================================================
// Implementation of parser functions
// ============================================================================

Result<Version> ParseVersion(Reader& reader) {
  reader.set_context("Parsing EXR version header");

  Version version;

  // Check minimum size
  if (reader.length() < 8) {
    return Result<Version>::error(
      ErrorInfo(ErrorCode::InvalidData,
                "File too small to contain EXR version header (need 8 bytes, got " +
                std::to_string(reader.length()) + " bytes)",
                reader.context(),
                0));
  }

  // Read and check magic number: 0x76 0x2f 0x31 0x01
  uint8_t magic[4];
  if (!reader.read(4, magic)) {
    return Result<Version>::error(reader.last_error());
  }

  const uint8_t expected_magic[] = {0x76, 0x2f, 0x31, 0x01};
  for (int i = 0; i < 4; i++) {
    if (magic[i] != expected_magic[i]) {
      char buf[256];
      snprintf(buf, sizeof(buf),
               "Invalid EXR magic number. Expected [0x76 0x2f 0x31 0x01], "
               "got [0x%02x 0x%02x 0x%02x 0x%02x]. "
               "This is not a valid OpenEXR file.",
               magic[0], magic[1], magic[2], magic[3]);
      return Result<Version>::error(
        ErrorInfo(ErrorCode::InvalidMagicNumber, buf, reader.context(), 0));
    }
  }

  // Read version byte (must be 2)
  uint8_t version_byte;
  if (!reader.read1(&version_byte)) {
    return Result<Version>::error(reader.last_error());
  }

  if (version_byte != 2) {
    char buf[128];
    snprintf(buf, sizeof(buf),
             "Unsupported EXR version %d. Only version 2 is supported.",
             version_byte);
    return Result<Version>::error(
      ErrorInfo(ErrorCode::InvalidVersion, buf, reader.context(), 4));
  }

  version.version = 2;

  // Read flags byte
  uint8_t flags;
  if (!reader.read1(&flags)) {
    return Result<Version>::error(reader.last_error());
  }

  version.tiled = (flags & 0x02) != 0;       // bit 1 (9th bit of file)
  version.long_name = (flags & 0x04) != 0;   // bit 2 (10th bit of file)
  version.non_image = (flags & 0x08) != 0;   // bit 3 (11th bit of file, deep data)
  version.multipart = (flags & 0x10) != 0;   // bit 4 (12th bit of file)

  // Read remaining 2 bytes to complete 8-byte header
  uint8_t padding[2];
  if (!reader.read(2, padding)) {
    return Result<Version>::error(reader.last_error());
  }

  // Create result with informational warnings
  Result<Version> result = Result<Version>::ok(version);

  if (version.tiled) {
    result.add_warning("File uses tiled format");
  }
  if (version.long_name) {
    result.add_warning("File uses long attribute names (>255 chars)");
  }
  if (version.non_image) {
    result.add_warning("File contains deep/non-image data");
  }
  if (version.multipart) {
    result.add_warning("File is multipart format");
  }

  return result;
}

Result<Header> ParseHeader(Reader& reader, const Version& version) {
  reader.set_context("Parsing EXR header attributes");

  Header header;
  header.tiled = version.tiled;

  // Required attributes according to OpenEXR spec
  bool has_channels = false;
  bool has_compression = false;
  bool has_data_window = false;
  bool has_display_window = false;
  bool has_line_order = false;
  bool has_pixel_aspect_ratio = false;
  bool has_screen_window_center = false;
  bool has_screen_window_width = false;

  size_t header_start = reader.tell();

  // Read attributes until we hit null terminator
  for (int attr_count = 0; attr_count < 1024; attr_count++) {  // Safety limit
    // Check for end of header (null byte)
    size_t attr_start = reader.tell();
    uint8_t first_byte;
    if (!reader.read1(&first_byte)) {
      return Result<Header>::error(reader.last_error());
    }

    if (first_byte == 0) {
      // End of header
      break;
    }

    // Rewind to read full attribute name
    reader.seek(attr_start);

    // Read attribute name
    std::string attr_name;
    if (!reader.read_string(&attr_name, 256)) {
      return Result<Header>::error(
        ErrorInfo(ErrorCode::InvalidData,
                  "Failed to read attribute name at position " +
                  std::to_string(attr_start),
                  reader.context(),
                  attr_start));
    }

    // Read attribute type
    std::string attr_type;
    if (!reader.read_string(&attr_type, 256)) {
      return Result<Header>::error(
        ErrorInfo(ErrorCode::InvalidData,
                  "Failed to read attribute type for '" + attr_name + "'",
                  reader.context(),
                  reader.tell()));
    }

    // Read attribute data size
    uint32_t data_size;
    if (!reader.read4(&data_size)) {
      return Result<Header>::error(reader.last_error());
    }

    // Sanity check on data size (max 10MB per attribute)
    if (data_size > 10 * 1024 * 1024) {
      char buf[256];
      snprintf(buf, sizeof(buf),
               "Attribute '%s' has unreasonably large size %u bytes. "
               "Possible file corruption.",
               attr_name.c_str(), data_size);
      return Result<Header>::error(
        ErrorInfo(ErrorCode::InvalidData, buf, reader.context(), reader.tell() - 4));
    }

    size_t data_start = reader.tell();

    // Parse specific attributes we care about
    if (attr_name == "channels" && attr_type == "chlist") {
      has_channels = true;

      // Parse channel list
      size_t chlist_end = reader.tell() + data_size;

      while (reader.tell() < chlist_end) {
        // Check for null terminator (end of channel list)
        uint8_t name_first;
        size_t name_start = reader.tell();
        if (!reader.read1(&name_first)) {
          return Result<Header>::error(reader.last_error());
        }
        if (name_first == 0) {
          break;  // End of channel list
        }
        reader.seek(name_start);

        // Read channel name
        std::string channel_name;
        if (!reader.read_string(&channel_name, 256)) {
          return Result<Header>::error(reader.last_error());
        }

        Channel ch;
        ch.name = channel_name;

        // Read pixel type (4 bytes)
        uint32_t pixel_type;
        if (!reader.read4(&pixel_type)) {
          return Result<Header>::error(reader.last_error());
        }
        ch.pixel_type = static_cast<int>(pixel_type);

        // Validate pixel type (0=UINT, 1=HALF, 2=FLOAT)
        if (ch.pixel_type > 2) {
          return Result<Header>::error(
            ErrorInfo(ErrorCode::InvalidData,
                      "Invalid pixel type " + std::to_string(ch.pixel_type) +
                      " for channel '" + channel_name + "' (must be 0, 1, or 2)",
                      reader.context(),
                      reader.tell()));
        }

        // Read pLinear (1 byte) + reserved (3 bytes)
        uint8_t plinear;
        if (!reader.read1(&plinear)) {
          return Result<Header>::error(reader.last_error());
        }
        ch.p_linear = (plinear != 0);

        // Skip reserved (3 bytes)
        uint8_t reserved[3];
        if (!reader.read(3, reserved)) {
          return Result<Header>::error(reader.last_error());
        }

        // Read x sampling (4 bytes)
        uint32_t x_sampling;
        if (!reader.read4(&x_sampling)) {
          return Result<Header>::error(reader.last_error());
        }
        ch.x_sampling = static_cast<int>(x_sampling);

        // Read y sampling (4 bytes)
        uint32_t y_sampling;
        if (!reader.read4(&y_sampling)) {
          return Result<Header>::error(reader.last_error());
        }
        ch.y_sampling = static_cast<int>(y_sampling);

        // Validate sampling factors (must be positive)
        if (ch.x_sampling <= 0 || ch.y_sampling <= 0) {
          return Result<Header>::error(
            ErrorInfo(ErrorCode::InvalidData,
                      "Invalid sampling factor for channel '" + channel_name +
                      "' (x=" + std::to_string(ch.x_sampling) +
                      ", y=" + std::to_string(ch.y_sampling) + "); must be > 0",
                      reader.context(),
                      reader.tell()));
        }

        header.channels.push_back(ch);
      }

      // Sort channels by name for consistent ordering
      std::sort(header.channels.begin(), header.channels.end(),
                [](const Channel& a, const Channel& b) {
                  return a.name < b.name;
                });

      // Ensure we're at the end of the attribute data
      reader.seek(data_start + data_size);
    }
    else if (attr_name == "compression" && attr_type == "compression") {
      has_compression = true;
      if (data_size != 1) {
        return Result<Header>::error(
          ErrorInfo(ErrorCode::InvalidData,
                    "Compression attribute must be 1 byte",
                    reader.context(),
                    data_start));
      }
      uint8_t comp;
      if (!reader.read1(&comp)) {
        return Result<Header>::error(reader.last_error());
      }
      header.compression = comp;
    }
    else if (attr_name == "dataWindow" && attr_type == "box2i") {
      has_data_window = true;
      if (data_size != 16) {
        return Result<Header>::error(
          ErrorInfo(ErrorCode::InvalidData,
                    "dataWindow attribute must be 16 bytes (4 ints)",
                    reader.context(),
                    data_start));
      }
      uint32_t vals[4];
      for (int i = 0; i < 4; i++) {
        if (!reader.read4(&vals[i])) {
          return Result<Header>::error(reader.last_error());
        }
      }
      header.data_window.min_x = static_cast<int>(vals[0]);
      header.data_window.min_y = static_cast<int>(vals[1]);
      header.data_window.max_x = static_cast<int>(vals[2]);
      header.data_window.max_y = static_cast<int>(vals[3]);

      // Validate data window bounds (min must be <= max)
      if (header.data_window.min_x > header.data_window.max_x ||
          header.data_window.min_y > header.data_window.max_y) {
        return Result<Header>::error(
          ErrorInfo(ErrorCode::InvalidData,
                    "Invalid dataWindow: min > max",
                    reader.context(),
                    data_start));
      }
    }
    else if (attr_name == "displayWindow" && attr_type == "box2i") {
      has_display_window = true;
      if (data_size != 16) {
        return Result<Header>::error(
          ErrorInfo(ErrorCode::InvalidData,
                    "displayWindow attribute must be 16 bytes",
                    reader.context(),
                    data_start));
      }
      uint32_t vals[4];
      for (int i = 0; i < 4; i++) {
        if (!reader.read4(&vals[i])) {
          return Result<Header>::error(reader.last_error());
        }
      }
      header.display_window.min_x = static_cast<int>(vals[0]);
      header.display_window.min_y = static_cast<int>(vals[1]);
      header.display_window.max_x = static_cast<int>(vals[2]);
      header.display_window.max_y = static_cast<int>(vals[3]);

      // Validate display window bounds (min must be <= max)
      if (header.display_window.min_x > header.display_window.max_x ||
          header.display_window.min_y > header.display_window.max_y) {
        return Result<Header>::error(
          ErrorInfo(ErrorCode::InvalidData,
                    "Invalid displayWindow: min > max",
                    reader.context(),
                    data_start));
      }
    }
    else if (attr_name == "lineOrder" && attr_type == "lineOrder") {
      has_line_order = true;
      if (data_size != 1) {
        return Result<Header>::error(
          ErrorInfo(ErrorCode::InvalidData,
                    "lineOrder attribute must be 1 byte",
                    reader.context(),
                    data_start));
      }
      uint8_t lo;
      if (!reader.read1(&lo)) {
        return Result<Header>::error(reader.last_error());
      }
      header.line_order = lo;

      // Validate line order (0=INCREASING_Y, 1=DECREASING_Y, 2=RANDOM_Y for tiled)
      if (header.line_order > 2) {
        return Result<Header>::error(
          ErrorInfo(ErrorCode::InvalidData,
                    "Invalid lineOrder value " + std::to_string(header.line_order) +
                    " (must be 0, 1, or 2)",
                    reader.context(),
                    data_start));
      }
    }
    else if (attr_name == "pixelAspectRatio" && attr_type == "float") {
      has_pixel_aspect_ratio = true;
      if (data_size != 4) {
        return Result<Header>::error(
          ErrorInfo(ErrorCode::InvalidData,
                    "pixelAspectRatio must be 4 bytes (float)",
                    reader.context(),
                    data_start));
      }
      uint32_t bits;
      if (!reader.read4(&bits)) {
        return Result<Header>::error(reader.last_error());
      }
      std::memcpy(&header.pixel_aspect_ratio, &bits, 4);

      // Validate pixel aspect ratio (must be positive and finite)
      if (header.pixel_aspect_ratio <= 0.0f ||
          !std::isfinite(header.pixel_aspect_ratio)) {
        return Result<Header>::error(
          ErrorInfo(ErrorCode::InvalidData,
                    "Invalid pixelAspectRatio (must be positive and finite)",
                    reader.context(),
                    data_start));
      }
    }
    else if (attr_name == "screenWindowCenter" && attr_type == "v2f") {
      has_screen_window_center = true;
      if (data_size != 8) {
        return Result<Header>::error(
          ErrorInfo(ErrorCode::InvalidData,
                    "screenWindowCenter must be 8 bytes (2 floats)",
                    reader.context(),
                    data_start));
      }
      for (int i = 0; i < 2; i++) {
        uint32_t bits;
        if (!reader.read4(&bits)) {
          return Result<Header>::error(reader.last_error());
        }
        std::memcpy(&header.screen_window_center[i], &bits, 4);
      }
    }
    else if (attr_name == "screenWindowWidth" && attr_type == "float") {
      has_screen_window_width = true;
      if (data_size != 4) {
        return Result<Header>::error(
          ErrorInfo(ErrorCode::InvalidData,
                    "screenWindowWidth must be 4 bytes (float)",
                    reader.context(),
                    data_start));
      }
      uint32_t bits;
      if (!reader.read4(&bits)) {
        return Result<Header>::error(reader.last_error());
      }
      std::memcpy(&header.screen_window_width, &bits, 4);
    }
    else if (attr_name == "tiles" && attr_type == "tiledesc") {
      // Parse tile description: x_size (4) + y_size (4) + mode (1) = 9 bytes
      if (data_size != 9) {
        return Result<Header>::error(
          ErrorInfo(ErrorCode::InvalidData,
                    "tiledesc attribute must be 9 bytes",
                    reader.context(),
                    data_start));
      }
      uint32_t tile_x, tile_y;
      uint8_t mode_byte;
      if (!reader.read4(&tile_x) || !reader.read4(&tile_y) || !reader.read1(&mode_byte)) {
        return Result<Header>::error(reader.last_error());
      }
      header.tile_size_x = static_cast<int>(tile_x);
      header.tile_size_y = static_cast<int>(tile_y);
      header.tile_level_mode = mode_byte & 0x0F;
      header.tile_rounding_mode = (mode_byte >> 4) & 0x01;
      header.tiled = true;  // Has tiles attribute, so it's a tiled part
    }
    // Multipart/deep attributes
    else if (attr_name == "name" && attr_type == "string") {
      // Part name (required for multipart)
      std::vector<uint8_t> str_data(data_size);
      if (!reader.read(data_size, str_data.data())) {
        return Result<Header>::error(reader.last_error());
      }
      header.name = std::string(reinterpret_cast<char*>(str_data.data()), data_size);
      // Remove trailing null if present
      while (!header.name.empty() && header.name.back() == '\0') {
        header.name.pop_back();
      }
    }
    else if (attr_name == "type" && attr_type == "string") {
      // Part type: "scanlineimage", "tiledimage", "deepscanline", "deeptile"
      std::vector<uint8_t> str_data(data_size);
      if (!reader.read(data_size, str_data.data())) {
        return Result<Header>::error(reader.last_error());
      }
      header.type = std::string(reinterpret_cast<char*>(str_data.data()), data_size);
      while (!header.type.empty() && header.type.back() == '\0') {
        header.type.pop_back();
      }
      // Set is_deep flag based on type
      if (header.type == "deepscanline" || header.type == "deeptile") {
        header.is_deep = true;
      }
      // Set tiled flag based on type
      if (header.type == "tiledimage" || header.type == "deeptile") {
        header.tiled = true;
      } else if (header.type == "scanlineimage" || header.type == "deepscanline") {
        header.tiled = false;
      }
    }
    else if (attr_name == "view" && attr_type == "string") {
      // View name for stereo (e.g., "left", "right")
      std::vector<uint8_t> str_data(data_size);
      if (!reader.read(data_size, str_data.data())) {
        return Result<Header>::error(reader.last_error());
      }
      header.view = std::string(reinterpret_cast<char*>(str_data.data()), data_size);
      while (!header.view.empty() && header.view.back() == '\0') {
        header.view.pop_back();
      }
    }
    else if (attr_name == "chunkCount" && attr_type == "int") {
      // Number of chunks (required for multipart)
      if (data_size != 4) {
        return Result<Header>::error(
          ErrorInfo(ErrorCode::InvalidData,
                    "chunkCount must be 4 bytes (int)",
                    reader.context(),
                    data_start));
      }
      uint32_t count;
      if (!reader.read4(&count)) {
        return Result<Header>::error(reader.last_error());
      }
      header.chunk_count = static_cast<int>(count);
    }
    else if (attr_name == "version" && attr_type == "int") {
      // Deep data version (version=1 is current)
      if (data_size != 4) {
        return Result<Header>::error(
          ErrorInfo(ErrorCode::InvalidData,
                    "version must be 4 bytes (int)",
                    reader.context(),
                    data_start));
      }
      uint32_t ver;
      if (!reader.read4(&ver)) {
        return Result<Header>::error(reader.last_error());
      }
      header.deep_data_version = static_cast<int>(ver);
    }
    else {
      // Unknown attribute - store it in custom_attributes
      Attribute custom_attr;
      custom_attr.name = attr_name;
      custom_attr.type = attr_type;
      custom_attr.data.resize(data_size);
      if (data_size > 0) {
        if (!reader.read(data_size, custom_attr.data.data())) {
          return Result<Header>::error(reader.last_error());
        }
      }
      header.custom_attributes.push_back(custom_attr);
    }
  }

  // Check for required attributes
  Result<Header> result = Result<Header>::ok(header);

  if (!has_channels) {
    result.add_error(ErrorInfo(ErrorCode::MissingRequiredAttribute,
                               "Required attribute 'channels' not found",
                               reader.context(), header_start));
  }
  if (!has_compression) {
    result.add_error(ErrorInfo(ErrorCode::MissingRequiredAttribute,
                               "Required attribute 'compression' not found",
                               reader.context(), header_start));
  }
  if (!has_data_window) {
    result.add_error(ErrorInfo(ErrorCode::MissingRequiredAttribute,
                               "Required attribute 'dataWindow' not found",
                               reader.context(), header_start));
  }
  if (!has_display_window) {
    result.add_error(ErrorInfo(ErrorCode::MissingRequiredAttribute,
                               "Required attribute 'displayWindow' not found",
                               reader.context(), header_start));
  }
  if (!has_line_order) {
    result.add_error(ErrorInfo(ErrorCode::MissingRequiredAttribute,
                               "Required attribute 'lineOrder' not found",
                               reader.context(), header_start));
  }
  if (!has_pixel_aspect_ratio) {
    result.add_error(ErrorInfo(ErrorCode::MissingRequiredAttribute,
                               "Required attribute 'pixelAspectRatio' not found",
                               reader.context(), header_start));
  }
  if (!has_screen_window_center) {
    result.add_error(ErrorInfo(ErrorCode::MissingRequiredAttribute,
                               "Required attribute 'screenWindowCenter' not found",
                               reader.context(), header_start));
  }
  if (!has_screen_window_width) {
    result.add_error(ErrorInfo(ErrorCode::MissingRequiredAttribute,
                               "Required attribute 'screenWindowWidth' not found",
                               reader.context(), header_start));
  }

  if (!result.success) {
    return result;
  }

  header.header_len = reader.tell() - header_start;
  return result;
}

// Forward declaration
static Result<ImageData> LoadTiledFromMemory(const uint8_t* data, size_t size,
                                              Reader& reader,
                                              const Version& version,
                                              const Header& header);

// Forward declaration for LoadOptions version
Result<ImageData> LoadFromMemory(const uint8_t* data, size_t size, const LoadOptions& opts);

Result<ImageData> LoadFromMemory(const uint8_t* data, size_t size) {
  // Call the LoadOptions version with default options
  return LoadFromMemory(data, size, LoadOptions());
}

Result<ImageData> LoadFromMemory(const uint8_t* data, size_t size, const LoadOptions& opts) {
  if (!data) {
    return Result<ImageData>::error(
      ErrorInfo(ErrorCode::InvalidArgument,
                "Null data pointer passed to LoadFromMemory",
                "LoadFromMemory", 0));
  }

  if (size == 0) {
    return Result<ImageData>::error(
      ErrorInfo(ErrorCode::InvalidArgument,
                "Zero size passed to LoadFromMemory",
                "LoadFromMemory", 0));
  }

  Reader reader(data, size, Endian::Little);

  // Parse version
  Result<Version> version_result = ParseVersion(reader);
  if (!version_result.success) {
    Result<ImageData> result;
    result.success = false;
    result.errors = version_result.errors;
    result.warnings = version_result.warnings;
    return result;
  }

  // For multipart files, use LoadMultipartFromMemory
  if (version_result.value.multipart) {
    // Load as multipart and return first regular image part
    Result<MultipartImageData> mp_result = LoadMultipartFromMemory(data, size);
    if (!mp_result.success) {
      Result<ImageData> result;
      result.success = false;
      result.errors = mp_result.errors;
      result.warnings = mp_result.warnings;
      return result;
    }

    // Return first non-deep part
    if (!mp_result.value.parts.empty()) {
      Result<ImageData> result = Result<ImageData>::ok(mp_result.value.parts[0]);
      result.warnings = mp_result.warnings;
      if (mp_result.value.parts.size() > 1) {
        result.add_warning("Multipart file has " +
                           std::to_string(mp_result.value.parts.size()) +
                           " parts; returning first part. Use LoadMultipartFromMemory for all parts.");
      }
      return result;
    }

    // No regular parts, maybe only deep
    if (!mp_result.value.deep_parts.empty()) {
      Result<ImageData> result;
      result.success = false;
      result.errors.push_back(ErrorInfo(
        ErrorCode::UnsupportedFormat,
        "File contains only deep image parts. Use LoadMultipartFromMemory.",
        "LoadFromMemory", 0));
      return result;
    }

    Result<ImageData> result;
    result.success = false;
    result.errors.push_back(ErrorInfo(
      ErrorCode::InvalidData,
      "Multipart file contains no image parts",
      "LoadFromMemory", 0));
    return result;
  }

  // Parse header (single-part files)
  Result<Header> header_result = ParseHeader(reader, version_result.value);
  if (!header_result.success) {
    Result<ImageData> result;
    result.success = false;
    result.errors = header_result.errors;
    result.warnings = header_result.warnings;
    return result;
  }

  // Handle deep images (non-multipart single-part deep files)
  // These have non_image flag but not multipart flag
  if (header_result.value.is_deep || version_result.value.non_image) {
    // For single-part deep files, use LoadMultipartFromMemory which handles them
    Result<MultipartImageData> mp_result = LoadMultipartFromMemory(data, size);
    if (!mp_result.success) {
      Result<ImageData> result;
      result.success = false;
      result.errors = mp_result.errors;
      result.warnings = mp_result.warnings;
      return result;
    }

    // Deep parts don't have RGBA output - report appropriately
    if (!mp_result.value.deep_parts.empty()) {
      Result<ImageData> result;
      result.success = false;
      result.errors.push_back(ErrorInfo(
        ErrorCode::UnsupportedFormat,
        "This is a deep image file. Use LoadMultipartFromMemory to access deep data.",
        "LoadFromMemory", 0));
      return result;
    }

    // If there are regular parts (shouldn't happen for deep-only files)
    if (!mp_result.value.parts.empty()) {
      return Result<ImageData>::ok(mp_result.value.parts[0]);
    }

    Result<ImageData> result;
    result.success = false;
    result.errors.push_back(ErrorInfo(
      ErrorCode::InvalidData,
      "Deep file contains no loadable parts",
      "LoadFromMemory", 0));
    return result;
  }

  // Handle tiled files separately
  if (version_result.value.tiled || header_result.value.tiled) {
    return LoadTiledFromMemory(data, size, reader, version_result.value, header_result.value);
  }

  // Setup image data
  ImageData img_data;
  img_data.header = header_result.value;
  img_data.width = header_result.value.data_window.width();
  img_data.height = header_result.value.data_window.height();
  img_data.num_channels = static_cast<int>(header_result.value.channels.size());

  const Header& hdr = header_result.value;
  int width = img_data.width;
  int height = img_data.height;

  // Allocate RGBA output buffer
  img_data.rgba.resize(static_cast<size_t>(width) * static_cast<size_t>(height) * 4, 0.0f);

  // Calculate bytes per pixel for each channel and total
  size_t bytes_per_pixel = 0;
  std::vector<size_t> channel_offsets;
  std::vector<int> channel_sizes;  // bytes per pixel for each channel

  for (size_t i = 0; i < hdr.channels.size(); i++) {
    channel_offsets.push_back(bytes_per_pixel);
    int sz = 0;
    switch (hdr.channels[i].pixel_type) {
      case PIXEL_TYPE_UINT:  sz = 4; break;
      case PIXEL_TYPE_HALF:  sz = 2; break;
      case PIXEL_TYPE_FLOAT: sz = 4; break;
      default: sz = 4; break;
    }
    channel_sizes.push_back(sz);
    bytes_per_pixel += static_cast<size_t>(sz);
  }

  // Allocate raw channel buffers if requested
  if (opts.preserve_raw_channels) {
    img_data.raw_channels.resize(hdr.channels.size());
    for (size_t c = 0; c < hdr.channels.size(); c++) {
      // For subsampled channels, the size is reduced
      int ch_width = width / hdr.channels[c].x_sampling;
      int ch_height = height / hdr.channels[c].y_sampling;
      size_t ch_size = static_cast<size_t>(ch_width) * ch_height * channel_sizes[c];
      img_data.raw_channels[c].resize(ch_size);
    }
  }

  // Calculate scanline data size accounting for subsampling
  // For subsampled channels, fewer samples per scanline
  auto CalcScanlineDataSize = [&](int num_lines) -> size_t {
    size_t total = 0;
    for (size_t c = 0; c < hdr.channels.size(); c++) {
      int ch_width = width / hdr.channels[c].x_sampling;
      // Number of lines that have data for this channel in the block
      int ch_lines = 0;
      for (int line = 0; line < num_lines; line++) {
        if ((line % hdr.channels[c].y_sampling) == 0) {
          ch_lines++;
        }
      }
      total += static_cast<size_t>(ch_width) * ch_lines * channel_sizes[c];
    }
    return total;
  };

  size_t pixel_data_size = bytes_per_pixel * static_cast<size_t>(width);
  int scanlines_per_block = GetScanlinesPerBlock(hdr.compression);
  int num_blocks = (height + scanlines_per_block - 1) / scanlines_per_block;

  // Check compression type support
  if (hdr.compression != COMPRESSION_NONE &&
      hdr.compression != COMPRESSION_RLE &&
      hdr.compression != COMPRESSION_ZIPS &&
      hdr.compression != COMPRESSION_ZIP &&
      hdr.compression != COMPRESSION_PIZ &&
      hdr.compression != COMPRESSION_PXR24 &&
      hdr.compression != COMPRESSION_B44 &&
      hdr.compression != COMPRESSION_B44A) {
    Result<ImageData> result = Result<ImageData>::ok(img_data);
    result.warnings = version_result.warnings;
    for (size_t i = 0; i < header_result.warnings.size(); i++) {
      result.warnings.push_back(header_result.warnings[i]);
    }
    result.add_warning("Compression type " + std::to_string(hdr.compression) +
                       " not yet supported in V2 API. Pixel data not loaded.");
    return result;
  }

  // Check for subsampled channels (luminance-chroma format)
  bool has_subsampled = false;
  for (size_t c = 0; c < hdr.channels.size(); c++) {
    if (hdr.channels[c].x_sampling > 1 || hdr.channels[c].y_sampling > 1) {
      has_subsampled = true;
      break;
    }
  }

  // Read offset table
  reader.set_context("Reading offset table");
  std::vector<uint64_t> offsets(static_cast<size_t>(num_blocks));
  for (int i = 0; i < num_blocks; i++) {
    uint64_t offset;
    if (!reader.read8(&offset)) {
      Result<ImageData> result;
      result.success = false;
      result.errors.push_back(ErrorInfo(ErrorCode::InvalidData,
                                        "Failed to read offset table entry " + std::to_string(i),
                                        reader.context(), reader.tell()));
      return result;
    }
    offsets[static_cast<size_t>(i)] = offset;
  }

  // Get scratch pool for decompression
  ScratchPool& pool = get_scratch_pool();

  // Map channel names to output indices (RGBA)
  auto GetOutputIndex = [&](const std::string& name) -> int {
    if (name == "R" || name == "r") return 0;
    if (name == "G" || name == "g") return 1;
    if (name == "B" || name == "b") return 2;
    if (name == "A" || name == "a") return 3;
    if (name == "Y" || name == "y") return 0;  // Luminance -> R
    return -1;  // Unknown channel
  };

  // Build channel mapping
  std::vector<int> channel_output_idx;
  for (size_t i = 0; i < hdr.channels.size(); i++) {
    channel_output_idx.push_back(GetOutputIndex(hdr.channels[i].name));
  }

  // Decompress buffer
  std::vector<uint8_t> decomp_buf(pixel_data_size * static_cast<size_t>(scanlines_per_block));

  // Process each scanline block
  reader.set_context("Decoding scanline data");

  for (int block = 0; block < num_blocks; block++) {
    // Seek to block
    if (!reader.seek(static_cast<size_t>(offsets[static_cast<size_t>(block)]))) {
      Result<ImageData> result;
      result.success = false;
      result.errors.push_back(ErrorInfo(ErrorCode::OutOfBounds,
                                        "Failed to seek to block " + std::to_string(block),
                                        reader.context(), reader.tell()));
      return result;
    }

    // Read y coordinate (4 bytes)
    uint32_t y_coord;
    if (!reader.read4(&y_coord)) {
      Result<ImageData> result;
      result.success = false;
      result.errors.push_back(reader.last_error());
      return result;
    }

    // Read data size (4 bytes)
    uint32_t data_size;
    if (!reader.read4(&data_size)) {
      Result<ImageData> result;
      result.success = false;
      result.errors.push_back(reader.last_error());
      return result;
    }

    // Calculate number of scanlines in this block
    int y_start = static_cast<int>(y_coord) - hdr.data_window.min_y;
    int num_lines = std::min(scanlines_per_block, height - y_start);
    if (num_lines <= 0) continue;

    // Calculate expected size accounting for subsampling
    size_t expected_size = has_subsampled
        ? CalcScanlineDataSize(num_lines)
        : pixel_data_size * static_cast<size_t>(num_lines);

    // Read compressed data
    const uint8_t* block_data = data + reader.tell();
    if (reader.tell() + data_size > size) {
      Result<ImageData> result;
      result.success = false;
      result.errors.push_back(ErrorInfo(ErrorCode::OutOfBounds,
                                        "Block data exceeds file size",
                                        reader.context(), reader.tell()));
      return result;
    }

    // Decompress
    bool decomp_ok = false;
    switch (hdr.compression) {
      case COMPRESSION_NONE:
        if (data_size == expected_size) {
          std::memcpy(decomp_buf.data(), block_data, expected_size);
          decomp_ok = true;
        }
        break;

      case COMPRESSION_RLE:
        decomp_ok = DecompressRleV2(decomp_buf.data(), expected_size,
                                     block_data, data_size, pool);
        break;

      case COMPRESSION_ZIPS:
      case COMPRESSION_ZIP: {
        size_t uncomp_size = expected_size;
        decomp_ok = DecompressZipV2(decomp_buf.data(), &uncomp_size,
                                     block_data, data_size, pool);
        break;
      }

#if TINYEXR_V2_USE_CUSTOM_DEFLATE
      case COMPRESSION_PIZ: {
        auto piz_result = tinyexr::piz::DecompressPizV2(
            decomp_buf.data(), expected_size,
            block_data, data_size,
            static_cast<int>(hdr.channels.size()), hdr.channels.data(),
            width, num_lines);
        decomp_ok = piz_result.success;
        break;
      }
#endif

      case COMPRESSION_PXR24:
        decomp_ok = DecompressPxr24V2(decomp_buf.data(), expected_size,
                                       block_data, data_size,
                                       width, num_lines,
                                       static_cast<int>(hdr.channels.size()),
                                       hdr.channels.data(), pool);
        break;

      case COMPRESSION_B44:
        decomp_ok = DecompressB44V2(decomp_buf.data(), expected_size,
                                     block_data, data_size,
                                     width, num_lines,
                                     static_cast<int>(hdr.channels.size()),
                                     hdr.channels.data(), false, pool);
        break;

      case COMPRESSION_B44A:
        decomp_ok = DecompressB44V2(decomp_buf.data(), expected_size,
                                     block_data, data_size,
                                     width, num_lines,
                                     static_cast<int>(hdr.channels.size()),
                                     hdr.channels.data(), true, pool);
        break;

      default:
        decomp_ok = false;
        break;
    }

    if (!decomp_ok) {
      Result<ImageData> result;
      result.success = false;
      result.errors.push_back(ErrorInfo(ErrorCode::CompressionError,
                                        "Failed to decompress block " + std::to_string(block),
                                        reader.context(), reader.tell()));
      return result;
    }

    // Copy raw channel data if requested
    if (opts.preserve_raw_channels) {
      // Data in decomp_buf is organized per-scanline, with channels grouped within each line:
      // Line0: [Ch0_allpixels][Ch1_allpixels]...[ChN_allpixels]
      // Line1: [Ch0_allpixels][Ch1_allpixels]...[ChN_allpixels]
      // ...
      // For subsampled channels, only lines where (y % y_sampling == 0) have data

      // Calculate scanline data layout
      size_t scanline_data_size = 0;
      std::vector<size_t> ch_scanline_offsets(hdr.channels.size());
      for (size_t c = 0; c < hdr.channels.size(); c++) {
        ch_scanline_offsets[c] = scanline_data_size;
        int ch_width = width / hdr.channels[c].x_sampling;
        scanline_data_size += static_cast<size_t>(ch_width) * channel_sizes[c];
      }

      for (int line = 0; line < num_lines; line++) {
        int y = y_start + line;
        if (y < 0 || y >= height) continue;

        // For each channel, copy this line's data
        for (size_t c = 0; c < hdr.channels.size(); c++) {
          int y_samp = hdr.channels[c].y_sampling;
          if ((y % y_samp) != 0) continue;

          int ch_pixel_size = channel_sizes[c];
          int ch_width = width / hdr.channels[c].x_sampling;
          int ch_height = height / y_samp;
          size_t ch_line_size = static_cast<size_t>(ch_width) * ch_pixel_size;

          int ch_y = y / y_samp;
          size_t dst_offset = static_cast<size_t>(ch_y) * ch_line_size;
          size_t src_offset = static_cast<size_t>(line) * scanline_data_size + ch_scanline_offsets[c];

          if (ch_y < ch_height && dst_offset + ch_line_size <= img_data.raw_channels[c].size() &&
              src_offset + ch_line_size <= decomp_buf.size()) {
            std::memcpy(img_data.raw_channels[c].data() + dst_offset,
                        decomp_buf.data() + src_offset,
                        ch_line_size);
          }
        }
      }
    }

    // Convert pixel data to RGBA float
    // EXR stores data per-channel per-scanline:
    // [Ch0_x0, Ch0_x1, ..., Ch0_xN][Ch1_x0, Ch1_x1, ..., Ch1_xN]...
    // For subsampled channels, the data is stored at reduced resolution

    if (has_subsampled) {
      // Handle subsampled channels (luminance-chroma format)
      // Data is organized by channel, then by scanline within channel

      const uint8_t* data_ptr = decomp_buf.data();

      // Process each channel
      for (size_t c = 0; c < hdr.channels.size(); c++) {
        int out_idx = channel_output_idx[c];
        int ch_pixel_size = channel_sizes[c];
        int x_samp = hdr.channels[c].x_sampling;
        int y_samp = hdr.channels[c].y_sampling;
        int ch_width = width / x_samp;

        // Process each scanline in the block
        for (int line = 0; line < num_lines; line++) {
          int y = y_start + line;
          if (y < 0 || y >= height) continue;

          // Check if this scanline has data for this channel
          if ((line % y_samp) != 0) continue;

          float* out_line = img_data.rgba.data() + static_cast<size_t>(y) * static_cast<size_t>(width) * 4;

          // Initialize alpha if needed
          if (line == 0 && out_idx == -1) {
            for (int x = 0; x < width; x++) {
              out_line[x * 4 + 3] = 1.0f;
            }
          }

          if (out_idx >= 0 && out_idx <= 3) {
            // Read and upsample the channel data
            for (int ch_x = 0; ch_x < ch_width; ch_x++) {
              const uint8_t* ch_data = data_ptr + static_cast<size_t>(ch_x) * ch_pixel_size;
              float val = 0.0f;

              switch (hdr.channels[c].pixel_type) {
                case PIXEL_TYPE_UINT: {
                  uint32_t u;
                  std::memcpy(&u, ch_data, 4);
                  val = static_cast<float>(u) / 4294967295.0f;
                  break;
                }
                case PIXEL_TYPE_HALF: {
                  uint16_t h;
                  std::memcpy(&h, ch_data, 2);
                  val = HalfToFloat(h);
                  break;
                }
                case PIXEL_TYPE_FLOAT: {
                  std::memcpy(&val, ch_data, 4);
                  break;
                }
              }

              // Upsample: replicate value to all covered pixels
              for (int dx = 0; dx < x_samp && (ch_x * x_samp + dx) < width; dx++) {
                for (int dy = 0; dy < y_samp && (y + dy) < height; dy++) {
                  float* dst = img_data.rgba.data() +
                               (static_cast<size_t>(y + dy) * width + ch_x * x_samp + dx) * 4;
                  dst[out_idx] = val;
                }
              }
            }

            data_ptr += static_cast<size_t>(ch_width) * ch_pixel_size;
          } else {
            // Skip this channel's data
            data_ptr += static_cast<size_t>(ch_width) * ch_pixel_size;
          }
        }
      }

      // Initialize alpha for all pixels if no alpha channel
      bool has_alpha_channel = false;
      for (size_t c = 0; c < hdr.channels.size(); c++) {
        if (channel_output_idx[c] == 3) {
          has_alpha_channel = true;
          break;
        }
      }
      if (!has_alpha_channel) {
        for (int line = 0; line < num_lines; line++) {
          int y = y_start + line;
          if (y < 0 || y >= height) continue;
          float* out_line = img_data.rgba.data() + static_cast<size_t>(y) * static_cast<size_t>(width) * 4;
          for (int x = 0; x < width; x++) {
            out_line[x * 4 + 3] = 1.0f;
          }
        }
      }
    } else {
      // Standard non-subsampled path
      for (int line = 0; line < num_lines; line++) {
        int y = y_start + line;
        if (y < 0 || y >= height) continue;

        const uint8_t* line_data = decomp_buf.data() + static_cast<size_t>(line) * pixel_data_size;
        float* out_line = img_data.rgba.data() + static_cast<size_t>(y) * static_cast<size_t>(width) * 4;

        // Initialize alpha to 1.0
        bool has_alpha = false;
        for (size_t c = 0; c < hdr.channels.size(); c++) {
          if (channel_output_idx[c] == 3) {
            has_alpha = true;
            break;
          }
        }
        if (!has_alpha) {
          for (int x = 0; x < width; x++) {
            out_line[x * 4 + 3] = 1.0f;
          }
        }

        // Process each channel - data is organized per-channel in the scanline
        size_t ch_byte_offset = 0;
        for (size_t c = 0; c < hdr.channels.size(); c++) {
          int out_idx = channel_output_idx[c];
          int ch_pixel_size = channel_sizes[c];

          const uint8_t* ch_start = line_data + ch_byte_offset;

          if (out_idx >= 0 && out_idx <= 3) {
            for (int x = 0; x < width; x++) {
              const uint8_t* ch_data = ch_start + static_cast<size_t>(x) * static_cast<size_t>(ch_pixel_size);
              float val = 0.0f;

              switch (hdr.channels[c].pixel_type) {
                case PIXEL_TYPE_UINT: {
                  uint32_t u;
                  std::memcpy(&u, ch_data, 4);
                  val = static_cast<float>(u) / 4294967295.0f;
                  break;
                }
                case PIXEL_TYPE_HALF: {
                  uint16_t h;
                  std::memcpy(&h, ch_data, 2);
                  val = HalfToFloat(h);
                  break;
                }
                case PIXEL_TYPE_FLOAT: {
                  std::memcpy(&val, ch_data, 4);
                  break;
                }
              }

              out_line[x * 4 + out_idx] = val;
            }
          }

          // Advance to next channel's data
          ch_byte_offset += static_cast<size_t>(ch_pixel_size) * static_cast<size_t>(width);
        }
      }
    }

    reader.seek_relative(static_cast<int64_t>(data_size));
  }

  Result<ImageData> result = Result<ImageData>::ok(img_data);

  // Carry forward warnings
  result.warnings = version_result.warnings;
  for (size_t i = 0; i < header_result.warnings.size(); i++) {
    result.warnings.push_back(header_result.warnings[i]);
  }

  return result;
}

// ============================================================================
// Tiled file loading implementation
// ============================================================================

static Result<ImageData> LoadTiledFromMemory(const uint8_t* data, size_t size,
                                              Reader& reader,
                                              const Version& version,
                                              const Header& header) {
  ImageData img_data;
  img_data.header = header;
  img_data.width = header.data_window.width();
  img_data.height = header.data_window.height();
  img_data.num_channels = static_cast<int>(header.channels.size());

  int width = img_data.width;
  int height = img_data.height;

  // Validate tile size
  if (header.tile_size_x <= 0 || header.tile_size_y <= 0) {
    return Result<ImageData>::error(
      ErrorInfo(ErrorCode::InvalidData,
                "Invalid tile size in tiled EXR file",
                "LoadTiledFromMemory", reader.tell()));
  }

  // Calculate tile info
  std::vector<int> num_x_tiles, num_y_tiles;
  if (!PrecalculateTileInfo(num_x_tiles, num_y_tiles, header)) {
    return Result<ImageData>::error(
      ErrorInfo(ErrorCode::InvalidData,
                "Failed to calculate tile info",
                "LoadTiledFromMemory", reader.tell()));
  }

  // Initialize offset data structure
  TileOffsetData offset_data;
  int num_tile_blocks = InitTileOffsets(offset_data, header, num_x_tiles, num_y_tiles);
  if (num_tile_blocks <= 0) {
    return Result<ImageData>::error(
      ErrorInfo(ErrorCode::InvalidData,
                "Failed to initialize tile offsets",
                "LoadTiledFromMemory", reader.tell()));
  }

  // Read tile offset table
  reader.set_context("Reading tile offset table");
  for (size_t l = 0; l < offset_data.offsets.size(); ++l) {
    for (size_t dy = 0; dy < offset_data.offsets[l].size(); ++dy) {
      for (size_t dx = 0; dx < offset_data.offsets[l][dy].size(); ++dx) {
        uint64_t offset;
        if (!reader.read8(&offset)) {
          return Result<ImageData>::error(
            ErrorInfo(ErrorCode::InvalidData,
                      "Failed to read tile offset",
                      reader.context(), reader.tell()));
        }
        if (offset >= size) {
          return Result<ImageData>::error(
            ErrorInfo(ErrorCode::InvalidData,
                      "Invalid tile offset (beyond file size)",
                      reader.context(), reader.tell()));
        }
        offset_data.offsets[l][dy][dx] = offset;
      }
    }
  }

  // Allocate RGBA output buffer
  img_data.rgba.resize(static_cast<size_t>(width) * static_cast<size_t>(height) * 4, 0.0f);

  // Initialize alpha to 1.0 for pixels without alpha channel
  bool has_alpha = false;
  for (size_t c = 0; c < header.channels.size(); c++) {
    const std::string& name = header.channels[c].name;
    if (name == "A" || name == "a") {
      has_alpha = true;
      break;
    }
  }
  if (!has_alpha) {
    for (size_t i = 0; i < img_data.rgba.size(); i += 4) {
      img_data.rgba[i + 3] = 1.0f;
    }
  }

  // Calculate bytes per pixel for each channel
  std::vector<int> channel_sizes;
  size_t bytes_per_pixel = 0;
  for (size_t c = 0; c < header.channels.size(); c++) {
    int sz = 0;
    switch (header.channels[c].pixel_type) {
      case PIXEL_TYPE_UINT:  sz = 4; break;
      case PIXEL_TYPE_HALF:  sz = 2; break;
      case PIXEL_TYPE_FLOAT: sz = 4; break;
      default: sz = 4; break;
    }
    channel_sizes.push_back(sz);
    bytes_per_pixel += static_cast<size_t>(sz);
  }

  // Map channel names to RGBA output indices
  auto GetOutputIndex = [&](const std::string& name) -> int {
    if (name == "R" || name == "r") return 0;
    if (name == "G" || name == "g") return 1;
    if (name == "B" || name == "b") return 2;
    if (name == "A" || name == "a") return 3;
    if (name == "Y" || name == "y") return 0;  // Luminance -> R
    return -1;
  };

  std::vector<int> channel_output_idx;
  for (size_t c = 0; c < header.channels.size(); c++) {
    channel_output_idx.push_back(GetOutputIndex(header.channels[c].name));
  }

  // Get scratch pool for decompression
  ScratchPool& pool = get_scratch_pool();

  // Process level 0 only (base resolution)
  // For simplicity, we only decode the highest resolution level
  int level_x = 0, level_y = 0;
  int level_idx = LevelIndex(level_x, level_y, header.tile_level_mode, offset_data.num_x_levels);

  // Calculate level dimensions
  int level_width = LevelSize(width, level_x, header.tile_rounding_mode);
  int level_height = LevelSize(height, level_y, header.tile_rounding_mode);

  // Get number of tiles at this level
  int n_tiles_x = static_cast<int>(offset_data.offsets[level_idx][0].size());
  int n_tiles_y = static_cast<int>(offset_data.offsets[level_idx].size());

  reader.set_context("Decoding tile data");

  // Process each tile
  for (int tile_y = 0; tile_y < n_tiles_y; ++tile_y) {
    for (int tile_x = 0; tile_x < n_tiles_x; ++tile_x) {
      uint64_t tile_offset = offset_data.offsets[level_idx][tile_y][tile_x];

      // Seek to tile data
      if (!reader.seek(static_cast<size_t>(tile_offset))) {
        return Result<ImageData>::error(
          ErrorInfo(ErrorCode::OutOfBounds,
                    "Failed to seek to tile data",
                    reader.context(), reader.tell()));
      }

      // Read tile header: tile_x (4), tile_y (4), level_x (4), level_y (4), data_size (4)
      uint32_t tile_coords[4];
      uint32_t tile_data_size;
      if (!reader.read4(&tile_coords[0]) || !reader.read4(&tile_coords[1]) ||
          !reader.read4(&tile_coords[2]) || !reader.read4(&tile_coords[3]) ||
          !reader.read4(&tile_data_size)) {
        return Result<ImageData>::error(
          ErrorInfo(ErrorCode::InvalidData,
                    "Failed to read tile header",
                    reader.context(), reader.tell()));
      }

      // Calculate tile pixel dimensions
      int tile_start_x = tile_x * header.tile_size_x;
      int tile_start_y = tile_y * header.tile_size_y;
      int tile_width = std::min(header.tile_size_x, level_width - tile_start_x);
      int tile_height = std::min(header.tile_size_y, level_height - tile_start_y);

      if (tile_width <= 0 || tile_height <= 0) continue;

      size_t tile_pixel_data_size = bytes_per_pixel * static_cast<size_t>(tile_width);
      size_t expected_size = tile_pixel_data_size * static_cast<size_t>(tile_height);

      // Read compressed tile data
      const uint8_t* tile_data = data + reader.tell();
      if (reader.tell() + tile_data_size > size) {
        return Result<ImageData>::error(
          ErrorInfo(ErrorCode::OutOfBounds,
                    "Tile data exceeds file size",
                    reader.context(), reader.tell()));
      }

      // Allocate decompression buffer
      std::vector<uint8_t> decomp_buf(expected_size);

      // Decompress tile
      bool decomp_ok = false;
      switch (header.compression) {
        case COMPRESSION_NONE:
          if (tile_data_size == expected_size) {
            std::memcpy(decomp_buf.data(), tile_data, expected_size);
            decomp_ok = true;
          }
          break;

        case COMPRESSION_RLE:
          decomp_ok = DecompressRleV2(decomp_buf.data(), expected_size,
                                       tile_data, tile_data_size, pool);
          break;

        case COMPRESSION_ZIPS:
        case COMPRESSION_ZIP: {
          size_t uncomp_size = expected_size;
          decomp_ok = DecompressZipV2(decomp_buf.data(), &uncomp_size,
                                       tile_data, tile_data_size, pool);
          break;
        }

#if TINYEXR_V2_USE_CUSTOM_DEFLATE
        case COMPRESSION_PIZ: {
          auto piz_result = tinyexr::piz::DecompressPizV2(
              decomp_buf.data(), expected_size,
              tile_data, tile_data_size,
              static_cast<int>(header.channels.size()), header.channels.data(),
              tile_width, tile_height);
          decomp_ok = piz_result.success;
          break;
        }
#endif

        case COMPRESSION_PXR24:
          decomp_ok = DecompressPxr24V2(decomp_buf.data(), expected_size,
                                         tile_data, tile_data_size,
                                         tile_width, tile_height,
                                         static_cast<int>(header.channels.size()),
                                         header.channels.data(), pool);
          break;

        case COMPRESSION_B44:
          decomp_ok = DecompressB44V2(decomp_buf.data(), expected_size,
                                       tile_data, tile_data_size,
                                       tile_width, tile_height,
                                       static_cast<int>(header.channels.size()),
                                       header.channels.data(), false, pool);
          break;

        case COMPRESSION_B44A:
          decomp_ok = DecompressB44V2(decomp_buf.data(), expected_size,
                                       tile_data, tile_data_size,
                                       tile_width, tile_height,
                                       static_cast<int>(header.channels.size()),
                                       header.channels.data(), true, pool);
          break;

        default:
          decomp_ok = false;
          break;
      }

      if (!decomp_ok) {
        return Result<ImageData>::error(
          ErrorInfo(ErrorCode::CompressionError,
                    "Failed to decompress tile at (" + std::to_string(tile_x) +
                    ", " + std::to_string(tile_y) + ")",
                    reader.context(), reader.tell()));
      }

      // Convert tile pixel data to RGBA float and copy to output image
      for (int line = 0; line < tile_height; line++) {
        int out_y = tile_start_y + line;
        if (out_y < 0 || out_y >= height) continue;

        const uint8_t* line_data = decomp_buf.data() + static_cast<size_t>(line) * tile_pixel_data_size;
        float* out_line = img_data.rgba.data() + static_cast<size_t>(out_y) * static_cast<size_t>(width) * 4;

        // Process each channel
        size_t ch_byte_offset = 0;
        for (size_t c = 0; c < header.channels.size(); c++) {
          int out_idx = channel_output_idx[c];
          int ch_pixel_size = channel_sizes[c];

          const uint8_t* ch_start = line_data + ch_byte_offset;

          if (out_idx >= 0 && out_idx <= 3) {
            for (int x = 0; x < tile_width; x++) {
              int out_x = tile_start_x + x;
              if (out_x < 0 || out_x >= width) continue;

              const uint8_t* ch_data = ch_start + static_cast<size_t>(x) * static_cast<size_t>(ch_pixel_size);
              float val = 0.0f;

              switch (header.channels[c].pixel_type) {
                case PIXEL_TYPE_UINT: {
                  uint32_t u;
                  std::memcpy(&u, ch_data, 4);
                  val = static_cast<float>(u) / 4294967295.0f;
                  break;
                }
                case PIXEL_TYPE_HALF: {
                  uint16_t h;
                  std::memcpy(&h, ch_data, 2);
                  val = HalfToFloat(h);
                  break;
                }
                case PIXEL_TYPE_FLOAT: {
                  std::memcpy(&val, ch_data, 4);
                  break;
                }
              }

              out_line[out_x * 4 + out_idx] = val;
            }
          }

          // Advance to next channel's data
          ch_byte_offset += static_cast<size_t>(ch_pixel_size) * static_cast<size_t>(tile_width);
        }
      }

      reader.seek_relative(static_cast<int64_t>(tile_data_size));
    }
  }

  Result<ImageData> result = Result<ImageData>::ok(img_data);
  result.add_warning("Loaded tiled EXR (level 0 only)");

  return result;
}

// ============================================================================
// Writer implementations
// ============================================================================

Result<void> WriteVersion(Writer& writer, const Version& version) {
  writer.set_context("Writing EXR version header");

  // Write magic number: 0x76 0x2f 0x31 0x01
  const uint8_t magic[] = {0x76, 0x2f, 0x31, 0x01};
  if (!writer.write(4, magic)) {
    return Result<void>::error(writer.last_error());
  }

  // Write version byte (must be 2)
  if (!writer.write1(static_cast<uint8_t>(version.version))) {
    return Result<void>::error(writer.last_error());
  }

  // Build flags byte
  uint8_t flags = 0;
  if (version.tiled) flags |= 0x02;       // bit 1
  if (version.long_name) flags |= 0x04;   // bit 2
  if (version.non_image) flags |= 0x08;   // bit 3
  if (version.multipart) flags |= 0x10;   // bit 4

  if (!writer.write1(flags)) {
    return Result<void>::error(writer.last_error());
  }

  // Write 2 bytes padding to complete 8-byte header
  const uint8_t padding[2] = {0, 0};
  if (!writer.write(2, padding)) {
    return Result<void>::error(writer.last_error());
  }

  return Result<void>::ok();
}

Result<void> WriteHeader(Writer& writer, const Header& header) {
  writer.set_context("Writing EXR header attributes");

  Result<void> result = Result<void>::ok();

  // -------------------------------------------------------------------------
  // Write channels attribute (required)
  // -------------------------------------------------------------------------
  // Channel list format:
  //   For each channel:
  //     - channel name (null-terminated string)
  //     - pixel type (4 bytes, int32)
  //     - pLinear (1 byte) + reserved (3 bytes)
  //     - xSampling (4 bytes, int32)
  //     - ySampling (4 bytes, int32)
  //   Followed by null byte terminator
  if (!writer.write_string("channels")) {
    return Result<void>::error(writer.last_error());
  }
  if (!writer.write_string("chlist")) {
    return Result<void>::error(writer.last_error());
  }

  // Calculate channel list data size
  uint32_t chlist_size = 1;  // null terminator at end
  for (size_t i = 0; i < header.channels.size(); ++i) {
    chlist_size += static_cast<uint32_t>(header.channels[i].name.length() + 1);  // name + null
    chlist_size += 4;   // pixel_type
    chlist_size += 4;   // pLinear + reserved
    chlist_size += 4;   // x_sampling
    chlist_size += 4;   // y_sampling
  }

  if (!writer.write4(chlist_size)) {
    return Result<void>::error(writer.last_error());
  }

  // Write each channel (sorted by name for consistency)
  std::vector<Channel> sorted_channels = header.channels;
  std::sort(sorted_channels.begin(), sorted_channels.end(),
            [](const Channel& a, const Channel& b) { return a.name < b.name; });

  for (size_t i = 0; i < sorted_channels.size(); ++i) {
    const Channel& ch = sorted_channels[i];

    // Channel name (null-terminated)
    if (!writer.write_string(ch.name.c_str())) {
      return Result<void>::error(writer.last_error());
    }

    // Pixel type
    if (!writer.write4(static_cast<uint32_t>(ch.pixel_type))) {
      return Result<void>::error(writer.last_error());
    }

    // pLinear (1 byte) + reserved (3 bytes)
    if (!writer.write1(ch.p_linear ? 1 : 0)) {
      return Result<void>::error(writer.last_error());
    }
    if (!writer.write1(0) || !writer.write1(0) || !writer.write1(0)) {
      return Result<void>::error(writer.last_error());
    }

    // x_sampling
    if (!writer.write4(static_cast<uint32_t>(ch.x_sampling))) {
      return Result<void>::error(writer.last_error());
    }

    // y_sampling
    if (!writer.write4(static_cast<uint32_t>(ch.y_sampling))) {
      return Result<void>::error(writer.last_error());
    }
  }

  // Channel list null terminator
  if (!writer.write1(0)) {
    return Result<void>::error(writer.last_error());
  }

  // -------------------------------------------------------------------------
  // Write compression attribute
  // -------------------------------------------------------------------------
  if (!writer.write_string("compression")) {
    return Result<void>::error(writer.last_error());
  }
  if (!writer.write_string("compression")) {
    return Result<void>::error(writer.last_error());
  }
  if (!writer.write4(1)) {
    return Result<void>::error(writer.last_error());
  }
  if (!writer.write1(static_cast<uint8_t>(header.compression))) {
    return Result<void>::error(writer.last_error());
  }

  // -------------------------------------------------------------------------
  // Write dataWindow attribute
  // -------------------------------------------------------------------------
  if (!writer.write_string("dataWindow")) {
    return Result<void>::error(writer.last_error());
  }
  if (!writer.write_string("box2i")) {
    return Result<void>::error(writer.last_error());
  }
  if (!writer.write4(16)) {
    return Result<void>::error(writer.last_error());
  }
  if (!writer.write4(static_cast<uint32_t>(header.data_window.min_x))) {
    return Result<void>::error(writer.last_error());
  }
  if (!writer.write4(static_cast<uint32_t>(header.data_window.min_y))) {
    return Result<void>::error(writer.last_error());
  }
  if (!writer.write4(static_cast<uint32_t>(header.data_window.max_x))) {
    return Result<void>::error(writer.last_error());
  }
  if (!writer.write4(static_cast<uint32_t>(header.data_window.max_y))) {
    return Result<void>::error(writer.last_error());
  }

  // -------------------------------------------------------------------------
  // Write displayWindow attribute
  // -------------------------------------------------------------------------
  if (!writer.write_string("displayWindow")) {
    return Result<void>::error(writer.last_error());
  }
  if (!writer.write_string("box2i")) {
    return Result<void>::error(writer.last_error());
  }
  if (!writer.write4(16)) {
    return Result<void>::error(writer.last_error());
  }
  if (!writer.write4(static_cast<uint32_t>(header.display_window.min_x))) {
    return Result<void>::error(writer.last_error());
  }
  if (!writer.write4(static_cast<uint32_t>(header.display_window.min_y))) {
    return Result<void>::error(writer.last_error());
  }
  if (!writer.write4(static_cast<uint32_t>(header.display_window.max_x))) {
    return Result<void>::error(writer.last_error());
  }
  if (!writer.write4(static_cast<uint32_t>(header.display_window.max_y))) {
    return Result<void>::error(writer.last_error());
  }

  // -------------------------------------------------------------------------
  // Write lineOrder attribute
  // -------------------------------------------------------------------------
  if (!writer.write_string("lineOrder")) {
    return Result<void>::error(writer.last_error());
  }
  if (!writer.write_string("lineOrder")) {
    return Result<void>::error(writer.last_error());
  }
  if (!writer.write4(1)) {
    return Result<void>::error(writer.last_error());
  }
  if (!writer.write1(static_cast<uint8_t>(header.line_order))) {
    return Result<void>::error(writer.last_error());
  }

  // -------------------------------------------------------------------------
  // Write pixelAspectRatio attribute
  // -------------------------------------------------------------------------
  if (!writer.write_string("pixelAspectRatio")) {
    return Result<void>::error(writer.last_error());
  }
  if (!writer.write_string("float")) {
    return Result<void>::error(writer.last_error());
  }
  if (!writer.write4(4)) {
    return Result<void>::error(writer.last_error());
  }
  if (!writer.write_float(header.pixel_aspect_ratio)) {
    return Result<void>::error(writer.last_error());
  }

  // -------------------------------------------------------------------------
  // Write screenWindowCenter attribute
  // -------------------------------------------------------------------------
  if (!writer.write_string("screenWindowCenter")) {
    return Result<void>::error(writer.last_error());
  }
  if (!writer.write_string("v2f")) {
    return Result<void>::error(writer.last_error());
  }
  if (!writer.write4(8)) {
    return Result<void>::error(writer.last_error());
  }
  if (!writer.write_float(header.screen_window_center[0])) {
    return Result<void>::error(writer.last_error());
  }
  if (!writer.write_float(header.screen_window_center[1])) {
    return Result<void>::error(writer.last_error());
  }

  // -------------------------------------------------------------------------
  // Write screenWindowWidth attribute
  // -------------------------------------------------------------------------
  if (!writer.write_string("screenWindowWidth")) {
    return Result<void>::error(writer.last_error());
  }
  if (!writer.write_string("float")) {
    return Result<void>::error(writer.last_error());
  }
  if (!writer.write4(4)) {
    return Result<void>::error(writer.last_error());
  }
  if (!writer.write_float(header.screen_window_width)) {
    return Result<void>::error(writer.last_error());
  }

  // -------------------------------------------------------------------------
  // Write tiles attribute (for tiled images)
  // -------------------------------------------------------------------------
  if (header.tiled) {
    if (!writer.write_string("tiles")) {
      return Result<void>::error(writer.last_error());
    }
    if (!writer.write_string("tiledesc")) {
      return Result<void>::error(writer.last_error());
    }
    if (!writer.write4(9)) {  // 4 + 4 + 1 = 9 bytes
      return Result<void>::error(writer.last_error());
    }
    if (!writer.write4(static_cast<uint32_t>(header.tile_size_x))) {
      return Result<void>::error(writer.last_error());
    }
    if (!writer.write4(static_cast<uint32_t>(header.tile_size_y))) {
      return Result<void>::error(writer.last_error());
    }
    // mode byte: bits 0-3 = level mode, bit 4 = rounding mode
    uint8_t mode = static_cast<uint8_t>(header.tile_level_mode & 0x0F);
    mode |= static_cast<uint8_t>((header.tile_rounding_mode & 0x01) << 4);
    if (!writer.write1(mode)) {
      return Result<void>::error(writer.last_error());
    }
  }

  // -------------------------------------------------------------------------
  // Write name attribute (required for multipart)
  // -------------------------------------------------------------------------
  if (!header.name.empty()) {
    if (!writer.write_string("name")) {
      return Result<void>::error(writer.last_error());
    }
    if (!writer.write_string("string")) {
      return Result<void>::error(writer.last_error());
    }
    if (!writer.write4(static_cast<uint32_t>(header.name.length()))) {
      return Result<void>::error(writer.last_error());
    }
    if (!writer.write(header.name.length(), reinterpret_cast<const uint8_t*>(header.name.data()))) {
      return Result<void>::error(writer.last_error());
    }
  }

  // -------------------------------------------------------------------------
  // Write type attribute (required for multipart)
  // -------------------------------------------------------------------------
  if (!header.type.empty()) {
    if (!writer.write_string("type")) {
      return Result<void>::error(writer.last_error());
    }
    if (!writer.write_string("string")) {
      return Result<void>::error(writer.last_error());
    }
    if (!writer.write4(static_cast<uint32_t>(header.type.length()))) {
      return Result<void>::error(writer.last_error());
    }
    if (!writer.write(header.type.length(), reinterpret_cast<const uint8_t*>(header.type.data()))) {
      return Result<void>::error(writer.last_error());
    }
  }

  // -------------------------------------------------------------------------
  // Write chunkCount attribute (required for multipart)
  // -------------------------------------------------------------------------
  if (header.chunk_count > 0) {
    if (!writer.write_string("chunkCount")) {
      return Result<void>::error(writer.last_error());
    }
    if (!writer.write_string("int")) {
      return Result<void>::error(writer.last_error());
    }
    if (!writer.write4(4)) {
      return Result<void>::error(writer.last_error());
    }
    if (!writer.write4(static_cast<uint32_t>(header.chunk_count))) {
      return Result<void>::error(writer.last_error());
    }
  }

  // -------------------------------------------------------------------------
  // Write custom attributes
  // -------------------------------------------------------------------------
  for (const auto& attr : header.custom_attributes) {
    // Skip empty names
    if (attr.name.empty()) continue;

    // Write attribute name (null-terminated)
    if (!writer.write_string(attr.name.c_str())) {
      return Result<void>::error(writer.last_error());
    }

    // Write attribute type (null-terminated)
    if (!writer.write_string(attr.type.c_str())) {
      return Result<void>::error(writer.last_error());
    }

    // Write attribute data size
    if (!writer.write4(static_cast<uint32_t>(attr.data.size()))) {
      return Result<void>::error(writer.last_error());
    }

    // Write attribute data
    if (!attr.data.empty()) {
      if (!writer.write(attr.data.size(), attr.data.data())) {
        return Result<void>::error(writer.last_error());
      }
    }
  }

  // -------------------------------------------------------------------------
  // Write end-of-header marker (null byte)
  // -------------------------------------------------------------------------
  if (!writer.write1(0)) {
    return Result<void>::error(writer.last_error());
  }

  return result;
}

// ============================================================================
// Helper: FP32 to FP16 conversion for writing
// ============================================================================

static uint16_t FloatToHalf(float f) {
#if defined(TINYEXR_ENABLE_SIMD) && TINYEXR_ENABLE_SIMD
  return tinyexr::simd::float_to_half_scalar(f);
#else
  union {
    float f;
    uint32_t u;
    struct {
      uint32_t Mantissa : 23;
      uint32_t Exponent : 8;
      uint32_t Sign : 1;
    } s;
  } fi;
  fi.f = f;

  union {
    uint16_t u;
    struct {
      uint16_t Mantissa : 10;
      uint16_t Exponent : 5;
      uint16_t Sign : 1;
    } s;
  } o;
  o.u = 0;

  if (fi.s.Exponent == 0) {
    o.s.Exponent = 0;
  } else if (fi.s.Exponent == 255) {
    o.s.Exponent = 31;
    o.s.Mantissa = fi.s.Mantissa ? 0x200 : 0;
  } else {
    int newexp = static_cast<int>(fi.s.Exponent) - 127 + 15;
    if (newexp >= 31) {
      o.s.Exponent = 31;
    } else if (newexp <= 0) {
      if ((14 - newexp) <= 24) {
        uint32_t mant = fi.s.Mantissa | 0x800000;
        o.s.Mantissa = static_cast<uint16_t>(mant >> (14 - newexp));
        if ((mant >> (13 - newexp)) & 1) {
          o.u++;
        }
      }
    } else {
      o.s.Exponent = static_cast<uint16_t>(newexp);
      o.s.Mantissa = static_cast<uint16_t>(fi.s.Mantissa >> 13);
      if (fi.s.Mantissa & 0x1000) {
        o.u++;
      }
    }
  }

  o.s.Sign = static_cast<uint16_t>(fi.s.Sign);
  return o.u;
#endif
}

// ============================================================================
// Compression Helpers for Writing
// ============================================================================

// Reorder bytes for compression (interleave even/odd bytes)
static void ReorderBytesForCompression(const uint8_t* src, uint8_t* dst, size_t size) {
  if (size == 0) return;
  const size_t half = (size + 1) / 2;

  uint8_t* dst1 = dst;
  uint8_t* dst2 = dst + half;

  for (size_t i = 0; i < size; i += 2) {
    *dst1++ = src[i];
    if (i + 1 < size) {
      *dst2++ = src[i + 1];
    }
  }
}

// Apply delta predictor for compression
static void ApplyDeltaPredictorEncode(uint8_t* data, size_t size) {
  if (size <= 1) return;

  for (size_t i = size - 1; i > 0; i--) {
    int d = static_cast<int>(data[i]) - static_cast<int>(data[i - 1]) + 128;
    data[i] = static_cast<uint8_t>(d);
  }
}

// RLE compression (matching OpenEXR format)
static bool CompressRle(const uint8_t* src, size_t src_size,
                        std::vector<uint8_t>& dst) {
  dst.clear();
  dst.reserve(src_size + src_size / 128 + 1);

  size_t src_pos = 0;

  while (src_pos < src_size) {
    // Look for a run
    uint8_t current = src[src_pos];
    size_t run_length = 1;
    size_t max_run = std::min(src_size - src_pos, static_cast<size_t>(128));

    while (run_length < max_run && src[src_pos + run_length] == current) {
      run_length++;
    }

    if (run_length >= 3) {
      // Write run: positive count means repeat
      dst.push_back(static_cast<uint8_t>(run_length - 1));
      dst.push_back(current);
      src_pos += run_length;
    } else {
      // Look for literal run
      size_t lit_start = src_pos;
      size_t lit_count = 0;

      while (src_pos < src_size && lit_count < 127) {
        // Check if we should start a repeat run
        if (src_pos + 2 < src_size &&
            src[src_pos] == src[src_pos + 1] &&
            src[src_pos] == src[src_pos + 2]) {
          break;
        }
        lit_count++;
        src_pos++;
      }

      if (lit_count > 0) {
        // Write literal run: negative count
        dst.push_back(static_cast<uint8_t>(-static_cast<int>(lit_count)));
        for (size_t i = 0; i < lit_count; i++) {
          dst.push_back(src[lit_start + i]);
        }
      }
    }
  }

  return true;
}

// ZIP compression using miniz or zlib
#if defined(TINYEXR_USE_MINIZ) || defined(TINYEXR_USE_ZLIB) || TINYEXR_V2_USE_CUSTOM_DEFLATE
static bool CompressZip(const uint8_t* src, size_t src_size,
                        std::vector<uint8_t>& dst, int level = 6) {
#if defined(TINYEXR_USE_MINIZ)
  unsigned long compressed_size = static_cast<unsigned long>(src_size + src_size / 1000 + 128);
  dst.resize(compressed_size);
  int ret = mz_compress2(dst.data(), &compressed_size, src, static_cast<unsigned long>(src_size), level);
  if (ret != MZ_OK) {
    return false;
  }
  dst.resize(compressed_size);
  return true;
#elif defined(TINYEXR_USE_ZLIB)
  uLongf compressed_size = compressBound(static_cast<uLong>(src_size));
  dst.resize(compressed_size);
  int ret = compress2(dst.data(), &compressed_size, src, static_cast<uLong>(src_size), level);
  if (ret != Z_OK) {
    return false;
  }
  dst.resize(compressed_size);
  return true;
#else
  (void)src; (void)src_size; (void)dst; (void)level;
  return false;
#endif
}

// PXR24 compression
// Reverse of DecompressPxr24V2: convert FLOAT to 24-bit, then ZIP compress
static bool CompressPxr24V2(const uint8_t* src, size_t src_size,
                            int width, int num_lines,
                            int num_channels, const Channel* channels,
                            std::vector<uint8_t>& dst,
                            int compression_level = 6) {
  (void)src_size;  // Not needed - we calculate from channel layout

  // Calculate PXR24 data size (UINT: 4 bytes, HALF: 2 bytes, FLOAT: 3 bytes)
  size_t pxr24_size = 0;
  for (int c = 0; c < num_channels; c++) {
    int ch_width = width / channels[c].x_sampling;
    int ch_height = num_lines / channels[c].y_sampling;
    int ch_pixels = ch_width * ch_height;

    switch (channels[c].pixel_type) {
      case PIXEL_TYPE_UINT:  pxr24_size += static_cast<size_t>(ch_pixels) * 4; break;
      case PIXEL_TYPE_HALF:  pxr24_size += static_cast<size_t>(ch_pixels) * 2; break;
      case PIXEL_TYPE_FLOAT: pxr24_size += static_cast<size_t>(ch_pixels) * 3; break;
    }
  }

  // Allocate buffer for PXR24 format data
  std::vector<uint8_t> pxr24_buf(pxr24_size);
  const uint8_t* in_ptr = src;
  uint8_t* out_ptr = pxr24_buf.data();

  // Convert standard EXR format to PXR24 format
  // Data is organized by scanline, then by channel
  for (int line = 0; line < num_lines; line++) {
    for (int c = 0; c < num_channels; c++) {
      int ch_width = width / channels[c].x_sampling;

      // Check if this line contains data for this channel (accounting for y_sampling)
      if ((line % channels[c].y_sampling) != 0) continue;

      switch (channels[c].pixel_type) {
        case PIXEL_TYPE_UINT:
          // UINT stored as 4 bytes, copy directly
          for (int x = 0; x < ch_width; x++) {
            std::memcpy(out_ptr, in_ptr, 4);
            in_ptr += 4;
            out_ptr += 4;
          }
          break;

        case PIXEL_TYPE_HALF:
          // HALF stored as 2 bytes, copy directly
          for (int x = 0; x < ch_width; x++) {
            std::memcpy(out_ptr, in_ptr, 2);
            in_ptr += 2;
            out_ptr += 2;
          }
          break;

        case PIXEL_TYPE_FLOAT:
          // FLOAT stored as 24-bit (3 bytes): truncate lower 8 mantissa bits
          for (int x = 0; x < ch_width; x++) {
            uint32_t val;
            std::memcpy(&val, in_ptr, 4);
            // Extract upper 24 bits (1 sign + 8 exponent + 15 mantissa)
            out_ptr[0] = static_cast<uint8_t>(val >> 24);
            out_ptr[1] = static_cast<uint8_t>(val >> 16);
            out_ptr[2] = static_cast<uint8_t>(val >> 8);
            // Lower 8 mantissa bits are discarded
            in_ptr += 4;
            out_ptr += 3;
          }
          break;
      }
    }
  }

  // Now ZIP compress the PXR24 data
  return CompressZip(pxr24_buf.data(), pxr24_size, dst, compression_level);
}
#endif

Result<std::vector<uint8_t>> SaveToMemory(const ImageData& image, int compression_level) {
  Writer writer;
  writer.set_context("Saving EXR to memory");

  const Header& header = image.header;
  int width = image.width;
  int height = image.height;

  // Validate input
  if (width <= 0 || height <= 0) {
    return Result<std::vector<uint8_t>>::error(
      ErrorInfo(ErrorCode::InvalidArgument, "Invalid image dimensions",
                "SaveToMemory", 0));
  }

  if (image.rgba.empty()) {
    return Result<std::vector<uint8_t>>::error(
      ErrorInfo(ErrorCode::InvalidArgument, "Empty image data",
                "SaveToMemory", 0));
  }

  if (image.rgba.size() < static_cast<size_t>(width) * height * 4) {
    return Result<std::vector<uint8_t>>::error(
      ErrorInfo(ErrorCode::InvalidArgument, "Image data size mismatch",
                "SaveToMemory", 0));
  }

  // Create version
  Version version;
  version.version = 2;
  version.tiled = header.tiled;
  version.long_name = false;
  version.non_image = false;
  version.multipart = false;

  // Write version
  Result<void> version_result = WriteVersion(writer, version);
  if (!version_result.success) {
    Result<std::vector<uint8_t>> result;
    result.success = false;
    result.errors = version_result.errors;
    return result;
  }

  // Create a modified header for writing - since we always write HALF data,
  // the header must reflect HALF pixel_type for all channels
  Header write_header = header;
  for (auto& ch : write_header.channels) {
    ch.pixel_type = PIXEL_TYPE_HALF;
  }

  // Write header
  Result<void> header_result = WriteHeader(writer, write_header);
  if (!header_result.success) {
    Result<std::vector<uint8_t>> result;
    result.success = false;
    result.errors = header_result.errors;
    result.warnings = version_result.warnings;
    return result;
  }

  // Calculate scanline block parameters
  int scanlines_per_block = GetScanlinesPerBlock(header.compression);
  int num_blocks = (height + scanlines_per_block - 1) / scanlines_per_block;

  // Calculate bytes per scanline
  // For simplicity, we write HALF pixels (2 bytes per channel)
  size_t num_channels = header.channels.size();
  if (num_channels == 0) {
    // Default to RGBA if no channels specified
    num_channels = 4;
  }
  size_t bytes_per_pixel = num_channels * 2;  // HALF = 2 bytes
  size_t bytes_per_scanline = bytes_per_pixel * width;
  size_t bytes_per_block = bytes_per_scanline * scanlines_per_block;

  // Reserve space for offset table
  size_t offset_table_pos = writer.tell();
  for (int i = 0; i < num_blocks; i++) {
    if (!writer.write8(0)) {  // Placeholder
      return Result<std::vector<uint8_t>>::error(writer.last_error());
    }
  }

  // Store actual offsets
  std::vector<uint64_t> offsets(num_blocks);

  // Work buffers
  std::vector<uint8_t> scanline_buffer(bytes_per_block);
  std::vector<uint8_t> reorder_buffer(bytes_per_block);
  std::vector<uint8_t> compress_buffer(bytes_per_block * 2);  // Extra space for worst case

  // Map channel names to RGBA indices
  auto GetRGBAIndex = [&](const std::string& name) -> int {
    if (name == "R" || name == "r") return 0;
    if (name == "G" || name == "g") return 1;
    if (name == "B" || name == "b") return 2;
    if (name == "A" || name == "a") return 3;
    if (name == "Y" || name == "y") return 0;  // Luminance
    return -1;
  };

  // Build channel mapping
  std::vector<Channel> sorted_channels = header.channels;
  std::sort(sorted_channels.begin(), sorted_channels.end(),
            [](const Channel& a, const Channel& b) { return a.name < b.name; });

  // Since SaveToMemory always writes HALF data to scanline_buffer,
  // ensure all channels report HALF pixel_type for compression functions
  for (auto& ch : sorted_channels) {
    ch.pixel_type = PIXEL_TYPE_HALF;
  }

  // Process each scanline block
  for (int block = 0; block < num_blocks; block++) {
    int y_start = header.data_window.min_y + block * scanlines_per_block;
    int y_end = std::min(y_start + scanlines_per_block,
                         header.data_window.min_y + height);
    int num_lines = y_end - y_start;

    // Record offset for this block
    offsets[block] = writer.tell();

    // Write y coordinate
    if (!writer.write4(static_cast<uint32_t>(y_start))) {
      return Result<std::vector<uint8_t>>::error(writer.last_error());
    }

    // Convert RGBA float data to half-precision per-channel format
    // EXR stores channels in alphabetical order (A, B, G, R)
    size_t actual_bytes = bytes_per_scanline * num_lines;

    // Fill scanline buffer with channel data
    for (int line = 0; line < num_lines; line++) {
      int y = y_start - header.data_window.min_y + line;
      if (y < 0 || y >= height) continue;

      uint8_t* line_ptr = scanline_buffer.data() + line * bytes_per_scanline;

      // Write channels in sorted (alphabetical) order
      size_t ch_offset = 0;
      for (size_t ch = 0; ch < sorted_channels.size(); ch++) {
        int rgba_idx = GetRGBAIndex(sorted_channels[ch].name);
        if (rgba_idx < 0) rgba_idx = static_cast<int>(ch % 4);

        for (int x = 0; x < width; x++) {
          float val = image.rgba[y * width * 4 + x * 4 + rgba_idx];
          uint16_t half_val = FloatToHalf(val);

          // Write as little-endian
          line_ptr[ch_offset + x * 2 + 0] = static_cast<uint8_t>(half_val & 0xFF);
          line_ptr[ch_offset + x * 2 + 1] = static_cast<uint8_t>(half_val >> 8);
        }
        ch_offset += width * 2;
      }
    }

    // Apply compression
    size_t compressed_size = actual_bytes;
    const uint8_t* data_to_write = scanline_buffer.data();

    switch (header.compression) {
      case COMPRESSION_NONE:
        // No compression - write raw data
        compressed_size = actual_bytes;
        data_to_write = scanline_buffer.data();
        break;

      case COMPRESSION_RLE: {
        // Reorder bytes
        ReorderBytesForCompression(scanline_buffer.data(), reorder_buffer.data(), actual_bytes);
        // Apply predictor
        ApplyDeltaPredictorEncode(reorder_buffer.data(), actual_bytes);
        // RLE compress
        if (!CompressRle(reorder_buffer.data(), actual_bytes, compress_buffer)) {
          return Result<std::vector<uint8_t>>::error(
            ErrorInfo(ErrorCode::CompressionError, "RLE compression failed",
                      "SaveToMemory", writer.tell()));
        }
        compressed_size = compress_buffer.size();
        data_to_write = compress_buffer.data();
        break;
      }

      case COMPRESSION_ZIPS:
      case COMPRESSION_ZIP: {
#if defined(TINYEXR_USE_MINIZ) || defined(TINYEXR_USE_ZLIB)
        // Reorder bytes
        ReorderBytesForCompression(scanline_buffer.data(), reorder_buffer.data(), actual_bytes);
        // Apply predictor
        ApplyDeltaPredictorEncode(reorder_buffer.data(), actual_bytes);
        // ZIP compress
        if (!CompressZip(reorder_buffer.data(), actual_bytes, compress_buffer, compression_level)) {
          return Result<std::vector<uint8_t>>::error(
            ErrorInfo(ErrorCode::CompressionError, "ZIP compression failed",
                      "SaveToMemory", writer.tell()));
        }
        compressed_size = compress_buffer.size();
        data_to_write = compress_buffer.data();
#else
        // No compression library available - fall back to no compression
        compressed_size = actual_bytes;
        data_to_write = scanline_buffer.data();
#endif
        break;
      }

      case COMPRESSION_PXR24: {
#if defined(TINYEXR_USE_MINIZ) || defined(TINYEXR_USE_ZLIB)
        if (!CompressPxr24V2(scanline_buffer.data(), actual_bytes,
                             width, num_lines,
                             static_cast<int>(sorted_channels.size()),
                             sorted_channels.data(),
                             compress_buffer, compression_level)) {
          return Result<std::vector<uint8_t>>::error(
            ErrorInfo(ErrorCode::CompressionError, "PXR24 compression failed",
                      "SaveToMemory", writer.tell()));
        }
        compressed_size = compress_buffer.size();
        data_to_write = compress_buffer.data();
#else
        // No compression library available - fall back to no compression
        compressed_size = actual_bytes;
        data_to_write = scanline_buffer.data();
#endif
        break;
      }

      case COMPRESSION_PIZ: {
        // PIZ compression: wavelet + Huffman
        // Ensure output buffer is large enough (worst case: uncompressed + overhead)
        compress_buffer.resize(actual_bytes + actual_bytes / 100 + 1024);
        auto piz_result = tinyexr::piz::CompressPizV2(
            compress_buffer.data(), compress_buffer.size(),
            scanline_buffer.data(), actual_bytes,
            static_cast<int>(sorted_channels.size()),
            sorted_channels.data(),
            width, num_lines);
        if (!piz_result.success) {
          return Result<std::vector<uint8_t>>::error(
            ErrorInfo(ErrorCode::CompressionError,
                      "PIZ compression failed: " + piz_result.error_string(),
                      "SaveToMemory", writer.tell()));
        }
        compressed_size = piz_result.value;
        data_to_write = compress_buffer.data();
        break;
      }

      case COMPRESSION_B44:
        // B44 compression - only works with HALF pixel types
        if (!CompressB44V2(scanline_buffer.data(), actual_bytes,
                           compress_buffer, width, num_lines,
                           static_cast<int>(sorted_channels.size()),
                           sorted_channels.data(), false)) {
          return Result<std::vector<uint8_t>>::error(
            ErrorInfo(ErrorCode::CompressionError, "B44 compression failed",
                      "SaveToMemory", writer.tell()));
        }
        compressed_size = compress_buffer.size();
        data_to_write = compress_buffer.data();
        break;

      case COMPRESSION_B44A:
        // B44A compression - B44 with flat block optimization
        if (!CompressB44V2(scanline_buffer.data(), actual_bytes,
                           compress_buffer, width, num_lines,
                           static_cast<int>(sorted_channels.size()),
                           sorted_channels.data(), true)) {
          return Result<std::vector<uint8_t>>::error(
            ErrorInfo(ErrorCode::CompressionError, "B44A compression failed",
                      "SaveToMemory", writer.tell()));
        }
        compressed_size = compress_buffer.size();
        data_to_write = compress_buffer.data();
        break;

      default:
        // Unknown compression - write uncompressed
        compressed_size = actual_bytes;
        data_to_write = scanline_buffer.data();
        break;
    }

    // Write data size
    if (!writer.write4(static_cast<uint32_t>(compressed_size))) {
      return Result<std::vector<uint8_t>>::error(writer.last_error());
    }

    // Write compressed data
    if (!writer.write(compressed_size, data_to_write)) {
      return Result<std::vector<uint8_t>>::error(writer.last_error());
    }
  }

  // Go back and write the offset table
  size_t end_pos = writer.tell();
  if (!writer.seek(offset_table_pos)) {
    return Result<std::vector<uint8_t>>::error(writer.last_error());
  }
  for (int i = 0; i < num_blocks; i++) {
    if (!writer.write8(offsets[i])) {
      return Result<std::vector<uint8_t>>::error(writer.last_error());
    }
  }
  writer.seek(end_pos);

  // Return data
  Result<std::vector<uint8_t>> result = Result<std::vector<uint8_t>>::ok(writer.data());

  // Carry forward warnings
  for (size_t i = 0; i < version_result.warnings.size(); i++) {
    result.warnings.push_back(version_result.warnings[i]);
  }
  for (size_t i = 0; i < header_result.warnings.size(); i++) {
    result.warnings.push_back(header_result.warnings[i]);
  }

  return result;
}

// Overload with default compression level
Result<std::vector<uint8_t>> SaveToMemory(const ImageData& image) {
  return SaveToMemory(image, 6);
}

// Save to file
Result<void> SaveToFile(const char* filename, const ImageData& image, int compression_level) {
  if (!filename) {
    return Result<void>::error(
      ErrorInfo(ErrorCode::InvalidArgument, "Null filename",
                "SaveToFile", 0));
  }

  // Save to memory first
  auto mem_result = SaveToMemory(image, compression_level);
  if (!mem_result.success) {
    Result<void> result;
    result.success = false;
    result.errors = mem_result.errors;
    result.warnings = mem_result.warnings;
    return result;
  }

  // Write to file
  FILE* fp = fopen(filename, "wb");
  if (!fp) {
    return Result<void>::error(
      ErrorInfo(ErrorCode::IOError, "Failed to open file for writing",
                filename, 0));
  }

  size_t written = fwrite(mem_result.value.data(), 1, mem_result.value.size(), fp);
  fclose(fp);

  if (written != mem_result.value.size()) {
    return Result<void>::error(
      ErrorInfo(ErrorCode::IOError, "Failed to write all data to file",
                filename, 0));
  }

  Result<void> result = Result<void>::ok();
  result.warnings = mem_result.warnings;
  return result;
}

// ============================================================================
// Tiled Image Writing
// ============================================================================

// Helper: Downsample image by 2x using box filter
static std::vector<float> DownsampleImage(const float* src, int src_w, int src_h,
                                           int* dst_w, int* dst_h) {
  *dst_w = std::max(1, src_w / 2);
  *dst_h = std::max(1, src_h / 2);

  std::vector<float> dst(static_cast<size_t>(*dst_w) * (*dst_h) * 4);

  for (int dy = 0; dy < *dst_h; dy++) {
    for (int dx = 0; dx < *dst_w; dx++) {
      // Source coordinates (2x2 block)
      int sx0 = dx * 2;
      int sy0 = dy * 2;
      int sx1 = std::min(sx0 + 1, src_w - 1);
      int sy1 = std::min(sy0 + 1, src_h - 1);

      // Average 2x2 block for each channel
      for (int c = 0; c < 4; c++) {
        float v00 = src[(sy0 * src_w + sx0) * 4 + c];
        float v10 = src[(sy0 * src_w + sx1) * 4 + c];
        float v01 = src[(sy1 * src_w + sx0) * 4 + c];
        float v11 = src[(sy1 * src_w + sx1) * 4 + c];
        dst[(dy * (*dst_w) + dx) * 4 + c] = (v00 + v10 + v01 + v11) * 0.25f;
      }
    }
  }

  return dst;
}

// Helper: Write a single tile with compression
static bool WriteTile(Writer& writer, const float* image_data,
                      int image_w, int image_h,
                      int tx, int ty, int tile_w, int tile_h,
                      int level_x, int level_y,
                      const std::vector<Channel>& sorted_channels,
                      int compression, int compression_level,
                      std::vector<uint8_t>& tile_buffer,
                      std::vector<uint8_t>& reorder_buffer,
                      std::vector<uint8_t>& compress_buffer) {
  // Map channel names to RGBA indices
  auto GetRGBAIndex = [](const std::string& name) -> int {
    if (name == "R" || name == "r") return 0;
    if (name == "G" || name == "g") return 1;
    if (name == "B" || name == "b") return 2;
    if (name == "A" || name == "a") return 3;
    if (name == "Y" || name == "y") return 0;
    return -1;
  };

  // Calculate tile bounds
  int x0 = tx * tile_w;
  int y0 = ty * tile_h;
  int x1 = std::min(x0 + tile_w, image_w);
  int y1 = std::min(y0 + tile_h, image_h);
  int actual_w = x1 - x0;
  int actual_h = y1 - y0;

  if (actual_w <= 0 || actual_h <= 0) return false;

  // Write tile header: tile_x, tile_y, level_x, level_y
  if (!writer.write4(static_cast<uint32_t>(tx))) return false;
  if (!writer.write4(static_cast<uint32_t>(ty))) return false;
  if (!writer.write4(static_cast<uint32_t>(level_x))) return false;
  if (!writer.write4(static_cast<uint32_t>(level_y))) return false;

  // Fill tile buffer with pixel data
  size_t num_channels = sorted_channels.size();
  size_t bytes_per_scanline = static_cast<size_t>(actual_w) * num_channels * 2;
  size_t actual_tile_size = bytes_per_scanline * actual_h;

  std::memset(tile_buffer.data(), 0, tile_buffer.size());

  for (int line = 0; line < actual_h; line++) {
    int y = y0 + line;
    uint8_t* line_ptr = tile_buffer.data() + line * bytes_per_scanline;

    size_t ch_offset = 0;
    for (size_t ch = 0; ch < sorted_channels.size(); ch++) {
      int rgba_idx = GetRGBAIndex(sorted_channels[ch].name);
      if (rgba_idx < 0) rgba_idx = static_cast<int>(ch % 4);

      for (int x = 0; x < actual_w; x++) {
        int src_x = x0 + x;
        float val = image_data[y * image_w * 4 + src_x * 4 + rgba_idx];
        uint16_t half_val = FloatToHalf(val);

        line_ptr[ch_offset + x * 2 + 0] = static_cast<uint8_t>(half_val & 0xFF);
        line_ptr[ch_offset + x * 2 + 1] = static_cast<uint8_t>(half_val >> 8);
      }
      ch_offset += actual_w * 2;
    }
  }

  // Apply compression
  size_t compressed_size = actual_tile_size;
  const uint8_t* data_to_write = tile_buffer.data();

  switch (compression) {
    case COMPRESSION_NONE:
      compressed_size = actual_tile_size;
      data_to_write = tile_buffer.data();
      break;

    case COMPRESSION_RLE:
      ReorderBytesForCompression(tile_buffer.data(), reorder_buffer.data(), actual_tile_size);
      ApplyDeltaPredictorEncode(reorder_buffer.data(), actual_tile_size);
      if (!CompressRle(reorder_buffer.data(), actual_tile_size, compress_buffer)) {
        compressed_size = actual_tile_size;
        data_to_write = tile_buffer.data();
      } else {
        compressed_size = compress_buffer.size();
        data_to_write = compress_buffer.data();
      }
      break;

    case COMPRESSION_ZIPS:
    case COMPRESSION_ZIP:
#if defined(TINYEXR_USE_MINIZ) || defined(TINYEXR_USE_ZLIB)
      ReorderBytesForCompression(tile_buffer.data(), reorder_buffer.data(), actual_tile_size);
      ApplyDeltaPredictorEncode(reorder_buffer.data(), actual_tile_size);
      if (!CompressZip(reorder_buffer.data(), actual_tile_size, compress_buffer, compression_level)) {
        compressed_size = actual_tile_size;
        data_to_write = tile_buffer.data();
      } else {
        compressed_size = compress_buffer.size();
        data_to_write = compress_buffer.data();
      }
#else
      compressed_size = actual_tile_size;
      data_to_write = tile_buffer.data();
#endif
      break;

    case COMPRESSION_PXR24:
#if defined(TINYEXR_USE_MINIZ) || defined(TINYEXR_USE_ZLIB)
      if (!CompressPxr24V2(tile_buffer.data(), actual_tile_size,
                           actual_w, actual_h,
                           static_cast<int>(sorted_channels.size()),
                           sorted_channels.data(),
                           compress_buffer, compression_level)) {
        compressed_size = actual_tile_size;
        data_to_write = tile_buffer.data();
      } else {
        compressed_size = compress_buffer.size();
        data_to_write = compress_buffer.data();
      }
#else
      compressed_size = actual_tile_size;
      data_to_write = tile_buffer.data();
#endif
      break;

    case COMPRESSION_PIZ: {
      // PIZ compression: wavelet + Huffman
      compress_buffer.resize(actual_tile_size + actual_tile_size / 100 + 1024);
      auto piz_result = tinyexr::piz::CompressPizV2(
          compress_buffer.data(), compress_buffer.size(),
          tile_buffer.data(), actual_tile_size,
          static_cast<int>(sorted_channels.size()),
          sorted_channels.data(),
          actual_w, actual_h);
      if (!piz_result.success) {
        // Fall back to uncompressed on error
        compressed_size = actual_tile_size;
        data_to_write = tile_buffer.data();
      } else {
        compressed_size = piz_result.value;
        data_to_write = compress_buffer.data();
      }
      break;
    }

    case COMPRESSION_B44:
      if (!CompressB44V2(tile_buffer.data(), actual_tile_size,
                         compress_buffer, actual_w, actual_h,
                         static_cast<int>(sorted_channels.size()),
                         sorted_channels.data(), false)) {
        compressed_size = actual_tile_size;
        data_to_write = tile_buffer.data();
      } else {
        compressed_size = compress_buffer.size();
        data_to_write = compress_buffer.data();
      }
      break;

    case COMPRESSION_B44A:
      if (!CompressB44V2(tile_buffer.data(), actual_tile_size,
                         compress_buffer, actual_w, actual_h,
                         static_cast<int>(sorted_channels.size()),
                         sorted_channels.data(), true)) {
        compressed_size = actual_tile_size;
        data_to_write = tile_buffer.data();
      } else {
        compressed_size = compress_buffer.size();
        data_to_write = compress_buffer.data();
      }
      break;

    default:
      compressed_size = actual_tile_size;
      data_to_write = tile_buffer.data();
      break;
  }

  // Write data size and data
  if (!writer.write4(static_cast<uint32_t>(compressed_size))) return false;
  if (!writer.write(compressed_size, data_to_write)) return false;

  return true;
}

Result<std::vector<uint8_t>> SaveTiledToMemory(const ImageData& image, int compression_level) {
  Writer writer;
  writer.set_context("Saving tiled EXR to memory");

  const Header& header = image.header;
  int width = image.width;
  int height = image.height;

  // Validate input
  if (width <= 0 || height <= 0) {
    return Result<std::vector<uint8_t>>::error(
      ErrorInfo(ErrorCode::InvalidArgument, "Invalid image dimensions",
                "SaveTiledToMemory", 0));
  }

  if (image.rgba.empty()) {
    return Result<std::vector<uint8_t>>::error(
      ErrorInfo(ErrorCode::InvalidArgument, "Empty image data",
                "SaveTiledToMemory", 0));
  }

  if (image.rgba.size() < static_cast<size_t>(width) * height * 4) {
    return Result<std::vector<uint8_t>>::error(
      ErrorInfo(ErrorCode::InvalidArgument, "Image data size mismatch",
                "SaveTiledToMemory", 0));
  }

  // Validate tile parameters
  int tile_w = header.tile_size_x;
  int tile_h = header.tile_size_y;
  if (tile_w <= 0 || tile_h <= 0) {
    return Result<std::vector<uint8_t>>::error(
      ErrorInfo(ErrorCode::InvalidArgument, "Invalid tile size (must be > 0)",
                "SaveTiledToMemory", 0));
  }

  // Create version with tiled flag
  Version version;
  version.version = 2;
  version.tiled = true;
  version.long_name = false;
  version.non_image = false;
  version.multipart = false;

  // Write version
  Result<void> version_result = WriteVersion(writer, version);
  if (!version_result.success) {
    Result<std::vector<uint8_t>> result;
    result.success = false;
    result.errors = version_result.errors;
    return result;
  }

  // Create a modified header for writing
  Header write_header = header;
  write_header.tiled = true;
  write_header.tile_size_x = tile_w;
  write_header.tile_size_y = tile_h;
  // Ensure all channels are HALF
  for (auto& ch : write_header.channels) {
    ch.pixel_type = PIXEL_TYPE_HALF;
  }

  // Write header
  Result<void> header_result = WriteHeader(writer, write_header);
  if (!header_result.success) {
    Result<std::vector<uint8_t>> result;
    result.success = false;
    result.errors = header_result.errors;
    result.warnings = version_result.warnings;
    return result;
  }

  // Build sorted channel list
  std::vector<Channel> sorted_channels = header.channels;
  std::sort(sorted_channels.begin(), sorted_channels.end(),
            [](const Channel& a, const Channel& b) { return a.name < b.name; });
  for (auto& ch : sorted_channels) {
    ch.pixel_type = PIXEL_TYPE_HALF;
  }

  // Determine tile level mode
  int tile_level_mode = write_header.tile_level_mode;
  int tile_rounding_mode = write_header.tile_rounding_mode;

  // Calculate number of levels
  int num_x_levels = CalculateNumXLevels(write_header);
  int num_y_levels = CalculateNumYLevels(write_header);

  // Calculate total tile count across all levels
  int total_tiles = 0;
  std::vector<std::vector<int>> tiles_per_level;  // [level][0]=num_x, [level][1]=num_y, [level][2]=level_w, [level][3]=level_h

  if (tile_level_mode == TILE_ONE_LEVEL) {
    // ONE_LEVEL: just base level
    int num_x = (width + tile_w - 1) / tile_w;
    int num_y = (height + tile_h - 1) / tile_h;
    total_tiles = num_x * num_y;
    tiles_per_level.push_back({num_x, num_y, width, height});
  } else if (tile_level_mode == TILE_MIPMAP_LEVELS) {
    // MIPMAP_LEVELS: symmetric downsample
    for (int level = 0; level < num_x_levels; level++) {
      int level_w = LevelSize(width, level, tile_rounding_mode);
      int level_h = LevelSize(height, level, tile_rounding_mode);
      int num_x = (level_w + tile_w - 1) / tile_w;
      int num_y = (level_h + tile_h - 1) / tile_h;
      total_tiles += num_x * num_y;
      tiles_per_level.push_back({num_x, num_y, level_w, level_h});
    }
  } else if (tile_level_mode == TILE_RIPMAP_LEVELS) {
    // RIPMAP_LEVELS: independent X/Y downsample
    for (int ly = 0; ly < num_y_levels; ly++) {
      for (int lx = 0; lx < num_x_levels; lx++) {
        int level_w = LevelSize(width, lx, tile_rounding_mode);
        int level_h = LevelSize(height, ly, tile_rounding_mode);
        int num_x = (level_w + tile_w - 1) / tile_w;
        int num_y = (level_h + tile_h - 1) / tile_h;
        total_tiles += num_x * num_y;
        tiles_per_level.push_back({num_x, num_y, level_w, level_h});
      }
    }
  }

  // Reserve space for offset table
  size_t offset_table_pos = writer.tell();
  for (int i = 0; i < total_tiles; i++) {
    if (!writer.write8(0)) {
      return Result<std::vector<uint8_t>>::error(writer.last_error());
    }
  }

  std::vector<uint64_t> offsets;
  offsets.reserve(total_tiles);

  // Work buffers
  size_t num_channels = sorted_channels.size();
  if (num_channels == 0) num_channels = 4;
  size_t tile_buffer_size = static_cast<size_t>(tile_w) * tile_h * num_channels * 2;

  std::vector<uint8_t> tile_buffer(tile_buffer_size);
  std::vector<uint8_t> reorder_buffer(tile_buffer_size);
  std::vector<uint8_t> compress_buffer(tile_buffer_size * 2);

  // Generate mipmap levels (base + downsampled)
  std::vector<std::vector<float>> mip_levels;
  std::vector<std::pair<int, int>> mip_dims;  // (width, height) for each level

  // Level 0 = original image
  mip_levels.push_back(image.rgba);
  mip_dims.push_back({width, height});

  // Generate additional mip levels if needed
  if (tile_level_mode == TILE_MIPMAP_LEVELS && num_x_levels > 1) {
    int cur_w = width, cur_h = height;
    const float* cur_data = image.rgba.data();
    std::vector<float> prev_level;

    for (int level = 1; level < num_x_levels; level++) {
      int new_w, new_h;
      std::vector<float> downsampled = DownsampleImage(cur_data, cur_w, cur_h, &new_w, &new_h);
      mip_levels.push_back(downsampled);
      mip_dims.push_back({new_w, new_h});
      prev_level = std::move(downsampled);
      cur_data = prev_level.data();
      cur_w = new_w;
      cur_h = new_h;
    }
  }

  // Write tiles for each level
  int level_idx = 0;
  if (tile_level_mode == TILE_ONE_LEVEL) {
    // Single level
    int num_x = tiles_per_level[0][0];
    int num_y = tiles_per_level[0][1];

    for (int ty = 0; ty < num_y; ty++) {
      for (int tx = 0; tx < num_x; tx++) {
        offsets.push_back(writer.tell());
        if (!WriteTile(writer, image.rgba.data(), width, height,
                       tx, ty, tile_w, tile_h, 0, 0,
                       sorted_channels, header.compression, compression_level,
                       tile_buffer, reorder_buffer, compress_buffer)) {
          return Result<std::vector<uint8_t>>::error(
            ErrorInfo(ErrorCode::CompressionError, "Failed to write tile",
                      "SaveTiledToMemory", writer.tell()));
        }
      }
    }
  } else if (tile_level_mode == TILE_MIPMAP_LEVELS) {
    // Mipmap levels
    for (int level = 0; level < num_x_levels; level++) {
      int level_w = mip_dims[level].first;
      int level_h = mip_dims[level].second;
      int num_x = tiles_per_level[level][0];
      int num_y = tiles_per_level[level][1];
      const float* level_data = mip_levels[level].data();

      for (int ty = 0; ty < num_y; ty++) {
        for (int tx = 0; tx < num_x; tx++) {
          offsets.push_back(writer.tell());
          if (!WriteTile(writer, level_data, level_w, level_h,
                         tx, ty, tile_w, tile_h, level, level,
                         sorted_channels, header.compression, compression_level,
                         tile_buffer, reorder_buffer, compress_buffer)) {
            return Result<std::vector<uint8_t>>::error(
              ErrorInfo(ErrorCode::CompressionError,
                        "Failed to write tile at level " + std::to_string(level),
                        "SaveTiledToMemory", writer.tell()));
          }
        }
      }
    }
  } else if (tile_level_mode == TILE_RIPMAP_LEVELS) {
    // Ripmap levels - generate on-the-fly since we need independent X/Y downsampling
    // For now, generate each level's data and write tiles
    for (int ly = 0; ly < num_y_levels; ly++) {
      for (int lx = 0; lx < num_x_levels; lx++) {
        int idx = ly * num_x_levels + lx;
        int level_w = tiles_per_level[idx][2];
        int level_h = tiles_per_level[idx][3];
        int num_x = tiles_per_level[idx][0];
        int num_y = tiles_per_level[idx][1];

        // Generate ripmap level data (simplified: box filter downsample)
        std::vector<float> level_data(static_cast<size_t>(level_w) * level_h * 4);
        for (int y = 0; y < level_h; y++) {
          for (int x = 0; x < level_w; x++) {
            // Map from level coords to base coords
            float src_x = static_cast<float>(x) * width / level_w;
            float src_y = static_cast<float>(y) * height / level_h;
            int sx = static_cast<int>(src_x);
            int sy = static_cast<int>(src_y);
            sx = std::min(sx, width - 1);
            sy = std::min(sy, height - 1);

            for (int c = 0; c < 4; c++) {
              level_data[(y * level_w + x) * 4 + c] = image.rgba[(sy * width + sx) * 4 + c];
            }
          }
        }

        for (int ty = 0; ty < num_y; ty++) {
          for (int tx = 0; tx < num_x; tx++) {
            offsets.push_back(writer.tell());
            if (!WriteTile(writer, level_data.data(), level_w, level_h,
                           tx, ty, tile_w, tile_h, lx, ly,
                           sorted_channels, header.compression, compression_level,
                           tile_buffer, reorder_buffer, compress_buffer)) {
              return Result<std::vector<uint8_t>>::error(
                ErrorInfo(ErrorCode::CompressionError,
                          "Failed to write ripmap tile",
                          "SaveTiledToMemory", writer.tell()));
            }
          }
        }
      }
    }
  }

  // Go back and write the offset table
  size_t end_pos = writer.tell();
  if (!writer.seek(offset_table_pos)) {
    return Result<std::vector<uint8_t>>::error(writer.last_error());
  }
  for (size_t i = 0; i < offsets.size(); i++) {
    if (!writer.write8(offsets[i])) {
      return Result<std::vector<uint8_t>>::error(writer.last_error());
    }
  }
  writer.seek(end_pos);

  // Return data
  Result<std::vector<uint8_t>> result = Result<std::vector<uint8_t>>::ok(writer.data());

  // Add info about mipmap levels if generated
  if (tile_level_mode == TILE_MIPMAP_LEVELS && num_x_levels > 1) {
    result.add_warning("Generated " + std::to_string(num_x_levels) + " mipmap levels");
  } else if (tile_level_mode == TILE_RIPMAP_LEVELS) {
    result.add_warning("Generated " + std::to_string(num_x_levels) + "x" +
                       std::to_string(num_y_levels) + " ripmap levels");
  }

  // Carry forward warnings
  for (size_t i = 0; i < version_result.warnings.size(); i++) {
    result.warnings.push_back(version_result.warnings[i]);
  }
  for (size_t i = 0; i < header_result.warnings.size(); i++) {
    result.warnings.push_back(header_result.warnings[i]);
  }

  return result;
}

// Overload with default compression level
Result<std::vector<uint8_t>> SaveTiledToMemory(const ImageData& image) {
  return SaveTiledToMemory(image, 6);
}

// Save tiled EXR to file
Result<void> SaveTiledToFile(const char* filename, const ImageData& image, int compression_level) {
  if (!filename) {
    return Result<void>::error(
      ErrorInfo(ErrorCode::InvalidArgument, "Null filename",
                "SaveTiledToFile", 0));
  }

  // Save to memory first
  auto mem_result = SaveTiledToMemory(image, compression_level);
  if (!mem_result.success) {
    Result<void> result;
    result.success = false;
    result.errors = mem_result.errors;
    result.warnings = mem_result.warnings;
    return result;
  }

  // Write to file
  FILE* fp = fopen(filename, "wb");
  if (!fp) {
    return Result<void>::error(
      ErrorInfo(ErrorCode::IOError, "Failed to open file for writing",
                filename, 0));
  }

  size_t written = fwrite(mem_result.value.data(), 1, mem_result.value.size(), fp);
  fclose(fp);

  if (written != mem_result.value.size()) {
    return Result<void>::error(
      ErrorInfo(ErrorCode::IOError, "Failed to write all data to file",
                filename, 0));
  }

  Result<void> result = Result<void>::ok();
  result.warnings = mem_result.warnings;
  return result;
}

// ============================================================================
// Deep Image Writing
// ============================================================================

// Save deep scanline EXR to memory
Result<std::vector<uint8_t>> SaveDeepToMemory(const DeepImageData& deep, int compression_level) {
  std::vector<uint8_t> output;
  std::vector<std::string> warnings;

  // Validate input
  if (deep.width <= 0 || deep.height <= 0) {
    return Result<std::vector<uint8_t>>::error(
      ErrorInfo(ErrorCode::InvalidArgument, "Invalid deep image dimensions",
                "SaveDeepToMemory", 0));
  }

  if (deep.sample_counts.size() != static_cast<size_t>(deep.width) * deep.height) {
    return Result<std::vector<uint8_t>>::error(
      ErrorInfo(ErrorCode::InvalidArgument,
                "Sample counts array size mismatch with dimensions",
                "SaveDeepToMemory", 0));
  }

  if (deep.header.channels.empty()) {
    return Result<std::vector<uint8_t>>::error(
      ErrorInfo(ErrorCode::InvalidArgument, "No channels specified",
                "SaveDeepToMemory", 0));
  }

  // Verify total_samples matches sum of sample_counts
  size_t counted_samples = 0;
  for (size_t i = 0; i < deep.sample_counts.size(); i++) {
    counted_samples += deep.sample_counts[i];
  }
  if (counted_samples != deep.total_samples) {
    return Result<std::vector<uint8_t>>::error(
      ErrorInfo(ErrorCode::InvalidArgument,
                "total_samples doesn't match sum of sample_counts",
                "SaveDeepToMemory", 0));
  }

  // Verify channel_data sizes
  for (size_t c = 0; c < deep.header.channels.size(); c++) {
    if (deep.channel_data.size() <= c || deep.channel_data[c].size() != deep.total_samples) {
      return Result<std::vector<uint8_t>>::error(
        ErrorInfo(ErrorCode::InvalidArgument,
                  "Channel data size mismatch for channel " + std::to_string(c),
                  "SaveDeepToMemory", 0));
    }
  }

  int width = deep.width;
  int height = deep.height;

  // Create header copy with deep-specific settings
  Header header = deep.header;
  header.type = "deepscanline";
  if (header.data_window.max_x == 0 && header.data_window.max_y == 0) {
    header.data_window.min_x = 0;
    header.data_window.min_y = 0;
    header.data_window.max_x = width - 1;
    header.data_window.max_y = height - 1;
    header.display_window = header.data_window;
  }
  if (header.pixel_aspect_ratio <= 0.0f) {
    header.pixel_aspect_ratio = 1.0f;
  }
  if (header.screen_window_width <= 0.0f) {
    header.screen_window_width = 1.0f;
  }

  // Default to ZIP compression for deep if none specified
  if (header.compression == COMPRESSION_NONE) {
    header.compression = COMPRESSION_ZIP;
  }
  // Deep only supports NONE, RLE, ZIPS, ZIP
  if (header.compression != COMPRESSION_NONE &&
      header.compression != COMPRESSION_RLE &&
      header.compression != COMPRESSION_ZIPS &&
      header.compression != COMPRESSION_ZIP) {
    warnings.push_back("Compression type not supported for deep images, using ZIP");
    header.compression = COMPRESSION_ZIP;
  }

  // Calculate bytes per sample for each channel
  std::vector<int> channel_sizes;
  for (size_t c = 0; c < header.channels.size(); c++) {
    int sz = 4;  // Default FLOAT
    switch (header.channels[c].pixel_type) {
      case PIXEL_TYPE_UINT:  sz = 4; break;
      case PIXEL_TYPE_HALF:  sz = 2; break;
      case PIXEL_TYPE_FLOAT: sz = 4; break;
      default: sz = 4; break;
    }
    channel_sizes.push_back(sz);
  }

  // Create version (deep scanline = non_image flag set)
  Version version;
  version.version = 2;
  version.tiled = false;
  version.long_name = false;
  version.non_image = true;  // Deep data flag
  version.multipart = false;

  // Reserve space for output
  output.reserve(1024 * 1024);  // 1MB initial

  // Write magic number
  output.push_back(0x76);
  output.push_back(0x2f);
  output.push_back(0x31);
  output.push_back(0x01);

  // Write version
  uint32_t version_bits = version.version;
  if (version.tiled) version_bits |= 0x200;
  if (version.long_name) version_bits |= 0x400;
  if (version.non_image) version_bits |= 0x800;
  if (version.multipart) version_bits |= 0x1000;
  output.push_back(static_cast<uint8_t>(version_bits & 0xFF));
  output.push_back(static_cast<uint8_t>((version_bits >> 8) & 0xFF));
  output.push_back(static_cast<uint8_t>((version_bits >> 16) & 0xFF));
  output.push_back(static_cast<uint8_t>((version_bits >> 24) & 0xFF));

  // Lambda to write bytes
  auto write_bytes = [&output](const void* data, size_t len) {
    const uint8_t* ptr = static_cast<const uint8_t*>(data);
    output.insert(output.end(), ptr, ptr + len);
  };

  // Lambda to write null-terminated string
  auto write_string = [&output](const std::string& s) {
    output.insert(output.end(), s.begin(), s.end());
    output.push_back(0);
  };

  // Lambda to write uint32
  auto write_u32 = [&output](uint32_t v) {
    output.push_back(static_cast<uint8_t>(v & 0xFF));
    output.push_back(static_cast<uint8_t>((v >> 8) & 0xFF));
    output.push_back(static_cast<uint8_t>((v >> 16) & 0xFF));
    output.push_back(static_cast<uint8_t>((v >> 24) & 0xFF));
  };

  // Lambda to write int32
  auto write_i32 = [&output](int32_t v) {
    uint32_t u;
    std::memcpy(&u, &v, 4);
    output.push_back(static_cast<uint8_t>(u & 0xFF));
    output.push_back(static_cast<uint8_t>((u >> 8) & 0xFF));
    output.push_back(static_cast<uint8_t>((u >> 16) & 0xFF));
    output.push_back(static_cast<uint8_t>((u >> 24) & 0xFF));
  };

  // Lambda to write uint64
  auto write_u64 = [&output](uint64_t v) {
    for (int i = 0; i < 8; i++) {
      output.push_back(static_cast<uint8_t>((v >> (i * 8)) & 0xFF));
    }
  };

  // Lambda to write float
  auto write_float = [&output](float f) {
    uint32_t u;
    std::memcpy(&u, &f, 4);
    output.push_back(static_cast<uint8_t>(u & 0xFF));
    output.push_back(static_cast<uint8_t>((u >> 8) & 0xFF));
    output.push_back(static_cast<uint8_t>((u >> 16) & 0xFF));
    output.push_back(static_cast<uint8_t>((u >> 24) & 0xFF));
  };

  // Lambda to write attribute
  auto write_attribute = [&](const std::string& name, const std::string& type,
                              const void* data, size_t size) {
    write_string(name);
    write_string(type);
    write_u32(static_cast<uint32_t>(size));
    write_bytes(data, size);
  };

  // Write header attributes

  // channels (chlist)
  {
    std::vector<uint8_t> chlist;
    for (const auto& ch : header.channels) {
      for (char c : ch.name) chlist.push_back(static_cast<uint8_t>(c));
      chlist.push_back(0);
      // pixel type (int32)
      uint32_t pt = ch.pixel_type;
      chlist.push_back(static_cast<uint8_t>(pt & 0xFF));
      chlist.push_back(static_cast<uint8_t>((pt >> 8) & 0xFF));
      chlist.push_back(static_cast<uint8_t>((pt >> 16) & 0xFF));
      chlist.push_back(static_cast<uint8_t>((pt >> 24) & 0xFF));
      // pLinear (uint8) + 3 padding
      chlist.push_back(0); chlist.push_back(0);
      chlist.push_back(0); chlist.push_back(0);
      // x_sampling (int32)
      int32_t xs = ch.x_sampling > 0 ? ch.x_sampling : 1;
      chlist.push_back(static_cast<uint8_t>(xs & 0xFF));
      chlist.push_back(static_cast<uint8_t>((xs >> 8) & 0xFF));
      chlist.push_back(static_cast<uint8_t>((xs >> 16) & 0xFF));
      chlist.push_back(static_cast<uint8_t>((xs >> 24) & 0xFF));
      // y_sampling (int32)
      int32_t ys = ch.y_sampling > 0 ? ch.y_sampling : 1;
      chlist.push_back(static_cast<uint8_t>(ys & 0xFF));
      chlist.push_back(static_cast<uint8_t>((ys >> 8) & 0xFF));
      chlist.push_back(static_cast<uint8_t>((ys >> 16) & 0xFF));
      chlist.push_back(static_cast<uint8_t>((ys >> 24) & 0xFF));
    }
    chlist.push_back(0);  // terminating null
    write_attribute("channels", "chlist", chlist.data(), chlist.size());
  }

  // compression
  {
    uint8_t comp = static_cast<uint8_t>(header.compression);
    write_attribute("compression", "compression", &comp, 1);
  }

  // dataWindow
  {
    int32_t dw[4] = {header.data_window.min_x, header.data_window.min_y,
                      header.data_window.max_x, header.data_window.max_y};
    write_attribute("dataWindow", "box2i", dw, 16);
  }

  // displayWindow
  {
    int32_t dw[4] = {header.display_window.min_x, header.display_window.min_y,
                      header.display_window.max_x, header.display_window.max_y};
    write_attribute("displayWindow", "box2i", dw, 16);
  }

  // lineOrder (INCREASING_Y = 0)
  {
    uint8_t lo = static_cast<uint8_t>(header.line_order);
    write_attribute("lineOrder", "lineOrder", &lo, 1);
  }

  // pixelAspectRatio
  write_attribute("pixelAspectRatio", "float", &header.pixel_aspect_ratio, 4);

  // screenWindowCenter
  {
    float swc[2] = {header.screen_window_center[0], header.screen_window_center[1]};
    write_attribute("screenWindowCenter", "v2f", swc, 8);
  }

  // screenWindowWidth
  write_attribute("screenWindowWidth", "float", &header.screen_window_width, 4);

  // type = "deepscanline"
  {
    std::string type = "deepscanline";
    write_attribute("type", "string", type.c_str(), type.size() + 1);
  }

  // End of header
  output.push_back(0);

  // Calculate number of scanline blocks
  int scanlines_per_block = GetScanlinesPerBlock(header.compression);
  int num_blocks = (height + scanlines_per_block - 1) / scanlines_per_block;

  // Reserve offset table space
  size_t offset_table_pos = output.size();
  for (int i = 0; i < num_blocks; i++) {
    write_u64(0);  // Placeholder
  }

  // Get compression parameters
  int miniz_level = (compression_level < 1) ? 6 : (compression_level > 9) ? 9 : compression_level;

  // Store block offsets
  std::vector<uint64_t> block_offsets(static_cast<size_t>(num_blocks));

  // Write each scanline block
  for (int block = 0; block < num_blocks; block++) {
    block_offsets[static_cast<size_t>(block)] = output.size();

    int block_start_y = block * scanlines_per_block;
    int block_end_y = std::min(block_start_y + scanlines_per_block, height);
    int num_lines = block_end_y - block_start_y;
    size_t num_block_pixels = static_cast<size_t>(width) * num_lines;

    // Y coordinate for this block (in data window coordinates)
    int32_t y_coord = header.data_window.min_y + block_start_y;
    write_i32(y_coord);

    // Gather sample counts for this block
    std::vector<uint32_t> block_counts(num_block_pixels);
    size_t block_total_samples = 0;
    size_t sample_start = 0;

    // Calculate sample_start (sum of all samples before this block)
    for (int y = 0; y < block_start_y; y++) {
      for (int x = 0; x < width; x++) {
        sample_start += deep.sample_counts[static_cast<size_t>(y) * width + x];
      }
    }

    for (int y = block_start_y; y < block_end_y; y++) {
      for (int x = 0; x < width; x++) {
        size_t pixel_idx = static_cast<size_t>(y) * width + x;
        size_t block_pixel_idx = static_cast<size_t>(y - block_start_y) * width + x;
        block_counts[block_pixel_idx] = deep.sample_counts[pixel_idx];
        block_total_samples += deep.sample_counts[pixel_idx];
      }
    }

    // Compress sample counts
    std::vector<uint8_t> counts_raw(num_block_pixels * 4);
    std::memcpy(counts_raw.data(), block_counts.data(), num_block_pixels * 4);

    std::vector<uint8_t> counts_compressed;
    uint64_t unpacked_count_size = num_block_pixels * 4;
    uint64_t packed_count_size = unpacked_count_size;

    if (header.compression != COMPRESSION_NONE) {
      // Compress with zlib (raw deflate, no delta predictor for deep data)
#if defined(TINYEXR_USE_MINIZ)
      mz_ulong compressed_size = static_cast<mz_ulong>(unpacked_count_size + unpacked_count_size / 1000 + 128);
      counts_compressed.resize(compressed_size);
      int z_result = mz_compress2(counts_compressed.data(), &compressed_size,
                                  counts_raw.data(), static_cast<mz_ulong>(unpacked_count_size),
                                  miniz_level);
      if (z_result == MZ_OK && compressed_size < unpacked_count_size) {
        counts_compressed.resize(compressed_size);
        packed_count_size = compressed_size;
      } else {
        counts_compressed = counts_raw;
        packed_count_size = unpacked_count_size;
      }
#elif defined(TINYEXR_USE_ZLIB)
      uLongf compressed_size = compressBound(static_cast<uLong>(unpacked_count_size));
      counts_compressed.resize(compressed_size);
      int z_result = compress2(counts_compressed.data(), &compressed_size,
                                counts_raw.data(), static_cast<uLong>(unpacked_count_size),
                                miniz_level);
      if (z_result == Z_OK && compressed_size < unpacked_count_size) {
        counts_compressed.resize(compressed_size);
        packed_count_size = compressed_size;
      } else {
        counts_compressed = counts_raw;
        packed_count_size = unpacked_count_size;
      }
#else
      // No compression available
      counts_compressed = counts_raw;
      packed_count_size = unpacked_count_size;
#endif
    } else {
      counts_compressed = counts_raw;
    }

    // Gather sample data for this block (channel by channel)
    size_t unpacked_data_size = 0;
    for (size_t c = 0; c < header.channels.size(); c++) {
      unpacked_data_size += block_total_samples * channel_sizes[c];
    }

    std::vector<uint8_t> data_raw(unpacked_data_size);
    uint8_t* data_ptr = data_raw.data();

    for (size_t c = 0; c < header.channels.size(); c++) {
      int ch_size = channel_sizes[c];
      for (size_t s = 0; s < block_total_samples; s++) {
        size_t sample_idx = sample_start + s;
        float val = deep.channel_data[c][sample_idx];

        if (ch_size == 2) {
          // HALF
          uint16_t h = FloatToHalf(val);
          std::memcpy(data_ptr, &h, 2);
          data_ptr += 2;
        } else if (header.channels[c].pixel_type == PIXEL_TYPE_UINT) {
          // UINT
          uint32_t u = static_cast<uint32_t>(val);
          std::memcpy(data_ptr, &u, 4);
          data_ptr += 4;
        } else {
          // FLOAT
          std::memcpy(data_ptr, &val, 4);
          data_ptr += 4;
        }
      }
    }

    // Compress sample data
    std::vector<uint8_t> data_compressed;
    uint64_t packed_data_size = unpacked_data_size;

    if (header.compression != COMPRESSION_NONE && unpacked_data_size > 0) {
#if defined(TINYEXR_USE_MINIZ)
      mz_ulong compressed_size = static_cast<mz_ulong>(unpacked_data_size + unpacked_data_size / 1000 + 128);
      data_compressed.resize(compressed_size);
      int z_result = mz_compress2(data_compressed.data(), &compressed_size,
                                  data_raw.data(), static_cast<mz_ulong>(unpacked_data_size),
                                  miniz_level);
      if (z_result == MZ_OK && compressed_size < unpacked_data_size) {
        data_compressed.resize(compressed_size);
        packed_data_size = compressed_size;
      } else {
        data_compressed = data_raw;
        packed_data_size = unpacked_data_size;
      }
#elif defined(TINYEXR_USE_ZLIB)
      uLongf compressed_size = compressBound(static_cast<uLong>(unpacked_data_size));
      data_compressed.resize(compressed_size);
      int z_result = compress2(data_compressed.data(), &compressed_size,
                                data_raw.data(), static_cast<uLong>(unpacked_data_size),
                                miniz_level);
      if (z_result == Z_OK && compressed_size < unpacked_data_size) {
        data_compressed.resize(compressed_size);
        packed_data_size = compressed_size;
      } else {
        data_compressed = data_raw;
        packed_data_size = unpacked_data_size;
      }
#else
      // No compression available
      data_compressed = data_raw;
      packed_data_size = unpacked_data_size;
#endif
    } else {
      data_compressed = data_raw;
    }

    // Write block header: packed_count_size, unpacked_count_size, packed_data_size
    write_u64(packed_count_size);
    write_u64(unpacked_count_size);
    write_u64(packed_data_size);

    // Write compressed sample counts
    write_bytes(counts_compressed.data(), packed_count_size);

    // Write compressed sample data
    if (packed_data_size > 0) {
      write_bytes(data_compressed.data(), packed_data_size);
    }
  }

  // Go back and write offset table
  for (int i = 0; i < num_blocks; i++) {
    size_t offset_pos = offset_table_pos + static_cast<size_t>(i) * 8;
    uint64_t offset = block_offsets[static_cast<size_t>(i)];
    for (int j = 0; j < 8; j++) {
      output[offset_pos + j] = static_cast<uint8_t>((offset >> (j * 8)) & 0xFF);
    }
  }

  auto result = Result<std::vector<uint8_t>>::ok(std::move(output));
  result.warnings = warnings;
  return result;
}

// Convenience overload with default compression level
Result<std::vector<uint8_t>> SaveDeepToMemory(const DeepImageData& deep) {
  return SaveDeepToMemory(deep, 6);
}

// Save deep scanline EXR to file
Result<void> SaveDeepToFile(const char* filename, const DeepImageData& deep, int compression_level) {
  if (!filename) {
    return Result<void>::error(
      ErrorInfo(ErrorCode::InvalidArgument, "Null filename",
                "SaveDeepToFile", 0));
  }

  // Save to memory first
  auto mem_result = SaveDeepToMemory(deep, compression_level);
  if (!mem_result.success) {
    Result<void> result;
    result.success = false;
    result.errors = mem_result.errors;
    result.warnings = mem_result.warnings;
    return result;
  }

  // Write to file
  FILE* fp = fopen(filename, "wb");
  if (!fp) {
    return Result<void>::error(
      ErrorInfo(ErrorCode::IOError, "Failed to open file for writing",
                filename, 0));
  }

  size_t written = fwrite(mem_result.value.data(), 1, mem_result.value.size(), fp);
  fclose(fp);

  if (written != mem_result.value.size()) {
    return Result<void>::error(
      ErrorInfo(ErrorCode::IOError, "Failed to write all data to file",
                filename, 0));
  }

  Result<void> result = Result<void>::ok();
  result.warnings = mem_result.warnings;
  return result;
}

// ============================================================================
// Deep Tiled Image Writing
// ============================================================================

Result<std::vector<uint8_t>> SaveDeepTiledToMemory(const DeepImageData& deep, int compression_level) {
  std::vector<uint8_t> output;
  std::vector<std::string> warnings;

  // Validate input
  if (deep.width <= 0 || deep.height <= 0) {
    return Result<std::vector<uint8_t>>::error(
      ErrorInfo(ErrorCode::InvalidArgument, "Invalid deep image dimensions",
                "SaveDeepTiledToMemory", 0));
  }

  if (deep.sample_counts.size() != static_cast<size_t>(deep.width) * deep.height) {
    return Result<std::vector<uint8_t>>::error(
      ErrorInfo(ErrorCode::InvalidArgument,
                "Sample counts array size mismatch with dimensions",
                "SaveDeepTiledToMemory", 0));
  }

  if (deep.header.channels.empty()) {
    return Result<std::vector<uint8_t>>::error(
      ErrorInfo(ErrorCode::InvalidArgument, "No channels specified",
                "SaveDeepTiledToMemory", 0));
  }

  // Verify total_samples matches sum of sample_counts
  size_t counted_samples = 0;
  for (size_t i = 0; i < deep.sample_counts.size(); i++) {
    counted_samples += deep.sample_counts[i];
  }
  if (counted_samples != deep.total_samples) {
    return Result<std::vector<uint8_t>>::error(
      ErrorInfo(ErrorCode::InvalidArgument,
                "total_samples doesn't match sum of sample_counts",
                "SaveDeepTiledToMemory", 0));
  }

  // Verify channel_data sizes
  for (size_t c = 0; c < deep.header.channels.size(); c++) {
    if (deep.channel_data.size() <= c || deep.channel_data[c].size() != deep.total_samples) {
      return Result<std::vector<uint8_t>>::error(
        ErrorInfo(ErrorCode::InvalidArgument,
                  "Channel data size mismatch for channel " + std::to_string(c),
                  "SaveDeepTiledToMemory", 0));
    }
  }

  int width = deep.width;
  int height = deep.height;

  // Create header copy with deep tiled settings
  Header header = deep.header;
  header.type = "deeptile";
  header.tiled = true;
  header.is_deep = true;

  // Default tile size if not specified
  if (header.tile_size_x <= 0) header.tile_size_x = 64;
  if (header.tile_size_y <= 0) header.tile_size_y = 64;
  header.tile_level_mode = TILE_ONE_LEVEL;  // Only single level for now
  header.tile_rounding_mode = 0;

  if (header.data_window.max_x == 0 && header.data_window.max_y == 0) {
    header.data_window.min_x = 0;
    header.data_window.min_y = 0;
    header.data_window.max_x = width - 1;
    header.data_window.max_y = height - 1;
    header.display_window = header.data_window;
  }
  if (header.pixel_aspect_ratio <= 0.0f) {
    header.pixel_aspect_ratio = 1.0f;
  }
  if (header.screen_window_width <= 0.0f) {
    header.screen_window_width = 1.0f;
  }

  // Default to ZIP compression for deep if none specified
  if (header.compression == COMPRESSION_NONE) {
    header.compression = COMPRESSION_ZIP;
  }
  // Deep only supports NONE, RLE, ZIPS, ZIP
  if (header.compression != COMPRESSION_NONE &&
      header.compression != COMPRESSION_RLE &&
      header.compression != COMPRESSION_ZIPS &&
      header.compression != COMPRESSION_ZIP) {
    warnings.push_back("Compression type not supported for deep images, using ZIP");
    header.compression = COMPRESSION_ZIP;
  }

  int miniz_level = compression_level;
  if (miniz_level < 1) miniz_level = 1;
  if (miniz_level > 9) miniz_level = 9;

  // Calculate tile counts
  int num_x_tiles = (width + header.tile_size_x - 1) / header.tile_size_x;
  int num_y_tiles = (height + header.tile_size_y - 1) / header.tile_size_y;
  int total_tiles = num_x_tiles * num_y_tiles;
  header.chunk_count = total_tiles;

  // Calculate bytes per sample for each channel
  std::vector<int> channel_sizes;
  for (size_t c = 0; c < header.channels.size(); c++) {
    int sz = 4;  // Default FLOAT
    switch (header.channels[c].pixel_type) {
      case PIXEL_TYPE_UINT:  sz = 4; break;
      case PIXEL_TYPE_HALF:  sz = 2; break;
      case PIXEL_TYPE_FLOAT: sz = 4; break;
      default: sz = 4; break;
    }
    channel_sizes.push_back(sz);
  }

  // Create version (deep tiled = tiled + non_image flags set)
  Version version;
  version.version = 2;
  version.tiled = true;
  version.long_name = false;
  version.non_image = true;  // Deep data flag
  version.multipart = false;

  // Reserve space for output
  output.reserve(1024 * 1024);  // 1MB initial

  // Write magic number
  output.push_back(0x76);
  output.push_back(0x2f);
  output.push_back(0x31);
  output.push_back(0x01);

  // Write version
  uint32_t version_bits = version.version;
  if (version.tiled) version_bits |= 0x200;
  if (version.long_name) version_bits |= 0x400;
  if (version.non_image) version_bits |= 0x800;
  if (version.multipart) version_bits |= 0x1000;
  output.push_back(static_cast<uint8_t>(version_bits & 0xFF));
  output.push_back(static_cast<uint8_t>((version_bits >> 8) & 0xFF));
  output.push_back(static_cast<uint8_t>((version_bits >> 16) & 0xFF));
  output.push_back(static_cast<uint8_t>((version_bits >> 24) & 0xFF));

  // Helper lambdas
  auto write_bytes = [&output](const void* data, size_t len) {
    const uint8_t* ptr = static_cast<const uint8_t*>(data);
    output.insert(output.end(), ptr, ptr + len);
  };

  auto write_string = [&output](const std::string& s) {
    output.insert(output.end(), s.begin(), s.end());
    output.push_back(0);
  };

  auto write_u32 = [&output](uint32_t v) {
    output.push_back(static_cast<uint8_t>(v & 0xFF));
    output.push_back(static_cast<uint8_t>((v >> 8) & 0xFF));
    output.push_back(static_cast<uint8_t>((v >> 16) & 0xFF));
    output.push_back(static_cast<uint8_t>((v >> 24) & 0xFF));
  };

  auto write_i32 = [&output](int32_t v) {
    uint32_t u;
    std::memcpy(&u, &v, 4);
    output.push_back(static_cast<uint8_t>(u & 0xFF));
    output.push_back(static_cast<uint8_t>((u >> 8) & 0xFF));
    output.push_back(static_cast<uint8_t>((u >> 16) & 0xFF));
    output.push_back(static_cast<uint8_t>((u >> 24) & 0xFF));
  };

  auto write_u64 = [&output](uint64_t v) {
    for (int i = 0; i < 8; i++) {
      output.push_back(static_cast<uint8_t>((v >> (i * 8)) & 0xFF));
    }
  };

  auto write_float = [&output](float f) {
    uint32_t u;
    std::memcpy(&u, &f, 4);
    output.push_back(static_cast<uint8_t>(u & 0xFF));
    output.push_back(static_cast<uint8_t>((u >> 8) & 0xFF));
    output.push_back(static_cast<uint8_t>((u >> 16) & 0xFF));
    output.push_back(static_cast<uint8_t>((u >> 24) & 0xFF));
  };

  auto write_attribute = [&](const std::string& name, const std::string& type,
                              const void* data, size_t size) {
    write_string(name);
    write_string(type);
    write_u32(static_cast<uint32_t>(size));
    write_bytes(data, size);
  };

  // Write header attributes

  // channels (chlist)
  {
    std::vector<uint8_t> chlist;
    for (const auto& ch : header.channels) {
      for (char c : ch.name) chlist.push_back(static_cast<uint8_t>(c));
      chlist.push_back(0);
      uint32_t pt = ch.pixel_type;
      chlist.push_back(static_cast<uint8_t>(pt & 0xFF));
      chlist.push_back(static_cast<uint8_t>((pt >> 8) & 0xFF));
      chlist.push_back(static_cast<uint8_t>((pt >> 16) & 0xFF));
      chlist.push_back(static_cast<uint8_t>((pt >> 24) & 0xFF));
      chlist.push_back(0); chlist.push_back(0);
      chlist.push_back(0); chlist.push_back(0);
      int32_t xs = ch.x_sampling > 0 ? ch.x_sampling : 1;
      chlist.push_back(static_cast<uint8_t>(xs & 0xFF));
      chlist.push_back(static_cast<uint8_t>((xs >> 8) & 0xFF));
      chlist.push_back(static_cast<uint8_t>((xs >> 16) & 0xFF));
      chlist.push_back(static_cast<uint8_t>((xs >> 24) & 0xFF));
      int32_t ys = ch.y_sampling > 0 ? ch.y_sampling : 1;
      chlist.push_back(static_cast<uint8_t>(ys & 0xFF));
      chlist.push_back(static_cast<uint8_t>((ys >> 8) & 0xFF));
      chlist.push_back(static_cast<uint8_t>((ys >> 16) & 0xFF));
      chlist.push_back(static_cast<uint8_t>((ys >> 24) & 0xFF));
    }
    chlist.push_back(0);
    write_attribute("channels", "chlist", chlist.data(), chlist.size());
  }

  // compression
  {
    uint8_t comp = static_cast<uint8_t>(header.compression);
    write_attribute("compression", "compression", &comp, 1);
  }

  // dataWindow
  {
    int32_t dw[4] = {header.data_window.min_x, header.data_window.min_y,
                     header.data_window.max_x, header.data_window.max_y};
    write_attribute("dataWindow", "box2i", dw, 16);
  }

  // displayWindow
  {
    int32_t dw[4] = {header.display_window.min_x, header.display_window.min_y,
                     header.display_window.max_x, header.display_window.max_y};
    write_attribute("displayWindow", "box2i", dw, 16);
  }

  // lineOrder
  {
    uint8_t lo = static_cast<uint8_t>(header.line_order);
    write_attribute("lineOrder", "lineOrder", &lo, 1);
  }

  // pixelAspectRatio
  {
    write_attribute("pixelAspectRatio", "float", &header.pixel_aspect_ratio, 4);
  }

  // screenWindowCenter
  {
    float swc[2] = {header.screen_window_center[0], header.screen_window_center[1]};
    write_attribute("screenWindowCenter", "v2f", swc, 8);
  }

  // screenWindowWidth
  {
    write_attribute("screenWindowWidth", "float", &header.screen_window_width, 4);
  }

  // tiles (tiledesc) - required for tiled images
  {
    std::vector<uint8_t> tiledesc(9);
    uint32_t tx = header.tile_size_x;
    uint32_t ty = header.tile_size_y;
    tiledesc[0] = static_cast<uint8_t>(tx & 0xFF);
    tiledesc[1] = static_cast<uint8_t>((tx >> 8) & 0xFF);
    tiledesc[2] = static_cast<uint8_t>((tx >> 16) & 0xFF);
    tiledesc[3] = static_cast<uint8_t>((tx >> 24) & 0xFF);
    tiledesc[4] = static_cast<uint8_t>(ty & 0xFF);
    tiledesc[5] = static_cast<uint8_t>((ty >> 8) & 0xFF);
    tiledesc[6] = static_cast<uint8_t>((ty >> 16) & 0xFF);
    tiledesc[7] = static_cast<uint8_t>((ty >> 24) & 0xFF);
    uint8_t mode = static_cast<uint8_t>(header.tile_level_mode & 0x0F);
    mode |= static_cast<uint8_t>((header.tile_rounding_mode & 0x01) << 4);
    tiledesc[8] = mode;
    write_attribute("tiles", "tiledesc", tiledesc.data(), 9);
  }

  // type (required for deep)
  {
    write_attribute("type", "string", header.type.data(), header.type.size());
  }

  // chunkCount (required for multipart/deep)
  {
    int32_t cc = header.chunk_count;
    write_attribute("chunkCount", "int", &cc, 4);
  }

  // version (deep data version = 1)
  {
    int32_t ver = 1;
    write_attribute("version", "int", &ver, 4);
  }

  // Custom attributes
  for (const auto& attr : header.custom_attributes) {
    if (attr.name.empty()) continue;
    write_string(attr.name);
    write_string(attr.type);
    write_u32(static_cast<uint32_t>(attr.data.size()));
    if (!attr.data.empty()) {
      write_bytes(attr.data.data(), attr.data.size());
    }
  }

  // End of header
  output.push_back(0);

  // Reserve space for tile offset table
  size_t offset_table_pos = output.size();
  std::vector<uint64_t> tile_offsets(static_cast<size_t>(total_tiles), 0);
  for (int i = 0; i < total_tiles; i++) {
    write_u64(0);  // Placeholder
  }

  // Build cumulative sample index for quick lookup
  std::vector<size_t> cumulative_samples(static_cast<size_t>(width) * height + 1);
  cumulative_samples[0] = 0;
  for (size_t i = 0; i < deep.sample_counts.size(); i++) {
    cumulative_samples[i + 1] = cumulative_samples[i] + deep.sample_counts[i];
  }

  // Write each tile
  int tile_idx = 0;
  for (int tile_y = 0; tile_y < num_y_tiles; tile_y++) {
    for (int tile_x = 0; tile_x < num_x_tiles; tile_x++) {
      tile_offsets[static_cast<size_t>(tile_idx)] = output.size();

      // Tile coordinates
      int tile_start_x = tile_x * header.tile_size_x;
      int tile_start_y = tile_y * header.tile_size_y;
      int tile_end_x = std::min(tile_start_x + header.tile_size_x, width);
      int tile_end_y = std::min(tile_start_y + header.tile_size_y, height);
      int tile_w = tile_end_x - tile_start_x;
      int tile_h = tile_end_y - tile_start_y;
      size_t num_tile_pixels = static_cast<size_t>(tile_w) * tile_h;

      // Write tile header: tile_x, tile_y, level_x, level_y
      write_i32(tile_x);
      write_i32(tile_y);
      write_i32(0);  // level_x (always 0 for ONE_LEVEL)
      write_i32(0);  // level_y

      // Gather sample counts for this tile
      std::vector<uint32_t> tile_counts(num_tile_pixels);
      size_t tile_total_samples = 0;

      for (int y = tile_start_y; y < tile_end_y; y++) {
        for (int x = tile_start_x; x < tile_end_x; x++) {
          size_t pixel_idx = static_cast<size_t>(y) * width + x;
          size_t tile_pixel_idx = static_cast<size_t>(y - tile_start_y) * tile_w + (x - tile_start_x);
          tile_counts[tile_pixel_idx] = deep.sample_counts[pixel_idx];
          tile_total_samples += deep.sample_counts[pixel_idx];
        }
      }

      // Compress sample counts
      std::vector<uint8_t> counts_raw(num_tile_pixels * 4);
      std::memcpy(counts_raw.data(), tile_counts.data(), num_tile_pixels * 4);

      std::vector<uint8_t> counts_compressed;
      uint64_t unpacked_count_size = num_tile_pixels * 4;
      uint64_t packed_count_size = unpacked_count_size;

      if (header.compression != COMPRESSION_NONE) {
#if defined(TINYEXR_USE_MINIZ)
        mz_ulong compressed_size = static_cast<mz_ulong>(unpacked_count_size + unpacked_count_size / 1000 + 128);
        counts_compressed.resize(compressed_size);
        int z_result = mz_compress2(counts_compressed.data(), &compressed_size,
                                    counts_raw.data(), static_cast<mz_ulong>(unpacked_count_size),
                                    miniz_level);
        if (z_result == MZ_OK && compressed_size < unpacked_count_size) {
          counts_compressed.resize(compressed_size);
          packed_count_size = compressed_size;
        } else {
          counts_compressed = counts_raw;
          packed_count_size = unpacked_count_size;
        }
#elif defined(TINYEXR_USE_ZLIB)
        uLongf compressed_size = compressBound(static_cast<uLong>(unpacked_count_size));
        counts_compressed.resize(compressed_size);
        int z_result = compress2(counts_compressed.data(), &compressed_size,
                                  counts_raw.data(), static_cast<uLong>(unpacked_count_size),
                                  miniz_level);
        if (z_result == Z_OK && compressed_size < unpacked_count_size) {
          counts_compressed.resize(compressed_size);
          packed_count_size = compressed_size;
        } else {
          counts_compressed = counts_raw;
          packed_count_size = unpacked_count_size;
        }
#else
        counts_compressed = counts_raw;
        packed_count_size = unpacked_count_size;
#endif
      } else {
        counts_compressed = counts_raw;
      }

      // Gather sample data for this tile (channel by channel)
      size_t unpacked_data_size = 0;
      for (size_t c = 0; c < header.channels.size(); c++) {
        unpacked_data_size += tile_total_samples * channel_sizes[c];
      }

      std::vector<uint8_t> data_raw(unpacked_data_size);
      uint8_t* data_ptr = data_raw.data();

      for (size_t c = 0; c < header.channels.size(); c++) {
        int ch_size = channel_sizes[c];
        // For each pixel in tile, write its samples
        for (int y = tile_start_y; y < tile_end_y; y++) {
          for (int x = tile_start_x; x < tile_end_x; x++) {
            size_t pixel_idx = static_cast<size_t>(y) * width + x;
            size_t sample_start = cumulative_samples[pixel_idx];
            uint32_t num_samples = deep.sample_counts[pixel_idx];

            for (uint32_t s = 0; s < num_samples; s++) {
              float val = deep.channel_data[c][sample_start + s];

              if (ch_size == 2) {
                uint16_t h = FloatToHalf(val);
                std::memcpy(data_ptr, &h, 2);
                data_ptr += 2;
              } else if (header.channels[c].pixel_type == PIXEL_TYPE_UINT) {
                uint32_t u = static_cast<uint32_t>(val);
                std::memcpy(data_ptr, &u, 4);
                data_ptr += 4;
              } else {
                std::memcpy(data_ptr, &val, 4);
                data_ptr += 4;
              }
            }
          }
        }
      }

      // Compress sample data
      std::vector<uint8_t> data_compressed;
      uint64_t packed_data_size = unpacked_data_size;

      if (header.compression != COMPRESSION_NONE && unpacked_data_size > 0) {
#if defined(TINYEXR_USE_MINIZ)
        mz_ulong compressed_size = static_cast<mz_ulong>(unpacked_data_size + unpacked_data_size / 1000 + 128);
        data_compressed.resize(compressed_size);
        int z_result = mz_compress2(data_compressed.data(), &compressed_size,
                                    data_raw.data(), static_cast<mz_ulong>(unpacked_data_size),
                                    miniz_level);
        if (z_result == MZ_OK && compressed_size < unpacked_data_size) {
          data_compressed.resize(compressed_size);
          packed_data_size = compressed_size;
        } else {
          data_compressed = data_raw;
          packed_data_size = unpacked_data_size;
        }
#elif defined(TINYEXR_USE_ZLIB)
        uLongf compressed_size = compressBound(static_cast<uLong>(unpacked_data_size));
        data_compressed.resize(compressed_size);
        int z_result = compress2(data_compressed.data(), &compressed_size,
                                  data_raw.data(), static_cast<uLong>(unpacked_data_size),
                                  miniz_level);
        if (z_result == Z_OK && compressed_size < unpacked_data_size) {
          data_compressed.resize(compressed_size);
          packed_data_size = compressed_size;
        } else {
          data_compressed = data_raw;
          packed_data_size = unpacked_data_size;
        }
#else
        data_compressed = data_raw;
        packed_data_size = unpacked_data_size;
#endif
      } else {
        data_compressed = data_raw;
      }

      // Write tile data: packed_count_size, unpacked_count_size, packed_data_size
      write_u64(packed_count_size);
      write_u64(unpacked_count_size);
      write_u64(packed_data_size);

      // Write compressed sample counts
      write_bytes(counts_compressed.data(), packed_count_size);

      // Write compressed sample data
      if (packed_data_size > 0) {
        write_bytes(data_compressed.data(), packed_data_size);
      }

      tile_idx++;
    }
  }

  // Go back and write offset table
  for (int i = 0; i < total_tiles; i++) {
    size_t offset_pos = offset_table_pos + static_cast<size_t>(i) * 8;
    uint64_t offset = tile_offsets[static_cast<size_t>(i)];
    for (int j = 0; j < 8; j++) {
      output[offset_pos + j] = static_cast<uint8_t>((offset >> (j * 8)) & 0xFF);
    }
  }

  auto result = Result<std::vector<uint8_t>>::ok(std::move(output));
  result.warnings = warnings;
  return result;
}

Result<std::vector<uint8_t>> SaveDeepTiledToMemory(const DeepImageData& deep) {
  return SaveDeepTiledToMemory(deep, 6);
}

Result<void> SaveDeepTiledToFile(const char* filename, const DeepImageData& deep, int compression_level) {
  if (!filename) {
    return Result<void>::error(
      ErrorInfo(ErrorCode::InvalidArgument, "Null filename",
                "SaveDeepTiledToFile", 0));
  }

  auto mem_result = SaveDeepTiledToMemory(deep, compression_level);
  if (!mem_result.success) {
    Result<void> result;
    result.success = false;
    result.errors = mem_result.errors;
    result.warnings = mem_result.warnings;
    return result;
  }

  FILE* fp = fopen(filename, "wb");
  if (!fp) {
    return Result<void>::error(
      ErrorInfo(ErrorCode::IOError, "Failed to open file for writing",
                filename, 0));
  }

  size_t written = fwrite(mem_result.value.data(), 1, mem_result.value.size(), fp);
  fclose(fp);

  if (written != mem_result.value.size()) {
    return Result<void>::error(
      ErrorInfo(ErrorCode::IOError, "Failed to write all data to file",
                filename, 0));
  }

  Result<void> result = Result<void>::ok();
  result.warnings = mem_result.warnings;
  return result;
}

// ============================================================================
// Multipart Image Writing
// ============================================================================

// Helper: Calculate tile count for a tiled part (for writing)
static int CalculateTileCountForWrite(const Header& header) {
  int width = header.data_window.width();
  int height = header.data_window.height();
  int tile_w = header.tile_size_x;
  int tile_h = header.tile_size_y;

  if (tile_w <= 0 || tile_h <= 0) return 0;

  int total_tiles = 0;

  if (header.tile_level_mode == 0) {
    // ONE_LEVEL: just base level
    int num_x = (width + tile_w - 1) / tile_w;
    int num_y = (height + tile_h - 1) / tile_h;
    total_tiles = num_x * num_y;
  } else if (header.tile_level_mode == 1) {
    // MIPMAP_LEVELS
    int w = width;
    int h = height;
    while (w >= 1 && h >= 1) {
      int num_x = (w + tile_w - 1) / tile_w;
      int num_y = (h + tile_h - 1) / tile_h;
      total_tiles += num_x * num_y;
      if (w == 1 && h == 1) break;
      w = std::max(1, (header.tile_rounding_mode == 0) ? (w / 2) : ((w + 1) / 2));
      h = std::max(1, (header.tile_rounding_mode == 0) ? (h / 2) : ((h + 1) / 2));
    }
  } else if (header.tile_level_mode == 2) {
    // RIPMAP_LEVELS
    int w = width;
    while (w >= 1) {
      int h = height;
      while (h >= 1) {
        int num_x = (w + tile_w - 1) / tile_w;
        int num_y = (h + tile_h - 1) / tile_h;
        total_tiles += num_x * num_y;
        if (h == 1) break;
        h = std::max(1, (header.tile_rounding_mode == 0) ? (h / 2) : ((h + 1) / 2));
      }
      if (w == 1) break;
      w = std::max(1, (header.tile_rounding_mode == 0) ? (w / 2) : ((w + 1) / 2));
    }
  }

  return total_tiles;
}

// Save multiple images as multipart EXR to memory
Result<std::vector<uint8_t>> SaveMultipartToMemory(const MultipartImageData& multipart,
                                                    int compression_level) {
  Writer writer;
  writer.set_context("Saving multipart EXR to memory");

  if (multipart.parts.empty() && multipart.deep_parts.empty()) {
    return Result<std::vector<uint8_t>>::error(
      ErrorInfo(ErrorCode::InvalidArgument, "No image parts to save",
                "SaveMultipartToMemory", 0));
  }

  // Determine if we need long_name support (attribute names > 31 chars)
  bool need_long_name = false;
  for (size_t i = 0; i < multipart.parts.size() && !need_long_name; i++) {
    if (multipart.parts[i].header.name.length() > 31) need_long_name = true;
    for (size_t ch = 0; ch < multipart.parts[i].header.channels.size(); ch++) {
      if (multipart.parts[i].header.channels[ch].name.length() > 31) {
        need_long_name = true;
        break;
      }
    }
  }

  // Create version
  Version version;
  version.version = 2;
  version.tiled = false;  // Can have mixed tiled/scanline parts
  version.long_name = need_long_name;
  version.non_image = !multipart.deep_parts.empty();
  version.multipart = true;

  // Check if any part is tiled
  for (size_t i = 0; i < multipart.parts.size(); i++) {
    if (multipart.parts[i].header.tiled) {
      version.tiled = true;
      break;
    }
  }

  // Write version
  Result<void> version_result = WriteVersion(writer, version);
  if (!version_result.success) {
    Result<std::vector<uint8_t>> result;
    result.success = false;
    result.errors = version_result.errors;
    return result;
  }

  // Build list of all parts (regular + deep) with their headers
  // For now, we only support regular image parts (deep writing is TODO)
  size_t total_parts = multipart.parts.size();
  std::vector<const ImageData*> part_data(total_parts);
  std::vector<Header> headers(total_parts);

  for (size_t i = 0; i < multipart.parts.size(); i++) {
    part_data[i] = &multipart.parts[i];
    headers[i] = multipart.parts[i].header;

    // Ensure required multipart attributes are set
    if (headers[i].name.empty()) {
      headers[i].name = "part" + std::to_string(i);
    }
    if (headers[i].type.empty()) {
      headers[i].type = headers[i].tiled ? "tiledimage" : "scanlineimage";
    }

    // Calculate chunk count if not set
    if (headers[i].chunk_count <= 0) {
      if (headers[i].tiled) {
        headers[i].chunk_count = CalculateTileCountForWrite(headers[i]);
      } else {
        int height = headers[i].data_window.height();
        int scanlines_per_block = GetScanlinesPerBlock(headers[i].compression);
        headers[i].chunk_count = (height + scanlines_per_block - 1) / scanlines_per_block;
      }
    }
  }

  // Write headers (each terminated by null byte, then empty header = just null byte)
  for (size_t i = 0; i < total_parts; i++) {
    Result<void> header_result = WriteHeader(writer, headers[i]);
    if (!header_result.success) {
      Result<std::vector<uint8_t>> result;
      result.success = false;
      result.errors = header_result.errors;
      return result;
    }
  }

  // Write empty header (just a null byte to terminate header list)
  if (!writer.write1(0)) {
    return Result<std::vector<uint8_t>>::error(writer.last_error());
  }

  // Reserve space for offset tables for all parts
  std::vector<size_t> offset_table_positions(total_parts);
  std::vector<std::vector<uint64_t>> part_offsets(total_parts);

  for (size_t part = 0; part < total_parts; part++) {
    int chunk_count = headers[part].chunk_count;
    offset_table_positions[part] = writer.tell();
    part_offsets[part].resize(static_cast<size_t>(chunk_count));

    // Write placeholder offsets
    for (int i = 0; i < chunk_count; i++) {
      if (!writer.write8(0)) {
        return Result<std::vector<uint8_t>>::error(writer.last_error());
      }
    }
  }

  // Work buffers
  size_t max_buffer_size = 0;
  for (size_t part = 0; part < total_parts; part++) {
    const Header& hdr = headers[part];
    size_t num_channels = hdr.channels.size();
    if (num_channels == 0) num_channels = 4;
    size_t bytes_per_pixel = num_channels * 2;  // HALF = 2 bytes

    if (hdr.tiled) {
      size_t tile_pixels = static_cast<size_t>(hdr.tile_size_x) * hdr.tile_size_y;
      max_buffer_size = std::max(max_buffer_size, bytes_per_pixel * tile_pixels);
    } else {
      int scanlines_per_block = GetScanlinesPerBlock(hdr.compression);
      size_t block_size = bytes_per_pixel * static_cast<size_t>(hdr.data_window.width()) * scanlines_per_block;
      max_buffer_size = std::max(max_buffer_size, block_size);
    }
  }

  std::vector<uint8_t> scanline_buffer(max_buffer_size);
  std::vector<uint8_t> reorder_buffer(max_buffer_size);
  std::vector<uint8_t> compress_buffer(max_buffer_size * 2);

  // Map channel names to RGBA indices
  auto GetRGBAIndex = [&](const std::string& name) -> int {
    if (name == "R" || name == "r") return 0;
    if (name == "G" || name == "g") return 1;
    if (name == "B" || name == "b") return 2;
    if (name == "A" || name == "a") return 3;
    if (name == "Y" || name == "y") return 0;  // Luminance
    return -1;
  };

  // Write chunk data for each part
  for (size_t part = 0; part < total_parts; part++) {
    const Header& hdr = headers[part];
    const ImageData& img = *part_data[part];
    int width = img.width;
    int height = img.height;

    // Build sorted channel list
    std::vector<Channel> sorted_channels = hdr.channels;
    std::sort(sorted_channels.begin(), sorted_channels.end(),
              [](const Channel& a, const Channel& b) { return a.name < b.name; });

    size_t num_channels = sorted_channels.size();
    if (num_channels == 0) num_channels = 4;
    size_t bytes_per_pixel = num_channels * 2;

    if (hdr.tiled) {
      // Write tiled data
      int tile_w = hdr.tile_size_x;
      int tile_h = hdr.tile_size_y;
      int num_tiles_x = (width + tile_w - 1) / tile_w;
      int num_tiles_y = (height + tile_h - 1) / tile_h;

      int chunk_idx = 0;
      for (int tile_y = 0; tile_y < num_tiles_y; tile_y++) {
        for (int tile_x = 0; tile_x < num_tiles_x; tile_x++) {
          // Record offset
          part_offsets[part][static_cast<size_t>(chunk_idx)] = writer.tell();

          // Write part number (for multipart)
          if (!writer.write4(static_cast<uint32_t>(part))) {
            return Result<std::vector<uint8_t>>::error(writer.last_error());
          }

          // Write tile header: tile_x, tile_y, level_x, level_y
          if (!writer.write4(static_cast<uint32_t>(tile_x)) ||
              !writer.write4(static_cast<uint32_t>(tile_y)) ||
              !writer.write4(0) ||  // level_x = 0 (base level)
              !writer.write4(0)) {  // level_y = 0 (base level)
            return Result<std::vector<uint8_t>>::error(writer.last_error());
          }

          // Calculate tile dimensions
          int tile_start_x = tile_x * tile_w;
          int tile_start_y = tile_y * tile_h;
          int actual_tile_w = std::min(tile_w, width - tile_start_x);
          int actual_tile_h = std::min(tile_h, height - tile_start_y);

          size_t tile_bytes_per_line = bytes_per_pixel * static_cast<size_t>(actual_tile_w);
          size_t actual_bytes = tile_bytes_per_line * static_cast<size_t>(actual_tile_h);

          // Convert tile data to half-precision per-channel format
          for (int line = 0; line < actual_tile_h; line++) {
            int y = tile_start_y + line;
            uint8_t* line_ptr = scanline_buffer.data() + static_cast<size_t>(line) * tile_bytes_per_line;

            size_t ch_offset = 0;
            for (size_t ch = 0; ch < sorted_channels.size(); ch++) {
              int rgba_idx = GetRGBAIndex(sorted_channels[ch].name);
              if (rgba_idx < 0) rgba_idx = static_cast<int>(ch % 4);

              for (int x = 0; x < actual_tile_w; x++) {
                int src_x = tile_start_x + x;
                float val = img.rgba[static_cast<size_t>(y) * width * 4 + src_x * 4 + rgba_idx];
                uint16_t half_val = FloatToHalf(val);

                line_ptr[ch_offset + x * 2 + 0] = static_cast<uint8_t>(half_val & 0xFF);
                line_ptr[ch_offset + x * 2 + 1] = static_cast<uint8_t>(half_val >> 8);
              }
              ch_offset += static_cast<size_t>(actual_tile_w) * 2;
            }
          }

          // Apply compression
          size_t compressed_size = actual_bytes;
          const uint8_t* data_to_write = scanline_buffer.data();

          switch (hdr.compression) {
            case COMPRESSION_NONE:
              break;

            case COMPRESSION_RLE:
              ReorderBytesForCompression(scanline_buffer.data(), reorder_buffer.data(), actual_bytes);
              ApplyDeltaPredictorEncode(reorder_buffer.data(), actual_bytes);
              if (CompressRle(reorder_buffer.data(), actual_bytes, compress_buffer)) {
                compressed_size = compress_buffer.size();
                data_to_write = compress_buffer.data();
              }
              break;

            case COMPRESSION_ZIPS:
            case COMPRESSION_ZIP:
#if defined(TINYEXR_USE_MINIZ) || defined(TINYEXR_USE_ZLIB)
              ReorderBytesForCompression(scanline_buffer.data(), reorder_buffer.data(), actual_bytes);
              ApplyDeltaPredictorEncode(reorder_buffer.data(), actual_bytes);
              if (CompressZip(reorder_buffer.data(), actual_bytes, compress_buffer, compression_level)) {
                compressed_size = compress_buffer.size();
                data_to_write = compress_buffer.data();
              }
#endif
              break;

            default:
              break;
          }

          // Write data size
          if (!writer.write4(static_cast<uint32_t>(compressed_size))) {
            return Result<std::vector<uint8_t>>::error(writer.last_error());
          }

          // Write compressed data
          if (!writer.write(compressed_size, data_to_write)) {
            return Result<std::vector<uint8_t>>::error(writer.last_error());
          }

          chunk_idx++;
        }
      }
    } else {
      // Write scanline data
      size_t bytes_per_scanline = bytes_per_pixel * static_cast<size_t>(width);
      int scanlines_per_block = GetScanlinesPerBlock(hdr.compression);
      int num_blocks = (height + scanlines_per_block - 1) / scanlines_per_block;

      for (int block = 0; block < num_blocks; block++) {
        int y_start = hdr.data_window.min_y + block * scanlines_per_block;
        int y_end = std::min(y_start + scanlines_per_block, hdr.data_window.min_y + height);
        int num_lines = y_end - y_start;

        // Record offset
        part_offsets[part][static_cast<size_t>(block)] = writer.tell();

        // Write part number (for multipart)
        if (!writer.write4(static_cast<uint32_t>(part))) {
          return Result<std::vector<uint8_t>>::error(writer.last_error());
        }

        // Write y coordinate
        if (!writer.write4(static_cast<uint32_t>(y_start))) {
          return Result<std::vector<uint8_t>>::error(writer.last_error());
        }

        size_t actual_bytes = bytes_per_scanline * static_cast<size_t>(num_lines);

        // Convert scanline data to half-precision per-channel format
        for (int line = 0; line < num_lines; line++) {
          int y = y_start - hdr.data_window.min_y + line;
          if (y < 0 || y >= height) continue;

          uint8_t* line_ptr = scanline_buffer.data() + static_cast<size_t>(line) * bytes_per_scanline;

          size_t ch_offset = 0;
          for (size_t ch = 0; ch < sorted_channels.size(); ch++) {
            int rgba_idx = GetRGBAIndex(sorted_channels[ch].name);
            if (rgba_idx < 0) rgba_idx = static_cast<int>(ch % 4);

            for (int x = 0; x < width; x++) {
              float val = img.rgba[static_cast<size_t>(y) * width * 4 + x * 4 + rgba_idx];
              uint16_t half_val = FloatToHalf(val);

              line_ptr[ch_offset + x * 2 + 0] = static_cast<uint8_t>(half_val & 0xFF);
              line_ptr[ch_offset + x * 2 + 1] = static_cast<uint8_t>(half_val >> 8);
            }
            ch_offset += static_cast<size_t>(width) * 2;
          }
        }

        // Apply compression
        size_t compressed_size = actual_bytes;
        const uint8_t* data_to_write = scanline_buffer.data();

        switch (hdr.compression) {
          case COMPRESSION_NONE:
            break;

          case COMPRESSION_RLE:
            ReorderBytesForCompression(scanline_buffer.data(), reorder_buffer.data(), actual_bytes);
            ApplyDeltaPredictorEncode(reorder_buffer.data(), actual_bytes);
            if (CompressRle(reorder_buffer.data(), actual_bytes, compress_buffer)) {
              compressed_size = compress_buffer.size();
              data_to_write = compress_buffer.data();
            }
            break;

          case COMPRESSION_ZIPS:
          case COMPRESSION_ZIP:
#if defined(TINYEXR_USE_MINIZ) || defined(TINYEXR_USE_ZLIB)
            ReorderBytesForCompression(scanline_buffer.data(), reorder_buffer.data(), actual_bytes);
            ApplyDeltaPredictorEncode(reorder_buffer.data(), actual_bytes);
            if (CompressZip(reorder_buffer.data(), actual_bytes, compress_buffer, compression_level)) {
              compressed_size = compress_buffer.size();
              data_to_write = compress_buffer.data();
            }
#endif
            break;

          default:
            break;
        }

        // Write data size
        if (!writer.write4(static_cast<uint32_t>(compressed_size))) {
          return Result<std::vector<uint8_t>>::error(writer.last_error());
        }

        // Write compressed data
        if (!writer.write(compressed_size, data_to_write)) {
          return Result<std::vector<uint8_t>>::error(writer.last_error());
        }
      }
    }
  }

  // Go back and write the offset tables for all parts
  size_t end_pos = writer.tell();
  for (size_t part = 0; part < total_parts; part++) {
    if (!writer.seek(offset_table_positions[part])) {
      return Result<std::vector<uint8_t>>::error(writer.last_error());
    }
    for (size_t i = 0; i < part_offsets[part].size(); i++) {
      if (!writer.write8(part_offsets[part][i])) {
        return Result<std::vector<uint8_t>>::error(writer.last_error());
      }
    }
  }
  writer.seek(end_pos);

  return Result<std::vector<uint8_t>>::ok(writer.data());
}

// Overload with default compression level
Result<std::vector<uint8_t>> SaveMultipartToMemory(const MultipartImageData& multipart) {
  return SaveMultipartToMemory(multipart, 6);
}

// Save multipart to file
Result<void> SaveMultipartToFile(const char* filename, const MultipartImageData& multipart,
                                  int compression_level) {
  if (!filename) {
    return Result<void>::error(
      ErrorInfo(ErrorCode::InvalidArgument, "Null filename",
                "SaveMultipartToFile", 0));
  }

  // Save to memory first
  auto mem_result = SaveMultipartToMemory(multipart, compression_level);
  if (!mem_result.success) {
    Result<void> result;
    result.success = false;
    result.errors = mem_result.errors;
    result.warnings = mem_result.warnings;
    return result;
  }

  // Write to file
  FILE* fp = fopen(filename, "wb");
  if (!fp) {
    return Result<void>::error(
      ErrorInfo(ErrorCode::IOError, "Failed to open file for writing",
                filename, 0));
  }

  size_t written = fwrite(mem_result.value.data(), 1, mem_result.value.size(), fp);
  fclose(fp);

  if (written != mem_result.value.size()) {
    return Result<void>::error(
      ErrorInfo(ErrorCode::IOError, "Failed to write all data to file",
                filename, 0));
  }

  Result<void> result = Result<void>::ok();
  result.warnings = mem_result.warnings;
  return result;
}

// ============================================================================
// Multipart/Deep Image Loading
// ============================================================================

// Helper: Load a single deep scanline part
static Result<DeepImageData> LoadDeepScanlinePart(
    const uint8_t* data, size_t size,
    Reader& reader, const Version& version, const Header& header,
    const std::vector<uint64_t>& offsets) {

  DeepImageData deep_data;
  deep_data.header = header;
  deep_data.width = header.data_window.width();
  deep_data.height = header.data_window.height();
  deep_data.num_channels = static_cast<int>(header.channels.size());

  int width = deep_data.width;
  int height = deep_data.height;
  size_t num_pixels = static_cast<size_t>(width) * height;

  // Allocate sample counts
  deep_data.sample_counts.resize(num_pixels, 0);

  // Calculate bytes per sample for each channel
  std::vector<int> channel_sizes;
  for (size_t i = 0; i < header.channels.size(); i++) {
    int sz = 0;
    switch (header.channels[i].pixel_type) {
      case PIXEL_TYPE_UINT:  sz = 4; break;
      case PIXEL_TYPE_HALF:  sz = 2; break;
      case PIXEL_TYPE_FLOAT: sz = 4; break;
      default: sz = 4; break;
    }
    channel_sizes.push_back(sz);
  }

  // Get scratch pool
  ScratchPool& pool = get_scratch_pool();

  // First pass: read sample counts for all scanlines
  int scanlines_per_block = GetScanlinesPerBlock(header.compression);
  int num_blocks = static_cast<int>(offsets.size());

  // Detect if this is multipart (has part number in chunks)
  bool is_multipart = version.multipart;

  for (int block = 0; block < num_blocks; block++) {
    if (!reader.seek(static_cast<size_t>(offsets[static_cast<size_t>(block)]))) {
      return Result<DeepImageData>::error(
        ErrorInfo(ErrorCode::InvalidData,
                  "Failed to seek to deep block " + std::to_string(block),
                  reader.context(), reader.tell()));
    }

    // For multipart files, skip part number
    if (is_multipart) {
      uint32_t part_number;
      if (!reader.read4(&part_number)) {
        return Result<DeepImageData>::error(reader.last_error());
      }
    }

    // Read block header: y_coord (4), packed_count_size (8),
    // unpacked_count_size (8), packed_data_size (8)
    // Note: OpenEXR 2.0 deep format does NOT store unpacked_data_size as a
    // separate field - it's calculated from sample counts and channel sizes
    int32_t y_coord;
    uint64_t packed_count_size, unpacked_count_size;
    uint64_t packed_data_size;

    if (!reader.read4(reinterpret_cast<uint32_t*>(&y_coord)) ||
        !reader.read8(&packed_count_size) ||
        !reader.read8(&unpacked_count_size) ||
        !reader.read8(&packed_data_size)) {
      return Result<DeepImageData>::error(
        ErrorInfo(ErrorCode::InvalidData,
                  "Failed to read deep block header",
                  reader.context(), reader.tell()));
    }

    // Sanity check on sizes to prevent memory allocation issues
    constexpr uint64_t kMaxDeepSize = 1024ULL * 1024ULL * 1024ULL;  // 1GB
    if (packed_count_size > kMaxDeepSize || unpacked_count_size > kMaxDeepSize ||
        packed_data_size > kMaxDeepSize) {
      return Result<DeepImageData>::error(
        ErrorInfo(ErrorCode::InvalidData,
                  "Unreasonable deep data size in block " + std::to_string(block),
                  reader.context(), reader.tell()));
    }

    // Calculate number of scanlines in this block
    int block_start_y = y_coord - header.data_window.min_y;
    int block_end_y = std::min(block_start_y + scanlines_per_block, height);
    int num_lines = block_end_y - block_start_y;
    size_t num_block_pixels = static_cast<size_t>(width) * num_lines;

    // Read and decompress sample counts
    std::vector<uint8_t> count_compressed(packed_count_size);
    if (packed_count_size > 0 &&
        !reader.read(packed_count_size, count_compressed.data())) {
      return Result<DeepImageData>::error(
        ErrorInfo(ErrorCode::InvalidData,
                  "Failed to read deep sample counts",
                  reader.context(), reader.tell()));
    }

    std::vector<uint32_t> sample_counts(num_block_pixels);
    if (packed_count_size == unpacked_count_size) {
      // Uncompressed
      if (packed_count_size == num_block_pixels * 4) {
        std::memcpy(sample_counts.data(), count_compressed.data(),
                    num_block_pixels * 4);
      }
    } else {
      // Decompress (raw zlib, no delta predictor or reordering for deep data)
#if defined(TINYEXR_USE_MINIZ)
      mz_ulong dest_len = static_cast<mz_ulong>(num_block_pixels * 4);
      mz_uncompress(reinterpret_cast<uint8_t*>(sample_counts.data()),
                    &dest_len, count_compressed.data(),
                    static_cast<mz_ulong>(packed_count_size));
#elif defined(TINYEXR_USE_ZLIB)
      uLongf dest_len = static_cast<uLongf>(num_block_pixels * 4);
      uncompress(reinterpret_cast<uint8_t*>(sample_counts.data()),
                 &dest_len, count_compressed.data(),
                 static_cast<uLong>(packed_count_size));
#else
      // No decompression available - this shouldn't happen
      return Result<DeepImageData>::error(
        ErrorInfo(ErrorCode::CompressionError,
                  "No compression library available for deep sample counts",
                  reader.context(), reader.tell()));
#endif
    }

    // Copy to output sample_counts
    for (size_t i = 0; i < num_block_pixels; i++) {
      size_t pixel_idx = static_cast<size_t>(block_start_y) * width + i;
      if (pixel_idx < num_pixels) {
        deep_data.sample_counts[pixel_idx] = sample_counts[i];
      }
    }

    // Skip sample data for now (we'll read in second pass)
    reader.seek_relative(packed_data_size);
  }

  // Calculate total samples
  deep_data.total_samples = 0;
  for (size_t i = 0; i < num_pixels; i++) {
    deep_data.total_samples += deep_data.sample_counts[i];
  }

  // Allocate channel data
  deep_data.channel_data.resize(header.channels.size());
  for (size_t c = 0; c < header.channels.size(); c++) {
    deep_data.channel_data[c].resize(deep_data.total_samples, 0.0f);
  }

  // Second pass: read sample data
  size_t sample_offset = 0;
  for (int block = 0; block < num_blocks; block++) {
    if (!reader.seek(static_cast<size_t>(offsets[static_cast<size_t>(block)]))) {
      return Result<DeepImageData>::error(
        ErrorInfo(ErrorCode::InvalidData,
                  "Failed to seek to deep block for data",
                  reader.context(), reader.tell()));
    }

    // For multipart files, skip part number
    if (is_multipart) {
      uint32_t part_number;
      reader.read4(&part_number);
    }

    // Read block header again
    int32_t y_coord;
    uint64_t packed_count_size, unpacked_count_size;
    uint64_t packed_data_size;

    reader.read4(reinterpret_cast<uint32_t*>(&y_coord));
    reader.read8(&packed_count_size);
    reader.read8(&unpacked_count_size);
    reader.read8(&packed_data_size);

    // Skip sample counts
    reader.seek_relative(packed_count_size);

    // Calculate block samples
    int block_start_y = y_coord - header.data_window.min_y;
    int block_end_y = std::min(block_start_y + scanlines_per_block, height);
    int num_lines = block_end_y - block_start_y;
    size_t num_block_pixels = static_cast<size_t>(width) * num_lines;

    size_t block_total_samples = 0;
    for (size_t i = 0; i < num_block_pixels; i++) {
      size_t pixel_idx = static_cast<size_t>(block_start_y) * width + i;
      if (pixel_idx < num_pixels) {
        block_total_samples += deep_data.sample_counts[pixel_idx];
      }
    }

    if (block_total_samples == 0 || packed_data_size == 0) {
      continue;  // No samples in this block
    }

    // Calculate unpacked data size from sample counts and channel sizes
    size_t unpacked_data_size = 0;
    for (size_t c = 0; c < header.channels.size(); c++) {
      unpacked_data_size += block_total_samples * channel_sizes[c];
    }

    // Read and decompress sample data
    std::vector<uint8_t> data_compressed(packed_data_size);
    if (packed_data_size > 0 &&
        !reader.read(packed_data_size, data_compressed.data())) {
      return Result<DeepImageData>::error(
        ErrorInfo(ErrorCode::InvalidData,
                  "Failed to read deep sample data",
                  reader.context(), reader.tell()));
    }

    std::vector<uint8_t> data_uncompressed(unpacked_data_size);
    if (packed_data_size == unpacked_data_size) {
      data_uncompressed = std::move(data_compressed);
    } else {
      // Decompress (raw zlib, no delta predictor or reordering for deep data)
#if defined(TINYEXR_USE_MINIZ)
      mz_ulong dest_len = static_cast<mz_ulong>(unpacked_data_size);
      mz_uncompress(data_uncompressed.data(), &dest_len,
                    data_compressed.data(), static_cast<mz_ulong>(packed_data_size));
#elif defined(TINYEXR_USE_ZLIB)
      uLongf dest_len = static_cast<uLongf>(unpacked_data_size);
      uncompress(data_uncompressed.data(), &dest_len,
                 data_compressed.data(), static_cast<uLong>(packed_data_size));
#else
      // No decompression available - shouldn't happen
      return Result<DeepImageData>::error(
        ErrorInfo(ErrorCode::CompressionError,
                  "No compression library available for deep sample data",
                  reader.context(), reader.tell()));
#endif
    }

    // Parse channel data from decompressed buffer
    // Deep data is stored channel by channel, sample by sample
    const uint8_t* ptr = data_uncompressed.data();
    for (size_t c = 0; c < header.channels.size(); c++) {
      int ch_size = channel_sizes[c];
      size_t ch_samples = block_total_samples;

      for (size_t s = 0; s < ch_samples && sample_offset + s < deep_data.total_samples; s++) {
        float val = 0.0f;
        if (ch_size == 2) {
          // HALF
          uint16_t h;
          std::memcpy(&h, ptr, 2);
          ptr += 2;
          val = HalfToFloat(h);
        } else {
          // FLOAT or UINT
          uint32_t u;
          std::memcpy(&u, ptr, 4);
          ptr += 4;
          if (header.channels[c].pixel_type == PIXEL_TYPE_FLOAT) {
            std::memcpy(&val, &u, 4);
          } else {
            val = static_cast<float>(u);
          }
        }
        deep_data.channel_data[c][sample_offset + s] = val;
      }
    }

    sample_offset += block_total_samples;
  }

  return Result<DeepImageData>::ok(deep_data);
}

// Helper: Calculate tile count for a tiled part
static int CalculateTileCount(const Header& header) {
  int width = header.data_window.width();
  int height = header.data_window.height();
  int tile_w = header.tile_size_x;
  int tile_h = header.tile_size_y;

  if (tile_w <= 0 || tile_h <= 0) return 0;

  int total_tiles = 0;

  if (header.tile_level_mode == 0) {
    // ONE_LEVEL: just base level
    int num_x = (width + tile_w - 1) / tile_w;
    int num_y = (height + tile_h - 1) / tile_h;
    total_tiles = num_x * num_y;
  } else if (header.tile_level_mode == 1) {
    // MIPMAP_LEVELS
    int w = width;
    int h = height;
    while (w >= 1 && h >= 1) {
      int num_x = (w + tile_w - 1) / tile_w;
      int num_y = (h + tile_h - 1) / tile_h;
      total_tiles += num_x * num_y;
      if (w == 1 && h == 1) break;
      w = std::max(1, (header.tile_rounding_mode == 0) ? (w / 2) : ((w + 1) / 2));
      h = std::max(1, (header.tile_rounding_mode == 0) ? (h / 2) : ((h + 1) / 2));
    }
  } else if (header.tile_level_mode == 2) {
    // RIPMAP_LEVELS
    int w = width;
    while (w >= 1) {
      int h = height;
      while (h >= 1) {
        int num_x = (w + tile_w - 1) / tile_w;
        int num_y = (h + tile_h - 1) / tile_h;
        total_tiles += num_x * num_y;
        if (h == 1) break;
        h = std::max(1, (header.tile_rounding_mode == 0) ? (h / 2) : ((h + 1) / 2));
      }
      if (w == 1) break;
      w = std::max(1, (header.tile_rounding_mode == 0) ? (w / 2) : ((w + 1) / 2));
    }
  }

  return total_tiles;
}

// Helper: Load a single tiled part from multipart file
static Result<ImageData> LoadMultipartTiledPart(
    const uint8_t* data, size_t size,
    Reader& reader, const Version& version, const Header& header,
    const std::vector<uint64_t>& offsets) {

  (void)version;  // Used for multipart detection (already handled by caller)

  ImageData img_data;
  img_data.header = header;
  img_data.width = header.data_window.width();
  img_data.height = header.data_window.height();
  img_data.num_channels = static_cast<int>(header.channels.size());

  int width = img_data.width;
  int height = img_data.height;

  // Validate tile size
  if (header.tile_size_x <= 0 || header.tile_size_y <= 0) {
    return Result<ImageData>::error(
      ErrorInfo(ErrorCode::InvalidData,
                "Invalid tile size in multipart tiled EXR file",
                "LoadMultipartTiledPart", 0));
  }

  // Allocate RGBA output buffer
  img_data.rgba.resize(static_cast<size_t>(width) * static_cast<size_t>(height) * 4, 0.0f);

  // Initialize alpha to 1.0 for pixels without alpha channel
  bool has_alpha = false;
  for (size_t c = 0; c < header.channels.size(); c++) {
    const std::string& name = header.channels[c].name;
    if (name == "A" || name == "a") {
      has_alpha = true;
      break;
    }
  }
  if (!has_alpha) {
    for (size_t i = 0; i < img_data.rgba.size(); i += 4) {
      img_data.rgba[i + 3] = 1.0f;
    }
  }

  // Calculate bytes per pixel for each channel
  std::vector<int> channel_sizes;
  size_t bytes_per_pixel = 0;
  for (size_t c = 0; c < header.channels.size(); c++) {
    int sz = 0;
    switch (header.channels[c].pixel_type) {
      case PIXEL_TYPE_UINT:  sz = 4; break;
      case PIXEL_TYPE_HALF:  sz = 2; break;
      case PIXEL_TYPE_FLOAT: sz = 4; break;
      default: sz = 4; break;
    }
    channel_sizes.push_back(sz);
    bytes_per_pixel += static_cast<size_t>(sz);
  }

  // Map channel names to RGBA output indices
  auto GetOutputIndex = [&](const std::string& name) -> int {
    if (name == "R" || name == "r") return 0;
    if (name == "G" || name == "g") return 1;
    if (name == "B" || name == "b") return 2;
    if (name == "A" || name == "a") return 3;
    if (name == "Y" || name == "y") return 0;  // Luminance -> R
    return -1;
  };

  std::vector<int> channel_output_idx;
  for (size_t c = 0; c < header.channels.size(); c++) {
    channel_output_idx.push_back(GetOutputIndex(header.channels[c].name));
  }

  // Get scratch pool for decompression
  ScratchPool& pool = get_scratch_pool();

  // Process each tile using the flat offset table
  // For multipart, we only decode level 0 (base resolution) tiles
  // Level 0 tiles come first in the offset table
  int base_tiles_x = (width + header.tile_size_x - 1) / header.tile_size_x;
  int base_tiles_y = (height + header.tile_size_y - 1) / header.tile_size_y;
  int base_tile_count = base_tiles_x * base_tiles_y;

  for (int tile_idx = 0; tile_idx < base_tile_count && tile_idx < static_cast<int>(offsets.size()); ++tile_idx) {
    uint64_t tile_offset = offsets[static_cast<size_t>(tile_idx)];

    // Seek to tile data
    if (!reader.seek(static_cast<size_t>(tile_offset))) {
      return Result<ImageData>::error(
        ErrorInfo(ErrorCode::OutOfBounds,
                  "Failed to seek to multipart tile data",
                  "LoadMultipartTiledPart", reader.tell()));
    }

    // Read part number (multipart files have part number before tile header)
    uint32_t part_number;
    if (!reader.read4(&part_number)) {
      return Result<ImageData>::error(reader.last_error());
    }

    // Read tile header: tile_x (4), tile_y (4), level_x (4), level_y (4), data_size (4)
    uint32_t tile_x_coord, tile_y_coord, level_x, level_y;
    uint32_t tile_data_size;
    if (!reader.read4(&tile_x_coord) || !reader.read4(&tile_y_coord) ||
        !reader.read4(&level_x) || !reader.read4(&level_y) ||
        !reader.read4(&tile_data_size)) {
      return Result<ImageData>::error(
        ErrorInfo(ErrorCode::InvalidData,
                  "Failed to read multipart tile header",
                  "LoadMultipartTiledPart", reader.tell()));
    }

    // Only process level 0 tiles
    if (level_x != 0 || level_y != 0) {
      continue;
    }

    // Calculate tile pixel dimensions
    int tile_start_x = static_cast<int>(tile_x_coord) * header.tile_size_x;
    int tile_start_y = static_cast<int>(tile_y_coord) * header.tile_size_y;
    int tile_width = std::min(header.tile_size_x, width - tile_start_x);
    int tile_height = std::min(header.tile_size_y, height - tile_start_y);

    if (tile_width <= 0 || tile_height <= 0) continue;

    size_t tile_pixel_data_size = bytes_per_pixel * static_cast<size_t>(tile_width);
    size_t expected_size = tile_pixel_data_size * static_cast<size_t>(tile_height);

    // Read compressed tile data
    const uint8_t* tile_data = data + reader.tell();
    if (reader.tell() + tile_data_size > size) {
      return Result<ImageData>::error(
        ErrorInfo(ErrorCode::OutOfBounds,
                  "Multipart tile data exceeds file size",
                  "LoadMultipartTiledPart", reader.tell()));
    }

    // Allocate decompression buffer
    std::vector<uint8_t> decomp_buf(expected_size);

    // Decompress tile
    bool decomp_ok = false;
    switch (header.compression) {
      case COMPRESSION_NONE:
        if (tile_data_size == expected_size) {
          std::memcpy(decomp_buf.data(), tile_data, expected_size);
          decomp_ok = true;
        }
        break;

      case COMPRESSION_RLE:
        decomp_ok = DecompressRleV2(decomp_buf.data(), expected_size,
                                     tile_data, tile_data_size, pool);
        break;

      case COMPRESSION_ZIPS:
      case COMPRESSION_ZIP: {
        size_t uncomp_size = expected_size;
        decomp_ok = DecompressZipV2(decomp_buf.data(), &uncomp_size,
                                     tile_data, tile_data_size, pool);
        break;
      }

#if TINYEXR_V2_USE_CUSTOM_DEFLATE
      case COMPRESSION_PIZ: {
        auto piz_result = tinyexr::piz::DecompressPizV2(
            decomp_buf.data(), expected_size,
            tile_data, tile_data_size,
            static_cast<int>(header.channels.size()), header.channels.data(),
            tile_width, tile_height);
        decomp_ok = piz_result.success;
        break;
      }
#endif

      case COMPRESSION_PXR24:
        decomp_ok = DecompressPxr24V2(decomp_buf.data(), expected_size,
                                       tile_data, tile_data_size,
                                       tile_width, tile_height,
                                       static_cast<int>(header.channels.size()),
                                       header.channels.data(), pool);
        break;

      case COMPRESSION_B44:
        decomp_ok = DecompressB44V2(decomp_buf.data(), expected_size,
                                     tile_data, tile_data_size,
                                     tile_width, tile_height,
                                     static_cast<int>(header.channels.size()),
                                     header.channels.data(), false, pool);
        break;

      case COMPRESSION_B44A:
        decomp_ok = DecompressB44V2(decomp_buf.data(), expected_size,
                                     tile_data, tile_data_size,
                                     tile_width, tile_height,
                                     static_cast<int>(header.channels.size()),
                                     header.channels.data(), true, pool);
        break;

      default:
        decomp_ok = false;
        break;
    }

    if (!decomp_ok) {
      return Result<ImageData>::error(
        ErrorInfo(ErrorCode::CompressionError,
                  "Failed to decompress multipart tile at (" +
                  std::to_string(tile_x_coord) + ", " + std::to_string(tile_y_coord) + ")",
                  "LoadMultipartTiledPart", reader.tell()));
    }

    // Convert tile pixel data to RGBA float and copy to output image
    for (int line = 0; line < tile_height; line++) {
      int out_y = tile_start_y + line;
      if (out_y < 0 || out_y >= height) continue;

      const uint8_t* line_data = decomp_buf.data() + static_cast<size_t>(line) * tile_pixel_data_size;
      float* out_line = img_data.rgba.data() + static_cast<size_t>(out_y) * static_cast<size_t>(width) * 4;

      // Process each channel
      size_t ch_byte_offset = 0;
      for (size_t c = 0; c < header.channels.size(); c++) {
        int out_idx = channel_output_idx[c];
        int ch_pixel_size = channel_sizes[c];

        const uint8_t* ch_start = line_data + ch_byte_offset;

        if (out_idx >= 0 && out_idx <= 3) {
          for (int x = 0; x < tile_width; x++) {
            int out_x = tile_start_x + x;
            if (out_x < 0 || out_x >= width) continue;

            const uint8_t* ch_data = ch_start + static_cast<size_t>(x) * static_cast<size_t>(ch_pixel_size);
            float val = 0.0f;

            switch (header.channels[c].pixel_type) {
              case PIXEL_TYPE_UINT: {
                uint32_t u;
                std::memcpy(&u, ch_data, 4);
                val = static_cast<float>(u) / 4294967295.0f;
                break;
              }
              case PIXEL_TYPE_HALF: {
                uint16_t h;
                std::memcpy(&h, ch_data, 2);
                val = HalfToFloat(h);
                break;
              }
              case PIXEL_TYPE_FLOAT: {
                std::memcpy(&val, ch_data, 4);
                break;
              }
            }

            out_line[out_x * 4 + out_idx] = val;
          }
        }

        // Advance to next channel's data
        ch_byte_offset += static_cast<size_t>(ch_pixel_size) * static_cast<size_t>(tile_width);
      }
    }
  }

  return Result<ImageData>::ok(img_data);
}

// Helper: Load a single regular scanline part from multipart file
static Result<ImageData> LoadMultipartScanlinePart(
    const uint8_t* data, size_t size,
    Reader& reader, const Version& version, const Header& header,
    const std::vector<uint64_t>& offsets) {

  ImageData img_data;
  img_data.header = header;
  img_data.width = header.data_window.width();
  img_data.height = header.data_window.height();
  img_data.num_channels = static_cast<int>(header.channels.size());

  int width = img_data.width;
  int height = img_data.height;

  // Allocate RGBA output buffer
  img_data.rgba.resize(static_cast<size_t>(width) * height * 4, 0.0f);

  // Calculate bytes per channel per scanline (EXR uses per-channel layout)
  std::vector<int> channel_sizes;
  std::vector<size_t> channel_byte_offsets;  // Byte offset for each channel within a scanline
  size_t scanline_bytes = 0;

  for (size_t i = 0; i < header.channels.size(); i++) {
    int sz = 0;
    switch (header.channels[i].pixel_type) {
      case PIXEL_TYPE_UINT:  sz = 4; break;
      case PIXEL_TYPE_HALF:  sz = 2; break;
      case PIXEL_TYPE_FLOAT: sz = 4; break;
      default: sz = 4; break;
    }
    channel_sizes.push_back(sz);
    channel_byte_offsets.push_back(scanline_bytes);
    scanline_bytes += static_cast<size_t>(sz) * static_cast<size_t>(width);
  }

  size_t pixel_data_size = scanline_bytes;
  int scanlines_per_block = GetScanlinesPerBlock(header.compression);
  int num_blocks = static_cast<int>(offsets.size());

  // Map channel names to output indices (RGBA)
  auto GetOutputIndex = [&](const std::string& name) -> int {
    if (name == "R" || name == "r") return 0;
    if (name == "G" || name == "g") return 1;
    if (name == "B" || name == "b") return 2;
    if (name == "A" || name == "a") return 3;
    if (name == "Y" || name == "y") return 0;
    return -1;
  };

  std::vector<int> channel_output_idx;
  for (size_t i = 0; i < header.channels.size(); i++) {
    channel_output_idx.push_back(GetOutputIndex(header.channels[i].name));
  }

  // Get scratch pool
  ScratchPool& pool = get_scratch_pool();

  std::vector<uint8_t> decomp_buf(pixel_data_size * static_cast<size_t>(scanlines_per_block));

  for (int block = 0; block < num_blocks; block++) {
    if (!reader.seek(static_cast<size_t>(offsets[static_cast<size_t>(block)]))) {
      return Result<ImageData>::error(
        ErrorInfo(ErrorCode::InvalidData,
                  "Failed to seek to block " + std::to_string(block),
                  reader.context(), reader.tell()));
    }

    // Read part number (for multipart files)
    uint32_t part_number;
    if (!reader.read4(&part_number)) {
      return Result<ImageData>::error(reader.last_error());
    }

    // Read y coordinate and data size
    int32_t y_coord;
    uint32_t data_size;
    if (!reader.read4(reinterpret_cast<uint32_t*>(&y_coord)) ||
        !reader.read4(&data_size)) {
      return Result<ImageData>::error(reader.last_error());
    }

    int block_start_y = y_coord - header.data_window.min_y;
    int block_end_y = std::min(block_start_y + scanlines_per_block, height);
    int num_lines = block_end_y - block_start_y;
    size_t expected_size = pixel_data_size * static_cast<size_t>(num_lines);

    // Read compressed data
    const uint8_t* block_data = data + reader.tell();

    // Decompress
    bool decomp_ok = false;
    switch (header.compression) {
      case COMPRESSION_NONE:
        if (data_size == expected_size) {
          std::memcpy(decomp_buf.data(), block_data, expected_size);
          decomp_ok = true;
        }
        break;

      case COMPRESSION_RLE:
        decomp_ok = DecompressRleV2(decomp_buf.data(), expected_size,
                                     block_data, data_size, pool);
        break;

      case COMPRESSION_ZIPS:
      case COMPRESSION_ZIP: {
        size_t uncomp_size = expected_size;
        decomp_ok = DecompressZipV2(decomp_buf.data(), &uncomp_size,
                                     block_data, data_size, pool);
        break;
      }

#if TINYEXR_V2_USE_CUSTOM_DEFLATE
      case COMPRESSION_PIZ: {
        auto piz_result = tinyexr::piz::DecompressPizV2(
            decomp_buf.data(), expected_size,
            block_data, data_size,
            static_cast<int>(header.channels.size()), header.channels.data(),
            width, num_lines);
        decomp_ok = piz_result.success;
        break;
      }
#endif

      default:
        decomp_ok = false;
        break;
    }

    if (!decomp_ok) {
      return Result<ImageData>::error(
        ErrorInfo(ErrorCode::CompressionError,
                  "Failed to decompress multipart block " + std::to_string(block),
                  reader.context(), reader.tell()));
    }

    // Convert to float RGBA
    // EXR data layout: for each scanline, channels are stored contiguously
    // (all values of channel 0, then all values of channel 1, etc.)
    for (int line = 0; line < num_lines; line++) {
      int y = block_start_y + line;
      if (y < 0 || y >= height) continue;

      const uint8_t* line_data = decomp_buf.data() + static_cast<size_t>(line) * pixel_data_size;

      for (size_t c = 0; c < header.channels.size(); c++) {
        int out_idx = channel_output_idx[c];
        if (out_idx < 0) continue;

        // Channel data starts at channel_byte_offsets[c] within the line
        const uint8_t* ch_data = line_data + channel_byte_offsets[c];

        for (int x = 0; x < width; x++) {
          float* out_pixel = img_data.rgba.data() + (static_cast<size_t>(y) * width + x) * 4;
          float val = 0.0f;

          switch (header.channels[c].pixel_type) {
            case PIXEL_TYPE_HALF: {
              uint16_t h;
              std::memcpy(&h, ch_data + x * 2, 2);
              val = HalfToFloat(h);
              break;
            }
            case PIXEL_TYPE_FLOAT: {
              std::memcpy(&val, ch_data + x * 4, 4);
              break;
            }
            case PIXEL_TYPE_UINT: {
              uint32_t u;
              std::memcpy(&u, ch_data + x * 4, 4);
              val = static_cast<float>(u);
              break;
            }
          }

          out_pixel[out_idx] = val;
        }
      }
    }

    reader.seek_relative(data_size);
  }

  return Result<ImageData>::ok(img_data);
}

// Load multipart EXR from memory
Result<MultipartImageData> LoadMultipartFromMemory(const uint8_t* data, size_t size) {
  if (!data) {
    return Result<MultipartImageData>::error(
      ErrorInfo(ErrorCode::InvalidArgument,
                "Null data pointer",
                "LoadMultipartFromMemory", 0));
  }

  if (size == 0) {
    return Result<MultipartImageData>::error(
      ErrorInfo(ErrorCode::InvalidArgument,
                "Zero size",
                "LoadMultipartFromMemory", 0));
  }

  Reader reader(data, size, Endian::Little);

  // Parse version
  Result<Version> version_result = ParseVersion(reader);
  if (!version_result.success) {
    Result<MultipartImageData> result;
    result.success = false;
    result.errors = version_result.errors;
    return result;
  }

  const Version& version = version_result.value;

  // Parse headers
  // For multipart: multiple headers, each ends with null, empty header (null) ends list
  // For single-part: one header ends with null, no empty header
  std::vector<Header> headers;

  if (version.multipart) {
    // Multipart: parse headers until empty header
    while (true) {
      size_t pos = reader.tell();
      uint8_t first_byte;
      if (!reader.read1(&first_byte)) {
        return Result<MultipartImageData>::error(
          ErrorInfo(ErrorCode::InvalidData,
                    "Unexpected end of file reading headers",
                    "LoadMultipartFromMemory", pos));
      }

      if (first_byte == 0) {
        // Empty header = end of headers list
        break;
      }

      // Rewind and parse header
      reader.seek(pos);

      Result<Header> header_result = ParseHeader(reader, version);
      if (!header_result.success) {
        Result<MultipartImageData> result;
        result.success = false;
        result.errors = header_result.errors;
        return result;
      }

      headers.push_back(header_result.value);

      if (headers.size() > 1000) {
        return Result<MultipartImageData>::error(
          ErrorInfo(ErrorCode::InvalidData,
                    "Too many parts (>1000)",
                    "LoadMultipartFromMemory", reader.tell()));
      }
    }
  } else {
    // Single-part: just one header
    Result<Header> header_result = ParseHeader(reader, version);
    if (!header_result.success) {
      Result<MultipartImageData> result;
      result.success = false;
      result.errors = header_result.errors;
      return result;
    }
    headers.push_back(header_result.value);
  }

  if (headers.empty()) {
    return Result<MultipartImageData>::error(
      ErrorInfo(ErrorCode::InvalidData,
                "No headers found in multipart file",
                "LoadMultipartFromMemory", reader.tell()));
  }

  // Read offset tables for each part
  std::vector<std::vector<uint64_t>> part_offsets(headers.size());

  for (size_t part = 0; part < headers.size(); part++) {
    int chunk_count = headers[part].chunk_count;
    if (chunk_count <= 0) {
      // Calculate from dimensions - handle tiled vs scanline differently
      if (headers[part].tiled || headers[part].type == "tiledimage") {
        // Tiled: count is total number of tiles across all levels
        chunk_count = CalculateTileCount(headers[part]);
      } else {
        // Scanline: count is number of scanline blocks
        int height = headers[part].data_window.height();
        int scanlines_per_block = GetScanlinesPerBlock(headers[part].compression);
        chunk_count = (height + scanlines_per_block - 1) / scanlines_per_block;
      }
    }

    // Sanity check on chunk count to prevent memory allocation issues
    if (chunk_count > 10000000) {
      return Result<MultipartImageData>::error(
        ErrorInfo(ErrorCode::InvalidData,
                  "Unreasonable chunk count: " + std::to_string(chunk_count),
                  "LoadMultipartFromMemory", reader.tell()));
    }

    part_offsets[part].resize(static_cast<size_t>(chunk_count));
    for (int i = 0; i < chunk_count; i++) {
      uint64_t offset;
      if (!reader.read8(&offset)) {
        return Result<MultipartImageData>::error(
          ErrorInfo(ErrorCode::InvalidData,
                    "Failed to read offset table for part " + std::to_string(part),
                    "LoadMultipartFromMemory", reader.tell()));
      }
      part_offsets[part][static_cast<size_t>(i)] = offset;
    }
  }

  // Load each part
  MultipartImageData mp_data;
  mp_data.headers = headers;

  for (size_t part = 0; part < headers.size(); part++) {
    const Header& hdr = headers[part];

    if (hdr.is_deep) {
      // Load as deep image
      Result<DeepImageData> deep_result = LoadDeepScanlinePart(
          data, size, reader, version, hdr, part_offsets[part]);

      if (deep_result.success) {
        mp_data.deep_parts.push_back(std::move(deep_result.value));
      } else {
        // Add warning but continue with other parts
        Result<MultipartImageData> result;
        result.add_warning("Failed to load deep part " + std::to_string(part) +
                           ": " + (deep_result.errors.empty() ? "unknown error" :
                                   deep_result.errors[0].message));
      }
    } else {
      // Load as regular image
      if (hdr.tiled || hdr.type == "tiledimage") {
        // Tiled multipart - use dedicated multipart tiled loader
        Result<ImageData> tiled_result = LoadMultipartTiledPart(
            data, size, reader, version, hdr, part_offsets[part]);

        if (tiled_result.success) {
          mp_data.parts.push_back(std::move(tiled_result.value));
        } else {
          Result<MultipartImageData> result;
          result.add_warning("Failed to load tiled part " + std::to_string(part) +
                             ": " + (tiled_result.errors.empty() ? "unknown error" :
                                     tiled_result.errors[0].message));
        }
      } else {
        // Scanline multipart
        Result<ImageData> scanline_result = LoadMultipartScanlinePart(
            data, size, reader, version, hdr, part_offsets[part]);

        if (scanline_result.success) {
          mp_data.parts.push_back(std::move(scanline_result.value));
        } else {
          Result<MultipartImageData> result;
          result.add_warning("Failed to load scanline part " + std::to_string(part) +
                             ": " + (scanline_result.errors.empty() ? "unknown error" :
                                     scanline_result.errors[0].message));
        }
      }
    }
  }

  return Result<MultipartImageData>::ok(mp_data);
}

// ============================================================================
// Spectral Image I/O
// ============================================================================

// Check if header contains spectral layout attributes
bool IsSpectralEXR(const Header& header) {
  return header.has_attribute("spectralLayoutVersion");
}

// Save spectral image to memory
Result<std::vector<uint8_t>> SaveSpectralToMemory(const SpectralImageData& spectral, int compression_level) {
  if (spectral.width <= 0 || spectral.height <= 0) {
    return Result<std::vector<uint8_t>>::error(
      ErrorInfo(ErrorCode::InvalidArgument, "Invalid spectral image dimensions",
                "SaveSpectralToMemory", 0));
  }

  if (spectral.wavelengths.empty()) {
    return Result<std::vector<uint8_t>>::error(
      ErrorInfo(ErrorCode::InvalidArgument, "No wavelengths specified",
                "SaveSpectralToMemory", 0));
  }

  bool is_polarised = (spectral.spectrum_type & SPECTRUM_POLARISED) != 0;
  bool is_reflective = (spectral.spectrum_type & SPECTRUM_REFLECTIVE) != 0 &&
                       (spectral.spectrum_type & SPECTRUM_EMISSIVE) == 0;

  // Verify data size
  size_t num_pixels = static_cast<size_t>(spectral.width) * spectral.height;
  size_t num_wavelengths = spectral.wavelengths.size();

  if (is_polarised) {
    if (spectral.stokes_data.size() != 4) {
      return Result<std::vector<uint8_t>>::error(
        ErrorInfo(ErrorCode::InvalidArgument,
                  "Polarised image requires 4 Stokes components",
                  "SaveSpectralToMemory", 0));
    }
    for (size_t s = 0; s < 4; s++) {
      if (spectral.stokes_data[s].size() != num_wavelengths) {
        return Result<std::vector<uint8_t>>::error(
          ErrorInfo(ErrorCode::InvalidArgument,
                    "Stokes component " + std::to_string(s) + " wavelength count mismatch",
                    "SaveSpectralToMemory", 0));
      }
      for (size_t w = 0; w < num_wavelengths; w++) {
        if (spectral.stokes_data[s][w].size() != num_pixels) {
          return Result<std::vector<uint8_t>>::error(
            ErrorInfo(ErrorCode::InvalidArgument,
                      "Stokes " + std::to_string(s) + " wavelength " + std::to_string(w) +
                      " pixel count mismatch",
                      "SaveSpectralToMemory", 0));
        }
      }
    }
  } else {
    if (spectral.spectral_data.size() != num_wavelengths) {
      return Result<std::vector<uint8_t>>::error(
        ErrorInfo(ErrorCode::InvalidArgument,
                  "Spectral data wavelength count mismatch",
                  "SaveSpectralToMemory", 0));
    }
    for (size_t w = 0; w < num_wavelengths; w++) {
      if (spectral.spectral_data[w].size() != num_pixels) {
        return Result<std::vector<uint8_t>>::error(
          ErrorInfo(ErrorCode::InvalidArgument,
                    "Wavelength " + std::to_string(w) + " pixel count mismatch",
                    "SaveSpectralToMemory", 0));
      }
    }
  }

  // Build ImageData with spectral channels
  ImageData image;
  image.width = spectral.width;
  image.height = spectral.height;
  image.header = spectral.header;

  // Set up header
  if (image.header.data_window.max_x == 0 && image.header.data_window.max_y == 0) {
    image.header.data_window.min_x = 0;
    image.header.data_window.min_y = 0;
    image.header.data_window.max_x = spectral.width - 1;
    image.header.data_window.max_y = spectral.height - 1;
    image.header.display_window = image.header.data_window;
  }
  if (image.header.pixel_aspect_ratio <= 0.0f) {
    image.header.pixel_aspect_ratio = 1.0f;
  }
  if (image.header.screen_window_width <= 0.0f) {
    image.header.screen_window_width = 1.0f;
  }
  if (image.header.compression == COMPRESSION_NONE) {
    image.header.compression = COMPRESSION_ZIP;
  }

  // Clear existing channels and rebuild
  image.header.channels.clear();

  // Add RGB preview channels first (if available)
  bool has_rgb = !spectral.rgb_preview.empty() &&
                 spectral.rgb_preview.size() == num_pixels * 3;
  if (has_rgb) {
    Channel ch_r, ch_g, ch_b;
    ch_r.name = "R"; ch_r.pixel_type = PIXEL_TYPE_FLOAT; ch_r.x_sampling = 1; ch_r.y_sampling = 1;
    ch_g.name = "G"; ch_g.pixel_type = PIXEL_TYPE_FLOAT; ch_g.x_sampling = 1; ch_g.y_sampling = 1;
    ch_b.name = "B"; ch_b.pixel_type = PIXEL_TYPE_FLOAT; ch_b.x_sampling = 1; ch_b.y_sampling = 1;
    image.header.channels.push_back(ch_b);
    image.header.channels.push_back(ch_g);
    image.header.channels.push_back(ch_r);
  }

  // Add spectral channels
  if (is_polarised) {
    // Stokes components S0-S3 for each wavelength
    for (int s = 0; s < 4; s++) {
      for (size_t w = 0; w < num_wavelengths; w++) {
        Channel ch;
        ch.name = SpectralChannelName(spectral.wavelengths[w], s);
        ch.pixel_type = PIXEL_TYPE_FLOAT;
        ch.x_sampling = 1;
        ch.y_sampling = 1;
        image.header.channels.push_back(ch);
      }
    }
  } else {
    // Single component per wavelength
    for (size_t w = 0; w < num_wavelengths; w++) {
      Channel ch;
      if (is_reflective) {
        ch.name = ReflectiveChannelName(spectral.wavelengths[w]);
      } else {
        ch.name = SpectralChannelName(spectral.wavelengths[w], 0);
      }
      ch.pixel_type = PIXEL_TYPE_FLOAT;
      ch.x_sampling = 1;
      ch.y_sampling = 1;
      image.header.channels.push_back(ch);
    }
  }

  // Sort channels by name (EXR requirement)
  std::sort(image.header.channels.begin(), image.header.channels.end(),
            [](const Channel& a, const Channel& b) { return a.name < b.name; });

  // Build RGBA data (we'll use a custom approach since SaveToMemory expects RGBA)
  // Instead, we'll build the raw channel data directly

  // Calculate total channels
  size_t total_channels = image.header.channels.size();
  image.num_channels = static_cast<int>(total_channels);

  // Create rgba array - but this is tricky since SaveToMemory expects RGBA format
  // We need to pack spectral data appropriately
  // For simplicity, let's use a modified approach: pack all channel data into rgba

  // Actually, let's create a custom save that handles spectral data directly
  // by using the raw channel format

  // Build raw pixel data per channel (sorted by channel name)
  std::vector<std::vector<float>> channel_data(total_channels);
  for (size_t c = 0; c < total_channels; c++) {
    channel_data[c].resize(num_pixels);
    const std::string& ch_name = image.header.channels[c].name;

    if (ch_name == "R" && has_rgb) {
      for (size_t i = 0; i < num_pixels; i++) {
        channel_data[c][i] = spectral.rgb_preview[i * 3 + 0];
      }
    } else if (ch_name == "G" && has_rgb) {
      for (size_t i = 0; i < num_pixels; i++) {
        channel_data[c][i] = spectral.rgb_preview[i * 3 + 1];
      }
    } else if (ch_name == "B" && has_rgb) {
      for (size_t i = 0; i < num_pixels; i++) {
        channel_data[c][i] = spectral.rgb_preview[i * 3 + 2];
      }
    } else {
      // Spectral channel
      float wl = ParseSpectralChannelWavelength(ch_name);
      int stokes = GetStokesComponent(ch_name);

      // Find wavelength index
      int wl_idx = -1;
      for (size_t w = 0; w < num_wavelengths; w++) {
        if (std::abs(spectral.wavelengths[w] - wl) < 0.001f) {
          wl_idx = static_cast<int>(w);
          break;
        }
      }

      if (wl_idx >= 0) {
        if (is_polarised && stokes >= 0 && stokes < 4) {
          channel_data[c] = spectral.stokes_data[stokes][wl_idx];
        } else if (!is_polarised) {
          channel_data[c] = spectral.spectral_data[wl_idx];
        }
      }
    }
  }

  // Now pack into RGBA format expected by SaveToMemory
  // We need to create an image with all channels as "RGBA"
  // Actually, SaveToMemory uses the header.channels for writing, not just RGBA
  // So we need to populate image.rgba with the interleaved channel data

  // For spectral data, use raw data approach
  // Pack channels in sorted order (which they already are in channel_data)
  image.rgba.resize(num_pixels * 4, 0.0f);  // RGBA for compatibility

  // Since SaveToMemory writes data based on header.channels, we need a different approach
  // Let's write directly using a custom spectral writer

  // Actually, we can reuse SaveToMemory by ensuring rgba contains data for all channels
  // The issue is SaveToMemory expects rgba to be in a specific format

  // Let's create a simplified approach: convert spectral to ImageData with raw_channels
  // and use a modified save

  // For now, let's just fill rgba with the first 4 spectral bands as a workaround
  // and rely on the existing SaveToMemory which writes based on header.channels

  // Better approach: Create the output directly similar to SaveToMemory
  // but with proper handling of FLOAT channels

  std::vector<uint8_t> output;
  output.reserve(1024 * 1024);

  // Helper lambdas for writing
  auto write_bytes = [&output](const void* data, size_t len) {
    const uint8_t* ptr = static_cast<const uint8_t*>(data);
    output.insert(output.end(), ptr, ptr + len);
  };

  auto write_string = [&output](const std::string& s) {
    output.insert(output.end(), s.begin(), s.end());
    output.push_back(0);
  };

  auto write_u32 = [&output](uint32_t v) {
    output.push_back(static_cast<uint8_t>(v & 0xFF));
    output.push_back(static_cast<uint8_t>((v >> 8) & 0xFF));
    output.push_back(static_cast<uint8_t>((v >> 16) & 0xFF));
    output.push_back(static_cast<uint8_t>((v >> 24) & 0xFF));
  };

  auto write_float = [&output](float f) {
    uint32_t u;
    std::memcpy(&u, &f, 4);
    output.push_back(static_cast<uint8_t>(u & 0xFF));
    output.push_back(static_cast<uint8_t>((u >> 8) & 0xFF));
    output.push_back(static_cast<uint8_t>((u >> 16) & 0xFF));
    output.push_back(static_cast<uint8_t>((u >> 24) & 0xFF));
  };

  auto write_attribute = [&](const std::string& name, const std::string& type,
                              const void* data, size_t size) {
    write_string(name);
    write_string(type);
    write_u32(static_cast<uint32_t>(size));
    write_bytes(data, size);
  };

  // Write magic number
  output.push_back(0x76);
  output.push_back(0x2f);
  output.push_back(0x31);
  output.push_back(0x01);

  // Write version (scanline, not tiled)
  uint32_t version_bits = 2;  // version 2
  output.push_back(static_cast<uint8_t>(version_bits & 0xFF));
  output.push_back(static_cast<uint8_t>((version_bits >> 8) & 0xFF));
  output.push_back(static_cast<uint8_t>((version_bits >> 16) & 0xFF));
  output.push_back(static_cast<uint8_t>((version_bits >> 24) & 0xFF));

  // Write header attributes manually

  // channels (chlist)
  {
    std::vector<uint8_t> chlist;
    for (const auto& ch : image.header.channels) {
      for (char c : ch.name) chlist.push_back(static_cast<uint8_t>(c));
      chlist.push_back(0);
      uint32_t pt = ch.pixel_type;
      chlist.push_back(static_cast<uint8_t>(pt & 0xFF));
      chlist.push_back(static_cast<uint8_t>((pt >> 8) & 0xFF));
      chlist.push_back(static_cast<uint8_t>((pt >> 16) & 0xFF));
      chlist.push_back(static_cast<uint8_t>((pt >> 24) & 0xFF));
      chlist.push_back(0); chlist.push_back(0);
      chlist.push_back(0); chlist.push_back(0);
      int32_t xs = ch.x_sampling > 0 ? ch.x_sampling : 1;
      chlist.push_back(static_cast<uint8_t>(xs & 0xFF));
      chlist.push_back(static_cast<uint8_t>((xs >> 8) & 0xFF));
      chlist.push_back(static_cast<uint8_t>((xs >> 16) & 0xFF));
      chlist.push_back(static_cast<uint8_t>((xs >> 24) & 0xFF));
      int32_t ys = ch.y_sampling > 0 ? ch.y_sampling : 1;
      chlist.push_back(static_cast<uint8_t>(ys & 0xFF));
      chlist.push_back(static_cast<uint8_t>((ys >> 8) & 0xFF));
      chlist.push_back(static_cast<uint8_t>((ys >> 16) & 0xFF));
      chlist.push_back(static_cast<uint8_t>((ys >> 24) & 0xFF));
    }
    chlist.push_back(0);
    write_attribute("channels", "chlist", chlist.data(), chlist.size());
  }

  // compression
  {
    uint8_t comp = static_cast<uint8_t>(image.header.compression);
    write_attribute("compression", "compression", &comp, 1);
  }

  // dataWindow
  {
    int32_t dw[4] = {image.header.data_window.min_x, image.header.data_window.min_y,
                     image.header.data_window.max_x, image.header.data_window.max_y};
    write_attribute("dataWindow", "box2i", dw, 16);
  }

  // displayWindow
  {
    int32_t dw[4] = {image.header.display_window.min_x, image.header.display_window.min_y,
                     image.header.display_window.max_x, image.header.display_window.max_y};
    write_attribute("displayWindow", "box2i", dw, 16);
  }

  // lineOrder
  {
    uint8_t lo = static_cast<uint8_t>(image.header.line_order);
    write_attribute("lineOrder", "lineOrder", &lo, 1);
  }

  // pixelAspectRatio
  {
    write_attribute("pixelAspectRatio", "float", &image.header.pixel_aspect_ratio, 4);
  }

  // screenWindowCenter
  {
    float swc[2] = {image.header.screen_window_center[0], image.header.screen_window_center[1]};
    write_attribute("screenWindowCenter", "v2f", swc, 8);
  }

  // screenWindowWidth
  {
    write_attribute("screenWindowWidth", "float", &image.header.screen_window_width, 4);
  }

  // Custom attributes (includes spectral attributes)
  for (const auto& attr : image.header.custom_attributes) {
    if (attr.name.empty()) continue;
    write_string(attr.name);
    write_string(attr.type);
    write_u32(static_cast<uint32_t>(attr.data.size()));
    if (!attr.data.empty()) {
      write_bytes(attr.data.data(), attr.data.size());
    }
  }

  // End of header
  output.push_back(0);

  // Scanline blocks
  int scanlines_per_block = GetScanlinesPerBlock(image.header.compression);
  int num_blocks = (spectral.height + scanlines_per_block - 1) / scanlines_per_block;

  // Reserve space for offset table
  size_t offset_table_pos = output.size();
  std::vector<uint64_t> block_offsets(static_cast<size_t>(num_blocks));
  for (int i = 0; i < num_blocks; i++) {
    for (int j = 0; j < 8; j++) {
      output.push_back(0);  // Placeholder
    }
  }

  // Calculate bytes per scanline
  size_t bytes_per_scanline = 0;
  for (const auto& ch : image.header.channels) {
    int ch_bytes = (ch.pixel_type == PIXEL_TYPE_HALF) ? 2 : 4;
    bytes_per_scanline += static_cast<size_t>(spectral.width) * ch_bytes;
  }

  // Buffers for compression
  std::vector<uint8_t> scanline_buffer;
  std::vector<uint8_t> reorder_buffer;
  std::vector<uint8_t> compress_buffer;

  int miniz_level = compression_level;
  if (miniz_level < 1) miniz_level = 1;
  if (miniz_level > 9) miniz_level = 9;

  // Write each block
  for (int block = 0; block < num_blocks; block++) {
    block_offsets[static_cast<size_t>(block)] = output.size();

    int block_start_y = block * scanlines_per_block;
    int block_end_y = std::min(block_start_y + scanlines_per_block, spectral.height);
    int num_lines = block_end_y - block_start_y;

    size_t block_data_size = bytes_per_scanline * num_lines;
    scanline_buffer.resize(block_data_size);

    // Pack channel data into scanline buffer (channel by channel, line by line)
    uint8_t* dst = scanline_buffer.data();
    for (int y = block_start_y; y < block_end_y; y++) {
      for (size_t c = 0; c < total_channels; c++) {
        int ch_bytes = (image.header.channels[c].pixel_type == PIXEL_TYPE_HALF) ? 2 : 4;
        for (int x = 0; x < spectral.width; x++) {
          float val = channel_data[c][y * spectral.width + x];
          if (ch_bytes == 2) {
            uint16_t h = FloatToHalf(val);
            std::memcpy(dst, &h, 2);
            dst += 2;
          } else {
            std::memcpy(dst, &val, 4);
            dst += 4;
          }
        }
      }
    }

    // Compress
    size_t compressed_size = block_data_size;
    const uint8_t* data_to_write = scanline_buffer.data();

    if (image.header.compression == COMPRESSION_ZIP ||
        image.header.compression == COMPRESSION_ZIPS) {
      reorder_buffer.resize(block_data_size);
      ReorderBytesForCompression(scanline_buffer.data(), reorder_buffer.data(), block_data_size);
      ApplyDeltaPredictorEncode(reorder_buffer.data(), block_data_size);

#if defined(TINYEXR_USE_MINIZ)
      compress_buffer.resize(block_data_size + block_data_size / 100 + 128);
      mz_ulong comp_size = static_cast<mz_ulong>(compress_buffer.size());
      int z_result = mz_compress2(compress_buffer.data(), &comp_size,
                                  reorder_buffer.data(), static_cast<mz_ulong>(block_data_size),
                                  miniz_level);
      if (z_result == MZ_OK && comp_size < block_data_size) {
        compressed_size = comp_size;
        data_to_write = compress_buffer.data();
      } else {
        data_to_write = scanline_buffer.data();
      }
#elif defined(TINYEXR_USE_ZLIB)
      compress_buffer.resize(compressBound(static_cast<uLong>(block_data_size)));
      uLongf comp_size = static_cast<uLongf>(compress_buffer.size());
      int z_result = compress2(compress_buffer.data(), &comp_size,
                               reorder_buffer.data(), static_cast<uLong>(block_data_size),
                               miniz_level);
      if (z_result == Z_OK && comp_size < block_data_size) {
        compressed_size = comp_size;
        data_to_write = compress_buffer.data();
      } else {
        data_to_write = scanline_buffer.data();
      }
#else
      data_to_write = scanline_buffer.data();
#endif
    }

    // Write block: y_coord (4 bytes) + data_size (4 bytes) + data
    int32_t y_coord = image.header.data_window.min_y + block_start_y;
    uint32_t yu;
    std::memcpy(&yu, &y_coord, 4);
    output.push_back(static_cast<uint8_t>(yu & 0xFF));
    output.push_back(static_cast<uint8_t>((yu >> 8) & 0xFF));
    output.push_back(static_cast<uint8_t>((yu >> 16) & 0xFF));
    output.push_back(static_cast<uint8_t>((yu >> 24) & 0xFF));

    uint32_t data_size = static_cast<uint32_t>(compressed_size);
    output.push_back(static_cast<uint8_t>(data_size & 0xFF));
    output.push_back(static_cast<uint8_t>((data_size >> 8) & 0xFF));
    output.push_back(static_cast<uint8_t>((data_size >> 16) & 0xFF));
    output.push_back(static_cast<uint8_t>((data_size >> 24) & 0xFF));

    output.insert(output.end(), data_to_write, data_to_write + compressed_size);
  }

  // Write offset table
  for (int i = 0; i < num_blocks; i++) {
    size_t offset_pos = offset_table_pos + static_cast<size_t>(i) * 8;
    uint64_t offset = block_offsets[static_cast<size_t>(i)];
    for (int j = 0; j < 8; j++) {
      output[offset_pos + j] = static_cast<uint8_t>((offset >> (j * 8)) & 0xFF);
    }
  }

  return Result<std::vector<uint8_t>>::ok(std::move(output));
}

Result<std::vector<uint8_t>> SaveSpectralToMemory(const SpectralImageData& spectral) {
  return SaveSpectralToMemory(spectral, 6);
}

Result<void> SaveSpectralToFile(const char* filename, const SpectralImageData& spectral, int compression_level) {
  if (!filename) {
    return Result<void>::error(
      ErrorInfo(ErrorCode::InvalidArgument, "Null filename",
                "SaveSpectralToFile", 0));
  }

  auto mem_result = SaveSpectralToMemory(spectral, compression_level);
  if (!mem_result.success) {
    Result<void> result;
    result.success = false;
    result.errors = mem_result.errors;
    result.warnings = mem_result.warnings;
    return result;
  }

  FILE* fp = fopen(filename, "wb");
  if (!fp) {
    return Result<void>::error(
      ErrorInfo(ErrorCode::IOError, "Failed to open file for writing",
                filename, 0));
  }

  size_t written = fwrite(mem_result.value.data(), 1, mem_result.value.size(), fp);
  fclose(fp);

  if (written != mem_result.value.size()) {
    return Result<void>::error(
      ErrorInfo(ErrorCode::IOError, "Failed to write all data to file",
                filename, 0));
  }

  Result<void> result = Result<void>::ok();
  result.warnings = mem_result.warnings;
  return result;
}

Result<SpectralImageData> LoadSpectralFromMemory(const uint8_t* data, size_t size) {
  // First load as regular image with raw channels
  LoadOptions opts;
  opts.preserve_raw_channels = true;
  opts.convert_to_rgba = false;

  auto load_result = LoadFromMemory(data, size, opts);
  if (!load_result.success) {
    Result<SpectralImageData> result;
    result.success = false;
    result.errors = load_result.errors;
    return result;
  }

  const ImageData& img = load_result.value;
  SpectralImageData spectral;
  spectral.width = img.width;
  spectral.height = img.height;
  spectral.header = img.header;

  // Detect spectral channels and extract wavelengths
  std::vector<float> wavelengths_set;
  bool has_stokes[4] = {false, false, false, false};
  bool is_reflective = false;

  for (const auto& ch : img.header.channels) {
    float wl = ParseSpectralChannelWavelength(ch.name);
    if (wl > 0.0f) {
      // Check if already in set
      bool found = false;
      for (float existing : wavelengths_set) {
        if (std::abs(existing - wl) < 0.001f) {
          found = true;
          break;
        }
      }
      if (!found) {
        wavelengths_set.push_back(wl);
      }

      int stokes = GetStokesComponent(ch.name);
      if (stokes >= 0 && stokes < 4) {
        has_stokes[stokes] = true;
      } else if (stokes == -1) {
        is_reflective = true;
      }
    }
  }

  if (wavelengths_set.empty()) {
    return Result<SpectralImageData>::error(
      ErrorInfo(ErrorCode::InvalidData, "No spectral channels found in image",
                "LoadSpectralFromMemory", 0));
  }

  // Sort wavelengths
  std::sort(wavelengths_set.begin(), wavelengths_set.end());
  spectral.wavelengths = wavelengths_set;

  size_t num_wavelengths = wavelengths_set.size();
  size_t num_pixels = static_cast<size_t>(img.width) * img.height;

  // Determine spectrum type
  bool is_polarised = has_stokes[0] && has_stokes[1] && has_stokes[2] && has_stokes[3];
  if (is_polarised) {
    spectral.spectrum_type = SPECTRUM_EMISSIVE | SPECTRUM_POLARISED;
    spectral.stokes_data.resize(4);
    for (int s = 0; s < 4; s++) {
      spectral.stokes_data[s].resize(num_wavelengths);
      for (size_t w = 0; w < num_wavelengths; w++) {
        spectral.stokes_data[s][w].resize(num_pixels, 0.0f);
      }
    }
  } else if (is_reflective) {
    spectral.spectrum_type = SPECTRUM_REFLECTIVE;
    spectral.spectral_data.resize(num_wavelengths);
    for (size_t w = 0; w < num_wavelengths; w++) {
      spectral.spectral_data[w].resize(num_pixels, 0.0f);
    }
  } else {
    spectral.spectrum_type = SPECTRUM_EMISSIVE;
    spectral.spectral_data.resize(num_wavelengths);
    for (size_t w = 0; w < num_wavelengths; w++) {
      spectral.spectral_data[w].resize(num_pixels, 0.0f);
    }
  }

  // Extract channel data
  for (size_t c = 0; c < img.header.channels.size(); c++) {
    const std::string& ch_name = img.header.channels[c].name;

    // Check for RGB preview
    if (ch_name == "R" || ch_name == "G" || ch_name == "B") {
      if (spectral.rgb_preview.empty()) {
        spectral.rgb_preview.resize(num_pixels * 3, 0.0f);
      }
      int rgb_idx = (ch_name == "R") ? 0 : (ch_name == "G") ? 1 : 2;

      // Get raw channel data
      if (c < img.raw_channels.size() && !img.raw_channels[c].empty()) {
        int ch_size = (img.header.channels[c].pixel_type == PIXEL_TYPE_HALF) ? 2 : 4;
        const uint8_t* src = img.raw_channels[c].data();
        for (size_t i = 0; i < num_pixels; i++) {
          float val;
          if (ch_size == 2) {
            uint16_t h;
            std::memcpy(&h, src + i * 2, 2);
            val = HalfToFloat(h);
          } else {
            std::memcpy(&val, src + i * 4, 4);
          }
          spectral.rgb_preview[i * 3 + rgb_idx] = val;
        }
      }
      continue;
    }

    // Check for spectral channel
    float wl = ParseSpectralChannelWavelength(ch_name);
    if (wl <= 0.0f) continue;

    int stokes = GetStokesComponent(ch_name);

    // Find wavelength index
    int wl_idx = -1;
    for (size_t w = 0; w < num_wavelengths; w++) {
      if (std::abs(spectral.wavelengths[w] - wl) < 0.001f) {
        wl_idx = static_cast<int>(w);
        break;
      }
    }
    if (wl_idx < 0) continue;

    // Get raw channel data
    if (c < img.raw_channels.size() && !img.raw_channels[c].empty()) {
      int ch_size = (img.header.channels[c].pixel_type == PIXEL_TYPE_HALF) ? 2 : 4;
      const uint8_t* src = img.raw_channels[c].data();

      std::vector<float>* dest = nullptr;
      if (is_polarised && stokes >= 0 && stokes < 4) {
        dest = &spectral.stokes_data[stokes][wl_idx];
      } else if (!is_polarised) {
        dest = &spectral.spectral_data[wl_idx];
      }

      if (dest) {
        for (size_t i = 0; i < num_pixels; i++) {
          float val;
          if (ch_size == 2) {
            uint16_t h;
            std::memcpy(&h, src + i * 2, 2);
            val = HalfToFloat(h);
          } else {
            std::memcpy(&val, src + i * 4, 4);
          }
          (*dest)[i] = val;
        }
      }
    }
  }

  return Result<SpectralImageData>::ok(std::move(spectral));
}

Result<SpectralImageData> LoadSpectralFromFile(const char* filename) {
  if (!filename) {
    return Result<SpectralImageData>::error(
      ErrorInfo(ErrorCode::InvalidArgument, "Null filename",
                "LoadSpectralFromFile", 0));
  }

  FILE* fp = fopen(filename, "rb");
  if (!fp) {
    return Result<SpectralImageData>::error(
      ErrorInfo(ErrorCode::IOError, "Failed to open file for reading",
                filename, 0));
  }

  fseek(fp, 0, SEEK_END);
  long file_size = ftell(fp);
  fseek(fp, 0, SEEK_SET);

  if (file_size <= 0) {
    fclose(fp);
    return Result<SpectralImageData>::error(
      ErrorInfo(ErrorCode::IOError, "File is empty or seek failed",
                filename, 0));
  }

  std::vector<uint8_t> data(static_cast<size_t>(file_size));
  size_t read_size = fread(data.data(), 1, data.size(), fp);
  fclose(fp);

  if (read_size != data.size()) {
    return Result<SpectralImageData>::error(
      ErrorInfo(ErrorCode::IOError, "Failed to read complete file",
                filename, 0));
  }

  return LoadSpectralFromMemory(data.data(), data.size());
}

}  // namespace v2
}  // namespace tinyexr

#endif  // TINYEXR_V2_IMPL_HH_
