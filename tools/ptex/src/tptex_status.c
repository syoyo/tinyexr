/* SPDX-License-Identifier: BSD-3-Clause
 * Copyright (c) 2014-2026 Syoyo Fujita and TinyEXR authors. */
#include "../include/tptex.h"

const char* tptex_status_str(tptex_status status) {
  switch (status) {
    case TPTEX_OK: return "ok";
    case TPTEX_E_INVALID_ARG: return "invalid argument";
    case TPTEX_E_NOMEM: return "out of memory";
    case TPTEX_E_IO: return "i/o error";
    case TPTEX_E_BAD_MAGIC: return "not a Ptex file";
    case TPTEX_E_BAD_VERSION: return "unsupported Ptex file version";
    case TPTEX_E_CORRUPT: return "corrupt Ptex file";
    case TPTEX_E_OVERFLOW: return "size arithmetic overflow";
    case TPTEX_E_INFLATE: return "zlib inflate failed";
    case TPTEX_E_RANGE: return "index or value out of range";
    case TPTEX_E_UNSUPPORTED: return "unsupported feature";
    case TPTEX_E_NOT_FOUND: return "not found";
    case TPTEX_E_LIMIT: return "resource limit exceeded";
  }
  return "unknown status";
}

size_t tptex_data_type_size(tptex_data_type type) {
  switch (type) {
    case TPTEX_UINT8: return 1u;
    case TPTEX_UINT16: return 2u;
    case TPTEX_HALF: return 2u;
    case TPTEX_FLOAT: return 4u;
  }
  return 0u;
}
