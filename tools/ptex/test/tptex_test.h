/* SPDX-License-Identifier: BSD-3-Clause
 * Copyright (c) 2014-2026 Syoyo Fujita and TinyEXR authors. */
#ifndef TPTEX_TEST_H_
#define TPTEX_TEST_H_

#include <stdio.h>
#include <stdlib.h>

extern int g_tptex_failures;
extern long g_tptex_checks;

#define TPTEX_CHECK(cond)                                                      \
  do {                                                                         \
    ++g_tptex_checks;                                                          \
    if (!(cond)) {                                                             \
      ++g_tptex_failures;                                                      \
      fprintf(stderr, "  FAIL %s:%d: %s\n", __FILE__, __LINE__, #cond);       \
    }                                                                          \
  } while (0)

#define TPTEX_CHECK_EQ_U(a, b)                                                 \
  do {                                                                         \
    unsigned long long tptex_a_ = (unsigned long long)(a);                     \
    unsigned long long tptex_b_ = (unsigned long long)(b);                     \
    ++g_tptex_checks;                                                          \
    if (tptex_a_ != tptex_b_) {                                                \
      ++g_tptex_failures;                                                      \
      fprintf(stderr, "  FAIL %s:%d: %s == %s (0x%llx vs 0x%llx)\n", __FILE__, \
              __LINE__, #a, #b, tptex_a_, tptex_b_);                           \
    }                                                                          \
  } while (0)

void test_half(void);
void test_reader(void);
void test_write(void);
void test_filter(void);
void test_utils(void);

#endif /* TPTEX_TEST_H_ */
