/* SPDX-License-Identifier: BSD-3-Clause
 * Copyright (c) 2014-2026 Syoyo Fujita and TinyEXR authors.
 *
 * tptex unit-test runner. Each milestone appends its test_* function here.
 */
#include <stdio.h>

#include "tptex_test.h"

int g_tptex_failures = 0;
long g_tptex_checks = 0;

static void run(const char* name, void (*fn)(void)) {
  int before = g_tptex_failures;
  fn();
  printf("%-24s %s\n", name, g_tptex_failures == before ? "ok" : "FAILED");
}

int main(void) {
  run("half", test_half);
  run("utils", test_utils);
  run("reader", test_reader);
  run("write", test_write);
  run("filter", test_filter);
  printf("tptex: %ld checks, %d failures\n", g_tptex_checks, g_tptex_failures);
  return g_tptex_failures ? 1 : 0;
}
