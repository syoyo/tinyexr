# tools/ptex — tptex, a pure-C11 port of Ptex. Included from the top-level
# Makefile (-include tools/ptex/ptex.mk); uses CC, V3_CSTD, V3_WARN, SAN from it.
#
#   make ptex-c11-gate         strict C11 -pedantic -Werror syntax gate + portability greps
#   make ptex-test             unit tests under ASan+UBSan
#   make ptex-half-exhaustive  full 2^32 float->half sweep (optimised, no sanitizers)
#   make ptex-compare          opt-in differential suite vs upstream OpenPtex (needs C++ + network once)

PTEX_DIR      = tools/ptex
PTEX_INC      = -I$(PTEX_DIR)/include -I$(PTEX_DIR)/src -Ideps/miniz
PTEX_MINIZ    = deps/miniz/miniz.c
PTEX_FP       = -ffp-contract=off
PTEX_ALL_SRC  = $(wildcard $(PTEX_DIR)/src/*.c)
PTEX_LIB_SRC  = $(filter-out $(PTEX_DIR)/src/tptex_file.c,$(PTEX_ALL_SRC))
PTEX_TEST_SRC = $(wildcard $(PTEX_DIR)/test/*.c)
PTEX_HDRS     = $(wildcard $(PTEX_DIR)/include/*.h $(PTEX_DIR)/src/*.h $(PTEX_DIR)/test/*.h)

.PHONY: ptex-c11-gate ptex-test ptex-half-exhaustive ptex-compare

ptex-c11-gate:
	@for f in $(PTEX_ALL_SRC); do \
	  echo "  c11-gate $$f"; \
	  $(CC) $(V3_CSTD) $(V3_WARN) -pedantic $(PTEX_FP) $(PTEX_INC) -O1 -fsyntax-only $$f || exit 1; \
	done
	@bad=`grep -rlE --exclude=tptex_file.c '^[[:space:]]*#[[:space:]]*include[[:space:]]*<stdio.h>' $(PTEX_DIR)/src $(PTEX_DIR)/include || true`; \
	  if [ -n "$$bad" ]; then echo "FAIL: <stdio.h> outside tptex_file.c: $$bad"; exit 1; fi
	@bad=`grep -rnE '(\bvolatile\b|_Atomic|stdatomic\.h|\balloca\b|pthread\.h|threads\.h)' $(PTEX_DIR)/src $(PTEX_DIR)/include \
	  | grep -vE ':[0-9]+:[[:space:]]*(/\*|\*|//)' || true`; \
	  if [ -n "$$bad" ]; then echo "FAIL: atomics/volatile/threads/alloca in tptex code:"; echo "$$bad"; exit 1; fi
	@echo "ptex pure-C11 gate: OK"

build/test_tptex: $(PTEX_ALL_SRC) $(PTEX_TEST_SRC) $(PTEX_HDRS) | build
	$(CC) $(V3_CSTD) -Wall -Wextra -pedantic $(PTEX_FP) $(PTEX_INC) -O1 -g $(SAN) \
	  $(PTEX_TEST_SRC) $(PTEX_ALL_SRC) $(PTEX_MINIZ) -lm -o $@

ptex-test: build/test_tptex
	./build/test_tptex

ptex-half-exhaustive: $(PTEX_LIB_SRC) $(PTEX_TEST_SRC) $(PTEX_HDRS) | build
	$(CC) $(V3_CSTD) -Wall -Wextra -pedantic $(PTEX_FP) $(PTEX_INC) -O2 \
	  $(PTEX_TEST_SRC) $(PTEX_ALL_SRC) $(PTEX_MINIZ) -lm -o build/test_tptex_exhaustive
	TPTEX_EXHAUSTIVE=1 ./build/test_tptex_exhaustive

ptex-compare:
	bash $(PTEX_DIR)/compare/run_compare.sh
