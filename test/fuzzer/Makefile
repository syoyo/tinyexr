ISSUE_63_FLAGS=-O1 -g -fsanitize=address,bool,float-cast-overflow,integer-divide-by-zero,return,returns-nonnull-attribute,shift-exponent,signed-integer-overflow,unreachable,vla-bound -fno-sanitize-recover=all -funsigned-char

all:
	clang++ -std=c++11 -o fuzz_62 -I../../ -g -fsanitize=address fuzz.cc /usr/lib/llvm-5.0/lib/libFuzzer.a
	clang++ -std=c++11 -o fuzz_63 -I../../ ${ISSUE_63_FLAGS} fuzz.cc /usr/lib/llvm-5.0/lib/libFuzzer.a


t:
	./fuzz_62 issue-62-tinyexr_memcpy_heap-buffer-overflow
	./fuzz_63 issue-63-tinyexr_signed-integer-overflow
