#ISSUE_63_FLAGS=-O1 -g -fsanitize=address,bool,float-cast-overflow,integer-divide-by-zero,return,returns-nonnull-attribute,shift-exponent,signed-integer-overflow,unreachable,vla-bound -fno-sanitize-recover=all -funsigned-char

all: miniz
	clang++ -std=c++11 -o fuzz -I../../ -I../../deps/miniz -g -fsanitize=address,fuzzer fuzz.cc miniz.o
	#clang++ -std=c++11 -o fuzz_63 -I../../ -I../../deps/miniz ${ISSUE_63_FLAGS} fuzz.cc libminiz.a

miniz:
	clang -c -I../../deps/miniz -g ../../deps/miniz/miniz.c
	#llvm-ar rc libminiz.a miniz.o

t:
	./fuzz
	#./fuzz_62 issue-62-tinyexr_memcpy_heap-buffer-overflow
	#./fuzz_63 issue-63-tinyexr_signed-integer-overflow
