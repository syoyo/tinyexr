all:
	clang++ -std=c++11 -o fuzz -I../../ -g -fsanitize=address fuzz.cc /usr/lib/llvm-5.0/lib/libFuzzer.a

t:
	./fuzz issue-62-tinyexr_memcpy_heap-buffer-overflow
