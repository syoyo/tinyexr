all:
	clang -g -O2 -c -I../../deps/miniz ../../deps/miniz/miniz.c
	clang++ -fsanitize=undefined -O2 -o exrresize -I../common -I../../ -I../../deps/miniz resize.cc ../../tinyexr.cc miniz.o
