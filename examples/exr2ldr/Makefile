all:
	clang -g -O2 -c -I../../deps/miniz ../../deps/miniz/miniz.c
	clang++ -g -fsanitize=address -O2 -o exr2ldr -I../common  -I../../ -I../../deps/miniz exr2ldr.cc ../../tinyexr.cc miniz.o
