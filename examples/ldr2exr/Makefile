all:
	gcc -O2 -c -I../../deps/miniz ../../deps/miniz/miniz.c
	g++ -O2 -o ldr2exr -I../common -I../../ -I../../deps/miniz ldr2exr.cc ../../tinyexr.cc miniz.o
