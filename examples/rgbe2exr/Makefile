all:
	gcc -O2 -c -I../../deps/miniz ../../deps/miniz/miniz.c
	g++ -O2 -o rgbe2exr -I../common -I../../ -I../../deps/miniz rgbe2exr.cc ../../tinyexr.cc miniz.o
