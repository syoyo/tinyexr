all:
	gcc -O2 -c -I../../deps/miniz ../../deps/miniz/miniz.c
	g++ -O2 -o exr2rgbe -I../common -I../../  -I../../deps/miniz  exr2rgbe.cc ../../tinyexr.cc miniz.o
