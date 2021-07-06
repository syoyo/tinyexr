all:
	gcc -O2 -I../../deps/miniz -c ../../deps/miniz/miniz.c
	g++ -std=c++11 -O2 -o testmapgen -I../common -I../../ -I../../deps/miniz testmapgen.cc ../../tinyexr.cc miniz.o
