all:
	gcc -O2 -c -I../../deps/miniz ../../deps/miniz/miniz.c
	g++ -std=c++11 -O2 -o exrfilter -I../common -I../../ -I ../../deps/miniz exrfilter.cc ../../tinyexr.cc miniz.o
