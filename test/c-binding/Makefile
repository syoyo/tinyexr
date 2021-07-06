all:
	gcc -c -I../../deps/miniz ../../deps/miniz/miniz.c
	g++ -c -I../../ -I../../deps/miniz ../../tinyexr.cc
	gcc -c -I../../ test.c
	gcc test.o tinyexr.o miniz.o -lstdc++
