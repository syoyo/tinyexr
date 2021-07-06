all:
	clang -O2 -c -I../../deps/miniz ../../deps/miniz/miniz.c
	clang++ -O2 -g -fsanitize=address -I../common -I../../ -I../../deps/miniz -o normalmap main.cc miniz.o
