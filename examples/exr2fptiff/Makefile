
CXX=clang++
CC=clang

CFLAGS = -fsanitize=address -Weverything -Wno-padded -g -O2 -I../../ -I../../deps/miniz
CXXFLAGS = -std=c++11 -Wno-c++98-compat -Wno-variadic-macros $(CFLAGS)
LDFLAGS = -fsanitize=address

# ZFP
#CXXFLAGS += -DTINYEXR_USE_ZFP=1 -I/home/syoyo/work/zfp/include
#LDFLAGS += -L/home/syoyo/work/zfp/build/lib -lzfp


all: exr2fptiff

exr2fptiff: exr2fptiff.o tinyexr.o miniz.o
	$(CXX) -o $@ $^ $(LDFLAGS)

exr2fptiff.o: exr2fptiff.cc tiny_dng_writer.h
	$(CXX) $(CXXFLAGS) -c -o $@ $<

tinyexr.o: ../../tinyexr.cc
	$(CXX) $(CXXFLAGS) -c -o $@ $<

miniz.o: ../../deps/miniz/miniz.c
	$(CC) $(CFLAGS) -c $(INC_DIR) $<

.PHONY: clean


clean:
	rm -rf tinyexr.o exr2fptiff.o
