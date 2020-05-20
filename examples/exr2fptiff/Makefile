
CXX=clang++

CXXFLAGS = -std=c++11 -fsanitize=address -Weverything -Werror -Wno-c++98-compat -Wno-padded -Wno-variadic-macros -g -O2 -I../../
LDFLAGS = -fsanitize=address

# ZFP
#CXXFLAGS += -DTINYEXR_USE_ZFP=1 -I/home/syoyo/work/zfp/include
#LDFLAGS += -L/home/syoyo/work/zfp/build/lib -lzfp


all: exr2fptiff

exr2fptiff: exr2fptiff.o tinyexr.o
	$(CXX) -o $@ $^ $(LDFLAGS)

exr2fptiff.o: exr2fptiff.cc tiny_dng_writer.h
	$(CXX) $(CXXFLAGS) -c -o $@ $<

tinyexr.o: ../../tinyexr.cc
	$(CXX) $(CXXFLAGS) -c -o $@ $<

.PHONY: clean


clean:
	rm -rf tinyexr.o exr2fptiff.o
