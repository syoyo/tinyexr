CC=clang
CXX=clang++
CXXFLAGS ?= -fsanitize=address -fsanitize=undefined -Weverything -Werror -Wextra -g -O0 -DTINYEXR_USE_MINIZ=1 -DTINYEXR_USE_PIZ=1
#LDFLAGS ?= -lz

# ZFP
#CXXFLAGS += -DTINYEXR_USE_ZFP=1 -I./deps/ZFP/inc
#LDFLAGS += -L./deps/ZFP/lib -lzfp

all: miniz.o
	$(CXX) $(CXXFLAGS) -I. -o test_tinyexr test_tinyexr.cc miniz.o $(LDFLAGS)

miniz.o: miniz.c
	$(CC) -O2 -g -c $<


test:
	./test_tinyexr asakusa.exr

.PHONY: test
