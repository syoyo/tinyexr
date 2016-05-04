
CXX ?= clang++
CXXFLAGS ?= -fsanitize=address -g -O0 -Wno-c++11-long-long -Wno-padded -Wno-sign-conversion -DTINYEXR_USE_MINIZ=0 -DTINYEXR_USE_PIZ=0
LDFLAGS ?= -lz

# ZFP
#CXXFLAGS += -DTINYEXR_USE_ZFP=1 -I./deps/ZFP/inc
#LDFLAGS += -L./deps/ZFP/lib -lzfp

all:
	$(CXX) $(CXXFLAGS) -o test_tinyexr test_tinyexr.cc $(LDFLAGS)

test:
	./test_tinyexr asakusa.exr

.PHONY: test
