CXX ?= clang++
CXXFLAGS ?= -fsanitize=address -g -O0 -Weverything -Werror -Wno-c++11-long-long -Wno-padded -Wno-sign-conversion -DTINYEXR_USE_MINIZ=0 -DTINYEXR_USE_PIZ=0
LDFLAGS ?= -lz

all:
	$(CXX) $(CXXFLAGS) -o test_tinyexr test_tinyexr.cc $(LDFLAGS)

test:
	./test_tinyexr asakusa.exr

.PHONY: test
