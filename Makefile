#CXX ?= clang++
#CXXFLAGS ?= -fsanitize=address -Werror -Wall -Wextra -g -O0 -DTINYEXR_USE_MINIZ=0 -DTINYEXR_USE_PIZ=0
#LDFLAGS ?= -lz

# ZFP(experimental)
#CXXFLAGS += -DTINYEXR_USE_ZFP=1 -I./deps/ZFP/include
#LDFLAGS += -L./deps/ZFP/lib -lzfp

# nanozlib(experimental)
#BUILD_NANOZLIB=1
#CXXFLAGS += -DTINYEXR_USE_NANOZLIB=1 -DTINYEXR_USE_MINIZ=0 -I./deps/nanozlib

ifeq ($(BUILD_NANOZLIB),1)
else
  DEPOBJS = miniz.o
  CFLAGS += -I./deps/miniz
  CXXFLAGS += -I./deps/miniz
endif

.PHONY: test clean

all: $(DEPOBJS)
	$(CXX) $(CXXFLAGS) -o test_tinyexr test_tinyexr.cc $(DEPOBJS) $(LDFLAGS)

miniz.o:
	$(CC) $(CFLAGS) -c ./deps/miniz/miniz.c

test:
	./test_tinyexr asakusa.exr

clean:
	rm -rf test_tinyexr miniz.o

