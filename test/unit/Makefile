.PHONY: clean

CC = clang
CXX = clang++
CXXFLAGS = -fsanitize=address,undefined -g -O2 -std=c++11 -I ../../deps/miniz
CFLAGS = -fsanitize=address,undefined -g -O2 -I ../../deps/miniz

all: tester test-issue230

miniz.o:
	$(CC) -c $(CFLAGS) ../../deps/miniz/miniz.c

tester: tester.cc ../../tinyexr.h miniz.o
	$(CXX) $(CXXFLAGS) -o tester tester.cc miniz.o

# Test for issue #230: Partial fread() handling
# Force fallback path by undefining memory mapping
test-issue230: test-issue230.cc ../../tinyexr.h miniz.o
	$(CXX) $(CXXFLAGS) -UTINYEXR_USE_WIN32_MMAP -UTINYEXR_USE_POSIX_MMAP -o test-issue230 test-issue230.cc miniz.o

check: tester test-issue230
	./tester
	./test-issue230

clean:
	rm -rf tester test-issue230 miniz.o

