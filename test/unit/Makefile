.PHONY: clean

CC = clang
CXX = clang++
CXXFLAGS = -fsanitize=address,undefined -g -O2 -std=c++11 -I ../../deps/miniz
CFLAGS = -fsanitize=address,undefined -g -O2 -I ../../deps/miniz

all: tester

miniz.o:
	$(CC) -c $(CFLAGS) ../../deps/miniz/miniz.c
	
tester: tester.cc ../../tinyexr.h miniz.o
	$(CXX) $(CXXFLAGS) -o tester tester.cc miniz.o

check: tester
	./tester

clean:
	rm -rf tester miniz.o

