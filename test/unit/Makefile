.PHONY: clean

CXX = clang++
CXXFLAGS = -fsanitize=address,undefined -g -O2 -std=c++11

tester: tester.cc ../../tinyexr.h
	$(CXX) $(CXXFLAGS) -o tester tester.cc

all: tester

check: tester
	./tester

clean:
	rm -rf tester

