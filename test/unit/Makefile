.PHONY: clean

CXX ?= g++
CXXFLAGS = -g -O2 -DCATCH_CONFIG_NO_CPP11

tester: tester.cc
	$(CXX) $(CXXFLAGS) -o tester tester.cc

all: tester

check: tester
	./tester	

clean:
	rm -rf tester

