all:
	g++-4.8 -g -fopenmp -O2 -o test_tinyexr tinyexr.cc test.cc

test:
	./test_tinyexr asakusa.exr

.PHONY: test
