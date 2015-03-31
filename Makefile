all:
	g++-4.8 -g -fopenmp -O2 -o test_tinyexr tinyexr.cc test.cc
