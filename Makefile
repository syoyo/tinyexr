all:
	g++ -g -Wall -Werror -O2 -o test_tinyexr test_tinyexr.cc

test:
	./test_tinyexr asakusa.exr

.PHONY: test
