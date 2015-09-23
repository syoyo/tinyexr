all:
	g++ -g -Wall -Werror -O2 -o test_tinyexr test.cc

test:
	./test_tinyexr asakusa.exr

.PHONY: test
