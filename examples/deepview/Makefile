all: miniz.o
	# macos
	#g++ -o deepview -g -O2 main.cc trackball.cc ../../tinyexr.cc -framework OpenGL -framework GLUT
	g++ -o deepview -fsanitize=address -g -O1 main.cc trackball.cc ../../tinyexr.cc miniz.o -lglut -lGL -lGLU

miniz.o: ../../miniz.c
	g++ -O2 -g -c ../../miniz.c

