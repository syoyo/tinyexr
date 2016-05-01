#include <stdio.h>
#include <stdlib.h>
#include <tinyexr.h>

int main(int argc, char** argv)
{
  float *rgba;
  const char* err;
  int width;
  int height;

  if (argc < 2) {
    return EXIT_FAILURE;
  }

  int ret = LoadEXR(&rgba, &width, &height, argv[1], &err);

  return ret; 
}
