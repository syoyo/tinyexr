#include <cstdio>
#include <cstdlib>
#include <vector>

#define STB_IMAGE_WRITE_IMPLEMENTATION
#include "stb_image_write.h"

#include "tinyexr.h"

int main(int argc, char** argv)
{
  if (argc < 3) {
    printf("Usage: exr2rgbe input.exr output.hdr\n");
    exit(-1);
  }

  int width, height;
  float* rgba;
  const char* err;

  {
    int ret = LoadEXR(&rgba, &width, &height, argv[1], &err);
    if (ret != 0) {
      printf("err: %s\n", err);
      return -1;
    }
  }

  {
    int ret = stbi_write_hdr(argv[2], width, height, 4, rgba);

    if (ret == 0) {
      return -1; // fail
    }
  }

  return 0;
}
