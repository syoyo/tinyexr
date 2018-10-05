#include <cstdio>
#include <cstdlib>
#include <vector>

#define STB_IMAGE_RESIZE_IMPLEMENTATION
#include "stb_image_resize.h"

#include "tinyexr.h"

int main(int argc, char** argv)
{
  if (argc < 5) {
    printf("Usage: exrresize input.exr output.exr dst_width dst_height.\n");
    printf("  Only supports RGB or RGBA EXR input.\n");
    exit(-1);
  }

  int dst_width = atoi(argv[3]);
  int dst_height = atoi(argv[4]);

  int width, height;
  float* rgba;
  const char* err;

  {
    int ret = LoadEXR(&rgba, &width, &height, argv[1], &err);
    if (ret != TINYEXR_SUCCESS) {
      printf("err: %s\n", err);
      return -1;
    }
  }

  std::vector<float> buf(dst_width * dst_height * 4);
  int ret = stbir_resize_float(rgba, width, height, width*4*sizeof(float), &buf.at(0), dst_width, dst_height,dst_width*4*sizeof(float), 4);
  assert(ret != 0);

  ret = SaveEXR(buf.data(), dst_width, dst_height, 4, /*fp16*/0, argv[2], &err);
  if (ret != TINYEXR_SUCCESS) {
    if (err) {
      fprintf(stderr, "err: %s\n", err);
      FreeEXRErrorMessage(err);
    }
  }

  return (ret == TINYEXR_SUCCESS);
}
