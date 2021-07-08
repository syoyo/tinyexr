#define TINYEXR_IMPLEMENTATION
#include "tinyexr.h"

#include "exr-io.h"

#include <cstdio>

namespace exrio {

bool LoadEXRRGBA(float** rgba, int *w, int *h, const char* filename)
{
  int width, height;
  float* image;
  const char *err;
  int ret = LoadEXR(&image, &width, &height, filename, &err);
  if (ret != 0) {
    fprintf(stderr, "Load EXR err: %s\n", err);
    return false;
  }

  (*rgba) = image;
  (*w) = width;
  (*h) = height;

  return true;
}

}
