#define TINYEXR_IMPLEMENTATION
#include "tinyexr.h"

#include "exr-io.h"

#include <cstdio>
#include <iostream>

namespace exrio {

bool GetEXRLayers(const char *filename)
{
  const char** layer_names = nullptr;
  int num_layers = 0;
  const char *err = nullptr;
  int ret = EXRLayers(filename, &layer_names, &num_layers, &err);

  if (err) {
    fprintf(stderr, "EXR error = %s\n", err);
  }

  if (ret != 0) {
    fprintf(stderr, "Load EXR err: %s\n", err);
    return false;
  }
  if (num_layers > 0)
  {
    fprintf(stdout, "EXR Contains %i Layers\n", num_layers);
    for (size_t i = 0; i < num_layers; ++i) {
      fprintf(stdout, "Layer %i : %s\n", i + 1, layer_names[i]);
    }
  }
  free(layer_names);
  return true;
}

bool LoadEXRRGBA(float** rgba, int *w, int *h, const char* filename, const char* layername)
{
  int width, height;
  float* image;
  const char *err = nullptr;
  int ret = LoadEXRWithLayer(&image, &width, &height, filename, layername, &err);

  if (err) {
    fprintf(stderr, "EXR error = %s\n", err);
  }

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
