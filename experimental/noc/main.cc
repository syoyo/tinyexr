#include <cassert>

#define NOC_PACKER_IMPLEMENTATION
#include "noc_packer.h"

#define TINYEXR_IMPLEMENTATION
#include "tinyexr.h"

#include <cstdio>
#include <cstdlib>

int main(int argc, char **argv) {
  if (argc < 2) {
    fprintf(stderr, "Needs input.exr.\n");
    exit(-1);
  }

  const char *err = NULL;
  int width, height;
  float *image;
  int ret = LoadEXR(&image, &width, &height, argv[1], &err);
  if (ret != TINYEXR_SUCCESS) {
    if (err) {
      fprintf(stderr, "Load EXR err: %s(code %d)\n", err, ret);
    } else {
      fprintf(stderr, "Load EXR err: code = %d\n", ret);
    }
    FreeEXRErrorMessage(err);
    return ret;
  }

  struct pixel {
    float r;
    float g;
    float b;
    float a;
  };

  const struct noc_packer_column cols[] = {{"r", 'f', 0, 4, .precision=8},
                                           {"g", 'f', 4, 4, .precision=8},
                                           {"b", 'f', 8, 4, .precision=8},
                                           {"a", 'f', 12, 4, .precision=8},
                                           {}};

  char *buf;
  int sz = noc_packer_compress(reinterpret_cast<const char *>(image),
                               width * height * sizeof(pixel),
                               sizeof(pixel), cols, &buf);

  std::cout << "input = " << (width * height * sizeof(pixel))
            << ", compressed = " << sz << std::endl;
  std::cout << " ratio = "
            << 100.0 * double(sz) / double(width * height * sizeof(pixel))
            << " %%" << std::endl;

  pixel *data2;
  sz = noc_packer_uncompress(buf, (width * height * sizeof(pixel)),
                             sizeof(pixel), cols, (char **)&data2);

  std::cout << "decompressed size = " << sz << std::endl;
  size_t original_size = width * height * sizeof(pixel);
  assert(sz == original_size);
  ret =
      SaveEXR(reinterpret_cast<const float *>(data2), width, height,
              4 /* =RGBA*/, 0 /* = save as fp16 format */, "decompressed.exr", &err);
  if (ret != TINYEXR_SUCCESS) {
    if (err) {
      fprintf(stderr, "Err = %s\n", err);
      FreeEXRErrorMessage(err);
    }
    fprintf(stderr, "Failed to save EXR image. code = %d\n", ret);
  }

  free(buf);
  free(data2);

  return EXIT_SUCCESS;
}
