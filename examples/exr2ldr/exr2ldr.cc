#include <cstdio>
#include <cstdlib>
#include <vector>

#ifdef __clang__
#pragma clang diagnostic push
#pragma clang diagnostic ignored "-Weverything"
#endif

#define STB_IMAGE_RESIZE_IMPLEMENTATION
#include "stb_image_resize.h"

#define STB_IMAGE_WRITE_IMPLEMENTATION
#include "stb_image_write.h"

#ifdef __clang__
#pragma clang diagnostic pop
#endif

#include "tinyexr.h"

inline unsigned char ftouc(float f, float gamma)
{
  int i = static_cast<int>(255.0f * powf(f, 1.0f / gamma));
  if (i > 255) i = 255;
  if (i < 0) i = 0;

  return static_cast<unsigned char>(i);
}

bool SaveImage(const char* filename, const float* rgba, float scale, float gamma, int width, int height, bool ignore_alpha) {

  std::vector<unsigned char> dst(width * height * 4);

  // alpha channel is also affected by `scale` parameter.
  if(ignore_alpha) {
    for (size_t i = 0; i < width * height; i++) {
        dst[i * 4 + 0] = ftouc(rgba[i * 4 + 0] * scale, gamma);
        dst[i * 4 + 1] = ftouc(rgba[i * 4 + 1] * scale, gamma);
        dst[i * 4 + 2] = ftouc(rgba[i * 4 + 2] * scale, gamma);
        dst[i * 4 + 3] = 255;
    }
  } else {
    for (size_t i = 0; i < width * height * 4; i++) {
        dst[i] = ftouc(rgba[i] * scale, gamma);
    }
  }

  int ret = stbi_write_png(filename, width, height, 4, static_cast<const void*>(dst.data()), width * 4);

  return (ret > 0);
}

int main(int argc, char** argv)
{
  if (argc < 3) {
    printf("Usage: exr2ldr input.exr output.png (scale) (resize_factor) (gammavalue) (-i or --ignore-alpha).\n");
    printf("    Pixel value [0.0, 1.0] in EXR is mapped to [0, 255] for LDR image.\n");
    printf("    You can adjust pixel value by `scale`(default = 1.0).\n");
    printf("    Resize image using `resize_factor`(default = 1.0). 2 = create half size image, 4 = 1/4 image, and so on\n");
    printf("    gammmavalue will be used for gamma correction when saving png image(default = 2.2).\n");
    printf("    Ignore alpha value of input using -i or --ignore-alpha flag, and alpha of output is set to 255.\n");
    exit(-1);
  }

  float scale = 1.0f;
  if (argc > 3) {
    scale = atof(argv[3]);
  }

  float resize_factor = 1.0f;
  if (argc > 4) {
    resize_factor = atof(argv[4]);
  }

  float gamma = 2.2f;
  if (argc > 5) {
    gamma = atof(argv[5]);
  }

  bool ignore_alpha = false;
  if (argc > 6 && (strcmp(argv[6], "-i") == 0 || strcmp(argv[6], "--ignore-alpha") == 0)) {
    ignore_alpha = true;
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

  int dst_width  = width / resize_factor;
  int dst_height = height / resize_factor;
  printf("dst = %d, %d\n", dst_width, dst_height);

  std::vector<float> buf(dst_width * dst_height * 4);
  int ret = stbir_resize_float(rgba, width, height, width*4*sizeof(float), &buf.at(0), dst_width, dst_height,dst_width*4*sizeof(float), 4);
  assert(ret != 0);

  bool ok = SaveImage(argv[2], &buf.at(0), scale, gamma, dst_width, dst_height, ignore_alpha);

  free(rgba);

  return (ok ? 0 : -1);
}
