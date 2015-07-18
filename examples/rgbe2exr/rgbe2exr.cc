#include <cstdio>
#include <cstdlib>
#include <vector>

#define STB_IMAGE_IMPLEMENTATION
#include "stb_image.h"

#include "tinyexr.h"

int main(int argc, char** argv)
{
  if (argc < 3) {
    printf("Usage: rgbe2exr input.hdr output.exr\n");
    exit(-1);
  }

  int width, height;
  int n;
  float *rgb = stbi_loadf(argv[1], &width, &height, &n, 0);
  if (!rgb || n != 3) {
    return -1;
  }

  EXRImage image;
  InitEXRImage(&image);

  image.num_channels = 3;

  // Must be BGR(A) order, since most of EXR viewers expect this channel order.
  const char* channel_names[] = {"B", "G", "R"}; // "B", "G", "R", "A" for RGBA image

  std::vector<float> images[3];
  images[0].resize(width * height);
  images[1].resize(width * height);
  images[2].resize(width * height);

  for (int i = 0; i < width * height; i++) {
    images[0][i] = rgb[3*i+0];
    images[1][i] = rgb[3*i+1];
    images[2][i] = rgb[3*i+2];
  }

  float* image_ptr[3];
  image_ptr[0] = &(images[2].at(0)); // B
  image_ptr[1] = &(images[1].at(0)); // G
  image_ptr[2] = &(images[0].at(0)); // R

  image.channel_names = channel_names;
  image.images = (unsigned char**)image_ptr;
  image.width = width;
  image.height = height;

  image.pixel_types = (int *)malloc(sizeof(int) * image.num_channels);
  image.requested_pixel_types = (int *)malloc(sizeof(int) * image.num_channels);
  for (int i = 0; i < image.num_channels; i++) {
    image.pixel_types[i] = TINYEXR_PIXELTYPE_FLOAT; // pixel type of input image
    image.requested_pixel_types[i] = TINYEXR_PIXELTYPE_HALF; // pixel type of output image to be stored in .EXR
  }

  const char* err;
  int ret = SaveMultiChannelEXRToFile(&image, argv[2], &err);
  if (ret != 0) {
    fprintf(stderr, "Save EXR err: %s\n", err);
    return ret;
  }
  printf("Saved exr file. [ %s ] \n", argv[2]);

  return 0;
}
