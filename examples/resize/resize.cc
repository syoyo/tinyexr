#include <cstdio>
#include <cstdlib>
#include <vector>

#define STB_IMAGE_RESIZE_IMPLEMENTATION
#include "stb_image_resize.h"

#include "tinyexr.h"

void SaveImage(const char* filename, const float* rgba, int width, int height) {

  float* image_ptr[4];
  std::vector<float> images[4];
  images[0].resize(width * height);
  images[1].resize(width * height);
  images[2].resize(width * height);
  images[3].resize(width * height);

  for (int i = 0; i < width * height; i++) {
    images[0][i] = rgba[4*i+0];
    images[1][i] = rgba[4*i+1];
    images[2][i] = rgba[4*i+2];
    images[3][i] = rgba[4*i+3];
  }

  image_ptr[0] = &(images[3].at(0)); // A
  image_ptr[1] = &(images[2].at(0)); // B
  image_ptr[2] = &(images[1].at(0)); // G
  image_ptr[3] = &(images[0].at(0)); // R

  EXRImage image;

  image.num_channels = 4;
  const char* channel_names[] = {"A", "B", "G", "R"}; // must be ABGR order.

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
  int fail = SaveMultiChannelEXRToFile(&image, filename, &err);
  if (fail) {
    fprintf(stderr, "Error: %s\n", err);
  } else {
    printf("Saved image to [ %s ]\n", filename);
  }

  free(image.pixel_types);
  free(image.requested_pixel_types);

}

int main(int argc, char** argv)
{
  if (argc < 5) {
    printf("Usage: exrresize input.exr output.hdr dst_width dst_height.\n");
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
    if (ret != 0) {
      printf("err: %s\n", err);
      return -1;
    }
  }

  std::vector<float> buf(dst_width * dst_height * 4);
  int ret = stbir_resize_float(rgba, width, height, width*4*sizeof(float), &buf.at(0), dst_width, dst_height,dst_width*4*sizeof(float), 4);
  assert(ret != 0);

  SaveImage(argv[2], &buf.at(0), dst_width, dst_height);


  return 0;
}
