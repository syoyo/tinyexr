// https://gist.github.com/mmp/21ea8ac6d7f682b6252b

#include "tinyexr/tinyexr.h"
#include "tinyexr/tinyexr.cc"
#include <stdio.h>
#include <assert.h>
#include <vector>
#include <algorithm>
#include <ImfInputFile.h>
#include <ImfRgbaFile.h>
#include <ImfChannelList.h>
#include <ImfFrameBuffer.h>
#include <half.h>
using namespace Imf;
using namespace Imath;
 
static float *OpenExrLoad(const char *name, int *width, int *height) {
  try {
    RgbaInputFile file (name);
    Box2i dw = file.dataWindow();
    *width = dw.max.x - dw.min.x + 1;
    *height = dw.max.y - dw.min.y + 1;
    std::vector<Rgba> pixels(*width * *height);
    file.setFrameBuffer(&pixels[0] - dw.min.x - dw.min.y * *width, 1, *width);
    file.readPixels(dw.min.y, dw.max.y);
 
    printf("OpenExr\n    datawindow: (%d %d) - (%d %d)\n", dw.min.x, dw.min.y,
            dw.max.x, dw.max.y);
    printf("    line order %s\n", (file.lineOrder() == INCREASING_Y) ?
           "increasing y" : ((file.lineOrder() == DECREASING_Y) ? "decreasing y"
                             : "random y"));
    printf("    compression: ");
    switch (file.compression()) {
      case NO_COMPRESSION:   printf("none"); break;
      case RLE_COMPRESSION:  printf("RLE"); break;
      case ZIPS_COMPRESSION: printf("zip"); break;
      case ZIP_COMPRESSION:  printf("zips"); break;
      case PIZ_COMPRESSION:  printf("piz"); break;
      case PXR24_COMPRESSION: printf("pxr24"); break;
      case B44_COMPRESSION: printf("b44"); break;
      case B44A_COMPRESSION: printf("b44a"); break;
      default: printf("unknown!");
    }
    printf("\n");
 
    printf("    channels: ");
    RgbaChannels channels = file.channels();
    if (channels & WRITE_R) printf("R");
    if (channels & WRITE_G) printf("G");
    if (channels & WRITE_B) printf("B");
    if (channels & WRITE_A) printf("A");
    if (channels & WRITE_Y) printf("Y");
    if (channels & WRITE_C) printf("C");
    printf("\n");
 
    float *ret = new float[4 * *width * *height];
    for (int i = 0; i < *width * *height; ++i) {
      ret[4*i] = pixels[i].r;
      ret[4*i+1] = pixels[i].g;
      ret[4*i+2] = pixels[i].b;
      ret[4*i+3] = pixels[i].a;
    }
    return ret;
  } catch (const std::exception &e) {
    return NULL;
  }
}
 
static void WriteImageEXR(const char *name, float *rgba,
                          int xRes, int yRes) {
    Rgba *hrgba = new Rgba[xRes * yRes];
    for (int i = 0; i < xRes * yRes; ++i)
      hrgba[i] = Rgba(rgba[4*i], rgba[4*i+1], rgba[4*i+2], rgba[4*i+3]);
 
    Box2i displayWindow(V2i(0,0), V2i(xRes-1, yRes-1));
    Box2i dataWindow(V2i(0, 0), V2i(xRes - 1, yRes - 1));
 
    try {
        RgbaOutputFile file(name, displayWindow, dataWindow, WRITE_RGBA);
        file.setFrameBuffer(hrgba, 1, xRes);
        file.writePixels(yRes);
    }
    catch (const std::exception &e) {
      fprintf(stderr, "Unable to write image file \"%s\": %s", name,
              e.what());
    }
 
    delete[] hrgba;
}
 
 
int main(int argc, char *argv[]) {
  if (argc != 3) {
    fprintf(stderr, "usage: exrwritetest <tinyexr-filename.exr> <openexr-filename.exr>\n");
    return 1;
  }
 
  int w = 1;
  int h = 2;
  float *rgba = new float[4 * w * h];
  for (int i = 0; i < 4 * w * h; ++i) {
    rgba[i] = drand48();
  }
 
  WriteImageEXR(argv[2], rgba, w, h);
  const char *err;
  SaveEXR(rgba, w, h, argv[1], &err);
  
  int ow, oh;
  float *orgba = OpenExrLoad(argv[2], &ow, &oh);
 
  int tw, th;
  float *trgba;
  if (LoadEXR(&trgba, &tw, &th, argv[1], &err) != 0) {
    fprintf(stderr, "exrwritetest: %s %s\n", argv[2], err);
    return 1;
  }
 
  int offset = 0;
  for (int y = 0; y < h; ++y) {
    for (int x = 0; x < w; ++x)
      for (int c = 0; c < 4; ++c, ++offset)
        if (orgba[offset] != trgba[offset])
          fprintf(stderr, "Mismatch at (%d,%d), component %d: "
                  "orig %g, OpenEXR %g (err %g), tinyexr %g (err %g)\n",
                  x, y, c, rgba[offset],
                  orgba[offset], fabsf(rgba[offset] - orgba[offset]),
                  trgba[offset], fabsf(rgba[offset] - trgba[offset]));
  }
 
  return 0;
}
