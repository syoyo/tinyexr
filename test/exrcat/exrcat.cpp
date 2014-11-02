// https://gist.github.com/mmp/ba384e1f509e2e38d5df#file-exrcat-cpp

#include "tinyexr/tinyexr.h"
#include "tinyexr/tinyexr.cc"
#include <stdio.h>
#include <assert.h>
#include <vector>
#include <ImfInputFile.h>
#include <ImfRgbaFile.h>
#include <ImfChannelList.h>
#include <ImfFrameBuffer.h>
#include <half.h>
using namespace Imf;
using namespace Imath;

#if 0
void
SaveAsPFM(const char* filename, int width, int height, float* data)
{
  FILE* fp = fopen(filename, "wb");
  if (!fp) {
    fprintf(stderr, "failed to write a PFM file.\n");
    return;
  }

  fprintf(fp, "PF\n");
  fprintf(fp, "%d %d\n", width, height);
  fprintf(fp, "-1\n"); // -1: little endian, 1: big endian

  // RGBA -> RGB
  std::vector<float> rgb(width*height*3);

  for (size_t i = 0; i < width * height; i++) {
    rgb[3*i+0] = data[4*i+0];
    rgb[3*i+1] = data[4*i+1];
    rgb[3*i+2] = data[4*i+2];
  }
  
  fwrite(&rgb.at(0), sizeof(float), width * height * 3, fp);

  fclose(fp);
}
#endif
 
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
 
int main(int argc, char *argv[]) {
  if (argc != 2) {
    fprintf(stderr, "usage: exrcat <file.exr>\n");
    return 1;
  }
 
  int ow, oh;
  float *orgb = OpenExrLoad(argv[1], &ow, &oh);

  //SaveAsPFM("out.pfm", ow, oh, orgb);
 
  int tw, th;
  float *trgb;
  const char *err;
  if (LoadEXR(&trgb, &tw, &th, argv[1], &err) != 0) {
    fprintf(stderr, "exrcat: %s %s\n", argv[1], err);
    return 1;
  }
 
  assert(ow == tw && oh == th);
  int o = 0;
  for (int y = 0; y < th; ++y) {
    for (int x = 0; x < tw; ++x, ++o) {
      printf("(%d, %d): %f %f %f %f - %f %f %f %f\n", x, y,
             orgb[4*o], orgb[4*o+1], orgb[4*o+2], orgb[4*o+3],
             trgb[4*o], trgb[4*o+1], trgb[4*o+2], trgb[4*o+3]);
    }
  }
 
  return 0;
}
