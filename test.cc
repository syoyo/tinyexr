#include <cstdlib>
#include <cstdio>
#include <vector>

#define TINYEXR_IMPLEMENTATION
#include "tinyexr.h"

const char* GetPixelType(int id)
{
  if (id == TINYEXR_PIXELTYPE_HALF) {
    return "HALF";
  } else if (id == TINYEXR_PIXELTYPE_FLOAT) {
    return "FLOAT";
  } else if (id == TINYEXR_PIXELTYPE_UINT) {
    return "UINT";
  }

  return "???";
}

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

  for (int i = 0; i < width * height; i++) {
    rgb[3*i+0] = data[4*i+0];
    rgb[3*i+1] = data[4*i+1];
    rgb[3*i+2] = data[4*i+2];
  }
  
  fwrite(&rgb.at(0), sizeof(float), width * height * 3, fp);

  fclose(fp);
}

int
main(int argc, char** argv)
{
  const char* outfilename = "output_test.exr";
  const char* err;
  EXRImage exrImage;
  InitEXRImage(&exrImage);

  if (argc < 2) {
    fprintf(stderr, "Needs input.exr.\n");
    exit(-1);
  }

  if (argc > 2) {
    outfilename = argv[2];
  }
    

  //float *rgba = NULL;
  //int width, height;
  //int ret = LoadEXR(&rgba, &width, &height, argv[1], &err);
  //if (ret != 0) {
  //  fprintf(stderr, "Load EXR err: %s\n", err);
  //  return ret;
  //}

  //SaveAsPFM("out.pfm", width, height, rgba);

#if 1

  int ret = ParseMultiChannelEXRHeaderFromFile(&exrImage, argv[1], &err);
  if (ret != 0) {
    fprintf(stderr, "Parse EXR err: %s\n", err);
    return ret;
  }

  printf("dataWindow = %d, %d, %d, %d\n",
    exrImage.data_window[0],
    exrImage.data_window[1],
    exrImage.data_window[2],
    exrImage.data_window[3]);
  printf("displayWindow = %d, %d, %d, %d\n",
    exrImage.display_window[0],
    exrImage.display_window[1],
    exrImage.display_window[2],
    exrImage.display_window[3]);
  printf("screenWindowCenter = %f, %f\n",
    exrImage.screen_window_center[0],
    exrImage.screen_window_center[1]);
  printf("screenWindowWidth = %f\n",
    exrImage.screen_window_width);
  printf("pixelAspectRatio = %f\n",
    exrImage.pixel_aspect_ratio);
  printf("lineOrder = %d\n",
    exrImage.line_order);

  if (exrImage.num_custom_attributes > 0) {
    printf("# of custom attributes = %d\n", exrImage.num_custom_attributes);
    for (int i = 0; i < exrImage.num_custom_attributes; i++) {
      printf("  [%d] name = %s, type = %s\n", i,
        exrImage.custom_attributes[i].name,
        exrImage.custom_attributes[i].type);
    }
  }

  // Read HALF channel as FLOAT.
  for (int i = 0; i < exrImage.num_channels; i++) {
    if (exrImage.pixel_types[i] == TINYEXR_PIXELTYPE_HALF) {
      exrImage.requested_pixel_types[i] = TINYEXR_PIXELTYPE_FLOAT;
    }
  }

  ret = LoadMultiChannelEXRFromFile(&exrImage, argv[1], &err);
  if (ret != 0) {
    fprintf(stderr, "Load EXR err: %s\n", err);
    return ret;
  }

  printf("EXR: %d x %d\n", exrImage.width, exrImage.height);

  for (int i = 0; i < exrImage.num_channels; i++) {
    printf("pixelType[%d]: %s\n", i, GetPixelType(exrImage.pixel_types[i]));
    printf("chan[%d] = %s\n", i, exrImage.channel_names[i]);
    printf("requestedPixelType[%d]: %s\n", i, GetPixelType(exrImage.requested_pixel_types[i]));
  }

  // Uncomment if you want to save image as FLOAT pixel type.
  for (int i = 0; i < exrImage.num_channels; i++) {
    if (exrImage.pixel_types[i] == TINYEXR_PIXELTYPE_FLOAT) {
      exrImage.requested_pixel_types[i] = TINYEXR_PIXELTYPE_HALF;
    }
  }

#if 0 // example to write custom attribute
  int version_minor = 3;
  exrImage.num_custom_attributes = 1;
  exrImage.custom_attributes[0].name = strdup("tinyexr_version_minor");
  exrImage.custom_attributes[0].type = strdup("int");
  exrImage.custom_attributes[0].size = sizeof(int);
  exrImage.custom_attributes[0].value = (unsigned char*)malloc(sizeof(int));
  memcpy(exrImage.custom_attributes[0].value, &version_minor, sizeof(int));
#endif

  ret = SaveMultiChannelEXRToFile(&exrImage, outfilename, &err);
  if (ret != 0) {
    fprintf(stderr, "Save EXR err: %s\n", err);
    return ret;
  }
  printf("Saved exr file. [ %s ] \n", outfilename);

  FreeEXRImage(&exrImage);
#endif

  return ret;
}
