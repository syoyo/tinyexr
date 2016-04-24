#include <cstdlib>
#include <cstdio>
#include <vector>

#define TINYEXR_IMPLEMENTATION
#include "tinyexr.h"

static const char* GetPixelType(int id)
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

#if 0
static void
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
#endif

int
main(int argc, char** argv)
{
  const char* outfilename = "output_test.exr";
  const char* err;

  if (argc < 2) {
    fprintf(stderr, "Needs input.exr.\n");
    exit(-1);
  }

  if (argc > 2) {
    outfilename = argv[2];
  }
    
  EXRHeader exr_header;

  int ret = ParseMultiChannelEXRHeaderFromFile(&exr_header, argv[1], &err);
  if (ret != 0) {
    fprintf(stderr, "Parse EXR err: %s\n", err);
    return ret;
  }

  printf("dataWindow = %d, %d, %d, %d\n",
    exr_header.data_window[0],
    exr_header.data_window[1],
    exr_header.data_window[2],
    exr_header.data_window[3]);
  printf("displayWindow = %d, %d, %d, %d\n",
    exr_header.display_window[0],
    exr_header.display_window[1],
    exr_header.display_window[2],
    exr_header.display_window[3]);
  printf("screenWindowCenter = %f, %f\n",
    static_cast<double>(exr_header.screen_window_center[0]),
    static_cast<double>(exr_header.screen_window_center[1]));
  printf("screenWindowWidth = %f\n",
    static_cast<double>(exr_header.screen_window_width));
  printf("pixelAspectRatio = %f\n",
    static_cast<double>(exr_header.pixel_aspect_ratio));
  printf("lineOrder = %d\n",
    exr_header.line_order);

  if (exr_header.num_custom_attributes > 0) {
    printf("# of custom attributes = %d\n", exr_header.num_custom_attributes);
    for (int i = 0; i < exr_header.num_custom_attributes; i++) {
      printf("  [%d] name = %s, type = %s\n", i,
        exr_header.custom_attributes[i].name,
        exr_header.custom_attributes[i].type);
    }
  }

  // Read HALF channel as FLOAT.
  for (int i = 0; i < exr_header.num_channels; i++) {
    if (exr_header.pixel_types[i] == TINYEXR_PIXELTYPE_HALF) {
      exr_header.requested_pixel_types[i] = TINYEXR_PIXELTYPE_FLOAT;
    }
  }

  EXRImage exr_image;
  InitEXRImage(&exr_image);

  ret = LoadMultiChannelEXRFromFile(&exr_image, &exr_header, argv[1], &err);
  if (ret != 0) {
    fprintf(stderr, "Load EXR err: %s\n", err);
    return ret;
  }

  printf("EXR: %d x %d\n", exr_image.width, exr_image.height);

  for (int i = 0; i < exr_header.num_channels; i++) {
    printf("pixelType[%d]: %s\n", i, GetPixelType(exr_header.pixel_types[i]));
    printf("chan[%d] = %s\n", i, exr_header.channels[i].name);
    printf("requestedPixelType[%d]: %s\n", i, GetPixelType(exr_header.requested_pixel_types[i]));
  }

  // Uncomment if you want to save image as FLOAT pixel type.
  for (int i = 0; i < exr_header.num_channels; i++) {
    if (exr_header.pixel_types[i] == TINYEXR_PIXELTYPE_FLOAT) {
      exr_header.requested_pixel_types[i] = TINYEXR_PIXELTYPE_HALF;
    }
  }

#if 0 // example to write custom attribute
  int version_minor = 3;
  exr_header.num_custom_attributes = 1;
  exr_header.custom_attributes[0].name = strdup("tinyexr_version_minor");
  exr_header.custom_attributes[0].type = strdup("int");
  exr_header.custom_attributes[0].size = sizeof(int);
  exr_header.custom_attributes[0].value = (unsigned char*)malloc(sizeof(int));
  memcpy(exr_header.custom_attributes[0].value, &version_minor, sizeof(int));
#endif

  exr_header.compression = TINYEXR_COMPRESSIONTYPE_NONE;
  ret = SaveMultiChannelEXRToFile(&exr_image, &exr_header, outfilename, &err);
  if (ret != 0) {
    fprintf(stderr, "Save EXR err: %s\n", err);
    return ret;
  }
  printf("Saved exr file. [ %s ] \n", outfilename);

  FreeEXRHeader(&exr_header);
  FreeEXRImage(&exr_image);

  return ret;
}
