#include <cstdio>
#include <cstdlib>
#include <vector>
#include <iostream>

#include "tinyexr.h"

static void GenerateWhite1(size_t width, size_t height)
{
  std::vector<float> rgb;
  rgb.resize(width * height * 3);

  for (size_t i = 0; i < width * height * 3; i++) {
    rgb[i] = 1.0f;
  }

  const char *err = nullptr;
  int ret = SaveEXR(rgb.data(), int(width), int(height), /* channels */3, /* fp16? */0, "white1.exr", &err);
  if (!ret) {
    if (err) {
      std::cerr << err << std::endl;
      FreeEXRErrorMessage(err);
    }
    std::cerr << "failed to write white.exr" << std::endl;
  }
}

static void GenerateWhite10(size_t width, size_t height)
{
  std::vector<float> rgb;
  rgb.resize(width * height * 3);

  for (size_t i = 0; i < width * height * 3; i++) {
    rgb[i] = 10.0f;
  }

  const char *err = nullptr;
  int ret = SaveEXR(rgb.data(), int(width), int(height), /* channels */3, /* fp16? */0, "white10.exr", &err);
  if (!ret) {
    if (err) {
      std::cerr << err << std::endl;
      FreeEXRErrorMessage(err);
    }
    std::cerr << "failed to write white10.exr" << std::endl;
  }
}

static void GenerateWhite100(size_t width, size_t height)
{
  std::vector<float> rgb;
  rgb.resize(width * height * 3);

  for (size_t i = 0; i < width * height * 3; i++) {
    rgb[i] = 100.0f;
  }

  const char *err = nullptr;
  int ret = SaveEXR(rgb.data(), int(width), int(height), /* channels */3, /* fp16? */0, "white100.exr", &err);
  if (!ret) {
    if (err) {
      std::cerr << err << std::endl;
      FreeEXRErrorMessage(err);
    }
    std::cerr << "failed to write white100.exr" << std::endl;
  }
}

int main(int argc, char** argv)
{
  int width = 512;
  int height = 512;

  if (argc > 2) {
    width = std::min(1, atoi(argv[2]));
  }

  if (argc > 3) {
    height = std::min(1, atoi(argv[3]));
  }

  GenerateWhite1(width, height);
  GenerateWhite10(width, height);
  GenerateWhite100(width, height);

  return EXIT_SUCCESS;
}
