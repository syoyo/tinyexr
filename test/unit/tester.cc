#define CATCH_CONFIG_MAIN  // This tells Catch to provide a main() - only do this in one cpp file
#include "catch.hpp"

#include <cstdio>
#include <cstdlib>
#include <cassert>
#include <iostream>
#include <sstream>
#include <fstream>

#define TINYEXR_IMPLEMENTATION
#define TINYEXR_USE_MINIZ 1
#include "../../tinyexr.h"

// path to https://github.com/openexr/openexr-images
const char *kOpenEXRImagePath = "../../../openexr-images/";

std::string GetPath(const char *basename)
{
  std::string s;
  s = std::string(kOpenEXRImagePath) + std::string(basename);
  return s;
}

TEST_CASE("asakusa", "[Load]") {
  EXRImage exr_image;
  EXRHeader exr_header;
  const char* err = NULL;
  int ret = ParseMultiChannelEXRHeaderFromFile(&exr_header, "../../asakusa.exr", &err);
  REQUIRE(NULL == err);
  REQUIRE(0 == ret);
}

TEST_CASE("GoldenGate", "[TileLoad]") {
  EXRImage exr_image;
  EXRHeader exr_header;
  const char* err = NULL;
  std::string filepath = GetPath("Tiles/GoldenGate.exr");
  int ret = ParseMultiChannelEXRHeaderFromFile(&exr_header, filepath.c_str(), &err);
  REQUIRE(NULL == err);
  REQUIRE(0 == ret);
  REQUIRE(true == exr_header.tiled);
}

