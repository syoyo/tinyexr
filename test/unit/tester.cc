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
  EXRVersion exr_version;
  EXRImage exr_image;
  EXRHeader exr_header;
  const char* err = NULL;
  int ret = ParseEXRVersionFromFile(&exr_version, "../../asakusa.exr");
  REQUIRE(TINYEXR_SUCCESS == ret);

  ret = ParseEXRHeaderFromFile(&exr_header, &exr_version, "../../asakusa.exr", &err);
  REQUIRE(NULL == err);
  REQUIRE(TINYEXR_SUCCESS == ret);
}

TEST_CASE("Tiles/GoldenGate.exr", "[Version]") {
  EXRVersion exr_version;
  std::string filepath = GetPath("Tiles/GoldenGate.exr");
  int ret = ParseEXRVersionFromFile(&exr_version, filepath.c_str());
  REQUIRE(TINYEXR_SUCCESS == ret);
  REQUIRE(true == exr_version.tiled);
}

TEST_CASE("Tiles/GoldenGate.exr|Load", "[Load]") {
  EXRVersion exr_version;
  std::string filepath = GetPath("Tiles/GoldenGate.exr");
  int ret = ParseEXRVersionFromFile(&exr_version, filepath.c_str());
  REQUIRE(TINYEXR_SUCCESS == ret);
  REQUIRE(true == exr_version.tiled);
  REQUIRE(false == exr_version.non_image);
  REQUIRE(false == exr_version.multipart);

  EXRVersion version;
  EXRHeader header;
  EXRImage image;
  InitEXRHeader(&header);
  InitEXRImage(&image);

  const char* err;
  ret = ParseEXRHeaderFromFile(&header, &exr_version, filepath.c_str(), &err);
  REQUIRE(TINYEXR_SUCCESS == ret);


  ret= LoadEXRImageFromFile(&image, &header, filepath.c_str(), &err);
  REQUIRE(TINYEXR_SUCCESS == ret);

  FreeEXRHeader(&header);
  FreeEXRImage(&image);
}

TEST_CASE("Beachball/multipart.0001.exr", "[Version]") {
  EXRVersion exr_version;
  std::string filepath = GetPath("Beachball/multipart.0001.exr");
  int ret = ParseEXRVersionFromFile(&exr_version, filepath.c_str());
  REQUIRE(TINYEXR_SUCCESS == ret);
  REQUIRE(true == exr_version.multipart);
}


TEST_CASE("GoldenGate", "[TileLoad]") {
  EXRVersion exr_version;
  EXRImage exr_image;
  EXRHeader exr_header;
  const char* err = NULL;
  std::string filepath = GetPath("Tiles/GoldenGate.exr");
  int ret = ParseEXRVersionFromFile(&exr_version, filepath.c_str());
  REQUIRE(TINYEXR_SUCCESS == ret);
  REQUIRE(true == exr_version.tiled);
  ret = ParseEXRHeaderFromFile(&exr_header, &exr_version, filepath.c_str(), &err);
  REQUIRE(NULL == err);
  REQUIRE(TINYEXR_SUCCESS == ret);
}

