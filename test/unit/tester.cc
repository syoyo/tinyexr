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


TEST_CASE("asakusa", "[Load]") {
  EXRImage exrImage;
  EXRHeader exrHeader;
  const char* err = NULL;
  int ret = ParseMultiChannelEXRHeaderFromFile(&exrHeader, "../../asakusa.exr", &err);
  REQUIRE(NULL == err);
  REQUIRE(0 == ret);
}

