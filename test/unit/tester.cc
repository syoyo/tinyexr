// Assume this file is encoded in UTF-8
#define CATCH_CONFIG_MAIN  // This tells Catch to provide a main() - only do
                           // this in one cpp file

#include <cassert>
#include <cstdio>
#include <cstdlib>
#include <fstream>
#include <iostream>
#include <sstream>

#include "catch.hpp"

#ifdef _WIN32
#ifndef _CRT_SECURE_NO_WARNINGS
#define _CRT_SECURE_NO_WARNINGS
#endif
#include <windows.h>
#endif

#define TINYEXR_IMPLEMENTATION
#include "../../tinyexr.h"

// uncomment it to write out memory-saved images to files
//#define DUMP_IMAGES

// path to https://github.com/openexr/openexr-images
// TODO(syoyo): Read openexr-images path from command argument.
const char* kOpenEXRImagePath = "../../../openexr-images/";

std::string GetPath(const char* basename) {
  std::string s;
  s = std::string(kOpenEXRImagePath) + std::string(basename);
  return s;
}

// simply dumping to build folder
std::string GetDumpPath(const char* basename) {
  std::string s = basename;
  size_t index = s.find_last_of("/\\");

  if (index != std::string::npos && index + 1 < s.size()) {
    s = s.substr(index + 1);
  }
  //return "dump/" + s;
  return s;
}

// https://stackoverflow.com/questions/148403/utf8-to-from-wide-char-conversion-in-stl/148665#148665
std::wstring UTF8_to_wchar(const char* in) {
  std::wstring out;
  unsigned int codepoint;
  while (*in != 0) {
    unsigned char ch = static_cast<unsigned char>(*in);
    if (ch <= 0x7f)
      codepoint = ch;
    else if (ch <= 0xbf)
      codepoint = (codepoint << 6) | (ch & 0x3f);
    else if (ch <= 0xdf)
      codepoint = ch & 0x1f;
    else if (ch <= 0xef)
      codepoint = ch & 0x0f;
    else
      codepoint = ch & 0x07;
    ++in;
    if (((*in & 0xc0) != 0x80) && (codepoint <= 0x10ffff)) {
      if (sizeof(wchar_t) > 2)
        out.append(1, static_cast<wchar_t>(codepoint));
      else if (codepoint > 0xffff) {
        out.append(1, static_cast<wchar_t>(0xd800 + (codepoint >> 10)));
        out.append(1, static_cast<wchar_t>(0xdc00 + (codepoint & 0x03ff)));
      } else if (codepoint < 0xd800 || codepoint >= 0xe000)
        out.append(1, static_cast<wchar_t>(codepoint));
    }
  }
  return out;
}

#ifdef DUMP_IMAGES
// return true if success
static bool WriteMemoryToFile(const char *filename, const unsigned char* memory, size_t size)
{
  std::cout << "Saving:" << std::string(filename) << std::endl;
  FILE *fp = NULL;
#ifdef _WIN32
#if defined(_MSC_VER) || defined(__MINGW32__)  // MSVC, MinGW gcc or clang
  errno_t errcode =
      _wfopen_s(&fp, UTF8_to_wchar(filename).c_str(), L"wb");
  if (errcode != 0) return false;
#else
  // Unknown compiler
  fp = fopen(filename, "wb");
#endif
#else
  fp = fopen(filename, "wb");
#endif
  if (!fp) return false;

  size_t written_size = 0;
  if (size && memory) {
    written_size = fwrite(memory, 1, size, fp);
  }

  fclose(fp);
  
  return written_size == size;
}
#endif

// some helper funcs
static bool operator == (const EXRBox2i& a, const EXRBox2i& b)
{
  return a.min_x == b.min_x && a.min_y == b.min_y &&
    a.max_x == b.max_x && a.max_y == b.max_y;
}

static int GetWidth(const EXRBox2i& box)
{
  return box.max_x - box.min_x + 1;
}

static int GetHeight(const EXRBox2i& box)
{
  return box.max_y - box.min_y + 1;
}

static void CompareHeaders(const EXRHeader& header1, const EXRHeader& header2)
{
#if 0
  printf("header1.dataWindow = %d, %d, %d, %d\n", header1.data_window.min_x,
     header1.data_window.min_y, header1.data_window.max_x, header1.data_window.max_y);
  printf("header2.dataWindow = %d, %d, %d, %d\n", header2.data_window.min_x,
     header2.data_window.min_y, header2.data_window.max_x, header2.data_window.max_y);
#endif
  REQUIRE(header1.compression_type == header2.compression_type);
  REQUIRE(header1.num_channels == header2.num_channels);
  REQUIRE(GetWidth(header1.data_window) == GetWidth(header2.data_window));
  REQUIRE(GetHeight(header1.data_window) == GetHeight(header2.data_window));
  //REQUIRE(header1.display_window == header2.display_window);
  //REQUIRE(header1.screen_window_width == header2.screen_window_width);
  //REQUIRE(header1.pixel_aspect_ratio == header2.pixel_aspect_ratio);
  REQUIRE(header1.tiled == header2.tiled);
  REQUIRE(header1.tile_size_x == header2.tile_size_x);
  REQUIRE(header1.tile_size_y == header2.tile_size_y);
  REQUIRE(header1.tile_level_mode == header2.tile_level_mode);
  REQUIRE(header1.tile_rounding_mode == header2.tile_rounding_mode);

  REQUIRE(header1.non_image == header2.non_image);

  REQUIRE(0 == strcmp(header1.name, header2.name));

  for (int c = 0; c < header1.num_channels; c++)
  {
    REQUIRE(header1.pixel_types[c] == header2.pixel_types[c]); // assume no conversion
    REQUIRE(0 == strcmp(header1.channels[c].name, header2.channels[c].name));
    REQUIRE(header1.channels[c].pixel_type == header2.pixel_types[c]);
    //REQUIRE(header1.channels[c].p_linear == header2.channels[c].p_linear);
    //REQUIRE(header1.channels[c].x_sampling == header2.channels[c].x_sampling);
    //REQUIRE(header1.channels[c].y_sampling == header2.channels[c].y_sampling);
  }
}

static void CompareImages(const EXRImage& image1, const EXRImage& image2)
{
  bool tiles_ok = image1.tiles && image2.tiles || image1.tiles == NULL && image2.tiles == NULL;
  REQUIRE(true == tiles_ok);
  bool images_ok = image1.images && image2.images || image1.images == NULL && image2.images == NULL;
  REQUIRE(true == images_ok);
  REQUIRE(image1.num_channels == image2.num_channels);
  
  const EXRImage* level_image1 = &image1;
  const EXRImage* level_image2 = &image2;
  while(level_image1 && level_image2)
  {
    REQUIRE(level_image1->level_x == level_image2->level_x);
    REQUIRE(level_image1->level_y == level_image2->level_y);
    REQUIRE(level_image1->width == level_image2->width);
    REQUIRE(level_image1->height == level_image2->height);
    REQUIRE(level_image1->num_tiles == level_image2->num_tiles);
    level_image1 = level_image1->next_level;
    level_image2 = level_image2->next_level;
    bool levels_ok = level_image1 && level_image2 || level_image1 == NULL && level_image2 == NULL;
    REQUIRE(true == levels_ok);
  }
}

TEST_CASE("asakusa", "[Load]") {
  EXRVersion exr_version;
  EXRImage exr_image;
  InitEXRImage(&exr_image);
  EXRHeader exr_header;
  InitEXRHeader(&exr_header);
  const char* err = NULL;
  int ret = ParseEXRVersionFromFile(&exr_version, "../../asakusa.exr");
  REQUIRE(TINYEXR_SUCCESS == ret);

  ret = ParseEXRHeaderFromFile(&exr_header, &exr_version, "../../asakusa.exr",
                               &err);
  REQUIRE(NULL == err);
  REQUIRE(TINYEXR_SUCCESS == ret);

  FreeEXRImage(&exr_image);
  FreeEXRHeader(&exr_header);
}

TEST_CASE("utf8filename", "[Load]") {
  EXRVersion exr_version;

  EXRHeader exr_header;
  InitEXRHeader(&exr_header);
  const char* err = NULL;

#ifdef _WIN32

#if defined(_MSC_VER)
  // Include UTF-16LE encoded string
  const wchar_t* wfilename =
#include "win32-filelist-utf16le.inc"
      ;

  // convert to char*
  // https://stackoverflow.com/questions/12637779/how-to-convert-const-wchar-to-const-char/12637971

  FILE* fp;
  errno_t errcode = _wfopen_s(&fp, wfilename, L"rb");

  REQUIRE(0 == errcode);

  char filename[1024];
  int charlen = 1000;

  int strlen = WideCharToMultiByte(65001 /* UTF8 */, 0, wfilename, -1, filename,
                                   (int)charlen, NULL, NULL);

  REQUIRE(strlen == 27);
#else
  // MinGW or clang.
  // At least clang cannot feed UTF-16LE source code, so provide UTF-8 encoded
  // file path
  const char* utf8filename =
#include "win32-filelist-utf8.inc"
      ;

  // to wchar_t
  const std::wstring wfilename = UTF8_to_wchar(utf8filename);

  FILE* fp;
  errno_t errcode = _wfopen_s(&fp, wfilename.c_str(), L"rb");

  REQUIRE(0 == errcode);

  char filename[1024];
  int charlen = 1000;

  // wchar_t to multibyte char
  int strlen = WideCharToMultiByte(65001 /* UTF8 */, 0, wfilename.c_str(), -1,
                                   filename, (int)charlen, NULL, NULL);

  REQUIRE(strlen == 27);

#endif

#else
  // Assume this source code is compiled with UTF-8(UNICODE)
  const char* filename = "./regression/日本語.exr";
#endif

  int ret = ParseEXRVersionFromFile(&exr_version, filename);
  REQUIRE(TINYEXR_SUCCESS == ret);

  ret = ParseEXRHeaderFromFile(&exr_header, &exr_version, filename, &err);
  REQUIRE(NULL == err);
  REQUIRE(TINYEXR_SUCCESS == ret);

  FreeEXRHeader(&exr_header);
}

TEST_CASE("ScanLines", "[Load]") {
  std::vector<std::string> inputs;
  inputs.push_back("ScanLines/Blobbies.exr");
  inputs.push_back("ScanLines/CandleGlass.exr");
  // inputs.push_back("ScanLines/Cannon.exr"); // Cannon.exr will fail since it
  // uses b44 compression which is not yet supported on TinyEXR.
  inputs.push_back("ScanLines/Desk.exr");
  inputs.push_back("ScanLines/MtTamWest.exr");
  inputs.push_back("ScanLines/PrismsLenses.exr");
  inputs.push_back("ScanLines/StillLife.exr");
  inputs.push_back("ScanLines/Tree.exr");

  for (size_t i = 0; i < inputs.size(); i++) {
    EXRVersion exr_version;
    std::string filepath = GetPath(inputs[i].c_str());
    std::cout << "Loading" << filepath << std::endl;
    int ret = ParseEXRVersionFromFile(&exr_version, filepath.c_str());
    REQUIRE(TINYEXR_SUCCESS == ret);
    REQUIRE(false == exr_version.tiled);
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

    ret = LoadEXRImageFromFile(&image, &header, filepath.c_str(), &err);
    REQUIRE(TINYEXR_SUCCESS == ret);

    FreeEXRHeader(&header);
    FreeEXRImage(&image);
  }
}

TEST_CASE("Chromaticities", "[Load]") {
  std::vector<std::string> inputs;
  inputs.push_back("Chromaticities/Rec709.exr");
  inputs.push_back("Chromaticities/Rec709_YC.exr");
  inputs.push_back("Chromaticities/XYZ.exr");
  inputs.push_back("Chromaticities/XYZ_YC.exr");

  for (size_t i = 0; i < inputs.size(); i++) {
    EXRVersion exr_version;
    std::string filepath = GetPath(inputs[i].c_str());
    std::cout << "Loading" << filepath << std::endl;
    int ret = ParseEXRVersionFromFile(&exr_version, filepath.c_str());
    REQUIRE(TINYEXR_SUCCESS == ret);
    REQUIRE(false == exr_version.tiled);
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

    ret = LoadEXRImageFromFile(&image, &header, filepath.c_str(), &err);
    REQUIRE(TINYEXR_SUCCESS == ret);

    FreeEXRHeader(&header);
    FreeEXRImage(&image);
  }
}

TEST_CASE("TestImages", "[Load]") {
  std::vector<std::string> inputs;
  inputs.push_back("TestImages/AllHalfValues.exr");
  inputs.push_back("TestImages/BrightRings.exr");
  inputs.push_back("TestImages/BrightRingsNanInf.exr");
  // inputs.push_back("TestImages/GammaChart.exr"); // disable since this uses
  // pxr24 compression
  // inputs.push_back("TestImages/GrayRampsDiagonal.exr"); // pxr24
  // inputs.push_back("TestImages/GrayRampsHorizontal.exr"); // pxr24
  // inputs.push_back("TestImages/RgbRampsDiagonal.exr"); // pxr24
  // inputs.push_back("TestImages/SquaresSwirls.exr"); // pxr24
  inputs.push_back("TestImages/WideColorGamut.exr");
  // inputs.push_back("TestImages/WideFloatRange.exr"); // pxr24

  for (size_t i = 0; i < inputs.size(); i++) {
    EXRVersion exr_version;
    std::string filepath = GetPath(inputs[i].c_str());
    std::cout << "Loading" << filepath << std::endl;
    int ret = ParseEXRVersionFromFile(&exr_version, filepath.c_str());
    REQUIRE(TINYEXR_SUCCESS == ret);
    REQUIRE(false == exr_version.tiled);
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

    ret = LoadEXRImageFromFile(&image, &header, filepath.c_str(), &err);
    REQUIRE(TINYEXR_SUCCESS == ret);

    FreeEXRHeader(&header);
    FreeEXRImage(&image);
  }
}

TEST_CASE("LuminanceChroma", "[Load]") {
  std::vector<std::string> inputs;
  // inputs.push_back("LuminanceChroma/CrissyField.exr"); // b44
  // inputs.push_back("LuminanceChroma/Flowers.exr"); // b44
  // inputs.push_back("LuminanceChroma/Garden.exr"); // tiled
  inputs.push_back("LuminanceChroma/MtTamNorth.exr");
  inputs.push_back("LuminanceChroma/StarField.exr");

  for (size_t i = 0; i < inputs.size(); i++) {
    EXRVersion exr_version;
    std::string filepath = GetPath(inputs[i].c_str());
    std::cout << "Loading" << filepath << std::endl;
    int ret = ParseEXRVersionFromFile(&exr_version, filepath.c_str());
    REQUIRE(TINYEXR_SUCCESS == ret);
    REQUIRE(false == exr_version.tiled);
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

    ret = LoadEXRImageFromFile(&image, &header, filepath.c_str(), &err);
    REQUIRE(TINYEXR_SUCCESS == ret);

    FreeEXRHeader(&header);
    FreeEXRImage(&image);
  }
}

TEST_CASE("DisplayWindow", "[Load]") {
  std::vector<std::string> inputs;
  inputs.push_back("DisplayWindow/t01.exr");
  inputs.push_back("DisplayWindow/t02.exr");
  inputs.push_back("DisplayWindow/t03.exr");
  inputs.push_back("DisplayWindow/t04.exr");
  inputs.push_back("DisplayWindow/t05.exr");
  inputs.push_back("DisplayWindow/t06.exr");
  inputs.push_back("DisplayWindow/t07.exr");
  inputs.push_back("DisplayWindow/t08.exr");
  inputs.push_back("DisplayWindow/t09.exr");
  inputs.push_back("DisplayWindow/t10.exr");
  inputs.push_back("DisplayWindow/t11.exr");
  inputs.push_back("DisplayWindow/t12.exr");
  inputs.push_back("DisplayWindow/t13.exr");
  inputs.push_back("DisplayWindow/t14.exr");
  inputs.push_back("DisplayWindow/t15.exr");
  inputs.push_back("DisplayWindow/t16.exr");

  for (size_t i = 0; i < inputs.size(); i++) {
    EXRVersion exr_version;
    std::string filepath = GetPath(inputs[i].c_str());
    std::cout << "Loading" << filepath << std::endl;
    int ret = ParseEXRVersionFromFile(&exr_version, filepath.c_str());
    REQUIRE(TINYEXR_SUCCESS == ret);
    REQUIRE(false == exr_version.tiled);
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

    ret = LoadEXRImageFromFile(&image, &header, filepath.c_str(), &err);
    REQUIRE(TINYEXR_SUCCESS == ret);

    FreeEXRHeader(&header);
    FreeEXRImage(&image);
  }
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
  REQUIRE(1 == header.tiled);
  REQUIRE(TINYEXR_TILE_ONE_LEVEL == header.tile_level_mode);
  REQUIRE(128 == header.tile_size_x);
  REQUIRE(128 == header.tile_size_y);
  
  ret = LoadEXRImageFromFile(&image, &header, filepath.c_str(), &err);
  REQUIRE(TINYEXR_SUCCESS == ret);
  REQUIRE(NULL != image.tiles);
  REQUIRE(0 == image.level_x);
  REQUIRE(0 == image.level_y);
  REQUIRE(1 == EXRNumLevels(&image));
  
  FreeEXRHeader(&header);
  FreeEXRImage(&image);
}

TEST_CASE("LuminanceChroma/Garden.exr|Load", "[Load]") {
  EXRVersion exr_version;
  std::string filepath = GetPath("LuminanceChroma/Garden.exr");
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

  ret = LoadEXRImageFromFile(&image, &header, filepath.c_str(), &err);
  REQUIRE(TINYEXR_SUCCESS == ret);

  FreeEXRHeader(&header);
  FreeEXRImage(&image);
}

TEST_CASE("Tiles/Ocean.exr", "[Load]") {
  EXRVersion exr_version;
  std::string filepath = GetPath("Tiles/Ocean.exr");
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

  ret = LoadEXRImageFromFile(&image, &header, filepath.c_str(), &err);
  REQUIRE(TINYEXR_SUCCESS == ret);

  FreeEXRHeader(&header);
  FreeEXRImage(&image);
}

TEST_CASE("MultiResolution/Bonita.exr", "[Load]") {
  EXRVersion exr_version;
  std::string filepath = GetPath("MultiResolution/Bonita.exr");
  std::cout << "Loading" << filepath << std::endl;
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
  REQUIRE(1 == header.tiled);
  REQUIRE(TINYEXR_TILE_MIPMAP_LEVELS == header.tile_level_mode);
  REQUIRE(TINYEXR_TILE_ROUND_DOWN == header.tile_rounding_mode);
  
  ret = LoadEXRImageFromFile(&image, &header, filepath.c_str(), &err);
  REQUIRE(TINYEXR_SUCCESS == ret);
  REQUIRE(10 == EXRNumLevels(&image));
  
  FreeEXRHeader(&header);
  FreeEXRImage(&image);
}

TEST_CASE("MultiResolution/Kapaa.exr", "[Load]") {
  EXRVersion exr_version;
  std::string filepath = GetPath("MultiResolution/Kapaa.exr");
  std::cout << "Loading" << filepath << std::endl;
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
  REQUIRE(1 == header.tiled);
  REQUIRE(TINYEXR_TILE_RIPMAP_LEVELS == header.tile_level_mode);
  REQUIRE(TINYEXR_TILE_ROUND_UP == header.tile_rounding_mode);
  REQUIRE(64 == header.tile_size_x);
  REQUIRE(64 == header.tile_size_y);
  
  ret = LoadEXRImageFromFile(&image, &header, filepath.c_str(), &err);
  REQUIRE(TINYEXR_SUCCESS == ret);
  REQUIRE(11*11 == EXRNumLevels(&image));
  
  FreeEXRHeader(&header);
  FreeEXRImage(&image);
}

TEST_CASE("Saving ScanLines", "[Save]") {
  std::vector<std::string> inputs;
  inputs.push_back("ScanLines/Blobbies.exr");
  inputs.push_back("ScanLines/CandleGlass.exr");
  // inputs.push_back("ScanLines/Cannon.exr"); // Cannon.exr will fail since it
  // uses b44 compression which is not yet supported on TinyEXR.
  inputs.push_back("ScanLines/Desk.exr");
  inputs.push_back("ScanLines/MtTamWest.exr");
  inputs.push_back("ScanLines/PrismsLenses.exr");
  inputs.push_back("ScanLines/StillLife.exr");
  inputs.push_back("ScanLines/Tree.exr");

  for (size_t i = 0; i < inputs.size(); i++) {
    std::string filepath = GetPath(inputs[i].c_str());
    std::cout << "Input:" << filepath << std::endl;
  
    EXRVersion version1;
    int ret = ParseEXRVersionFromFile(&version1, filepath.c_str());
    REQUIRE(TINYEXR_SUCCESS == ret);

    EXRHeader header1;
    EXRImage image1;
    unsigned char *data = NULL;
    size_t data_size;
    // loading from file
    {
      InitEXRHeader(&header1);
      InitEXRImage(&image1);

      const char* err;
      ret = ParseEXRHeaderFromFile(&header1, &version1, filepath.c_str(), &err);
      REQUIRE(TINYEXR_SUCCESS == ret);

      ret = LoadEXRImageFromFile(&image1, &header1, filepath.c_str(), &err);
      REQUIRE(TINYEXR_SUCCESS == ret);
    }
    // saving to memory
    {
      const char* err = NULL;
      data_size = SaveEXRImageToMemory(&image1, &header1, &data, &err);
      REQUIRE(0 != data_size);
      //FreeEXRHeader(&header);
#ifdef DUMP_IMAGES
      bool ret = WriteMemoryToFile(GetDumpPath(inputs[i].c_str()).c_str(), data, data_size);
      REQUIRE(true == ret);
#endif
    }
    // loading back from memory
    {
      EXRVersion version2;
      {
        int ret = ParseEXRVersionFromMemory(&version2, data, data_size);
        REQUIRE(0 == ret);
      }
      EXRHeader header2;
      {
        const char* err = NULL;
        InitEXRHeader(&header2);
        int ret = ParseEXRHeaderFromMemory(&header2, &version2, data, data_size, &err);
        REQUIRE(0 == ret);
      }
      EXRImage image2;
      {
        const char* err = NULL;
        InitEXRImage(&image2);
        int ret = LoadEXRImageFromMemory(&image2, &header2, data, data_size, &err);
        REQUIRE(TINYEXR_SUCCESS == ret);
        free(data);
      }
    
      CompareHeaders(header1, header2);
      CompareImages(image1, image2);
    
      FreeEXRImage(&image2);
      FreeEXRHeader(&header2);
    }
  
    FreeEXRHeader(&header1);
    FreeEXRImage(&image1);
  }
}

TEST_CASE("Saving MultiResolution", "[Save]") {
  //std::string filepath = GetPath("MultiResolution/Bonita.exr");
  //std::cout << "Load-save-reload:" << filepath << std::endl;
  
  std::vector<std::string> inputs;
  inputs.push_back("MultiResolution/Bonita.exr");
  inputs.push_back("MultiResolution/Kapaa.exr");

  for (size_t i = 0; i < inputs.size(); i++) {
    std::string filepath = GetPath(inputs[i].c_str());
    std::cout << "Input:" << filepath << std::endl;
  
    EXRVersion version1;
    int ret = ParseEXRVersionFromFile(&version1, filepath.c_str());
    REQUIRE(TINYEXR_SUCCESS == ret);

    EXRHeader header1;
    EXRImage image1;
    unsigned char *data = NULL;
    size_t data_size;
    // loading from file
    {
      InitEXRHeader(&header1);
      InitEXRImage(&image1);

      const char* err;
      ret = ParseEXRHeaderFromFile(&header1, &version1, filepath.c_str(), &err);
      REQUIRE(TINYEXR_SUCCESS == ret);

      ret = LoadEXRImageFromFile(&image1, &header1, filepath.c_str(), &err);
      REQUIRE(TINYEXR_SUCCESS == ret);
    }
    // saving to memory
    {
      const char* err = NULL;
      data_size = SaveEXRImageToMemory(&image1, &header1, &data, &err);
      REQUIRE(0 != data_size);
#ifdef DUMP_IMAGES
      bool ret = WriteMemoryToFile(GetDumpPath(inputs[i].c_str()).c_str(), data, data_size);
      REQUIRE(true == ret);
#endif
    }
    // loading back from memory
    {
      EXRVersion version2;
      {
        int ret = ParseEXRVersionFromMemory(&version2, data, data_size);
        REQUIRE(0 == ret);
      }
      EXRHeader header2;
      {
        const char* err = NULL;
        InitEXRHeader(&header2);
        int ret = ParseEXRHeaderFromMemory(&header2, &version2, data, data_size, &err);
        REQUIRE(0 == ret);
      }
      EXRImage image2;
      {
        const char* err = NULL;
        InitEXRImage(&image2);
        int ret = LoadEXRImageFromMemory(&image2, &header2, data, data_size, &err);
        REQUIRE(TINYEXR_SUCCESS == ret);
        free(data);
      }
    
      CompareHeaders(header1, header2);
      CompareImages(image1, image2);
    
      FreeEXRImage(&image2);
      FreeEXRHeader(&header2);
    } 
    FreeEXRHeader(&header1);
    FreeEXRImage(&image1);
  }
}

TEST_CASE("Saving multipart", "[Save]") {
  
  std::vector<std::string> inputs;
  inputs.push_back("Beachball/multipart.0001.exr");

  for (size_t i = 0; i < inputs.size(); i++) {
    std::string filepath = GetPath(inputs[i].c_str());
    std::cout << "Input:" << filepath << std::endl;
  
    EXRVersion version1;
    {
      int ret = ParseEXRVersionFromFile(&version1, filepath.c_str());
      REQUIRE(TINYEXR_SUCCESS == ret);
      REQUIRE(true == version1.multipart);
    }
  
    EXRHeader** headers1;  // list of EXRHeader pointers.
    int num_headers1;
    {
      const char* err = NULL;
      int ret = ParseEXRMultipartHeaderFromFile(&headers1, &num_headers1,
                        &version1, filepath.c_str(), &err);
      REQUIRE(TINYEXR_SUCCESS == ret);
    }
  
    unsigned char *data = NULL;
    size_t data_size;
  
    std::vector<EXRImage> images1(num_headers1);
    // loading from file
    {
      const char* err = NULL;
      for (int j = 0; j < num_headers1; j++) {
        InitEXRImage(&images1[j]);
      }
      int ret = LoadEXRMultipartImageFromFile(&images1[0], const_cast<const EXRHeader**>(headers1),
      static_cast<unsigned int>(num_headers1), filepath.c_str(), &err);
      REQUIRE(TINYEXR_SUCCESS == ret);
    }
    // saving to memory
    {
      const char* err = NULL;
      data_size = SaveEXRMultipartImageToMemory(&images1[0],
        const_cast<const EXRHeader**>(headers1), static_cast<unsigned int>(num_headers1), &data, &err);
      REQUIRE(0 != data_size);
  #ifdef DUMP_IMAGES
      bool ret = WriteMemoryToFile(GetDumpPath(inputs[i].c_str()).c_str(), data, data_size);
      REQUIRE(true == ret);
  #endif
    }
    // loading back from memory
    {
      EXRVersion version2;
      {
        int ret = ParseEXRVersionFromMemory(&version2, data, data_size);
        REQUIRE(TINYEXR_SUCCESS == ret);
        REQUIRE(true == version2.multipart);
      }
      EXRHeader** headers2;
      int num_headers2;
      {
        const char* err = NULL;
        int ret = ParseEXRMultipartHeaderFromMemory(&headers2, &num_headers2, &version2,
                                               data, data_size, &err);
              REQUIRE(TINYEXR_SUCCESS == ret);
                           
      }
      REQUIRE(num_headers1 == num_headers2);
    
      std::vector<EXRImage> images2(num_headers2);
      {
        for (int j = 0; j < num_headers2; j++) {
          InitEXRImage(&images2[j]);
        }
        const char* err = NULL;
        int ret = LoadEXRMultipartImageFromMemory(&images2[0], const_cast<const EXRHeader**>(headers2),
                              static_cast<unsigned int>(num_headers2),
                               data, data_size, &err);
        REQUIRE(TINYEXR_SUCCESS == ret);
        free(data);
      }
    
      for (int j = 0; j < num_headers2; j++) {
        CompareHeaders(*headers1[j], *headers2[j]);
      }
      for (int j = 0; j < num_headers2; j++) {
        CompareImages(images1[j], images2[j]);
      }
        
      for (int j = 0; j < num_headers2; j++) {
        FreeEXRImage(&images2[j]);
        FreeEXRHeader(headers2[j]);
        free(headers2[j]);
      }
      free(headers2);
    }
  
    for (int j = 0; j < num_headers1; j++) {
      FreeEXRImage(&images1[j]);
      FreeEXRHeader(headers1[j]);
      free(headers1[j]);
    }
    free(headers1);
  }
}

TEST_CASE("Saving multipart|Combine", "[Save]") {

  std::vector<std::string> inputs;
  inputs.push_back("MultiResolution/Kapaa.exr"); // tiled, ripmap
  inputs.push_back("Tiles/GoldenGate.exr"); // tiled, one level
  inputs.push_back("ScanLines/Desk.exr"); // scanline
  inputs.push_back("MultiResolution/PeriodicPattern.exr"); // tiled, mipmap

  const char* dstName = "multipart.collection.exr";

  unsigned num_headers1 = inputs.size();
  std::vector<EXRHeader> headers1(num_headers1);
  std::vector<EXRImage> images1(num_headers1);
  // collecting images
  for (size_t i = 0; i < num_headers1; i++) {
    std::string filepath = GetPath(inputs[i].c_str());
    std::cout << "Input:" << filepath << std::endl;

    EXRVersion version1;
    {
      int ret = ParseEXRVersionFromFile(&version1, filepath.c_str());
      REQUIRE(TINYEXR_SUCCESS == ret);
      REQUIRE(false == version1.multipart);
    }
    {
      InitEXRHeader(&headers1[i]);
      const char* err = NULL;
      int ret = ParseEXRHeaderFromFile(&headers1[i], &version1, filepath.c_str(), &err);
      REQUIRE(TINYEXR_SUCCESS == ret);
    }
    {
      InitEXRImage(&images1[i]);
      const char* err = NULL;
      int ret = LoadEXRImageFromFile(&images1[i], &headers1[i], filepath.c_str(), &err);
      REQUIRE(TINYEXR_SUCCESS == ret);
    }
  }

  unsigned char *data = NULL;
  size_t data_size;
  // saving collection to memory as multipart
  {
    std::vector<EXRHeader*> pheaders1(num_headers1);
    for(unsigned i = 0; i < num_headers1; ++i) pheaders1[i] = &headers1[i];
    for (size_t i = 0; i < num_headers1; i++) {
      EXRSetNameAttr(pheaders1[i], inputs[i].c_str());
    }
    const char* err = NULL;
    data_size = SaveEXRMultipartImageToMemory(&images1[0],
                                              const_cast<const EXRHeader**>(&pheaders1[0]),
                                              static_cast<unsigned int>(num_headers1),
                                              &data, &err);
    REQUIRE(0 != data_size);
#ifdef DUMP_IMAGES
    bool ret = WriteMemoryToFile(GetDumpPath(dstName).c_str(), data, data_size);
    REQUIRE(true == ret);
#endif
  }
  // loading back from memory
  {
    EXRVersion version2;
    {
      int ret = ParseEXRVersionFromMemory(&version2, data, data_size);
      REQUIRE(TINYEXR_SUCCESS == ret);
      REQUIRE(true == version2.multipart);
    }
    EXRHeader** headers2;
    int num_headers2;
    {
      const char* err = NULL;
      int ret = ParseEXRMultipartHeaderFromMemory(&headers2, &num_headers2, &version2,
                                                  data, data_size, &err);
      REQUIRE(TINYEXR_SUCCESS == ret);

    }
    REQUIRE(num_headers1 == num_headers2);

    std::vector<EXRImage> images2(num_headers2);
    {
      for (int j = 0; j < num_headers2; j++) {
        InitEXRImage(&images2[j]);
      }
      const char* err = NULL;
      int ret = LoadEXRMultipartImageFromMemory(&images2[0], const_cast<const EXRHeader**>(headers2),
                                                static_cast<unsigned int>(num_headers2),
                                                data, data_size, &err);
      REQUIRE(TINYEXR_SUCCESS == ret);
      free(data);
    }

    for (int j = 0; j < num_headers2; j++) {
      CompareHeaders(headers1[j], *headers2[j]);
    }
    for (int j = 0; j < num_headers2; j++) {
      CompareImages(images1[j], images2[j]);
    }

    for (int j = 0; j < num_headers2; j++) {
      FreeEXRImage(&images2[j]);
      FreeEXRHeader(headers2[j]);
      free(headers2[j]);
    }
    free(headers2);
  }

  for (int i = 0; i < num_headers1; i++) {
    FreeEXRImage(&images1[i]);
    FreeEXRHeader(&headers1[i]);
  }
}

#if 0  // Spirals.exr uses pxr24 compression
TEST_CASE("Tiles/Spirals.exr", "[Load]") {
  EXRVersion exr_version;
  std::string filepath = GetPath("Tiles/Spirals.exr");
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
#endif

TEST_CASE("Beachball/multipart.0001.exr", "[Version]") {
  EXRVersion exr_version;
  std::string filepath = GetPath("Beachball/multipart.0001.exr");
  int ret = ParseEXRVersionFromFile(&exr_version, filepath.c_str());
  REQUIRE(TINYEXR_SUCCESS == ret);
  REQUIRE(true == exr_version.multipart);

  EXRHeader* headers;
}

TEST_CASE("Beachball/multipart.0001.exr|Load", "[Load]") {
  EXRVersion exr_version;
  std::string filepath = GetPath("Beachball/multipart.0001.exr");
  int ret = ParseEXRVersionFromFile(&exr_version, filepath.c_str());
  REQUIRE(TINYEXR_SUCCESS == ret);
  REQUIRE(true == exr_version.multipart);

  EXRHeader** exr_headers;  // list of EXRHeader pointers.
  int num_exr_headers;
  const char* err;

  ret = ParseEXRMultipartHeaderFromFile(&exr_headers, &num_exr_headers,
                                        &exr_version, filepath.c_str(), &err);
  REQUIRE(TINYEXR_SUCCESS == ret);

  REQUIRE(10 == num_exr_headers);

  std::vector<EXRImage> images(static_cast<size_t>(num_exr_headers));
  for (int i = 0; i < num_exr_headers; i++) {
    InitEXRImage(&images[static_cast<size_t>(i)]);
  }

  ret = LoadEXRMultipartImageFromFile(
      &images.at(0), const_cast<const EXRHeader**>(exr_headers),
      static_cast<unsigned int>(num_exr_headers), filepath.c_str(), &err);
  REQUIRE(TINYEXR_SUCCESS == ret);

  for (int i = 0; i < num_exr_headers; i++) {
    FreeEXRImage(&images.at(static_cast<size_t>(i)));
  }

  for (int i = 0; i < num_exr_headers; i++) {
    FreeEXRHeader(exr_headers[static_cast<size_t>(i)]);  // free content
    free(exr_headers[static_cast<size_t>(i)]);           // free pointer
  }
  free(exr_headers);
}

TEST_CASE("Beachbal multiparts", "[Load]") {
  int num = 8;
  char buf[1024];
  for (int i = 0; i < num + 1; i++) {
    sprintf(buf, "Beachball/multipart.%04d.exr", i);
    EXRVersion exr_version;
    std::string filepath = GetPath(buf);
    int ret = ParseEXRVersionFromFile(&exr_version, filepath.c_str());

    if (i == 0) {  // multipart.0000.exr does not exist.
      REQUIRE(TINYEXR_ERROR_CANT_OPEN_FILE == ret);
      continue;
    }

    REQUIRE(TINYEXR_SUCCESS == ret);
    REQUIRE(true == exr_version.multipart);

    EXRHeader** exr_headers;  // list of EXRHeader pointers.
    int num_exr_headers;
    const char* err;

    ret = ParseEXRMultipartHeaderFromFile(&exr_headers, &num_exr_headers,
                                          &exr_version, filepath.c_str(), &err);
    REQUIRE(TINYEXR_SUCCESS == ret);

    REQUIRE(10 == num_exr_headers);

    std::vector<EXRImage> images(static_cast<size_t>(num_exr_headers));
    for (int j = 0; j < num_exr_headers; j++) {
      InitEXRImage(&images[static_cast<size_t>(j)]);
    }

    ret = LoadEXRMultipartImageFromFile(
        &images.at(0), const_cast<const EXRHeader**>(exr_headers),
        static_cast<unsigned int>(num_exr_headers), filepath.c_str(), &err);
    REQUIRE(TINYEXR_SUCCESS == ret);

    for (int j = 0; j < num_exr_headers; j++) {
      FreeEXRImage(&images.at(static_cast<size_t>(j)));
    }

    for (int j = 0; j < num_exr_headers; j++) {
      FreeEXRHeader(exr_headers[static_cast<size_t>(j)]);
      free(exr_headers[static_cast<size_t>(j)]);
    }
    free(exr_headers);
  }
}

TEST_CASE("Beachbal singleparts", "[Load]") {
  int num = 8;
  char buf[1024];
  for (int i = 0; i < num + 1; i++) {
    sprintf(buf, "Beachball/singlepart.%04d.exr", i);
    EXRVersion exr_version;
    std::string filepath = GetPath(buf);
    int ret = ParseEXRVersionFromFile(&exr_version, filepath.c_str());

    if (i == 0) {  // multipart.0000.exr does not exist.
      REQUIRE(TINYEXR_ERROR_CANT_OPEN_FILE == ret);
      continue;
    }

    REQUIRE(TINYEXR_SUCCESS == ret);
    REQUIRE(false == exr_version.tiled);
    REQUIRE(false == exr_version.non_image);
    REQUIRE(false == exr_version.multipart);

    EXRVersion version;
    memset(&version, 0, sizeof(EXRVersion));
    EXRHeader header;
    EXRImage image;
    InitEXRHeader(&header);
    InitEXRImage(&image);

    const char* err;
    ret = ParseEXRHeaderFromFile(&header, &exr_version, filepath.c_str(), &err);
    REQUIRE(TINYEXR_SUCCESS == ret);

    ret = LoadEXRImageFromFile(&image, &header, filepath.c_str(), &err);
    REQUIRE(TINYEXR_SUCCESS == ret);

    REQUIRE(image.tiles == NULL);
    REQUIRE(image.images);

    FreeEXRHeader(&header);
    FreeEXRImage(&image);
  }
}

TEST_CASE("ParseEXRVersionFromMemory invalid input", "[Parse]") {
  int ret = ParseEXRVersionFromMemory(NULL, NULL, 0);
  REQUIRE(ret == TINYEXR_ERROR_INVALID_ARGUMENT);

  {
    EXRVersion version;
    memset(&version, 0, sizeof(EXRVersion));
    ret = ParseEXRVersionFromMemory(&version, NULL, 0);
    REQUIRE(ret == TINYEXR_ERROR_INVALID_ARGUMENT);
  }

  {
    EXRVersion version;
    memset(&version, 0, sizeof(EXRVersion));
    std::vector<unsigned char> buf(128);
    ret = ParseEXRVersionFromMemory(&version, buf.data(), 0);
    REQUIRE(ret == TINYEXR_ERROR_INVALID_DATA);
  }

  {
    EXRVersion version;
    memset(&version, 0, sizeof(EXRVersion));
    std::vector<unsigned char> buf(4);
    ret = ParseEXRVersionFromMemory(
        &version, buf.data(), 1);  // size is less than version header size
    REQUIRE(ret == TINYEXR_ERROR_INVALID_DATA);
  }

  {
    EXRVersion version;
    memset(&version, 0, sizeof(EXRVersion));
    std::vector<unsigned char> buf(8, 0);  // invalid magic number
    ret = ParseEXRVersionFromMemory(&version, buf.data(), 8);
    REQUIRE(ret == TINYEXR_ERROR_INVALID_MAGIC_NUMBER);
  }
}

TEST_CASE("ParseEXRHeaderFromMemory invalid input", "[Parse]") {
  {
    int ret = ParseEXRHeaderFromMemory(NULL, NULL, NULL, 0, NULL);
    REQUIRE(ret == TINYEXR_ERROR_INVALID_ARGUMENT);
  }

  {
    EXRHeader header;
    InitEXRHeader(&header);
    EXRVersion version;
    memset(&version, 0, sizeof(EXRVersion));

    int ret = ParseEXRHeaderFromMemory(&header, &version, NULL, 0, NULL);
    REQUIRE(ret == TINYEXR_ERROR_INVALID_ARGUMENT);
    FreeEXRHeader(&header);
  }

  {
    EXRHeader header;
    InitEXRHeader(&header);
    EXRVersion version;
    memset(&version, 0, sizeof(EXRVersion));
    std::vector<unsigned char> buf(128);

    int ret = ParseEXRHeaderFromMemory(&header, &version, buf.data(), 0, NULL);
    REQUIRE(ret == TINYEXR_ERROR_INVALID_DATA);
    FreeEXRHeader(&header);
  }

  {
    EXRHeader header;
    InitEXRHeader(&header);
    EXRVersion version;
    memset(&version, 0, sizeof(EXRVersion));
    std::vector<unsigned char> buf(128, 0);

    int ret =
        ParseEXRHeaderFromMemory(&header, &version, buf.data(), 128, NULL);
    REQUIRE(ret == TINYEXR_ERROR_INVALID_HEADER);
    FreeEXRHeader(&header);
  }
}

TEST_CASE("Compressed is smaller than uncompressed", "[Issue40]") {
  EXRHeader header;
  InitEXRHeader(&header);

  header.compression_type = TINYEXR_COMPRESSIONTYPE_ZIP;

  EXRImage image;
  InitEXRImage(&image);

  image.num_channels = 3;

  float const images[3][1] = {
      {1.0f},
      {0.0f},
      {0.0f},
  };

  float const* const image_ptr[3] = {
      images[2],
      images[1],
      images[0],
  };

  image.images = const_cast<unsigned char**>(reinterpret_cast<const unsigned char*const *>(image_ptr));
  image.width = 1;
  image.height = 1;

  header.num_channels = 3;
  header.channels =
      static_cast<EXRChannelInfo*>(malloc(sizeof(EXRChannelInfo) * static_cast<size_t>(header.num_channels)));
  // Must be BGR(A) order, since most of EXR viewers expect this channel order.
  strncpy(header.channels[0].name, "B", 255);
  header.channels[0].name[strlen("B")] = '\0';
  strncpy(header.channels[1].name, "G", 255);
  header.channels[1].name[strlen("G")] = '\0';
  strncpy(header.channels[2].name, "R", 255);
  header.channels[2].name[strlen("R")] = '\0';

  header.pixel_types = static_cast<int*>(malloc(sizeof(int) * static_cast<size_t>(header.num_channels)));
  header.requested_pixel_types =
      static_cast<int*>(malloc(sizeof(int) * static_cast<size_t>(header.num_channels)));
  for (int i = 0; i < header.num_channels; i++) {
    header.pixel_types[i] =
        TINYEXR_PIXELTYPE_FLOAT;  // pixel type of input image
    header.requested_pixel_types[i] =
        TINYEXR_PIXELTYPE_FLOAT;  // pixel type of output image to be stored in
                                  // .EXR
  }

  const char* err;
  int const ret = SaveEXRImageToFile(&image, &header, "issue40.exr", &err);
  REQUIRE(ret == TINYEXR_SUCCESS);

  free(header.channels);
  free(header.requested_pixel_types);
  free(header.pixel_types);
}

// TEST_CASE("Regression: Issue54", "[fuzzing]") {
//  EXRVersion exr_version;
//  std::string filepath =
//  "./regression/poc-360c3b0555cb979ca108f2d178cf8a80959cfeabaa4ec1d310d062fa653a8c6b_min";
//  int ret = ParseEXRVersionFromFile(&exr_version, filepath.c_str());
//  REQUIRE(TINYEXR_SUCCESS == ret);
//  REQUIRE(false == exr_version.tiled);
//  REQUIRE(false == exr_version.non_image);
//  REQUIRE(false == exr_version.multipart);
//
//  EXRVersion version;
//  EXRHeader header;
//  EXRImage image;
//  InitEXRHeader(&header);
//  InitEXRImage(&image);
//
//  const char* err;
//  ret = ParseEXRHeaderFromFile(&header, &exr_version, filepath.c_str(), &err);
//  REQUIRE(TINYEXR_SUCCESS == ret);
//
//  ret = LoadEXRImageFromFile(&image, &header, filepath.c_str(), &err);
//  REQUIRE(TINYEXR_SUCCESS == ret);
//
//  FreeEXRHeader(&header);
//  FreeEXRImage(&image);
//}

TEST_CASE("Regression: Issue50", "[fuzzing]") {
  EXRVersion exr_version;
  std::string filepath =
      "./regression/"
      "poc-eedff3a9e99eb1c0fd3a3b0989e7c44c0a69f04f10b23e5264f362a4773f4397_"
      "min";
  int ret = ParseEXRVersionFromFile(&exr_version, filepath.c_str());
  REQUIRE(TINYEXR_SUCCESS == ret);
  REQUIRE(false == exr_version.tiled);
  REQUIRE(false == exr_version.non_image);
  REQUIRE(false == exr_version.multipart);

  EXRVersion version;
  EXRHeader header;
  EXRImage image;
  InitEXRHeader(&header);
  InitEXRImage(&image);

  const char* err = nullptr;
  ret = ParseEXRHeaderFromFile(&header, &exr_version, filepath.c_str(), &err);
  REQUIRE(TINYEXR_SUCCESS == false);
  if (ret) {
    FreeEXRErrorMessage(err);
  }

  FreeEXRHeader(&header);
  // FreeEXRImage(&image);
}

TEST_CASE("Regression: Issue57", "[fuzzing]") {
  EXRVersion exr_version;
  std::string filepath =
      "./regression/"
      "poc-df76d1f27adb8927a1446a603028272140905c168a336128465a1162ec7af270."
      "mini";
  int ret = ParseEXRVersionFromFile(&exr_version, filepath.c_str());
  REQUIRE(TINYEXR_SUCCESS == ret);
  REQUIRE(false == exr_version.tiled);
  REQUIRE(false == exr_version.non_image);
  REQUIRE(false == exr_version.multipart);

  EXRVersion version;
  EXRHeader header;
  EXRImage image;
  InitEXRHeader(&header);
  InitEXRImage(&image);

  const char* err = nullptr;
  ret = ParseEXRHeaderFromFile(&header, &exr_version, filepath.c_str(), &err);
  REQUIRE(TINYEXR_SUCCESS == false);
  if (err) {
    FreeEXRErrorMessage(err);
  }

  FreeEXRHeader(&header);
  // FreeEXRImage(&image);
}

TEST_CASE("Regression: Issue56", "[fuzzing]") {
  EXRVersion exr_version;
  std::string filepath =
      "./regression/"
      "poc-1383755b301e5f505b2198dc0508918b537fdf48bbfc6deeffe268822e6f6cd6";
  int ret = ParseEXRVersionFromFile(&exr_version, filepath.c_str());
  REQUIRE(TINYEXR_SUCCESS == ret);
  REQUIRE(false == exr_version.tiled);
  REQUIRE(false == exr_version.non_image);
  REQUIRE(false == exr_version.multipart);

  EXRVersion version;
  EXRHeader header;
  EXRImage image;
  InitEXRHeader(&header);
  InitEXRImage(&image);

  const char* err = nullptr;
  ret = ParseEXRHeaderFromFile(&header, &exr_version, filepath.c_str(), &err);
  REQUIRE(TINYEXR_SUCCESS == false);
  if (err) {
    FreeEXRErrorMessage(err);
  }

  FreeEXRHeader(&header);
  // FreeEXRImage(&image);
}

TEST_CASE("Regression: Issue61", "[fuzzing]") {
  EXRVersion exr_version;
  std::string filepath =
      "./regression/"
      "poc-3f1f642c3356fd8e8d2a0787613ec09a56572b3a1e38c9629b6db9e8dead1117_"
      "min";
  int ret = ParseEXRVersionFromFile(&exr_version, filepath.c_str());
  REQUIRE(TINYEXR_SUCCESS == ret);
  REQUIRE(false == exr_version.tiled);
  REQUIRE(false == exr_version.non_image);
  REQUIRE(false == exr_version.multipart);

  EXRVersion version;
  EXRHeader header;
  EXRImage image;
  InitEXRHeader(&header);
  InitEXRImage(&image);

  const char* err = nullptr;
  ret = ParseEXRHeaderFromFile(&header, &exr_version, filepath.c_str(), &err);
  REQUIRE(TINYEXR_SUCCESS == false);
  if (err) {
    FreeEXRErrorMessage(err);
  }

  FreeEXRHeader(&header);
  // FreeEXRImage(&image);
}

TEST_CASE("Regression: Issue60", "[fuzzing]") {
  EXRVersion exr_version;
  std::string filepath =
      "./regression/"
      "poc-5b66774a7498c635334ad386be0c3b359951738ac47f14878a3346d1c6ea0fe5_"
      "min";
  int ret = ParseEXRVersionFromFile(&exr_version, filepath.c_str());
  REQUIRE(TINYEXR_SUCCESS == ret);
  REQUIRE(false == exr_version.tiled);
  REQUIRE(false == exr_version.non_image);
  REQUIRE(false == exr_version.multipart);

  EXRVersion version;
  EXRHeader header;
  EXRImage image;
  InitEXRHeader(&header);
  InitEXRImage(&image);

  const char* err = nullptr;
  ret = ParseEXRHeaderFromFile(&header, &exr_version, filepath.c_str(), &err);
  REQUIRE(TINYEXR_SUCCESS == false);
  if (err) {
    FreeEXRErrorMessage(err);
  }

  FreeEXRHeader(&header);
  // FreeEXRImage(&image);
}

TEST_CASE("Regression: Issue71", "[issue71]") {
  std::string filepath = "./regression/2by2.exr";

  const char* err;
  int width, height;
  float* image;
  int ret = LoadEXR(&image, &width, &height, filepath.c_str(), &err);
  REQUIRE(TINYEXR_SUCCESS == ret);
  REQUIRE(2 == width);
  REQUIRE(2 == height);

  REQUIRE(0.0f == Approx(image[8]));
  REQUIRE(0.447021f == Approx(image[9]));
  REQUIRE(1.0f == Approx(image[10]));
  REQUIRE(0.250977f == Approx(image[11]));
  REQUIRE(0.0f == Approx(image[12]));
  REQUIRE(0.0f == Approx(image[13]));
  REQUIRE(0.0f == Approx(image[14]));
  REQUIRE(1.0f == Approx(image[15]));

  free(image);
}

// LoadEXRLoadFromMemory fails to load tiled image.
TEST_CASE("Regression: Issue93", "[issue93]") {
  std::string filepath = GetPath("Tiles/GoldenGate.exr");

  std::ifstream f(filepath.c_str(), std::ifstream::binary);
  REQUIRE(f.good());

  f.seekg(0, f.end);
  size_t sz = static_cast<size_t>(f.tellg());
  f.seekg(0, f.beg);

  REQUIRE(sz > 16);

  std::vector<unsigned char> data;

  data.resize(sz);
  f.read(reinterpret_cast<char*>(&data.at(0)),
         static_cast<std::streamsize>(sz));
  f.close();

  const char* err;
  int width, height;
  float* image;
  int ret = LoadEXRFromMemory(&image, &width, &height, data.data(), data.size(),
                              &err);
  REQUIRE(TINYEXR_SUCCESS == ret);

  std::cout << "val = " << image[0] << ", " << image[1] << ", " << image[2]
            << ", " << image[3] << std::endl;

  REQUIRE(0.0612183 == Approx(image[0]));
  REQUIRE(0.0892334 == Approx(image[1]));
  REQUIRE(0.271973 == Approx(image[2]));

  free(image);
}

// PIZ decompress bug(issue 100)
TEST_CASE("Regression: Issue100", "[issue100]") {
  std::string filepath = "./regression/piz-bug-issue-100.exr";

  std::ifstream f(filepath.c_str(), std::ifstream::binary);
  REQUIRE(f.good());

  f.seekg(0, f.end);
  size_t sz = static_cast<size_t>(f.tellg());
  f.seekg(0, f.beg);

  REQUIRE(sz > 16);

  std::vector<unsigned char> data;

  data.resize(sz);
  f.read(reinterpret_cast<char*>(&data.at(0)),
         static_cast<std::streamsize>(sz));
  f.close();

  const char* err = nullptr;
  int width, height;
  float* image;
  int ret = LoadEXRFromMemory(&image, &width, &height, data.data(), data.size(),
                              &err);
  if (err) {
    std::cerr << "issue100 err " << err << std::endl;
    FreeEXRErrorMessage(err);
  }
  REQUIRE(TINYEXR_SUCCESS == ret);
  REQUIRE(35 == width);
  REQUIRE(1 == height);

  // pixel should be white.

  std::cout << "pixel[0] = " << image[0] << ", " << image[1] << ", " << image[2]
            << ", " << image[3] << std::endl;
  std::cout << "pixel[34] = " << image[4 * 34 + 0] << ", " << image[4 * 34 + 1]
            << ", " << image[4 * 34 + 2] << ", " << image[4 * 34 + 3]
            << std::endl;

  REQUIRE(0.0 == Approx(image[0]));
  REQUIRE(0.0 == Approx(image[1]));
  REQUIRE(0.0 == Approx(image[2]));
  REQUIRE(0.0 == Approx(image[3]));

  REQUIRE(1.0 == Approx(image[4 * 34 + 0]));
  REQUIRE(1.0 == Approx(image[4 * 34 + 1]));
  REQUIRE(1.0 == Approx(image[4 * 34 + 2]));
  REQUIRE(1.0 == Approx(image[4 * 34 + 3]));

  free(image);
}

TEST_CASE("Regression: Issue53|Channels", "[issue53]") {
  EXRVersion exr_version;
  std::string filepath = "./regression/flaga.exr";
  int ret = ParseEXRVersionFromFile(&exr_version, filepath.c_str());
  REQUIRE(TINYEXR_SUCCESS == ret);

  EXRHeader header;
  EXRImage image;
  InitEXRHeader(&header);

  const char* err = nullptr;
  ret = ParseEXRHeaderFromFile(&header, &exr_version, filepath.c_str(), &err);
  REQUIRE(TINYEXR_SUCCESS == ret);

  std::vector<std::string> layer_names;
  tinyexr::GetLayers(header, layer_names);

  REQUIRE(2 == layer_names.size());

  std::vector<tinyexr::LayerChannel> channels;
  tinyexr::ChannelsInLayer(header, "", channels);
  REQUIRE(8 == channels.size());

  channels.clear();
  tinyexr::ChannelsInLayer(header, "Warstwa 3", channels);
  REQUIRE(0 == channels.size());

  channels.clear();
  tinyexr::ChannelsInLayer(header, "Warstwa 1", channels);
  REQUIRE(4 == channels.size());

  FreeEXRHeader(&header);

  if (err) {
    FreeEXRErrorMessage(err);
  }
}

TEST_CASE("Regression: Issue53|Image", "[issue53]") {
  std::string filepath = "./regression/flaga.exr";

  const char* err = nullptr;
  const char** layer_names = nullptr;
  int num_layers = 0;
  int ret = EXRLayers(filepath.c_str(), &layer_names, &num_layers, &err);
  REQUIRE(TINYEXR_SUCCESS == ret);
  REQUIRE(2 == num_layers);
  for (int i = 0; i < num_layers; i++) {
    free(reinterpret_cast<void*>(const_cast<char*>(layer_names[i])));
  }
  free(layer_names);

  int width, height;
  float* image;
  ret = LoadEXRWithLayer(&image, &width, &height, filepath.c_str(), NULL, &err);
  REQUIRE(TINYEXR_SUCCESS == ret);
  free(image);
  if (err) {
    FreeEXRErrorMessage(err);
  }

  ret = LoadEXRWithLayer(&image, &width, &height, filepath.c_str(), "Warstwa 1",
                         &err);
  REQUIRE(TINYEXR_SUCCESS == ret);
  free(image);
  if (err) {
    FreeEXRErrorMessage(err);
  }
}

TEST_CASE("Regression: Issue53|Image|Missing Layer", "[issue53]") {
  std::string filepath = GetPath("MultiView/Impact.exr");

  const char* err = nullptr;
  int width, height;
  float* image = nullptr;
  int ret = LoadEXRWithLayer(&image, &width, &height, filepath.c_str(),
                             "Warstwa", &err);
  REQUIRE(TINYEXR_ERROR_LAYER_NOT_FOUND == ret);
  if (image) {
    free(image);
  }
  if (err) {
    FreeEXRErrorMessage(err);
  }
}

TEST_CASE("Regression: PR150|Read|1x1 1xhalf", "[pr150]") {
  std::string filepath = "./regression/tiled_half_1x1_alpha.exr";

  EXRVersion exr_version;
  std::cout << "Loading" << filepath << std::endl;
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

  ret = LoadEXRImageFromFile(&image, &header, filepath.c_str(), &err);
  REQUIRE(TINYEXR_SUCCESS == ret);

  FreeEXRHeader(&header);
  FreeEXRImage(&image);
}
