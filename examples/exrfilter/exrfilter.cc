#include <cstdio>
#include <cstdlib>
#include <vector>

#include "tinyexr.h"

#include "cxxopts.hpp"

int main(int argc, char** argv)
{

  float min_value = -std::numeric_limits<float>::max();
  float max_value = std::numeric_limits<float>::max();

  float rgb_min[3] = {min_value, min_value, min_value};
  float rgb_max[3] = {max_value, max_value, max_value};

  cxxopts::Options options("normalmap", "help");
  options.show_positional_help();

  options.add_options()
    ("max", "Max intensity(apply all RGB channels)", cxxopts::value<float>())
    ("rmax", "Max Red intensity", cxxopts::value<float>())
    ("gmax", "Max Green intensity", cxxopts::value<float>())
    ("bmax", "Max Blue intensity", cxxopts::value<float>())
    ("min", "Min intensity(apply all RGB channels)", cxxopts::value<float>())
    ("rmin", "Min Red intensity", cxxopts::value<float>())
    ("gmin", "Min Green intensity", cxxopts::value<float>())
    ("bmin", "Min Blue intensity", cxxopts::value<float>())
    ("i,input", "Input filename", cxxopts::value<std::string>())
    ("o,output", "Output filename", cxxopts::value<std::string>())
    ("help", "Print help")
    ;

  auto result = options.parse(argc, argv);

  if (result.count("help")) {
    std::cout << options.help() << std::endl;
  }

  if (result.count("input") == 0) {
    std::cerr << "input filename missing" << std::endl;
    std::cout << options.help() << std::endl;
    return EXIT_FAILURE;
  }

  if (result.count("output") == 0) {
    std::cerr << "output filename missing" << std::endl;
    std::cout << options.help() << std::endl;
    return EXIT_FAILURE;
  }

  std::string input_filename = result["input"].as<std::string>();
  std::string output_filename = result["output"].as<std::string>();


  if (result.count("max")) {
    rgb_max[0] = result["max"].as<float>();
    rgb_max[1] = result["max"].as<float>();
    rgb_max[2] = result["max"].as<float>();
  }
  if (result.count("rmax")) {
    rgb_max[0] = result["rmax"].as<float>();
  }
  if (result.count("gmax")) {
    rgb_max[1] = result["gmax"].as<float>();
  }
  if (result.count("bmax")) {
    rgb_max[2] = result["bmax"].as<float>();
  }

  if (result.count("min")) {
    rgb_min[0] = result["min"].as<float>();
    rgb_min[1] = result["min"].as<float>();
    rgb_min[2] = result["min"].as<float>();
  }
  if (result.count("rmin")) {
    rgb_min[0] = result["rmin"].as<float>();
  }
  if (result.count("gmin")) {
    rgb_min[1] = result["gmin"].as<float>();
  }
  if (result.count("bmin")) {
    rgb_min[2] = result["bmin"].as<float>();
  }

  float *rgba = nullptr;
  int width, height;
  const char *err = nullptr;
  {
    int ret = LoadEXR(&rgba, &width, &height, input_filename.c_str(), &err);
    if (TINYEXR_SUCCESS != ret) {
      std::cerr << "Failed to load EXR file [" << input_filename << "] code = " << ret << std::endl;
      if (err) {
        std::cerr << err << std::endl;
        FreeEXRErrorMessage(err);
      }

      return EXIT_FAILURE;
    }
  }

  // clip pixel values.
  // ignore alpha channel for now.
  std::vector<float> rgb;
  rgb.resize(width * height * 3);

  float v_max[3] = {
    -std::numeric_limits<float>::max(),
    -std::numeric_limits<float>::max(),
    -std::numeric_limits<float>::max()};
  float v_min[3] = {
    std::numeric_limits<float>::max(),
    std::numeric_limits<float>::max(),
    std::numeric_limits<float>::max()};

  {
    for (size_t i = 0; i < width * height; i++) {
      rgb[3 * i + 0] = std::max(rgb_min[0], std::min(rgb_max[0], rgba[4 * i + 0]));    
      rgb[3 * i + 1] = std::max(rgb_min[1], std::min(rgb_max[1], rgba[4 * i + 1]));    
      rgb[3 * i + 2] = std::max(rgb_min[2], std::min(rgb_max[2], rgba[4 * i + 2]));    

      v_max[0] = std::max(rgb[3 * i + 0], v_max[0]);
      v_max[1] = std::max(rgb[3 * i + 1], v_max[1]);
      v_max[2] = std::max(rgb[3 * i + 2], v_max[2]);

      v_min[0] = std::min(rgb[3 * i + 0], v_min[0]);
      v_min[1] = std::min(rgb[3 * i + 1], v_min[1]);
      v_min[2] = std::min(rgb[3 * i + 2], v_min[2]);

    }
  }

  std::cout << "v min = " << v_min[0] << ", " << v_min[1] << ", " << v_min[2] << std::endl;
  std::cout << "v max = " << v_max[0] << ", " << v_max[1] << ", " << v_max[2] << std::endl;

  {
    int ret = SaveEXR(rgb.data(), width, height, /* component */3, /* fp16 */0, output_filename.c_str(), &err);
    if (TINYEXR_SUCCESS != ret) {
      if (err) { 
        std::cerr << err << std::endl;
        FreeEXRErrorMessage(err);
      }
      std::cerr << "Failed to save EXR file [" << input_filename << "] code = " << ret << std::endl;
      return EXIT_FAILURE;
    }
  }

  return EXIT_SUCCESS;
}
