#define TINYEXR_IMPLEMENTATION
#include "tinyexr.h"

#ifdef __clang__
#pragma clang diagnostic push
#pragma clang diagnostic ignored "-Weverything"
#endif

#define STB_IMAGE_RESIZE_IMPLEMENTATION
#include "stb_image_resize.h"

#define STB_IMAGE_WRITE_IMPLEMENTATION
#include "stb_image_write.h"

#include "cxxopts.hpp"

#ifdef __clang__
#pragma clang diagnostic pop
#endif

namespace {

static void vnormalize(float v[3]) {
  const float d2 = v[0] * v[0] + v[1] * v[1] + v[2] * v[2];
  if (d2 > 1.0e-6f) {
    const float inv_d = 1.0f / std::sqrt(d2);
    v[0] *= inv_d;
    v[1] *= inv_d;
    v[2] *= inv_d;
  }
  return;
}


template<typename T>
static inline T clamp(const T v, const T min_v, const T max_v)
{
  return std::max(min_v, std::min(max_v, v));
}

//
// Compute gradient from scalar field.
// dx = (x + 1, y    ) - (x, y) 
// dy = (x    , y + 1) - (x, y) 
//
// TODO(syoyo): Use central difference with texel filtering.
//
static void Gradient(
  const std::vector<float> &src,
  const size_t width,
  const size_t height,
  const size_t x, const size_t y,
  const float bumpness,
  float dir[3])
{
  const size_t x1 = clamp(x + 1, size_t(0), width - 1);
  const size_t y1 = clamp(y + 1, size_t(0), height - 1);


  float v00 = src[y * width + x];
  float v01 = src[y * width + x1];
  float v11 = src[y1 * width + x];

  
  float dx = bumpness * (v01 - v00);
  float dy = bumpness * (v11 - v00);

  dir[0] = dx;
  dir[1] = dy;
  dir[2] = 0.0f;
    
}

///
/// Convert image(bump map for single channel, vector displacement map for 3 channels input) to normal map.
/// @param[in] base Base value fo
///
///
static void ToNormalMap(
  const std::vector<float> &src,
  const size_t width,
  const size_t height,
  const size_t channels,
  const float strength,
  std::vector<float> *dst)
{
  assert((channels == 1) || (channels == 3) || (channels == 4));

  dst->resize(width * height * 3);

  if (channels == 1) {
    // bump map
    for (size_t y = 0; y < height; y++) {
      for (size_t x = 0; x < width; x++) {
        float d[3];
        Gradient(src, width, height, x, y, strength, d);

        (*dst)[3 * (y * width + x) + 0] = d[0];
        (*dst)[3 * (y * width + x) + 1] = d[1];
        (*dst)[3 * (y * width + x) + 2] = d[2];

      }
    }

  } else {
    // vector displacement map

    for (size_t y = 0; y < height; y++) {
      for (size_t x = 0; x < width; x++) {

        float v[3];
        v[0] = src[channels * (y * width + x) + 0];
        v[1] = src[channels * (y * width + x) + 1];
        v[2] = src[channels * (y * width + x) + 2];

        v[0] *= strength;
        v[1] *= strength;
        v[2] *= strength;

        // Add (0, 0, 1)
        v[2] += 1.0f;

        // TODO(syoyo): Add option to not normalize.
        vnormalize(v);

        (*dst)[3 * (y * width + x) + 0] = 0.5f * v[0] + 0.5f;
        (*dst)[3 * (y * width + x) + 1] = 0.5f * v[1] + 0.5f;
        (*dst)[3 * (y * width + x) + 2] = 0.5f * v[2] + 0.5f;

      }
    }

  }

}

inline unsigned char ftouc(float f)
{
  int i = static_cast<int>(f * 255.0f);
  if (i > 255) i = 255;
  if (i < 0) i = 0;

  return static_cast<unsigned char>(i);
}

bool SaveImage(const char* filename, const float* rgb, int width, int height) {

  std::vector<unsigned char> dst(width * height * 3);

  for (size_t i = 0; i < width * height; i++) {
      dst[i * 3 + 0] = ftouc(rgb[i * 3 + 0]);
      dst[i * 3 + 1] = ftouc(rgb[i * 3 + 1]);
      dst[i * 3 + 2] = ftouc(rgb[i * 3 + 2]);
  }

  int ret = stbi_write_png(filename, width, height, 3, static_cast<const void*>(dst.data()), width * 3);

  return (ret > 0);
}

std::string GetFileExtension(const std::string &filename) {
  if (filename.find_last_of(".") != std::string::npos)
    return filename.substr(filename.find_last_of(".") + 1);
  return "";
}

} // namespace

int main(int argc, char **argv)
{
  cxxopts::Options options("normalmap", "help");
  options.add_options()
    ("s,strength", "Strength(scaling) for normal value", cxxopts::value<float>())
    ("i,input", "Input filename", cxxopts::value<std::string>())
    ("o,output", "Output filename", cxxopts::value<std::string>())
    ("r,resize", "Resize image. 0.5 = 50%%, 0.1 = 10%%", cxxopts::value<float>())
    ;

  auto result = options.parse(argc, argv);

  if (result.count("input") == 0) {
    std::cerr << "input filename missing" << std::endl;
    return EXIT_FAILURE;
  }

  if (result.count("output") == 0) {
    std::cerr << "output filename missing" << std::endl;
    return EXIT_FAILURE;
  }

  float strength = 1.0f;
  if (result.count("strength")) {
    strength = result["strength"].as<float>();
  }

  float resize = 1.0f;
  if (result.count("resize")) {
    resize = result["resize"].as<float>();
  }

  std::string input_filename = result["input"].as<std::string>();
  std::string output_filename = result["output"].as<std::string>();

  std::vector<float> src;
  size_t src_width;
  size_t src_height;

  {
    float *rgba = nullptr;
    int width, height;
    const char *err = nullptr;
    int ret = LoadEXR(&rgba, &width, &height, input_filename.c_str(), &err);
    if (TINYEXR_SUCCESS != ret) {
      std::cerr << "Failed to load EXR file [" << input_filename << "] code = " << ret << std::endl;
      if (err) {
        std::cerr << err << std::endl;
        FreeEXRErrorMessage(err);
      }
      
      return EXIT_FAILURE;
    }

    std::cout << "loaded EXR. width x height = " << width << "x" << height << std::endl;
    src.resize(size_t(width * height * 3));

    // ignore alpha for now
    for (size_t i = 0; i < size_t(width * height); i++) {
      src[3 * i + 0] = rgba[4 * i + 0];
      src[3 * i + 1] = rgba[4 * i + 1];
      src[3 * i + 2] = rgba[4 * i + 2];
    }

    src_width  = size_t(width);
    src_height = size_t(height);

    free(rgba);
  }

  std::cout << "strength = " << strength << std::endl;

  std::vector<float> dst;
  ToNormalMap(src, src_width, src_height, 3, strength, &dst);


  std::string ext = GetFileExtension(output_filename);
  if ((ext.compare("png") == 0) ||
      (ext.compare("PNG") == 0)) {
    // Save as LDR image.
    // Do not apply sRGB conversion for PNG(LDR) image.
    if (!SaveImage(output_filename.c_str(), dst.data(), int(src_width), int(src_height))) {
      std::cerr << "Failed to write a file : " << output_filename << std::endl;
      return EXIT_FAILURE;
    } 
  } else {
    // assume EXR.
    float *rgba = nullptr;
    int width, height;
    int ret = SaveEXR(dst.data(), int(src_width), int(src_height), /* component */3, /* fp16 */0, output_filename.c_str(), nullptr);
    if (TINYEXR_SUCCESS != ret) {
      std::cerr << "Failed to save EXR file [" << input_filename << "] code = " << ret << std::endl;
      return EXIT_FAILURE;
    }
  }

  return EXIT_SUCCESS;
}

