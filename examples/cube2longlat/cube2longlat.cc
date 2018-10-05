#include "tinyexr.h"

#define STB_IMAGE_IMPLEMENTATION
#include "stb_image.h"

#define STB_IMAGE_WRITE_IMPLEMENTATION
#include "stb_image_write.h"

#include <array>
#include <cmath>
#include <iostream>
#include <string>
#include <vector>

// From Filament.
static inline void RGBMtoLinear(const float rgbm[4], float linear[3]) {
  linear[0] = rgbm[0] * rgbm[3] * 16.0f;
  linear[1] = rgbm[1] * rgbm[3] * 16.0f;
  linear[2] = rgbm[2] * rgbm[3] * 16.0f;

  // Gamma to linear space
  linear[0] = linear[0] * linear[0];
  linear[1] = linear[1] * linear[1];
  linear[2] = linear[2] * linear[2];
}

static inline void LinearToRGBM(const float linear[3], float rgbm[4]) {
  rgbm[0] = linear[0];
  rgbm[1] = linear[1];
  rgbm[2] = linear[2];
  rgbm[3] = 1.0f;

  // Linear to gamma space
  rgbm[0] = rgbm[0] * rgbm[0];
  rgbm[1] = rgbm[1] * rgbm[1];
  rgbm[2] = rgbm[2] * rgbm[2];

  // Set the range
  rgbm[0] /= 16.0f;
  rgbm[1] /= 16.0f;
  rgbm[2] /= 16.0f;

  float maxComponent =
      std::max(std::max(rgbm[0], rgbm[1]), std::max(rgbm[2], 1e-6f));
  // Don't let M go below 1 in the [0..16] range
  rgbm[3] = std::max(1.0f / 16.0f, std::min(maxComponent, 1.0f));
  rgbm[3] = std::ceil(rgbm[3] * 255.0f) / 255.0f;

  // saturate([0.0, 1.0])
  rgbm[0] = std::max(0.0f, std::min(1.0f, rgbm[0] / rgbm[3]));
  rgbm[1] = std::max(0.0f, std::min(1.0f, rgbm[1] / rgbm[3]));
  rgbm[2] = std::max(0.0f, std::min(1.0f, rgbm[2] / rgbm[3]));
}

static std::string GetFileExtension(const std::string& filename) {
  if (filename.find_last_of(".") != std::string::npos)
    return filename.substr(filename.find_last_of(".") + 1);
  return "";
}

struct Image {
  int width;
  int height;
  std::vector<float> data;
};

static bool LoadCubemaps(const std::array<std::string, 6> face_filenames,
                         std::array<Image, 6>* output) {
  for (size_t i = 0; i < 6; i++) {
    std::string ext = GetFileExtension(face_filenames[i]);

    Image image;

    if ((ext.compare("exr") == 0) || (ext.compare("EXR") == 0)) {
      int width, height;
      float* rgba;
      const char* err;

      int ret =
          LoadEXR(&rgba, &width, &height, face_filenames[i].c_str(), &err);
      if (ret != 0) {
        if (err) {
          std::cerr << "EXR load error: " << err << std::endl;
        } else {
          std::cerr << "EXR load error: code " << ret << std::endl;
        }
        return false;
      }

      image.width = width;
      image.height = height;
      image.data.resize(width * height * 3);

      // RGBA -> RGB
      for (size_t j = 0; j < size_t(width * height); j++) {
        image.data[3 * j + 0] = rgba[4 * j + 0];
        image.data[3 * j + 1] = rgba[4 * j + 1];
        image.data[3 * j + 2] = rgba[4 * j + 2];
      }

      free(rgba);

      (*output)[i] = std::move(image);

    } else if ((ext.compare("rgbm") == 0) || (ext.compare("RGBM") == 0)) {
      int width, height;
      int n;

      unsigned char* data = stbi_load(face_filenames[i].c_str(), &width,
                                      &height, &n, STBI_default);

      if (!data) {
        std::cerr << "Failed to load file: " << face_filenames[i] << std::endl;
        return false;
      }

      if ((n != 4)) {
        std::cerr << "Not a RGBM encoded image: " << face_filenames[i]
                  << std::endl;
        return false;
      }

      image.width = width;
      image.height = height;
      image.data.resize(size_t(width * height));

      for (size_t i = 0; i < size_t(width * height); i++) {
        float rgbm[4];
        // [0, 1.0]
        rgbm[0] = data[4 * i + 0] / 255.0f;
        rgbm[1] = data[4 * i + 1] / 255.0f;
        rgbm[2] = data[4 * i + 2] / 255.0f;
        rgbm[3] = data[4 * i + 3] / 255.0f;

        float linear[3];
        RGBMtoLinear(rgbm, linear);

        image.data[3 * i + 0] = linear[0];
        image.data[3 * i + 1] = linear[1];
        image.data[3 * i + 2] = linear[2];
      }

      (*output)[i] = std::move(image);

    } else {
      std::cerr << "Unknown file extension : " << ext << std::endl;
      return false;
    }
    std::cout << "Loaded " << face_filenames[i] << std::endl;
  }

  return true;
}

void convert_xyz_to_cube_uv(float x, float y, float z, int* index, float* u,
                            float* v) {
  float absX = fabs(x);
  float absY = fabs(y);
  float absZ = fabs(z);

  int isXPositive = x > 0.0f ? 1 : 0;
  int isYPositive = y > 0.0f ? 1 : 0;
  int isZPositive = z > 0.0f ? 1 : 0;

  float maxAxis, uc, vc;

  // POSITIVE X
  if (isXPositive && absX >= absY && absX >= absZ) {
    // u (0 to 1) goes from +z to -z
    // v (0 to 1) goes from -y to +y
    maxAxis = absX;
    uc = -z;
    vc = y;
    *index = 0;
  }
  // NEGATIVE X
  if (!isXPositive && absX >= absY && absX >= absZ) {
    // u (0 to 1) goes from -z to +z
    // v (0 to 1) goes from -y to +y
    maxAxis = absX;
    uc = z;
    vc = y;
    *index = 1;
  }
  // POSITIVE Y
  if (isYPositive && absY >= absX && absY >= absZ) {
    // u (0 to 1) goes from -x to +x
    // v (0 to 1) goes from +z to -z
    maxAxis = absY;
    uc = x;
    vc = -z;
    *index = 2;
  }
  // NEGATIVE Y
  if (!isYPositive && absY >= absX && absY >= absZ) {
    // u (0 to 1) goes from -x to +x
    // v (0 to 1) goes from -z to +z
    maxAxis = absY;
    uc = x;
    vc = z;
    *index = 3;
  }
  // POSITIVE Z
  if (isZPositive && (absZ >= absX) && (absZ >= absY)) {
    // u (0 to 1) goes from -x to +x
    // v (0 to 1) goes from -y to +y
    maxAxis = absZ;
    uc = x;
    vc = y;
    *index = 4;
  }
  // NEGATIVE Z
  if (!isZPositive && (absZ >= absX) && (absZ >= absY)) {
    // u (0 to 1) goes from +x to -x
    // v (0 to 1) goes from -y to +y
    maxAxis = absZ;
    uc = -x;
    vc = y;
    *index = 5;
  }

  // Convert range from -1 to 1 to 0 to 1
  *u = 0.5f * (uc / maxAxis + 1.0f);
  *v = 0.5f * (vc / maxAxis + 1.0f);
}

//
// Simple bilinear texture filtering.
//
static void SampleTexture(float* rgba, float u, float v, int width, int height,
                          int channels, const float* texels) {
  float sx = std::floor(u);
  float sy = std::floor(v);

  // Wrap mode = repeat
  float uu = u - sx;
  float vv = v - sy;

  // clamp
  uu = std::max(uu, 0.0f);
  uu = std::min(uu, 1.0f);
  vv = std::max(vv, 0.0f);
  vv = std::min(vv, 1.0f);

  float px = (width - 1) * uu;
  float py = (height - 1) * vv;

  int x0 = std::max(0, std::min((int)px, (width - 1)));
  int y0 = std::max(0, std::min((int)py, (height - 1)));
  int x1 = std::max(0, std::min((x0 + 1), (width - 1)));
  int y1 = std::max(0, std::min((y0 + 1), (height - 1)));

  float dx = px - (float)x0;
  float dy = py - (float)y0;

  float w[4];

  w[0] = (1.0f - dx) * (1.0 - dy);
  w[1] = (1.0f - dx) * (dy);
  w[2] = (dx) * (1.0 - dy);
  w[3] = (dx) * (dy);

  int i00 = channels * (y0 * width + x0);
  int i01 = channels * (y0 * width + x1);
  int i10 = channels * (y1 * width + x0);
  int i11 = channels * (y1 * width + x1);

  for (int i = 0; i < channels; i++) {
    rgba[i] = w[0] * texels[i00 + i] + w[1] * texels[i10 + i] +
              w[2] * texels[i01 + i] + w[3] * texels[i11 + i];
  }
}

static void SampleCubemap(const std::array<Image, 6>& cubemap_faces,
                          const float n[3], float col[3]) {
  int face;
  float u, v;
  convert_xyz_to_cube_uv(n[0], n[1], n[2], &face, &u, &v);

  v = 1.0f - v;

  // std::cout << "face = " << face << std::endl;

  // TODO(syoyo): Do we better consider seams on the cubemap face border?
  const Image& tex = cubemap_faces[face];

  // std::cout << "n = " << n[0] << ", " << n[1] << ", " << n[2] << ", uv = " <<
  // u << ", " << v << std::endl;

  SampleTexture(col, u, v, tex.width, tex.height, /* RGB */ 3, tex.data.data());

// col[0] = u;
// col[1] = v;
// col[2] = 0.0f;
#if 0
  if (face == 0) {
    col[0] = 1.0f; 
    col[1] = 0.0f; 
    col[2] = 0.0f; 
  } else if (face == 1) {
    col[0] = 0.0f; 
    col[1] = 1.0f; 
    col[2] = 0.0f; 
  } else if (face == 2) {
    col[0] = 0.0f; 
    col[1] = 0.0f; 
    col[2] = 1.0f; 
  } else if (face == 3) {
    col[0] = 1.0f; 
    col[1] = 0.0f; 
    col[2] = 1.0f; 
  } else if (face == 4) {
    col[0] = 0.0f; 
    col[1] = 1.0f; 
    col[2] = 1.0f; 
  } else if (face == 5) {
    col[0] = 1.0f; 
    col[1] = 1.0f; 
    col[2] = 1.0f; 
  }
#endif
}

static void CubemapToLonglat(const std::array<Image, 6>& cubemap_faces,
                             const float phi_offset, /* in angle */
                             const int width, Image* longlat) {
  int height = width / 2;

  longlat->width = width;
  longlat->height = height;
  longlat->data.resize(size_t(width * height * 3));  // RGB

  const float kPI = 3.141592f;

  for (size_t y = 0; y < size_t(height); y++) {
    float theta = ((y + 0.5f) / float(height)) * kPI;  // [0, pi]
    for (size_t x = 0; x < size_t(width); x++) {
      float phi = ((x + 0.5f) / float(width)) * 2.0f * kPI;  // [0, 2 pi]

      phi += (phi_offset) * kPI / 180.0f;

      float n[3];

      // Y-up
      n[0] = std::sin(theta) * std::cos(phi);
      n[1] = std::cos(theta);
      n[2] = -std::sin(theta) * std::sin(phi);

      float col[3];
      SampleCubemap(cubemap_faces, n, col);

      longlat->data[3 * size_t(y * width + x) + 0] = col[0];
      longlat->data[3 * size_t(y * width + x) + 1] = col[1];
      longlat->data[3 * size_t(y * width + x) + 2] = col[2];
    }
  }
}

static unsigned char ftouc(const float f) {
  int i(f * 255.0f);
  i = std::max(0, std::min(255, i));
  return static_cast<unsigned char>(i);
}

int main(int argc, char** argv) {
  float phi_offset = 0.0f;

  if (argc < 9) {
    printf(
        "Usage: cube2longlat px.exr nx.exr py.exr ny.exr pz.exr nz.exr "
        "output_width output.exr\n");
    exit(-1);
  }

  std::array<std::string, 6> face_filenames;

  face_filenames[0] = argv[1];
  face_filenames[1] = argv[2];
  face_filenames[2] = argv[3];
  face_filenames[3] = argv[4];
  face_filenames[4] = argv[5];
  face_filenames[5] = argv[6];

  int output_width = atoi(argv[7]);

  std::string output_filename = argv[8];

  if (argc > 9) {
    phi_offset = atof(argv[9]);
  }

  std::array<Image, 6> cubemaps;

  if (!LoadCubemaps(face_filenames, &cubemaps)) {
    std::cerr << "Failed to load cubemap faces." << std::endl;
    return EXIT_FAILURE;
  }

  Image longlat;

  CubemapToLonglat(cubemaps, phi_offset, output_width, &longlat);

  {
    std::string ext = GetFileExtension(output_filename);
    if ((ext.compare("exr") == 0) || (ext.compare("EXR") == 0)) {
      const char *err;
      int ret = SaveEXR(longlat.data.data(), longlat.width, longlat.height,
                        /* RGB */ 3, /* fp16 */ 0, output_filename.c_str(), &err);
      if (ret != TINYEXR_SUCCESS) {
        if (err) {
          std::cout << "Failed to save image as EXR. msg = " << err << ", code = " << ret << std::endl;
          FreeEXRErrorMessage(err);
        } else {
          std::cout << "Failed to save image as EXR. code = " << ret << std::endl;
        }
        return EXIT_FAILURE;
      }
    } else if ((ext.compare("rgbm") == 0) || (ext.compare("RGBM") == 0)) {
      std::vector<unsigned char> rgbm_image;

      for (size_t j = 0; j < size_t(longlat.width * longlat.height); j++) {
        float linear[3];
        linear[0] = longlat.data[3 * j + 0];
        linear[1] = longlat.data[3 * j + 1];
        linear[2] = longlat.data[3 * j + 2];

        float rgbm[4];

        LinearToRGBM(linear, rgbm);

        rgbm_image[4 * j + 0] = ftouc(rgbm[0]);
        rgbm_image[4 * j + 1] = ftouc(rgbm[1]);
        rgbm_image[4 * j + 2] = ftouc(rgbm[2]);
        rgbm_image[4 * j + 3] = ftouc(rgbm[2]);
      }

      // Save as PNG.
      int ret =
          stbi_write_png(output_filename.c_str(), longlat.width, longlat.height,
                         4, rgbm_image.data(), longlat.width * 4);

      if (ret == 0) {
        std::cerr << "Failed to save image as RGBM file : " << output_filename
                  << std::endl;
        return EXIT_FAILURE;
      }

    } else {
      if ((ext.compare("hdr") == 0) || (ext.compare("HDR") == 0)) {
        // ok
      } else {
        std::cout << "Unknown file extension. Interpret it as RGBE format : "
                  << ext << std::endl;
      }

      int ret = stbi_write_hdr(output_filename.c_str(), longlat.width,
                               longlat.height, 3, longlat.data.data());

      if (ret == 0) {
        std::cerr << "Failed to save image as HDR file : " << output_filename
                  << std::endl;
        return EXIT_FAILURE;
      }
    }
  }

  std::cout << "Write " << output_filename << std::endl;

  return 0;
}
