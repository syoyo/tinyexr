#include <algorithm>
#include <cassert>
#include <cmath>
#include <cstdio>
#include <limits>

namespace example {

template <typename T = float>
class real2 {
 public:
  real2() {}
  real2(T x) {
    v[0] = x;
    v[1] = x;
  }
  real2(T xx, T yy) {
    v[0] = xx;
    v[1] = yy;
  }
  explicit real2(const T *p) {
    v[0] = p[0];
    v[1] = p[1];
  }

  inline T x() const { return v[0]; }
  inline T y() const { return v[1]; }

  real2 operator*(T f) const { return real2(x() * f, y() * f); }
  real2 operator-(const real2 &f2) const {
    return real2(x() - f2.x(), y() - f2.y());
  }
  real2 operator*(const real2 &f2) const {
    return real2(x() * f2.x(), y() * f2.y());
  }
  real2 operator+(const real2 &f2) const {
    return real2(x() + f2.x(), y() + f2.y());
  }
  real2 &operator+=(const real2 &f2) {
    v[0] += f2.x();
    v[1] += f2.y();
    return (*this);
  }
  real2 operator/(const real2 &f2) const {
    return real2(x() / f2.x(), y() / f2.y());
  }
  real2 operator-() const { return real2(-x(), -y()); }
  T operator[](int i) const { return v[i]; }
  T &operator[](int i) { return v[i]; }

  T v[2];
  // T pad[2];  // for alignment(when T = float)
};

template <typename T = float>
class real3 {
 public:
  real3() {}
  real3(T x) {
    v[0] = x;
    v[1] = x;
    v[2] = x;
  }
  real3(T xx, T yy, T zz) {
    v[0] = xx;
    v[1] = yy;
    v[2] = zz;
  }
  explicit real3(const T *p) {
    v[0] = p[0];
    v[1] = p[1];
    v[2] = p[2];
  }

  inline T x() const { return v[0]; }
  inline T y() const { return v[1]; }
  inline T z() const { return v[2]; }

  real3 operator*(T f) const { return real3(x() * f, y() * f, z() * f); }
  real3 operator-(const real3 &f2) const {
    return real3(x() - f2.x(), y() - f2.y(), z() - f2.z());
  }
  real3 operator*(const real3 &f2) const {
    return real3(x() * f2.x(), y() * f2.y(), z() * f2.z());
  }
  real3 operator+(const real3 &f2) const {
    return real3(x() + f2.x(), y() + f2.y(), z() + f2.z());
  }
  real3 &operator+=(const real3 &f2) {
    v[0] += f2.x();
    v[1] += f2.y();
    v[2] += f2.z();
    return (*this);
  }
  real3 operator/(const real3 &f2) const {
    return real3(x() / f2.x(), y() / f2.y(), z() / f2.z());
  }
  real3 operator-() const { return real3(-x(), -y(), -z()); }
  T operator[](int i) const { return v[i]; }
  T &operator[](int i) { return v[i]; }

  T v[3];
  // T pad;  // for alignment(when T = float)
};

template <typename T>
inline real3<T> operator*(T f, const real3<T> &v) {
  return real3<T>(v.x() * f, v.y() * f, v.z() * f);
}

template <typename T>
inline real3<T> vneg(const real3<T> &rhs) {
  return real3<T>(-rhs.x(), -rhs.y(), -rhs.z());
}

template <typename T>
inline T vlength(const real3<T> &rhs) {
  return std::sqrt(rhs.x() * rhs.x() + rhs.y() * rhs.y() + rhs.z() * rhs.z());
}

template <typename T>
inline real3<T> vnormalize(const real3<T> &rhs) {
  real3<T> v = rhs;
  T len = vlength(rhs);
  if (std::fabs(len) > std::numeric_limits<T>::epsilon()) {
    T inv_len = static_cast<T>(1.0) / len;
    v.v[0] *= inv_len;
    v.v[1] *= inv_len;
    v.v[2] *= inv_len;
  }
  return v;
}

template <typename T>
inline real3<T> vcross(const real3<T> a, const real3<T> b) {
  real3<T> c;
  c[0] = a[1] * b[2] - a[2] * b[1];
  c[1] = a[2] * b[0] - a[0] * b[2];
  c[2] = a[0] * b[1] - a[1] * b[0];
  return c;
}

template <typename T>
inline T vdot(const real3<T> a, const real3<T> b) {
  return a[0] * b[0] + a[1] * b[1] + a[2] * b[2];
}

template <typename T>
inline real3<T> vsafe_inverse(const real3<T> v) {
  real3<T> r;

#ifdef NANORT_USE_CPP11_FEATURE

  if (std::fabs(v[0]) < std::numeric_limits<T>::epsilon()) {
    r[0] = std::numeric_limits<T>::infinity() *
           std::copysign(static_cast<T>(1), v[0]);
  } else {
    r[0] = static_cast<T>(1.0) / v[0];
  }

  if (std::fabs(v[1]) < std::numeric_limits<T>::epsilon()) {
    r[1] = std::numeric_limits<T>::infinity() *
           std::copysign(static_cast<T>(1), v[1]);
  } else {
    r[1] = static_cast<T>(1.0) / v[1];
  }

  if (std::fabs(v[2]) < std::numeric_limits<T>::epsilon()) {
    r[2] = std::numeric_limits<T>::infinity() *
           std::copysign(static_cast<T>(1), v[2]);
  } else {
    r[2] = static_cast<T>(1.0) / v[2];
  }
#else

  if (std::fabs(v[0]) < std::numeric_limits<T>::epsilon()) {
    T sgn = (v[0] < static_cast<T>(0)) ? static_cast<T>(-1) : static_cast<T>(1);
    r[0] = std::numeric_limits<T>::infinity() * sgn;
  } else {
    r[0] = static_cast<T>(1.0) / v[0];
  }

  if (std::fabs(v[1]) < std::numeric_limits<T>::epsilon()) {
    T sgn = (v[1] < static_cast<T>(0)) ? static_cast<T>(-1) : static_cast<T>(1);
    r[1] = std::numeric_limits<T>::infinity() * sgn;
  } else {
    r[1] = static_cast<T>(1.0) / v[1];
  }

  if (std::fabs(v[2]) < std::numeric_limits<T>::epsilon()) {
    T sgn = (v[2] < static_cast<T>(0)) ? static_cast<T>(-1) : static_cast<T>(1);
    r[2] = std::numeric_limits<T>::infinity() * sgn;
  } else {
    r[2] = static_cast<T>(1.0) / v[2];
  }
#endif

  return r;
}

typedef real3<float> float3;
typedef real2<float> float2;

struct Image {
  std::vector<float> pixels;
  size_t width;
  size_t height;
  size_t channels;

  float3 get(size_t x, size_t y) const {
    float3 ret(0.0f, 0.0f, 0.0f);
    if (channels == 1) {
      ret[0] = ret[1] = ret[2] = pixels[y * width + x];
    } else if (channels == 2) {
      ret[0] = pixels[channels * (y * width + x) + 0];
      ret[1] = pixels[channels * (y * width + x) + 1];
    } else if (channels >= 3) {
      ret[0] = pixels[channels * (y * width + x) + 0];
      ret[1] = pixels[channels * (y * width + x) + 1];
      ret[2] = pixels[channels * (y * width + x) + 2];
    }

    return ret;
  }
};

// ------------------------------------------------------------------
// solveVMF and prefilter is based on Filament's code.

/*
 * Copyright (C) 2015 The Android Open Source Project
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

float solveVMF(const float2 pos, const size_t sampleCount,
               const float roughness, const Image &normal) {
  float3 averageNormal(0.0f);
  float2 topLeft(-float(sampleCount) / 2.0f + 0.5f);

  for (size_t y = 0; y < sampleCount; y++) {
    for (size_t x = 0; x < sampleCount; x++) {
      float2 offset(topLeft[0] + float(x), topLeft[1] + float(y));
      float2 samplePos;
      samplePos[0] = std::floor(pos[0] + offset[0]) + 0.5f;
      samplePos[1] = std::floor(pos[1] + offset[1]) + 0.5f;

      float3 sampleNormal =
          normal.get(size_t(samplePos[0]), size_t(samplePos[1]));
      sampleNormal = sampleNormal * 2.0f - 1.0f;

      averageNormal += vnormalize(sampleNormal);
    }
  }

  averageNormal = averageNormal / (sampleCount * sampleCount);

  float r = vlength(averageNormal);
  float kappa = 10000.0f;

  if (r < 1.0f) {
    kappa = (3.0f * r - r * r * r) / (1.0f - r * r);
  }

  // See: Karis, 2018, "Normal map filtering using vMF (part 3)"
  // The original formulation in Neubelt et al. 2013,
  // "Crafting a Next-Gen Material Pipeline for The Order: 1886" contains an
  // error and defines alpha' = sqrt(alpha^2 + 1 / kappa)
  return std::sqrt(roughness * roughness + (2.0f / kappa));
}

void prefilter(const Image &normal, const float roughness,
               const size_t mipLevel, Image &output) {
  assert(output.channels == 3);
  const size_t width = output.width;
  const size_t height = output.height;
  const size_t sampleCount = 1u << mipLevel;

  for (size_t y = 0; y < height; y++) {
    for (size_t x = 0; x < width; x++) {
      const float2 uv = (float2(x, y) + 0.5f) / float2(width, height);
      const float2 pos(uv[0] * normal.width, uv[1] * normal.height);
      const float3 value = solveVMF(pos, sampleCount, roughness, normal);
      output.pixels[3 * (y * output.width + x) + 0] = value[0];
      output.pixels[3 * (y * output.width + x) + 1] = value[1];
      output.pixels[3 * (y * output.width + x) + 2] = value[2];
    }
  }
}

template <bool FIRST_MIP>
void prefilter(const Image &normal, const Image &roughness,
               const size_t mipLevel, Image &output) {
  assert(output.channels == 3);
  const size_t width = output.width;
  const size_t height = output.height;
  const size_t sampleCount = 1u << mipLevel;

  for (size_t y = 0; y < height; y++) {
    for (size_t x = 0; x < width; x++) {
      float3 data = roughness.get(x, y);  // scalar value
      if (FIRST_MIP) {
        output.pixels[3 * (y * output.width + x) + 0] = data[0];
        output.pixels[3 * (y * output.width + x) + 1] = data[1];
        output.pixels[3 * (y * output.width + x) + 2] = data[2];
      } else {
        const float2 uv = (float2(x, y) + 0.5f) / float2(width, height);
        const float2 pos(uv[0] * normal.width, uv[1] * normal.height);
        const float3 value =
            solveVMF(pos, sampleCount, /* scalar */ data[0], normal);
        output.pixels[3 * (y * output.width + x) + 0] = value[0];
        output.pixels[3 * (y * output.width + x) + 1] = value[1];
        output.pixels[3 * (y * output.width + x) + 2] = value[2];
      }
    }
  }
}

// ------------------------------------------------------------------

}  // namespace example
