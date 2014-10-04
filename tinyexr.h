/*
Copyright (c) 2014, Syoyo Fujita
All rights reserved.

Redistribution and use in source and binary forms, with or without
modification, are permitted provided that the following conditions are met:
    * Redistributions of source code must retain the above copyright
      notice, this list of conditions and the following disclaimer.
    * Redistributions in binary form must reproduce the above copyright
      notice, this list of conditions and the following disclaimer in the
      documentation and/or other materials provided with the distribution.
    * Neither the name of the <organization> nor the
      names of its contributors may be used to endorse or promote products
      derived from this software without specific prior written permission.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND
ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
DISCLAIMED. IN NO EVENT SHALL <COPYRIGHT HOLDER> BE LIABLE FOR ANY
DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
(INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND
ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
(INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
*/
#ifndef __TINYEXR_H__
#define __TINYEXR_H__

#ifdef __cplusplus
extern "C" {
#endif

typedef struct {
  const char **channel_names;
  int num_channels;
  float ***image;     // image[channels][scanlines][samples]
  int **offset_table; // offset_table[scanline][offsets]
  int width;
  int height;
} DeepImage;

// Loads single-frame OpenEXR image.
// Application must free image data as returned by `out_rgba`
// Result image format is: float x RGBA x width x hight
// Return 0 if success
// Returns error string in `err` when there's an error
extern int LoadEXR(float **out_rgba, int *width, int *height,
                   const char *filename, const char **err);

// Saves floating point RGBA image as OpenEXR.
// Image is compressed with ZIP.
// Return 0 if success
// Returns error string in `err` when there's an error
extern int SaveEXR(const float *in_rgba, int width, int height, const char *filename,
            const char **err);

// NOT YET IMPLEMENTED:
// Loads multi-part OpenEXR image.
// Application must free image data as returned by `out_rgba`
// Result image format is: [parts][float x RGBA x width x hight]
// Return 0 if success
// Returns error string in `err` when there's an error
//extern int LoadMultiPartEXR(
//                  float ***out_rgba, int *num_parts, int *width, int *height,
//                  const char *filename, const char **err);

// Loads single-frame OpenEXR deep image.
// Application must free memory of variables in DeepImage(image, offset_table)
// Return 0 if success
// Returns error string in `err` when there's an error
extern int LoadDeepEXR(DeepImage *out_image, const char *filename,
                       const char **err);

// NOT YET IMPLEMENTED:
// Saves single-frame OpenEXR deep image.
// Return 0 if success
// Returns error string in `err` when there's an error
//extern int SaveDeepEXR(const DeepImage *in_image, const char *filename,
//                       const char **err);

// NOT YET IMPLEMENTED:
// Loads multi-part OpenEXR deep image.
// Application must free memory of variables in DeepImage(image, offset_table)
//extern int LoadMultiPartDeepEXR(DeepImage **out_image, int num_parts, const char *filename,
//                       const char **err);

#ifdef __cplusplus
}
#endif

#endif // __TINYEXR_H__
