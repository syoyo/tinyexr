#ifndef __TINYEXR_H__
#define __TINYEXR_H__

#ifdef __cplusplus
extern "C" {
#endif

typedef struct {
  const char** channel_names;
  int         num_channels;
  float***    image;              // image[channels][scanlines][samples]
  int**       offset_table;       // offset_table[scanline][offsets]
  int         width;
  int         height;
} DeepImage;

// Loads single-frame OpenEXR image.
// Application must free image data as returned by `out_rgba`
// Result image format is: float x RGBA x width x hight
// returns error string in `err` when there's an error
extern int LoadEXR(float **out_rgba, int *width, int *height,
                   const char *filename, const char **err);

// Loads single-frame OpenEXR deep image.
// Application must free image data as returned by `out_deep_image`
extern int LoadDeepEXR(
  DeepImage*    out_image,
  const char*   filename,
  const char**  err);

#ifdef __cplusplus
}
#endif

#endif // __TINYEXR_H__
