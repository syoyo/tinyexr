#ifndef __TINYEXR_H__
#define __TINYEXR_H__

#ifdef __cplusplus
extern "C" {
#endif

// Loads single-frame OpenEXR image.
// Application must free image data as returned by `out_rgba`
// Result image format is: float x RGBA x width x hight
// returns error string in `err` when there's an error
extern int LoadEXR(float **out_rgba, int *width, int *height,
                   const char *filename, const char **err);

// Loads single-frame OpenEXR deep image.
// Application must free image data as returned by `out_deep_image`
extern int LoadDeepEXR(
  const char**  out_channel_names,
  int*          out_num_channel_names,
  float**       out_deep_image,
  int**         out_sample_offset,
  int*          width,
  int*          height,
  const char*   filename,
  const char **err);

#ifdef __cplusplus
}
#endif

#endif // __TINYEXR_H__
