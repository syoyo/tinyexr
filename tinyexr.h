#ifndef __TINYEXR_H__
#define __TINYEXR_H__

#ifdef __cplusplus
extern "C" {
#endif

// Application must free image data as returned by `out_rgba`
// Result image format is: float x RGBA x width x hight
// returns error string in `err` when there's an error
extern int LoadEXR(float** out_rgba, int* width, int* height, const char* filename, const char** err);

#ifdef __cplusplus
}
#endif

#endif // __TINYEXR_H__
