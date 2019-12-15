#ifndef EXR_IO_H_
#define EXR_IO_H_

#include "tinyexr.h"

namespace exrio
{

bool GetEXRLayers(const char *filename);

bool LoadEXRRGBA(float** rgba, int* w, int *h, const char* filename, const char* layername = nullptr);

}


#endif // EXR_IO_H_
