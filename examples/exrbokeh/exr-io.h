#ifndef EXR_IO_H_
#define EXR_IO_H_

#include "tinyexr.h"

namespace exrio
{

bool LoadEXRRGBA(float** rgba, int* w, int *h, const char* filename);

}


#endif // EXR_IO_H_
