#include <emscripten/bind.h>

#define TINYEXR_IMPLEMENTATION
#include "tinyexr.h"

// Simple C++ class for Emscripten
class EXRLoader
{
 public:
	EXRLoader() {}
	~EXRLoader() {}

	const float *image() const {
		return image_.data();
	}

	std::vector<float> image_;
};

EMSCRIPTEN_BINDINGS(tinyexr_module) {
    emscripten::class_<EXRLoader>("EXRLoader")
		.function("image", &EXRLoader::image, emscripten::allow_raw_pointers());
}
