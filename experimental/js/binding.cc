#include <vector>

#include <emscripten/bind.h>

#define TINYEXR_IMPLEMENTATION
#include "tinyexr.h"

using namespace emscripten;

// Simple C++ class for Emscripten
class EXRLoader
{
 public:
	EXRLoader() {}
	~EXRLoader() {}

	int getInt() {
		return 1;
	}

	const std::vector<float> &image() const {
		return image_;
	}

 private:
	std::vector<float> image_;
};

// Register STL
EMSCRIPTEN_BINDINGS(stl_wrappters) {
	register_vector<float>("VectorFloat");
}

EMSCRIPTEN_BINDINGS(tinyexr_module) {
    class_<EXRLoader>("EXRLoader")
    .constructor()
		.function("image", &EXRLoader::image, allow_raw_pointers())
		.function("getInt", &EXRLoader::getInt);
}
