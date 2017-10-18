#include <vector>

#include <emscripten/bind.h>

#define TINYEXR_IMPLEMENTATION
#include "tinyexr.h"

using namespace emscripten;

// Simple C++ class for Emscripten
class EXRLoader
{
 public:
	///
	/// std::string can be used as UInt8Array in JS layer.
	///
	EXRLoader(const std::string &binary) {
		const float *ptr = reinterpret_cast<const float *>(binary.data());	

		float *rgba = nullptr;
		int width = -1;
		int height = -1;
		const char *err = nullptr;

		result_ = LoadEXRFromMemory(&rgba, &width, &height, reinterpret_cast<const unsigned char *>(binary.data()), binary.size(), &err);

		if (TINYEXR_SUCCESS == result_) {
			image_.resize(width * height * 4);
			memcpy(image_.data(), rgba, size_t(width * height * 4) * sizeof(float));
			free(rgba);
		}

	}
	~EXRLoader() {}

	const std::vector<float> &image() const {
		return image_;
	}

	bool ok() const {
		return (TINYEXR_SUCCESS == result_);
	}

 private:
	std::vector<float> image_;
	int result_;
};

// Register STL
EMSCRIPTEN_BINDINGS(stl_wrappters) {
	register_vector<float>("VectorFloat");
}

EMSCRIPTEN_BINDINGS(tinyexr_module) {
    class_<EXRLoader>("EXRLoader")
    .constructor<const std::string &>()
		.function("image", &EXRLoader::image, allow_raw_pointers())
		.function("ok", &EXRLoader::ok);
}
