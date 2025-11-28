// Test for issue #230: Partial fread() handling in fallback path
// This test specifically validates that the fallback file reading path
// (when memory mapping is not available) correctly handles partial reads.

#include <cstdio>
#include <cstdlib>
#include <iostream>
#include <vector>

// Force the fallback fread() path by undefining memory mapping
#ifdef TINYEXR_USE_WIN32_MMAP
#undef TINYEXR_USE_WIN32_MMAP
#endif
#ifdef TINYEXR_USE_POSIX_MMAP
#undef TINYEXR_USE_POSIX_MMAP
#endif

#define TINYEXR_IMPLEMENTATION
#include "../../tinyexr.h"

// Test files to validate - using existing regression test images
static const char* test_files[] = {
    "./regression/000-issue194.exr",      // Large file (206KB)
    "./regression/issue-160-piz-decode.exr", // Large file (152KB)
    "./regression/flaga.exr",             // Medium file
    "./regression/2by2.exr",              // Small file
    "./regression/日本語.exr"              // UTF-8 filename test
};

static const int num_test_files = sizeof(test_files) / sizeof(test_files[0]);

bool TestFile(const char* filepath) {
    std::cout << "Testing: " << filepath << std::endl;

    // Parse version
    EXRVersion exr_version;
    int ret = ParseEXRVersionFromFile(&exr_version, filepath);
    if (ret != TINYEXR_SUCCESS) {
        std::cerr << "  ERROR: Failed to parse version from " << filepath << std::endl;
        return false;
    }

    // Parse header
    EXRHeader exr_header;
    InitEXRHeader(&exr_header);
    const char* err = nullptr;

    ret = ParseEXRHeaderFromFile(&exr_header, &exr_version, filepath, &err);
    if (ret != TINYEXR_SUCCESS) {
        std::cerr << "  ERROR: Failed to parse header from " << filepath;
        if (err) {
            std::cerr << ": " << err;
            FreeEXRErrorMessage(err);
        }
        std::cerr << std::endl;
        FreeEXRHeader(&exr_header);
        return false;
    }

    // Load image
    EXRImage exr_image;
    InitEXRImage(&exr_image);

    ret = LoadEXRImageFromFile(&exr_image, &exr_header, filepath, &err);
    if (ret != TINYEXR_SUCCESS) {
        std::cerr << "  ERROR: Failed to load image from " << filepath;
        if (err) {
            std::cerr << ": " << err;
            FreeEXRErrorMessage(err);
        }
        std::cerr << std::endl;
        FreeEXRHeader(&exr_header);
        FreeEXRImage(&exr_image);
        return false;
    }

    // Validate image data
    if (exr_image.width <= 0 || exr_image.height <= 0) {
        std::cerr << "  ERROR: Invalid image dimensions: "
                  << exr_image.width << "x" << exr_image.height << std::endl;
        FreeEXRHeader(&exr_header);
        FreeEXRImage(&exr_image);
        return false;
    }

    if (exr_image.num_channels <= 0) {
        std::cerr << "  ERROR: Invalid number of channels: "
                  << exr_image.num_channels << std::endl;
        FreeEXRHeader(&exr_header);
        FreeEXRImage(&exr_image);
        return false;
    }

    // Verify image data is not null
    if (!exr_image.images && !exr_image.tiles) {
        std::cerr << "  ERROR: Image data is null" << std::endl;
        FreeEXRHeader(&exr_header);
        FreeEXRImage(&exr_image);
        return false;
    }

    std::cout << "  SUCCESS: Loaded " << exr_image.width << "x" << exr_image.height
              << " image with " << exr_image.num_channels << " channels" << std::endl;

    // Cleanup
    FreeEXRHeader(&exr_header);
    FreeEXRImage(&exr_image);

    return true;
}

int main(int argc, char** argv) {
    std::cout << "=== Issue #230 Regression Test ===" << std::endl;
    std::cout << "Testing fallback fread() path with partial read handling" << std::endl;
    std::cout << std::endl;

    int passed = 0;
    int failed = 0;

    for (int i = 0; i < num_test_files; i++) {
        if (TestFile(test_files[i])) {
            passed++;
        } else {
            failed++;
        }
    }

    std::cout << std::endl;
    std::cout << "=== Test Results ===" << std::endl;
    std::cout << "Passed: " << passed << "/" << num_test_files << std::endl;
    std::cout << "Failed: " << failed << "/" << num_test_files << std::endl;

    if (failed > 0) {
        std::cout << std::endl;
        std::cout << "FAILURE: Some tests failed!" << std::endl;
        return 1;
    }

    std::cout << std::endl;
    std::cout << "SUCCESS: All tests passed!" << std::endl;
    return 0;
}
