// Test for Issue #230: Partial fread() handling in fallback path
// This test specifically disables memory mapping to test the fread fallback

#include <cstdio>
#include <cstdlib>
#include <iostream>

// Force the fallback fread path by undefining memory mapping
#undef TINYEXR_USE_WIN32_MMAP
#undef TINYEXR_USE_POSIX_MMAP

#define TINYEXR_IMPLEMENTATION
#include "../../tinyexr.h"

int main(int argc, char** argv) {
    const char* test_files[] = {
        "./regression/000-issue194.exr",  // 206KB file
        "./regression/issue-160-piz-decode.exr",  // 152KB file
        "./regression/flaga.exr",
        "./regression/2by2.exr",
        "./regression/日本語.exr"  // UTF-8 filename test
    };

    int test_count = sizeof(test_files) / sizeof(test_files[0]);
    int passed = 0;
    int failed = 0;

    std::cout << "Testing TinyEXR with fallback fread() path (no memory mapping)" << std::endl;
    std::cout << "This tests the fix for issue #230: partial fread() handling" << std::endl;
    std::cout << std::endl;

    for (int i = 0; i < test_count; i++) {
        const char* filename = test_files[i];
        std::cout << "Test " << (i + 1) << "/" << test_count << ": " << filename << " ... ";

        EXRVersion exr_version;
        int ret = ParseEXRVersionFromFile(&exr_version, filename);

        if (ret != TINYEXR_SUCCESS) {
            std::cout << "FAILED (ParseEXRVersionFromFile returned " << ret << ")" << std::endl;
            failed++;
            continue;
        }

        EXRHeader exr_header;
        InitEXRHeader(&exr_header);
        const char* err = NULL;

        ret = ParseEXRHeaderFromFile(&exr_header, &exr_version, filename, &err);
        if (ret != TINYEXR_SUCCESS) {
            std::cout << "FAILED (ParseEXRHeaderFromFile: " << (err ? err : "unknown error") << ")" << std::endl;
            if (err) FreeEXRErrorMessage(err);
            failed++;
            continue;
        }

        EXRImage exr_image;
        InitEXRImage(&exr_image);

        ret = LoadEXRImageFromFile(&exr_image, &exr_header, filename, &err);
        if (ret != TINYEXR_SUCCESS) {
            std::cout << "FAILED (LoadEXRImageFromFile: " << (err ? err : "unknown error") << ")" << std::endl;
            if (err) FreeEXRErrorMessage(err);
            FreeEXRHeader(&exr_header);
            failed++;
            continue;
        }

        // Verify we got valid image data
        if (exr_image.width <= 0 || exr_image.height <= 0 || !exr_image.images) {
            std::cout << "FAILED (invalid image data)" << std::endl;
            FreeEXRImage(&exr_image);
            FreeEXRHeader(&exr_header);
            failed++;
            continue;
        }

        std::cout << "PASSED (width=" << exr_image.width
                  << ", height=" << exr_image.height
                  << ", channels=" << exr_header.num_channels << ")" << std::endl;

        FreeEXRImage(&exr_image);
        FreeEXRHeader(&exr_header);
        passed++;
    }

    std::cout << std::endl;
    std::cout << "Results: " << passed << " passed, " << failed << " failed" << std::endl;

    return (failed == 0) ? 0 : 1;
}
