# Emscripten build of the TinyEXR v3 browser viewer (web/viewer/).
#
# Configure with emcmake so the toolchain is the Emscripten one:
#
#   emcmake cmake -S . -B build -DCMAKE_BUILD_TYPE=MinSizeRel
#   cmake --build build
#
# Produces build/exr_viewer.mjs + build/exr_viewer.wasm (ES6 module). The
# build.sh wrapper copies them next to index.html.

cmake_minimum_required(VERSION 3.13)
project(exr_viewer C)

if(NOT EMSCRIPTEN)
  message(FATAL_ERROR
    "Configure with emcmake, e.g. `emcmake cmake -S . -B build`. "
    "This target only builds with the Emscripten toolchain.")
endif()

# Default to a small build; -Oz is added explicitly below regardless.
if(NOT CMAKE_BUILD_TYPE)
  set(CMAKE_BUILD_TYPE MinSizeRel CACHE STRING "" FORCE)
endif()

set(CMAKE_C_STANDARD 11)
set(CMAKE_C_STANDARD_REQUIRED ON)

set(TINYEXR_ROOT "${CMAKE_CURRENT_SOURCE_DIR}/../..")

# v3 core sources: all of src/*.c except the stdio + freestanding shims (matches
# the Makefile's V3_CORE_SRC), plus the bundled zstd codec.
file(GLOB V3_SOURCES "${TINYEXR_ROOT}/src/*.c")
list(FILTER V3_SOURCES EXCLUDE REGEX "/exr_stdio\\.c$")
list(FILTER V3_SOURCES EXCLUDE REGEX "/exr_freestanding\\.c$")

set(ZSTD_SOURCE "${TINYEXR_ROOT}/deps/zstd/tinyexr_zstd.c")

add_executable(exr_viewer
  exr_viewer_wasm.c
  ${V3_SOURCES}
  ${ZSTD_SOURCE})

target_include_directories(exr_viewer PRIVATE
  "${TINYEXR_ROOT}/include"
  "${TINYEXR_ROOT}/src"
  "${TINYEXR_ROOT}/deps/zstd")

# Size-first optimization. -Oz on both compile and link; warnings off (the core
# is exercised by its own test suite, not this example build).
target_compile_options(exr_viewer PRIVATE -Oz -w)

set_target_properties(exr_viewer PROPERTIES SUFFIX ".mjs")

target_link_options(exr_viewer PRIVATE
  -Oz
  "-sMODULARIZE=1"
  "-sEXPORT_ES6=1"
  "-sENVIRONMENT=web"
  "-sFILESYSTEM=0"
  "-sALLOW_MEMORY_GROWTH=1"
  "-sEXPORTED_FUNCTIONS=['_exrv_open','_exrv_close','_exrv_num_parts','_exrv_header_json','_exrv_select','_exrv_select_channels','_exrv_select_ycc','_exrv_level_width','_exrv_level_height','_exrv_decode_block','_exrv_rgba','_exrv_deep_load','_exrv_deep_points','_exrv_deep_count','_exrv_is_spectral','_exrv_spectral_open','_exrv_spectral_open_part','_exrv_spectral_width','_exrv_spectral_height','_exrv_spectral_wavelengths','_exrv_spectral_show','_exrv_spectral_composite','_exrv_spectral_pixel','_exrv_free','_malloc','_free']"
  "-sEXPORTED_RUNTIME_METHODS=['HEAPU8','HEAPF32','HEAP32','HEAPU32','UTF8ToString']")
