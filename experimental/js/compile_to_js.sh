#!/bin/sh

EMCC=em++

# Export EXR loader/saver function to JS.
# TODO: export more functions
${EMCC} -std=c++11 -O0 -I../../ binding.cc --memory-init-file 0 -s TOTAL_MEMORY=67108864 -s EXPORTED_FUNCTIONS="['_ParseEXRHeaderFromMemory', '_LoadEXRFromMemory']" -o tinyexr.js
