#!/bin/sh

# Export EXR loader/saver function to JS.
# TODO: export more functions
~/work/emsdk_portable/emscripten/1.30.0/em++ -Os tinyexr.cc --memory-init-file 0 -s TOTAL_MEMORY=67108864 -s EXPORTED_FUNCTIONS="['_ParseEXRHeaderFromMemory', '_LoadEXRFromMemory']" -o tinyexr.js
