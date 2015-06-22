# Tiny OpenEXR image library.

![Example](https://github.com/syoyo/tinyexr/blob/master/asakusa.png?raw=true)

[![Build status](https://ci.appveyor.com/api/projects/status/k07ftfe4ph057qau/branch/master?svg=true)](https://ci.appveyor.com/project/syoyo/tinyexr/branch/master)

`tinyexr` is a small library to load and save OpenEXR(.exr) images.
`tinyexr` is written in portable C++(no library dependency except for STL), thus `tinyexr` is good to embed into your application.
To use `tinyexr`, simply copy `tinyexr.cc` and `tinyexr.h` into your project.

`tinyexr` currently supports:

* OpenEXR version 1.x.
* Normal image
  * Scanline format.
  * Uncompress("compress" = 0) and ZIP compression("compress" = 3).
  * Half/Uint/Float pixel type.
* Deep image
  * Scanline format.
  * ZIPS compression("compress" = 2).
  * Half, float pixel type.
* Litte endian machine.
* Limited support for big endian machine.
  * read/write normal image.
* C interface.
  * You can easily write language bindings(e.g. golang)
* EXR saving
  * with ZIP compression.
* JavaScript library
  * Through emscripten.

# Use case 

* mallie https://github.com/lighttransport/mallie
* PBRT v3 https://github.com/mmp/pbrt-v3
* Your project here!

## Usage

NOTE: **API is still subject to change**. See the source code for details.

Quickly reading RGB(A) EXR file.

```
  const char* input = "asakusa.exr";
  float* out; // width * height * RGBA
  int width;
  int height;
  const char* err;

  int ret = LoadEXR(&out, &width, &height, input, &err);
```

Loading EXR from a file.

```
  const char* input = "asakusa.exr";
  const char* err;

  EXRImage exrImage;
  InitEXRImage(&exrImage);

  int ret = ParseMultiChannelEXRHeaderFromFile(&exrImage, input, &err);
  if (ret != 0) {
    fprintf(stderr, "Parse EXR err: %s\n", err);
    return;
  }

  //// Uncomment if you want reading HALF image as FLOAT.
  //for (int i = 0; i < exrImage.num_channels; i++) {
  //  if (exrImage.pixel_types[i] = TINYEXR_PIXELTYPE_HALF) {
  //    exrImage.requested_pixel_types[i] = TINYEXR_PIXELTYPE_FLOAT;
  //  }
  //}

  ret = LoadMultiChannelEXRFromFile(&exrImage, input, &err);
  if (ret != 0) {
    fprintf(stderr, "Load EXR err: %s\n", err);
    return;
  }
```

Saving EXR file.

```
  bool SaveEXR(const float* rgb, int width, int height, const char* outfilename) {

    float* channels[3];

    EXRImage image;
    InitEXRImage(&image);

    image.num_channels = 3;

    // Must be BGR(A) order, since most of EXR viewers expect this channel order.
    const char* channel_names[] = {"B", "G", "R"}; // "B", "G", "R", "A" for RGBA image

    std::vector<float> images[3];
    images[0].resize(width * height);
    images[1].resize(width * height);
    images[2].resize(width * height);

    for (int i = 0; i < width * height; i++) {
      images[0][i] = rgb[3*i+0];
      images[1][i] = rgb[3*i+1];
      images[2][i] = rgb[3*i+2];
    }

    float* image_ptr[3];
    image_ptr[0] = &(images[2].at(0)); // B
    image_ptr[1] = &(images[1].at(0)); // G
    image_ptr[2] = &(images[0].at(0)); // R

    image.channel_names = channel_names;
    image.images = image_ptr;
    image.width = gWidth;
    image.height = gHeight;

    image.pixel_types = (int *)malloc(sizeof(int) * image.num_channels);
    image.requested_pixel_types = (int *)malloc(sizeof(int) * image.num_channels);
    for (int i = 0; i < image.num_channels; i++) {
      image.pixel_types[i] = TINYEXR_PIXELTYPE_FLOAT;
      image.requested_pixel_types[i] = TINYEXR_PIXELTYPE_FLOAT;
    }

    ret = SaveMultiChannelEXRToFile(&image, outfilename, &err);
    if (ret != 0) {
      fprintf(stderr, "Save EXR err: %s\n", err);
      return ret;
    }
    printf("Saved exr file. [ %s ] \n", outfilename);
    return ret;

  }
```


Reading deep image EXR file.
See `example/deepview` for actual usage.

```
  const char* input = "deepimage.exr";
  const char* err;
  DeepImage deepImage;

  int ret = LoadDeepEXR(&deepImage, input, &err);

  // acccess to each sample in the deep pixel.
  for (int y = 0; y < deepImage.height; y++) {
    int sampleNum = deepImage.offset_table[y][deepImage.width-1];
    for (int x = 0; x < deepImage.width-1; x++) {
      int s_start = deepImage.offset_table[y][x];
      int s_end   = deepImage.offset_table[y][x+1];
      if (s_start >= sampleNum) {
        continue;
      }
      s_end = (s_end < sampleNum) ? s_end : sampleNum;
      for (int s = s_start; s < s_end; s++) {
        float val = deepImage.image[depthChan][y][s];
        ...
      }
    }
  }

```

### Example

#### deepview 

`examples/deepview` is simple deep image viewer in OpenGL.

![DeepViewExample](https://github.com/syoyo/tinyexr/blob/master/examples/deepview/deepview_screencast.gif?raw=true)

## TODO

Contribution is welcome!

- [ ] JavaScript library
  - [x] LoadEXRFromMemory
  - [ ] SaveMultiChannelEXR
  - [ ] Deep image save/load
- [ ] Write from/to memory buffer.
  - [x] SaveMultiChannelEXR
  - [x] LoadMultiChannelEXR
  - [ ] Deep image save/load
- [ ] Tile format.
- [ ] Support for various compression type.
- [x] Multi-channel.
- [ ] Multi-part(EXR2.0)
- [x] Line order.
- [ ] Pixel format(UINT, FLOAT).
  - [x] UINT, FLOAT(load)
  - [x] UINT, FLOAT(deep load)
  - [x] UINT, FLOAT(save)
  - [ ] UINT, FLOAT(deep save)
- [ ] Full support for big endian machine.
  - [x] Loading multi channel EXR
  - [x] Saving multi channel EXR
  - [ ] Loading deep image
  - [ ] Saving deep image
- [ ] Optimization
  - [ ] ISPC?
  - [x] OpenMP multi-threading in EXR loading.
  - [x] OpenMP multi-threading in EXR saving.
  - [ ] OpenMP multi-threading in deep image loading.
  - [ ] OpenMP multi-threading in deep image saving.

## Similar projects

* miniexr: https://github.com/aras-p/miniexr (Write OpenEXR)

## License

3-clause BSD

`tinyexr` uses miniz, which is developed by Rich Geldreich <richgel99@gmail.com>, and licensed under public domain.

## Author(s)

Syoyo Fujita(syoyo@lighttransport.com)

## Contributor(s)

* Matt Ebb (http://mattebb.com) : deep image example. Thanks!
* Matt Pharr (http://pharr.org/matt/) : Testing tinyexr with OpenEXR(IlmImf). Thanks! 
