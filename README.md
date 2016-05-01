# Tiny OpenEXR image library.

![Example](https://github.com/syoyo/tinyexr/blob/master/asakusa.png?raw=true)

[![AppVeyor build status](https://ci.appveyor.com/api/projects/status/k07ftfe4ph057qau/branch/master?svg=true)](https://ci.appveyor.com/project/syoyo/tinyexr/branch/master)

[![Travis build Status](https://travis-ci.org/syoyo/tinyexr.svg)](https://travis-ci.org/syoyo/tinyexr)

[![Coverity Scan Build Status](https://scan.coverity.com/projects/5827/badge.svg)](https://scan.coverity.com/projects/5827)

`tinyexr` is a small, single header-only library to load and save OpenEXR(.exr) images.
`tinyexr` is written in portable C++(no library dependency except for STL), thus `tinyexr` is good to embed into your application.
To use `tinyexr`, simply copy `tinyexr.h` into your project.

`tinyexr` currently supports:

* OpenEXR version 1.x.
* Normal image
  * Scanline format.
  * Uncompress("compress" = 0), RLE("compress" = 1), ZIPS("compress" = 2), ZIP compression("compress" = 3) and PIZ compression("compress" = 4).
  * Half/Uint/Float pixel type.
  * Custom attributes(up to 128)
* Deep image
  * Scanline format.
  * ZIPS compression("compress" = 2).
  * Half, float pixel type.
* Litte endian machine.
* Limited support for big endian machine.
  * read/write scalinel image.
* C interface.
  * You can easily write language bindings(e.g. golang)
* EXR saving
  * with ZIP compression.
* JavaScript library
  * Through emscripten.

# Use case 

* mallie https://github.com/lighttransport/mallie
* Cinder 0.9.0 https://libcinder.org/notes/v0.9.0
* Piccante(develop branch) http://piccantelib.net/
* Your project here!

## Examples

* [examples/deepview/](examples/deepview) Deep image view
* [examples/rgbe2exr/](examples/rgbe2exr) .hdr to EXR converter
* [examples/exr2rgbe/](examples/exr2rgbe) EXR to .hdr converter

## Usage

NOTE: **API is still subject to change**. See the source code for details.

Include `tinyexr.h` with `TINYEXR_IMPLEMENTATION` flag(do this only for **one** .cc file).

```
#define TINYEXR_IMPLEMENTATION
#include "tinyexr.h"
```

### Quickly reading RGB(A) EXR file.

```
  const char* input = "asakusa.exr";
  float* out; // width * height * RGBA
  int width;
  int height;
  const char* err;

  int ret = LoadEXR(&out, &width, &height, input, &err);
```

### Loading Singlepart EXR from a file.

Scanline and tiled format are supported.

```
  // 1. Read EXR version.
  EXRVersion exr_version;

  int ret = ParseEXRVersionFromFile(&exr_version, argv[1]);
  if (ret != 0) {
    fprintf(stderr, "Invalid EXR file: %s\n", argv[1]);
    return -1;
  }

  if (exr_version.multipart) {
    // must be multipart flag is false.
    return -1;
  }

  // 2. Read EXR header
  EXRHeader exr_header;
  InitEXRHeader(&exr_header);

  ret = ParseEXRHeaderFromFile(&exr_header, &exr_version, argv[1], &err);
  if (ret != 0) {
    fprintf(stderr, "Parse EXR err: %s\n", err);
    return ret;
  }

  // // Read HALF channel as FLOAT.
  // for (int i = 0; i < exr_header.num_channels; i++) {
  //   if (exr_header.pixel_types[i] == TINYEXR_PIXELTYPE_HALF) {
  //     exr_header.requested_pixel_types[i] = TINYEXR_PIXELTYPE_FLOAT;
  //   }
  // }

  EXRImage exr_image;
  InitEXRImage(&exr_image);

  ret = LoadEXRImageFromFile(&exr_image, &exr_header, argv[1], &err);
  if (ret != 0) {
    fprintf(stderr, "Load EXR err: %s\n", err);
    return ret;
  }

  // 3. Access image data
  // `exr_image.images` will be filled when EXR is scanline format.
  // `exr_image.tiled` will be filled when EXR is tiled format.

  // 4. Free image data
  FreeEXRImage(&exr_image);
```

### Loading Multipart EXR from a file.

Scanline and tiled format are supported.

```
  // 1. Read EXR version.
  EXRVersion exr_version;

  int ret = ParseEXRVersionFromFile(&exr_version, argv[1]);
  if (ret != 0) {
    fprintf(stderr, "Invalid EXR file: %s\n", argv[1]);
    return -1;
  }

  if (!exr_version.multipart) {
    // must be multipart flag is true.
    return -1;
  }

  // 2. Read EXR headers in the EXR.
  EXRHeader **exr_headers; // list of EXRHeader pointers.
  int num_exr_headers;

  // Memory for EXRHeader is allocated inside of ParseEXRMultipartHeaderFromFile,
  ret = ParseEXRMultipartHeaderFromFile(&exr_headers, &num_exr_headers, &exr_version, argv[1], &err);
  if (ret != 0) {
    fprintf(stderr, "Parse EXR err: %s\n", err);
    return ret;
  }

  printf("num parts = %d\n", num_exr_headers);


  // 3. Load images.

  // Prepare array of EXRImage.
  std::vector<EXRImage> images(num_exr_headers);
  for (int i =0; i < num_exr_headers; i++) {
    InitEXRImage(&images[i]);
  }

  ret = LoadEXRMultipartImageFromFile(&images.at(0), const_cast<const EXRHeader**>(exr_headers), num_exr_headers, argv[1], &err);
  if (ret != 0) {
    fprintf(stderr, "Parse EXR err: %s\n", err);
    return ret;
  }

  printf("Loaded %d part images\n", num_exr_headers);

  // 4. Access image data
  // `exr_image.images` will be filled when EXR is scanline format.
  // `exr_image.tiled` will be filled when EXR is tiled format.

  // 5. Free images
  for (int i =0; i < num_exr_headers; i++) {
    FreeEXRImage(&images.at(i));
  }

  // 6. Free headers.
  for (int i =0; i < num_exr_headers; i++) {
    FreeEXRHeader(exr_headers[i]);
    free(exr_headers[i]);
  }
  free(exr_headers);


Saving Scanline EXR file.

```
  // See `examples/rgbe2exr/` for more details.
  bool SaveEXR(const float* rgb, int width, int height, const char* outfilename) {

    EXRHeader header;
    InitEXRHeader(&header);

    EXRImage image;
    InitEXRImage(&image);

    image.num_channels = 3;

    std::vector<float> images[3];
    images[0].resize(width * height);
    images[1].resize(width * height);
    images[2].resize(width * height);

    // Split RGBRGBRGB... into R, G and B layer
    for (int i = 0; i < width * height; i++) {
      images[0][i] = rgb[3*i+0];
      images[1][i] = rgb[3*i+1];
      images[2][i] = rgb[3*i+2];
    }

    float* image_ptr[3];
    image_ptr[0] = &(images[2].at(0)); // B
    image_ptr[1] = &(images[1].at(0)); // G
    image_ptr[2] = &(images[0].at(0)); // R

    image.images = (unsigned char**)image_ptr;
    image.width = width;
    image.height = height;

    header.num_channels = 3;
    header.channels = (EXRChannelInfo *)malloc(sizeof(EXRChannelInfo) * header.num_channels); 
    // Must be BGR(A) order, since most of EXR viewers expect this channel order.
    strncpy(header.channels[0].name, "B", 255); header.channels[0].name[strlen("B")] = '\0';
    strncpy(header.channels[1].name, "G", 255); header.channels[1].name[strlen("G")] = '\0';
    strncpy(header.channels[2].name, "R", 255); header.channels[2].name[strlen("R")] = '\0';

    header.pixel_types = (int *)malloc(sizeof(int) * header.num_channels); 
    header.requested_pixel_types = (int *)malloc(sizeof(int) * header.num_channels);
    for (int i = 0; i < header.num_channels; i++) {
      header.pixel_types[i] = TINYEXR_PIXELTYPE_FLOAT; // pixel type of input image
      header.requested_pixel_types[i] = TINYEXR_PIXELTYPE_HALF; // pixel type of output image to be stored in .EXR
    }

    const char* err;
    int ret = SaveEXRImageToFile(&image, &header, argv[2], &err);
    if (ret != TINYEXR_SUCCESS) {
      fprintf(stderr, "Save EXR err: %s\n", err);
      return ret;
    }
    printf("Saved exr file. [ %s ] \n", argv[2]);

    free(rgb);

    free(header.channels);
    free(header.pixel_types);
    free(header.requested_pixel_types);

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

### deepview

`examples/deepview` is simple deep image viewer in OpenGL.

![DeepViewExample](https://github.com/syoyo/tinyexr/blob/master/examples/deepview/deepview_screencast.gif?raw=true)

## TinyEXR extension

### ZFP

TinyEXR adds ZFP compression as an experimemtal support(Linux and MacOSX only).


    $ git submodule update --init

Then build ZFP

    $ cd dep/ZFP
    $ mkdir -p lib   # Create `lib` directory if not exist
    $ make

Set `1` to TINYEXT_USE_ZFP define in `tinyexr.h`

Build your app with linking `deps/ZFP/lib/libzfp.a`

## TODO

Contribution is welcome!

- [ ] Compression
  - [ ] B44?
  - [ ] B44A?
  - [ ] PIX24?
- [ ] Custom attributes
  - [x] Normal image(EXR 1.x)
  - [ ] Deep image(EXR 2.x)
- [ ] JavaScript library
  - [ ] LoadEXRFromMemory
  - [ ] SaveMultiChannelEXR
  - [ ] Deep image save/load
- [ ] Write from/to memory buffer.
  - [ ] Deep image save/load
- [ ] Tile format.
  - [x] Tile format with no LoD(load).
  - [ ] Tile format with LoD(load).
  - [ ] Tile format with no LoD(save).
  - [ ] Tile format with LoD(save).
- [ ] Support for custom compression type.
  - [ ] zfp compression(Not in OpenEXR spec, though)
- [x] Multi-channel.
- [ ] Multi-part(EXR2.0)
  - [x] Load multi-part image
  - [ ] Load multi-part deep image
- [ ] Line order.
  - [x] Increasing, decreasing(load)
  - [ ] Random?
  - [ ] Increasing, decreasing(save)
- [ ] Pixel format(UINT, FLOAT).
  - [x] UINT, FLOAT(load)
  - [x] UINT, FLOAT(deep load)
  - [x] UINT, FLOAT(save)
  - [ ] UINT, FLOAT(deep save)
- [ ] Support for big endian machine.
  - [ ] Loading multi-part channel EXR
  - [ ] Saving multi-part channel EXR
  - [ ] Loading deep image
  - [ ] Saving deep image
- [ ] Optimization
  - [ ] ISPC?
  - [x] OpenMP multi-threading in EXR loading.
  - [x] OpenMP multi-threading in EXR saving.
  - [ ] OpenMP multi-threading in deep image loading.
  - [ ] OpenMP multi-threading in deep image saving.

## Similar or related projects

* miniexr: https://github.com/aras-p/miniexr (Write OpenEXR)
* stb_image_resize.h: https://github.com/nothings/stb (Good for HDR image resizing)

## License

3-clause BSD

`tinyexr` uses miniz, which is developed by Rich Geldreich <richgel99@gmail.com>, and licensed under public domain.

`tinyexr` tools uses stb, which is licensed under public domain: https://github.com/nothings/stb
`tinyexr` uses some code from OpenEXR, which is licensed under 3-clause BSD license.

## Author(s)

Syoyo Fujita(syoyo@lighttransport.com)

## Contributor(s)

* Matt Ebb (http://mattebb.com) : deep image example. Thanks!
* Matt Pharr (http://pharr.org/matt/) : Testing tinyexr with OpenEXR(IlmImf). Thanks! 
* Andrew Bell (https://github.com/andrewfb) & Richard Eakin (https://github.com/richardeakin) : Improving TinyEXR API. Thanks!
* Mike Wong (https://github.com/mwkm) : ZIPS compression support in loading. Thanks!
