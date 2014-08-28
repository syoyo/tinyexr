# Tiny OpenEXR image loader.

![Example](https://github.com/syoyo/tinyexr/blob/master/asakusa.png?raw=true)

`tinyexr` is a small library to load OpenEXR(.exr) image.
`tinyexr` is written in portable C++(no library dependency except for STL), thus `tinyext` is good to embed into your application.
To use `tinyexr`, simply copy `tinyexr.cc` and `tinyexr.h` into your project.

`tinyexr` currently supports:

* OpenEXR version 1.x.
* RGB(A) channel.
* Scanline format.
* Uncompress("compress" = 0) and ZIP compression("compress" = 3).
* Half pixel type.
* Litte endian machine.
* C interface

## Usage

```
  const char* input = "asakusa.exr";
  float* out;
  int width;
  int height;
  const char* err;

  int ret = LoadEXR(&out, &width, &height, input, &err);
```

## TODO

* Tile format.
* Support for various compression type.
* Multi-channel.
* Pixel order.
* EXR 2.0(deep image).
* Big endian machine.

## Similar projects

* miniexr: https://github.com/aras-p/miniexr (Write OpenEXR)

## License

3-clause BSD

`tinyexr` uses miniz, which is developed by Rich Geldreich <richgel99@gmail.com>, and licensed under public domain.

## Author(s)

Syoyo Fujita(syoyo@lighttransport.com)
