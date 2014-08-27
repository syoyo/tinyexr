# Tiny OpenEXR image loader.

![Example](https://github.com/syoyo/tinyexr/blob/master/asakusa.png?raw=true)

`tinyexr` is a small library to load OpenEXR(.exr) image.
TO use `tinyexr`, simply copy `tinyexr.cc` and `tinyexr.h` into your project.

`tinyexr` currently supports:

* OpenEXR version 1.x.
* RGB(A) channel.
* Scanline format.
* ZIP compression.
* Half pixel type.
* Litte endian machine.

## TODO

* Tile format.
* Support for various compression type.
* Multi-channel.
* Pixel order.
* EXR 2.0(deep image).
* Big endian machine.

## License

3-clause BSD

`tinyexr` uses miniz, which is developed by Rich Geldreich <richgel99@gmail.com>, and licensed under public domain.

## Author(s)

Syoyo Fujita(syoyo@lighttransport.com)
