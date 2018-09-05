# Simple HDR cubemap to longlat(longitude latitude. or known as equirectangular) converter.

## Requirements

* C++11 compiler

## Coordinate definition.

* Y-up
* Right-handed
* 270 angle in phi as -z

## Usage

Assume cubemap image is given by 6 images(6 faces).

## Supported input image format

* RGBM(Filament's RGBM encoding. Multiplier is 16, and gamma corrected)
* EXR

## Supported output image format

* RGBM(Filament's RGBM encoding. Multiplier is 16, and gamma corrected)
* EXR
* RGBE

```
$ cube2longloat nx.exr ny.exr nz.exr px.exr py.exr pz.exr output.exr
```

## TODO

* Single cubemap image(cross layout)

