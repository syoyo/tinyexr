# Simple HDR cubemap to longlat(longitude latitude. or known as equirectangular) converter.

## Requirements

* C++11 compiler

## Coordinate definition.

* Y-up
* Right-handed
* Center is -z

## Usage

Assume cubemap image is given by 6 images(6 faces).

```
$ ./cube2longlat px.exr nx.exr py.exr ny.exr pz.exr nz.exr 512 longlat.exr (phi_offset)
```

Optional `phi_offset` is used to add offset(by angle) to phi to rotate X and Z faces.


## Supported input image format

* [ ] RGBM(Filament's RGBM encoding. Multiplier is 16, and gamma corrected) Implemented but not tested.
* [x] EXR

## Supported output image format

* [ ] RGBM(Filament's RGBM encoding. Multiplier is 16, and gamma corrected) Implemented but not tested.
* [x] EXR
* [x] RGBE

## Note

When you create cubemap using Filament's cmgen https://github.com/google/filament/tree/master/tools/cmgen , its generated cubemap images are mirrored by X direction.
Use `--mirror` when invoking `cmgen` if required.

## TODO

* Single cubemap image(cross layout)
* Better antialiasing
* theta offset
* Mirroring.

