# exrview

![ScreenShot](screenshots/exrview.png)

Simple cross-platform OpenEXR viewer using TinyEXR, bullet3's windows library and nukler UI library.
Currently only EXR image with RGB channels can be displayed.

## Requirements

* premake5
* Visual Studio 2015(2013 will work)
* OpenGL 2.x
* GTK+3(optional and Linux only. Used for file dialog support on Linux)

## Build on Windows

    $ premake5 vs2015

## Build on Linux

    $ premake5 gmake

If you want nativefiledialog support(File dialog UI), Install GTK+3 then,

    $ premake5 --with-gtk3nfd gmake

## Build on Mac

    $ premake5 gmake

## Usage

    $ ./bin/native/Release/exrview input.exr

## TODO

* [ ] Retina resolution
* [ ] Display arbitrary channel EXR
* [ ] Zoom and pan image
* [ ] Tone mapping

## Third party licenses

`OpenGLWindow` and `CommonInterfaces` is grabbed from bullet3, which is licensed under zlib lince.

https://github.com/bulletphysics/bullet://github.com/bulletphysics/bullet3

`ThirdPartyLibs/Glew/` is licensed under  licensed under the Modified BSD License, the Mesa 3-D License (MIT) and the Khronos License (MIT).

http://glew.sourceforge.net/

nuklear is licensed under MIT.

https://github.com/vurtun/nuklear

See `ThirdPartyLibs/nativefiledialog/LICENSE` for nativefiledialog license.
