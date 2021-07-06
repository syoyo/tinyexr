newoption {
   trigger     = "with-gtk3nfd",
   description = "Build with nativefiledialog support. GTK3 required(Linux only)"
}

sources = {
   "main.cc",
   "exr-io.cc",
   "../../deps/miniz/miniz.c"
}

-- premake4.lua
solution "EXRViewSolution"
   configurations { "Release", "Debug" }

   platforms { "native", "x64", "x32" }


   projectRootDir = os.getcwd() .. "/"
   dofile ("findOpenGLGlewGlut.lua")
   initOpenGL()
   initGlew()

   -- A project defines one build target
   project "exrview"
      kind "ConsoleApp"
      language "C++"
      files { sources }

      includedirs { "./", "../../", "../../deps/miniz" }

      if os.is("Windows") then
         defines { "USE_NATIVEFILEDIALOG" }
         files{
            "OpenGLWindow/Win32OpenGLWindow.cpp",
            "OpenGLWindow/Win32OpenGLWindow.h",
            "OpenGLWindow/Win32Window.cpp",
            "OpenGLWindow/Win32Window.h",
            }
         includedirs { "./ThirdPartyLibs/nativefiledialog/src/include/" }
         files  {
            "ThirdPartyLibs/nativefiledialog/src/nfd_common.c",
            "ThirdPartyLibs/nativefiledialog/src/nfd_win.cpp"
         }
      end
      if os.is("Linux") then
         files {
            "OpenGLWindow/X11OpenGLWindow.cpp",
            "OpenGLWindow/X11OpenGLWindows.h"
            }
         links {"X11", "pthread", "dl"}

         if _OPTIONS["with-gtk3nfd"] then -- NFD + GTK3
            defines { "USE_NATIVEFILEDIALOG" }
            includedirs { "./ThirdPartyLibs/nativefiledialog/src/include/" }
            buildoptions { "`pkg-config --cflags gtk+-3.0`" }
            linkoptions { "`pkg-config --libs gtk+-3.0`" }
            files  {
               "ThirdPartyLibs/nativefiledialog/src/nfd_common.c",
               "ThirdPartyLibs/nativefiledialog/src/nfd_gtk.c"
            }
         end

      end
      if os.is("MacOSX") then
         defines { "USE_NATIVEFILEDIALOG" }
         links {"Cocoa.framework"}
         files {
                "OpenGLWindow/MacOpenGLWindow.h",
                "OpenGLWindow/MacOpenGLWindow.mm",
               }
         includedirs { "./ThirdPartyLibs/nativefiledialog/src/include/" }
         files  {
            "ThirdPartyLibs/nativefiledialog/src/nfd_common.c",
            "ThirdPartyLibs/nativefiledialog/src/nfd_cocoa.m"
         }
      end

      configuration "Debug"
         defines { "DEBUG" } -- -DDEBUG
         flags { "Symbols" }
         targetname "exrview_debug"

      configuration "Release"
         -- defines { "NDEBUG" } -- -NDEBUG
         flags { "Symbols", "Optimize" }
         targetname "exrview"
