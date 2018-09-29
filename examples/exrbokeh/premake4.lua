newoption {
   trigger     = "with-gtk3nfd",
   description = "Build with nativefiledialog support. GTK3 required(Linux only)"
}

newoption {
   trigger     = "asan",
   description = "Enable address sanitizer(Linux gcc/clang only)"
}

sources = {
   "main.cc",
   "exr-io.cc",
   }

-- premake4.lua
solution "EXRBokehSolution"
   configurations { "Release", "Debug" }

   platforms { "native", "x64", "x32" }


   projectRootDir = os.getcwd() .. "/"
   dofile ("findOpenGLGlewGlut.lua")
   initOpenGL()
   initGlew()

   -- A project defines one build target
   project "exrbokeh"
      kind "ConsoleApp"
      language "C++"
      files { sources }

      includedirs { "./", "../../", "../common/" }

      if os.is("Windows") then
         defines { "USE_NATIVEFILEDIALOG" }
         files{
            "../common/OpenGLWindow/Win32OpenGLWindow.cpp",
            "../common/OpenGLWindow/Win32OpenGLWindow.h",
            "../common/OpenGLWindow/Win32Window.cpp",
            "../common/OpenGLWindow/Win32Window.h",
            }
         includedirs { "../common/ThirdPartyLibs/nativefiledialog/src/include/" }
         files  {
            "../common/ThirdPartyLibs/nativefiledialog/src/nfd_common.c",
            "../common/ThirdPartyLibs/nativefiledialog/src/nfd_win.cpp"
         }
      end
      if os.is("Linux") then
         if _OPTIONS["asan"] then
            buildoptions { "-fsanitize=address" }  
            linkoptions { "-fsanitize=address" }  
         end

         files {
            "../common/OpenGLWindow/X11OpenGLWindow.cpp",
            "../common/OpenGLWindow/X11OpenGLWindows.h"
            }
         links {"X11", "pthread", "dl"}

         if _OPTIONS["with-gtk3nfd"] then -- NFD + GTK3
            defines { "USE_NATIVEFILEDIALOG" }
            includedirs { "../common/ThirdPartyLibs/nativefiledialog/src/include/" }
            buildoptions { "`pkg-config --cflags gtk+-3.0`" }
            linkoptions { "`pkg-config --libs gtk+-3.0`" }
            files  {
               "../common/ThirdPartyLibs/nativefiledialog/src/nfd_common.c",
               "../common/ThirdPartyLibs/nativefiledialog/src/nfd_gtk.c"
            }
         end

      end
      if os.is("MacOSX") then
         defines { "USE_NATIVEFILEDIALOG" }
         links {"Cocoa.framework"}
         files {
                "../common/OpenGLWindow/MacOpenGLWindow.h",
                "../common/OpenGLWindow/MacOpenGLWindow.mm",
               }
         includedirs { "../common/ThirdPartyLibs/nativefiledialog/src/include/" }
         files  {
            "../common/ThirdPartyLibs/nativefiledialog/src/nfd_common.c",
            "../common/ThirdPartyLibs/nativefiledialog/src/nfd_cocoa.m"
         }
      end

      configuration "Debug"
         defines { "DEBUG" } -- -DDEBUG
         flags { "Symbols" }
         targetname "exrbokeh_debug"

      configuration "Release"
         -- defines { "NDEBUG" } -- -NDEBUG
         flags { "Symbols", "Optimize" }
         targetname "exrbokeh"
