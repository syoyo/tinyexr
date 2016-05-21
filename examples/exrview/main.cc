#define USE_OPENGL2
//#include "OpenGLWindow/b3CommandLineArgs.h"
#include "OpenGLWindow/OpenGLInclude.h"
//#include "OpenGLWindow/b3Quickprof.h"
#ifdef _WIN32
#include "OpenGLWindow/Win32OpenGLWindow.h"
#elif defined  __APPLE__
#include "OpenGLWindow/MacOpenGLWindow.h"
#else
//assume linux
#include "OpenGLWindow/X11OpenGLWindow.h"
#endif

#include "CommonInterfaces/CommonRenderInterface.h"

#ifdef _WIN32
#include <sys/types.h>
#include <sys/stat.h>
#include <time.h>
#else
#include <sys/stat.h>
#include <sys/mman.h>
#include <fcntl.h>
#endif

#include <cstdio>
#include <cstdlib>
#include <string>

#define NK_INCLUDE_FIXED_TYPES
#define NK_INCLUDE_STANDARD_IO
#define NK_INCLUDE_DEFAULT_ALLOCATOR
#define NK_INCLUDE_VERTEX_BUFFER_OUTPUT
#define NK_INCLUDE_FONT_BAKING
#define NK_INCLUDE_DEFAULT_FONT
#define NK_IMPLEMENTATION
#define NK_BTGUI_GL2_IMPLEMENTATION
#include "nuklear.h"
#include "nuklear_btgui_gl2.h"

b3gDefaultOpenGLWindow* window = 0;
int gWidth = 512;
int gHeight = 512;

#define MAX_VERTEX_BUFFER 512 * 1024
#define MAX_ELEMENT_BUFFER 128 * 1024

void checkErrors(std::string desc) {
	GLenum e = glGetError();
	if (e != GL_NO_ERROR) {
		fprintf(stderr, "OpenGL error in \"%s\": %d (%d)\n", desc.c_str(), e, e);
		exit(20);
	}
}

void keyboardCallback(int keycode, int state)
{
	printf("hello key %d, state %d\n", keycode, state);
	if (keycode == 27)
	{
		if (window)
			window->setRequestExit();
	}
}

void mouseMoveCallback(float x, float y)
{
	printf("Mouse Move: %f, %f\n", x, y);

}
void mouseButtonCallback(int button, int state, float x, float y)
{
}


void resizeCallback(float width, float height)
{
	GLfloat h = (GLfloat)height / (GLfloat)width;
	GLfloat xmax, znear, zfar;

	znear = 1.0f;
	zfar = 1000.0f;
	xmax = znear * 0.5f;

  gWidth = width;
  gHeight = height;
}



int
main(int argc, char** argv)
{
	window = new b3gDefaultOpenGLWindow;
	b3gWindowConstructionInfo ci;
#ifdef USE_OPENGL2
  ci.m_openglVersion = 2;
#endif
	window->createWindow(ci);
	window->setWindowTitle("EXR Viewer");

  checkErrors("init");

	window->setMouseButtonCallback(mouseButtonCallback);
	window->setMouseMoveCallback(mouseMoveCallback);
  checkErrors("mouse");
	window->setKeyboardCallback(keyboardCallback);
  checkErrors("keyboard");
	window->setResizeCallback(resizeCallback);
  checkErrors("resize");

  struct nk_context *ctx;
  struct nk_color background;

  /* GUI */
  ctx = nk_btgui_init(window, NK_BTGUI3_DEFAULT);
  /* Load Fonts: if none of these are loaded a default font will be used  */
  {struct nk_font_atlas *atlas;
  nk_btgui_font_stash_begin(&atlas);
  /*struct nk_font *droid = nk_font_atlas_add_from_file(atlas, "../../../extra_font/DroidSans.ttf", 14, 0);*/
  /*struct nk_font *roboto = nk_font_atlas_add_from_file(atlas, "../../../extra_font/Roboto-Regular.ttf", 14, 0);*/
  /*struct nk_font *future = nk_font_atlas_add_from_file(atlas, "../../../extra_font/kenvector_future_thin.ttf", 13, 0);*/
  /*struct nk_font *clean = nk_font_atlas_add_from_file(atlas, "../../../extra_font/ProggyClean.ttf", 12, 0);*/
  /*struct nk_font *tiny = nk_font_atlas_add_from_file(atlas, "../../../extra_font/ProggyTiny.ttf", 10, 0);*/
  /*struct nk_font *cousine = nk_font_atlas_add_from_file(atlas, "../../../extra_font/Cousine-Regular.ttf", 13, 0);*/
  nk_btgui_font_stash_end();
  }
  
  checkErrors("start");

	int i = 0;
	while (!window->requestedExit())
	{
		window->startRendering();

    checkErrors("begin frame");
    nk_btgui_new_frame();

    /* GUI */
    {struct nk_panel layout;
    if (nk_begin(ctx, &layout, "Demo", nk_rect(50, 50, 230, 250),
        NK_WINDOW_BORDER|NK_WINDOW_MOVABLE|NK_WINDOW_SCALABLE|
        NK_WINDOW_MINIMIZABLE|NK_WINDOW_TITLE))
    {
        enum {EASY, HARD};
        static int op = EASY;
        static int property = 20;
        nk_layout_row_static(ctx, 30, 80, 1);
        if (nk_button_label(ctx, "button", NK_BUTTON_DEFAULT))
            fprintf(stdout, "button pressed\n");

        nk_layout_row_dynamic(ctx, 30, 2);
        if (nk_option_label(ctx, "easy", op == EASY)) op = EASY;
        if (nk_option_label(ctx, "hard", op == HARD)) op = HARD;

        nk_layout_row_dynamic(ctx, 25, 1);
        nk_property_int(ctx, "Compression:", 0, &property, 100, 10, 1);

        {struct nk_panel combo;
        nk_layout_row_dynamic(ctx, 20, 1);
        nk_label(ctx, "background:", NK_TEXT_LEFT);
        nk_layout_row_dynamic(ctx, 25, 1);
        if (nk_combo_begin_color(ctx, &combo, background, 400)) {
            nk_layout_row_dynamic(ctx, 120, 1);
            background = nk_color_picker(ctx, background, NK_RGBA);
            nk_layout_row_dynamic(ctx, 25, 1);
            background.r = (nk_byte)nk_propertyi(ctx, "#R:", 0, background.r, 255, 1,1);
            background.g = (nk_byte)nk_propertyi(ctx, "#G:", 0, background.g, 255, 1,1);
            background.b = (nk_byte)nk_propertyi(ctx, "#B:", 0, background.b, 255, 1,1);
            background.a = (nk_byte)nk_propertyi(ctx, "#A:", 0, background.a, 255, 1,1);
            nk_combo_end(ctx);
        }}
    }
    nk_end(ctx);}


    /* Draw */
    {float bg[4];
    nk_color_fv(bg, background);
    glViewport(0, 0, window->getWidth(), window->getHeight());
    glClear(GL_COLOR_BUFFER_BIT);
    glClearColor(bg[0], bg[1], bg[2], bg[3]);
    /* IMPORTANT: `nk_glfw_render` modifies some global OpenGL state
     * with blending, scissor, face culling and depth test and defaults everything
     * back into a default state. Make sure to either save and restore or
     * reset your own state after drawing rendering the UI. */
    nk_btgui_render(NK_ANTI_ALIASING_ON, MAX_VERTEX_BUFFER, MAX_ELEMENT_BUFFER);
    }

		window->endRendering();

		i++;
		if ((i & 127) == 0)//once every 128 frames
		{

			printf("Rendered 1024 frames.\n");
	
			//break;
		}
	}

  nk_btgui_shutdown();

	delete window;

	return EXIT_SUCCESS;
}
