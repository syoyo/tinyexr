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

#ifdef _WIN32
#include <sys/types.h>
#include <sys/stat.h>
#include <time.h>
#else
#include <sys/stat.h>
#include <sys/mman.h>
#include <fcntl.h>
#endif

#include <string>

b3gDefaultOpenGLWindow* window = 0;

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

	glViewport(0, 0, (GLint)width, (GLint)height);
	glMatrixMode(GL_PROJECTION);
	glLoadIdentity();
	glFrustum(-xmax, xmax, -xmax*h, xmax*h, znear, zfar);

	glMatrixMode(GL_MODELVIEW);
	glLoadIdentity();
	glTranslatef(0.0, 0.0, -5.0);
}



int
main(int argc, char** argv)
{
	window = new b3gDefaultOpenGLWindow;
	b3gWindowConstructionInfo ci;

	window->createWindow(ci);
	window->setWindowTitle("EXR Viewer");

	window->setResizeCallback(resizeCallback);
	window->setKeyboardCallback(keyboardCallback);
	window->setMouseButtonCallback(mouseButtonCallback);
	window->setMouseMoveCallback(mouseMoveCallback);

	int i = 0;
	while (!window->requestedExit())
	{
		window->startRendering();
		window->endRendering();
		i++;
		if ((i & 127) == 0)//once every 128 frames
		{

			printf("Rendered 1024 frames.\n");
	
			//break;
		}
	}

	delete window;

	return EXIT_SUCCESS;
}
