#define USE_OPENGL2
#include "OpenGLWindow/OpenGLInclude.h"
#ifdef _WIN32
#include "OpenGLWindow/Win32OpenGLWindow.h"
#elif defined __APPLE__
#include "OpenGLWindow/MacOpenGLWindow.h"
#else
// assume linux
#include "OpenGLWindow/X11OpenGLWindow.h"
#endif

#ifdef _WIN32
#include <sys/stat.h>
#include <sys/types.h>
#include <time.h>
#else
#include <fcntl.h>
#include <sys/mman.h>
#include <sys/stat.h>
#endif

#include <cstdio>
#include <cstdlib>
#include <string>
#include <cstring>

#ifdef USE_NATIVEFILEDIALOG
#include <nfd.h>
#endif

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

#include "exr-io.h"

b3gDefaultOpenGLWindow* window = 0;
int gWidth = 512;
int gHeight = 512;
GLuint gTexId;
float gIntensityScale = 1.0;
float gGamma = 1.0;
float gBokeh = 0.75;
int gExrWidth, gExrHeight;
float* gExrRGBA;
float* gInitialExrRGBA;
float* gDepthExrRGBA;
float gFocusDepth = 0.22;
int gMousePosX, gMousePosY;

struct nk_context* ctx;

#define MAX_VERTEX_BUFFER 512 * 1024
#define MAX_ELEMENT_BUFFER 128 * 1024

void checkErrors(std::string desc) {
  GLenum e = glGetError();
  if (e != GL_NO_ERROR) {
    fprintf(stderr, "OpenGL error in \"%s\": %d (%d)\n", desc.c_str(), e, e);
    exit(20);
  }
}

void keyboardCallback(int keycode, int state) {
  // printf("hello key %d, state %d\n", keycode, state);
  if (keycode == 27) {
    if (window) window->setRequestExit();
  }
}

void mouseMoveCallback(float x, float y) {
  // printf("Mouse Move: %f, %f\n", x, y);

  gMousePosX = (int)x;
  gMousePosY = (int)y;

  // @todo { move to nuklear_btgui_gl2.h }
  nk_btgui_update_mouse_pos((int)x, (int)y);
}
void mouseButtonCallback(int button, int state, float x, float y) {
  nk_btgui_update_mouse_state((button == 0) && (state == 1), 0, 0);
}

void resizeCallback(float width, float height) {
  GLfloat h = (GLfloat)height / (GLfloat)width;
  GLfloat xmax, znear, zfar;

  znear = 1.0f;
  zfar = 1000.0f;
  xmax = znear * 0.5f;

  gWidth = width;
  gHeight = height;
}

GLuint GenTexture(int w, int h, const float* rgba)
{
  // Create floating point RGBA texture
  GLuint texHandle;
  glGenTextures(1, &texHandle);

  glActiveTexture(GL_TEXTURE0);
  glBindTexture(GL_TEXTURE_2D, texHandle);
  glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_MIN_FILTER, GL_LINEAR);
  glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_MAG_FILTER, GL_NEAREST);

  // @todo { Use GL_RGBA32F for internal texture format. }
  glTexImage2D(GL_TEXTURE_2D, 0, GL_RGBA, w, h, 0, GL_RGBA, GL_FLOAT, rgba);
  checkErrors("GenTexture");

  return texHandle;
}


bool
LoadShader(
  GLenum shaderType,  // GL_VERTEX_SHADER or GL_FRAGMENT_SHADER(or maybe GL_COMPUTE_SHADER)
  GLuint& shader,
  const char* shaderSourceFilename)
{
  GLint val = 0;

  // free old shader/program
  if (shader != 0) glDeleteShader(shader);

  static GLchar srcbuf[16384];
  FILE *fp = fopen(shaderSourceFilename, "rb");
  if (!fp) {
    fprintf(stderr, "failed to load shader: %s\n", shaderSourceFilename);
    return false;
  }
  fseek(fp, 0, SEEK_END);
  size_t len = ftell(fp);
  rewind(fp);
  len = fread(srcbuf, 1, len, fp);
  srcbuf[len] = 0;
  fclose(fp);

  static const GLchar *src = srcbuf;

  shader = glCreateShader(shaderType);
  glShaderSource(shader, 1, &src, NULL);
  glCompileShader(shader);
  glGetShaderiv(shader, GL_COMPILE_STATUS, &val);
  if (val != GL_TRUE) {
    char log[4096];
    GLsizei msglen;
    glGetShaderInfoLog(shader, 4096, &msglen, log);
    printf("%s\n", log);
    assert(val == GL_TRUE && "failed to compile shader");
  }

  printf("Load shader [ %s ] OK\n", shaderSourceFilename);
  return true;
}

bool
LinkShader(
  GLuint& prog,
  GLuint& vertShader,
  GLuint& fragShader)
{
  GLint val = 0;

  if (prog != 0) {
    glDeleteProgram(prog);
  }

  prog = glCreateProgram();

  glAttachShader(prog, vertShader);
  glAttachShader(prog, fragShader);
  glLinkProgram(prog);

  glGetProgramiv(prog, GL_LINK_STATUS, &val);
  assert(val == GL_TRUE && "failed to link shader");

  printf("Link shader OK\n");

  return true;
}

void
Render(GLuint prog_id, int w, int h)
{
  glDisable(GL_DEPTH_TEST);

  glUseProgram(prog_id);

  glActiveTexture(GL_TEXTURE0);
  glBindTexture(GL_TEXTURE_2D, gTexId);

  glEnable(GL_TEXTURE_2D);
  GLint texLoc = glGetUniformLocation(prog_id, "tex");
  assert(texLoc >= 0);
  glUniform1i(texLoc, 0); // TEXTURE0

  GLint intensityScaleLoc = glGetUniformLocation(prog_id, "intensity_scale");
  if (intensityScaleLoc >= 0) {
    glUniform1f(intensityScaleLoc, gIntensityScale);
  }

  GLint gammaLoc = glGetUniformLocation(prog_id, "gamma");
  if (gammaLoc >= 0) {
    glUniform1f(gammaLoc, gGamma);
  }

  GLint pos_id = glGetAttribLocation(prog_id, "in_position");
  assert(pos_id >= 0);
  GLint texcoord_id = glGetAttribLocation(prog_id, "in_texcoord");
  assert(texcoord_id >= 0);

  const float vertices[] = {-1, -1, -1, 1, 1, 1, 1, -1};
  const float texcoords[] = {0, 1, 0, 0, 1, 0, 1, 1};

  glVertexAttribPointer(pos_id, 2, GL_FLOAT, GL_FALSE, 0, (const void*)(vertices));
  glVertexAttribPointer(texcoord_id, 2, GL_FLOAT, GL_FALSE, 0, (const void*)(texcoords));

  glEnableVertexAttribArray(pos_id);
  glEnableVertexAttribArray(texcoord_id);

  glDrawArrays(GL_QUADS, 0, 4);

  glDisableVertexAttribArray(pos_id);
  glDisableVertexAttribArray(texcoord_id);

  checkErrors("render");

  glUseProgram(0);
  checkErrors("UseProgram(0)");

  glEnable(GL_DEPTH_TEST);
  glDisable(GL_TEXTURE_2D);
}

void InspectPixel(float rgba[4], int x, int y) {
  if (x < 0) x = 0;
  if (x > (gExrWidth-1)) x = gExrWidth - 1;

  if (y < 0) y = 0;
  if (y > (gExrHeight-1)) y = gExrHeight - 1;

  rgba[0] = gExrRGBA[4 * (y * gExrWidth + x) + 0];
  rgba[1] = gExrRGBA[4 * (y * gExrWidth + x) + 1];
  rgba[2] = gExrRGBA[4 * (y * gExrWidth + x) + 2];
  rgba[3] = gExrRGBA[4 * (y * gExrWidth + x) + 3];

}

void multComplex(float reP, float imP, float reQ, float imQ,
                 float &reResult, float &imResult)
{
    reResult = reP * reQ - imP * imQ;
    imResult = reP * imQ + imP * reQ;
}

float vdot(float reA, float imA, float reB, float imB) {
    return reA * reB + imA * imB;
}

// These kernels are computed by CircularDofFilterGenerator
// https://github.com/kecho/CircularDofFilterGenerator
const float MAX_FILTER_SIZE = 1.0;
const int KERNEL_RADIUS = 8;
const int KERNEL_COUNT = 17;
// # of Component ... 2
const float Kernel0BracketsRealXY_ImZW[4] = {-0.038708,0.943062,-0.025574,0.660892};
const float Kernel0Weights_RealX_ImY[2] = {0.411259,-0.548794};
const float Kernel0_RealX_ImY_RealZ_ImW[17][4] = {
        {/*XY: Non Bracketed*/0.014096,-0.022658,/*Bracketed WZ:*/0.055991,0.004413},
        {/*XY: Non Bracketed*/-0.020612,-0.025574,/*Bracketed WZ:*/0.019188,0.000000},
        {/*XY: Non Bracketed*/-0.038708,0.006957,/*Bracketed WZ:*/0.000000,0.049223},
        {/*XY: Non Bracketed*/-0.021449,0.040468,/*Bracketed WZ:*/0.018301,0.099929},
        {/*XY: Non Bracketed*/0.013015,0.050223,/*Bracketed WZ:*/0.054845,0.114689},
        {/*XY: Non Bracketed*/0.042178,0.038585,/*Bracketed WZ:*/0.085769,0.097080},
        {/*XY: Non Bracketed*/0.057972,0.019812,/*Bracketed WZ:*/0.102517,0.068674},
        {/*XY: Non Bracketed*/0.063647,0.005252,/*Bracketed WZ:*/0.108535,0.046643},
        {/*XY: Non Bracketed*/0.064754,0.000000,/*Bracketed WZ:*/0.109709,0.038697},
        {/*XY: Non Bracketed*/0.063647,0.005252,/*Bracketed WZ:*/0.108535,0.046643},
        {/*XY: Non Bracketed*/0.057972,0.019812,/*Bracketed WZ:*/0.102517,0.068674},
        {/*XY: Non Bracketed*/0.042178,0.038585,/*Bracketed WZ:*/0.085769,0.097080},
        {/*XY: Non Bracketed*/0.013015,0.050223,/*Bracketed WZ:*/0.054845,0.114689},
        {/*XY: Non Bracketed*/-0.021449,0.040468,/*Bracketed WZ:*/0.018301,0.099929},
        {/*XY: Non Bracketed*/-0.038708,0.006957,/*Bracketed WZ:*/0.000000,0.049223},
        {/*XY: Non Bracketed*/-0.020612,-0.025574,/*Bracketed WZ:*/0.019188,0.000000},
        {/*XY: Non Bracketed*/0.014096,-0.022658,/*Bracketed WZ:*/0.055991,0.004413}
};

const float Kernel1BracketsRealXY_ImZW[4] = {0.000115,0.559524,0.000000,0.178226};
const float Kernel1Weights_RealX_ImY[2] = {0.513282,4.561110};
const float Kernel1_RealX_ImY_RealZ_ImW[17][4] = {
        {/*XY: Non Bracketed*/0.000115,0.009116,/*Bracketed WZ:*/0.000000,0.051147},
        {/*XY: Non Bracketed*/0.005324,0.013416,/*Bracketed WZ:*/0.009311,0.075276},
        {/*XY: Non Bracketed*/0.013753,0.016519,/*Bracketed WZ:*/0.024376,0.092685},
        {/*XY: Non Bracketed*/0.024700,0.017215,/*Bracketed WZ:*/0.043940,0.096591},
        {/*XY: Non Bracketed*/0.036693,0.015064,/*Bracketed WZ:*/0.065375,0.084521},
        {/*XY: Non Bracketed*/0.047976,0.010684,/*Bracketed WZ:*/0.085539,0.059948},
        {/*XY: Non Bracketed*/0.057015,0.005570,/*Bracketed WZ:*/0.101695,0.031254},
        {/*XY: Non Bracketed*/0.062782,0.001529,/*Bracketed WZ:*/0.112002,0.008578},
        {/*XY: Non Bracketed*/0.064754,0.000000,/*Bracketed WZ:*/0.115526,0.000000},
        {/*XY: Non Bracketed*/0.062782,0.001529,/*Bracketed WZ:*/0.112002,0.008578},
        {/*XY: Non Bracketed*/0.057015,0.005570,/*Bracketed WZ:*/0.101695,0.031254},
        {/*XY: Non Bracketed*/0.047976,0.010684,/*Bracketed WZ:*/0.085539,0.059948},
        {/*XY: Non Bracketed*/0.036693,0.015064,/*Bracketed WZ:*/0.065375,0.084521},
        {/*XY: Non Bracketed*/0.024700,0.017215,/*Bracketed WZ:*/0.043940,0.096591},
        {/*XY: Non Bracketed*/0.013753,0.016519,/*Bracketed WZ:*/0.024376,0.092685},
        {/*XY: Non Bracketed*/0.005324,0.013416,/*Bracketed WZ:*/0.009311,0.075276},
        {/*XY: Non Bracketed*/0.000115,0.009116,/*Bracketed WZ:*/0.000000,0.051147}
};

// # of Component ... 1
const float C0Kernel0BracketsRealXY_ImZW[4] = {0.022490,0.048231,-0.017701,0.199448};
const float C0Kernel0Weights_RealX_ImY[2] = {5.268909,-0.886528};
const float C0Kernel0_RealX_ImY_RealZ_ImW[17][4] = {
	{/*XY: Non Bracketed*/0.028949,-0.017701,/*Bracketed WZ:*/0.133906,0.000000},
	{/*XY: Non Bracketed*/0.028133,-0.012569,/*Bracketed WZ:*/0.116999,0.025728},
	{/*XY: Non Bracketed*/0.027004,-0.008611,/*Bracketed WZ:*/0.093589,0.045572},
	{/*XY: Non Bracketed*/0.025805,-0.005618,/*Bracketed WZ:*/0.068729,0.060579},
	{/*XY: Non Bracketed*/0.024691,-0.003409,/*Bracketed WZ:*/0.045637,0.071656},
	{/*XY: Non Bracketed*/0.023758,-0.001837,/*Bracketed WZ:*/0.026292,0.079537},
	{/*XY: Non Bracketed*/0.023062,-0.000791,/*Bracketed WZ:*/0.011860,0.084780},
	{/*XY: Non Bracketed*/0.022634,-0.000194,/*Bracketed WZ:*/0.002989,0.087775},
	{/*XY: Non Bracketed*/0.022490,-0.000000,/*Bracketed WZ:*/0.000000,0.088748},
	{/*XY: Non Bracketed*/0.022634,-0.000194,/*Bracketed WZ:*/0.002989,0.087775},
	{/*XY: Non Bracketed*/0.023062,-0.000791,/*Bracketed WZ:*/0.011860,0.084780},
	{/*XY: Non Bracketed*/0.023758,-0.001837,/*Bracketed WZ:*/0.026292,0.079537},
	{/*XY: Non Bracketed*/0.024691,-0.003409,/*Bracketed WZ:*/0.045637,0.071656},
	{/*XY: Non Bracketed*/0.025805,-0.005618,/*Bracketed WZ:*/0.068729,0.060579},
	{/*XY: Non Bracketed*/0.027004,-0.008611,/*Bracketed WZ:*/0.093589,0.045572},
	{/*XY: Non Bracketed*/0.028133,-0.012569,/*Bracketed WZ:*/0.116999,0.025728},
	{/*XY: Non Bracketed*/0.028949,-0.017701,/*Bracketed WZ:*/0.133906,0.000000}
};

void applyBokeh(float bokeh, float focusDepth, int w, int h) {
    float **rVal = new float*[w * h];
    for (int i = 0; i < w * h; i++) {
        rVal[i] = new float[4];
    }

    float **gVal = new float*[w * h];
    for (int i = 0; i < w * h; i++) {
        gVal[i] = new float[4];
    }

    float **bVal = new float*[w * h];
    for (int i = 0; i < w * h; i++) {
        bVal[i] = new float[4];
    }
    const float dofRadius = 0.15;

    // horizontal
    for(int x = 0; x < w; x++) {
        for(int y = 0; y < h; y++) {
            const float depth = gDepthExrRGBA[4 * (y * w + x) + 0];
            if(depth < focusDepth - dofRadius) {
                // near
                for(int i = -KERNEL_RADIUS; i <= KERNEL_RADIUS; i++) {
                    int horizontalTex = int(x + i * bokeh);
                    if (horizontalTex < 0) {
                        horizontalTex = int(x - i * bokeh);
                    } else if (horizontalTex >= w) {
                        horizontalTex = int(x - i * bokeh);
                    }

                    float rTexel = gInitialExrRGBA[4 * (y * gExrWidth + horizontalTex) + 0];
                    float gTexel = gInitialExrRGBA[4 * (y * gExrWidth + horizontalTex) + 1];
                    float bTexel = gInitialExrRGBA[4 * (y * gExrWidth + horizontalTex) + 2];

                    float c0[2] = {
                        C0Kernel0_RealX_ImY_RealZ_ImW[i + KERNEL_RADIUS][0],
                        C0Kernel0_RealX_ImY_RealZ_ImW[i + KERNEL_RADIUS][1]
                    };

                    rVal[y * gExrWidth + x][0] += rTexel * c0[0];
                    rVal[y * gExrWidth + x][1] += rTexel * c0[1];

                    gVal[y * gExrWidth + x][0] += gTexel * c0[0];
                    gVal[y * gExrWidth + x][1] += gTexel * c0[1];

                    bVal[y * gExrWidth + x][0] += bTexel * c0[0];
                    bVal[y * gExrWidth + x][1] += bTexel * c0[1];
                }
            } else if (focusDepth + dofRadius < depth) {
                // far
                for(int i = -KERNEL_RADIUS; i <= KERNEL_RADIUS; i++) {
                    int horizontalTex = int(x + i * bokeh);
                    if (horizontalTex < 0) {
                        horizontalTex = int(x - i * bokeh);
                    } else if (horizontalTex >= w) {
                        horizontalTex = int(x - i * bokeh);
                    }
                    float rTexel = gInitialExrRGBA[4 * (y * gExrWidth + horizontalTex) + 0];
                    float gTexel = gInitialExrRGBA[4 * (y * gExrWidth + horizontalTex) + 1];
                    float bTexel = gInitialExrRGBA[4 * (y * gExrWidth + horizontalTex) + 2];
                    float c0_c1[4] = {
                        Kernel0_RealX_ImY_RealZ_ImW[i + KERNEL_RADIUS][0],
                        Kernel0_RealX_ImY_RealZ_ImW[i + KERNEL_RADIUS][1],
                        Kernel1_RealX_ImY_RealZ_ImW[i + KERNEL_RADIUS][0],
                        Kernel1_RealX_ImY_RealZ_ImW[i + KERNEL_RADIUS][1]
                    };

                    rVal[y * gExrWidth + x][0] += rTexel * c0_c1[0];
                    rVal[y * gExrWidth + x][1] += rTexel * c0_c1[1];
                    rVal[y * gExrWidth + x][2] += rTexel * c0_c1[2];
                    rVal[y * gExrWidth + x][3] += rTexel * c0_c1[3];

                    gVal[y * gExrWidth + x][0] += gTexel * c0_c1[0];
                    gVal[y * gExrWidth + x][1] += gTexel * c0_c1[1];
                    gVal[y * gExrWidth + x][2] += gTexel * c0_c1[2];
                    gVal[y * gExrWidth + x][3] += gTexel * c0_c1[3];

                    bVal[y * gExrWidth + x][0] += bTexel * c0_c1[0];
                    bVal[y * gExrWidth + x][1] += bTexel * c0_c1[1];
                    bVal[y * gExrWidth + x][2] += bTexel * c0_c1[2];
                    bVal[y * gExrWidth + x][3] += bTexel * c0_c1[3];
                }
            }
        }
    }

    // vertical
    for(int x = 0; x < w; x++) {
        for(int y = 0; y < h; y++) {
            const float depth = gDepthExrRGBA[4 * (y * w + x) + 0];
            if(depth < focusDepth - dofRadius) {
                // near
                float rVertical[2] = {0, 0};
                float gVertical[2] = {0, 0};
                float bVertical[2] = {0, 0};
                for(int i = -KERNEL_RADIUS; i <= KERNEL_RADIUS; i++) {
                    int verticalTex = int(y + i * bokeh);
                    if (verticalTex < 0) {
                        verticalTex = int(y - i * bokeh);
                    } else if (verticalTex >= h) {
                        verticalTex = int(y - i * bokeh);
                    }
                    float rTexel[2] = {rVal[verticalTex * gExrWidth + x][0],
                                       rVal[verticalTex * gExrWidth + x][1]};
                    float gTexel[2] = {gVal[verticalTex * gExrWidth + x][0],
                                       gVal[verticalTex * gExrWidth + x][1]};
                    float bTexel[2] = {bVal[verticalTex * gExrWidth + x][0],
                                       bVal[verticalTex * gExrWidth + x][1]};

                    float c0[2] = {
                        C0Kernel0_RealX_ImY_RealZ_ImW[i + KERNEL_RADIUS][0],
                        C0Kernel0_RealX_ImY_RealZ_ImW[i + KERNEL_RADIUS][1]
                    };
                    float re, im;
                    multComplex(rTexel[0], rTexel[1], c0[0], c0[1],
                                re, im);
                    rVertical[0] += re;
                    rVertical[1] += im;

                    multComplex(gTexel[0], gTexel[1], c0[0], c0[1],
                                re, im);
                    gVertical[0] += re;
                    gVertical[1] += im;

                    multComplex(bTexel[0], bTexel[1], c0[0], c0[1],
                                re, im);
                    bVertical[0] += re;
                    bVertical[1] += im;
                }

                float red = vdot(rVertical[0], rVertical[1], C0Kernel0Weights_RealX_ImY[0], C0Kernel0Weights_RealX_ImY[1]);
                float green = vdot(gVertical[0], gVertical[1], C0Kernel0Weights_RealX_ImY[0], C0Kernel0Weights_RealX_ImY[1]);
                float blue = vdot(bVertical[0], bVertical[1], C0Kernel0Weights_RealX_ImY[0], C0Kernel0Weights_RealX_ImY[1]);

                gExrRGBA[4 * (y * gExrWidth + x) + 0] = red;
                gExrRGBA[4 * (y * gExrWidth + x) + 1] = green;
                gExrRGBA[4 * (y * gExrWidth + x) + 2] = blue;

            } else if (focusDepth + dofRadius < depth) {
                // far
                float rVertical[4] = {0, 0, 0, 0};
                float gVertical[4] = {0, 0, 0, 0};
                float bVertical[4] = {0, 0, 0, 0};
                for(int i = -KERNEL_RADIUS; i <= KERNEL_RADIUS; i++) {
                    int verticalTex = int(y + i * bokeh);
                    if (verticalTex < 0) {
                        verticalTex = int(y - i * bokeh);
                    } else if (verticalTex >= h) {
                        verticalTex = int(y - i * bokeh);
                    }
                    float rTexel[4] = {rVal[verticalTex * gExrWidth + x][0],
                                       rVal[verticalTex * gExrWidth + x][1],
                                       rVal[verticalTex * gExrWidth + x][2],
                                       rVal[verticalTex * gExrWidth + x][3]};
                    float gTexel[4] = {gVal[verticalTex * gExrWidth + x][0],
                                       gVal[verticalTex * gExrWidth + x][1],
                                       gVal[verticalTex * gExrWidth + x][2],
                                       gVal[verticalTex * gExrWidth + x][3]};
                    float bTexel[4] = {bVal[verticalTex * gExrWidth + x][0],
                                       bVal[verticalTex * gExrWidth + x][1],
                                       bVal[verticalTex * gExrWidth + x][2],
                                       bVal[verticalTex * gExrWidth + x][3]};

                    float c0_c1[4] = {
                        Kernel0_RealX_ImY_RealZ_ImW[i + KERNEL_RADIUS][0],
                        Kernel0_RealX_ImY_RealZ_ImW[i + KERNEL_RADIUS][1],
                        Kernel1_RealX_ImY_RealZ_ImW[i + KERNEL_RADIUS][0],
                        Kernel1_RealX_ImY_RealZ_ImW[i + KERNEL_RADIUS][1]
                    };

                    float re, im;
                    multComplex(rTexel[0], rTexel[1], c0_c1[0], c0_c1[1],
                                re, im);
                    rVertical[0] += re;
                    rVertical[1] += im;
                    multComplex(rTexel[2], rTexel[3], c0_c1[2], c0_c1[3],
                                re, im);
                    rVertical[2] += re;
                    rVertical[3] += im;

                    multComplex(gTexel[0], gTexel[1], c0_c1[0], c0_c1[1],
                                re, im);
                    gVertical[0] += re;
                    gVertical[1] += im;
                    multComplex(gTexel[2], gTexel[3], c0_c1[2], c0_c1[3],
                                re, im);
                    gVertical[2] += re;
                    gVertical[3] += im;

                    multComplex(bTexel[0], bTexel[1], c0_c1[0], c0_c1[1],
                                re, im);
                    bVertical[0] += re;
                    bVertical[1] += im;
                    multComplex(bTexel[2], bTexel[3], c0_c1[2], c0_c1[3],
                                re, im);
                    bVertical[2] += re;
                    bVertical[3] += im;
                }

                float red = vdot(rVertical[0], rVertical[1], Kernel0Weights_RealX_ImY[0], Kernel0Weights_RealX_ImY[1]) +
                    vdot(rVertical[2], rVertical[3], Kernel1Weights_RealX_ImY[0], Kernel1Weights_RealX_ImY[1]);
                float green = vdot(gVertical[0], gVertical[1], Kernel0Weights_RealX_ImY[0], Kernel0Weights_RealX_ImY[1]) +
                    vdot(gVertical[2], gVertical[3], Kernel1Weights_RealX_ImY[0], Kernel1Weights_RealX_ImY[1]);
                float blue = vdot(bVertical[0], bVertical[1], Kernel0Weights_RealX_ImY[0], Kernel0Weights_RealX_ImY[1]) +
                    vdot(bVertical[2], bVertical[3], Kernel1Weights_RealX_ImY[0], Kernel1Weights_RealX_ImY[1]);

                gExrRGBA[4 * (y * gExrWidth + x) + 0] = red;
                gExrRGBA[4 * (y * gExrWidth + x) + 1] = green;
                gExrRGBA[4 * (y * gExrWidth + x) + 2] = blue;
            } else {
                gExrRGBA[4 * (y * gExrWidth + x) + 0] = gInitialExrRGBA[4 * (y * gExrWidth + x) + 0];
                gExrRGBA[4 * (y * gExrWidth + x) + 1] = gInitialExrRGBA[4 * (y * gExrWidth + x) + 1];
                gExrRGBA[4 * (y * gExrWidth + x) + 2] = gInitialExrRGBA[4 * (y * gExrWidth + x) + 2];
            }
        }
    }

    for (int i = 0; i < w * h; i++) {
        delete[] rVal[i];
        delete[] gVal[i];
        delete[] bVal[i];
    }
    delete[] rVal;
    delete[] gVal;
    delete[] bVal;
}

int main(int argc, char** argv) {

  const char *filename = NULL;
  const char *depthFilename = NULL;

#ifdef USE_NATIVEFILEDIALOG
  if (argc < 2) {
    nfdchar_t *outPath = NULL;
    nfdresult_t result = NFD_OpenDialog( "exr", NULL, &outPath );
    if ( result == NFD_OKAY )
    {
        puts("Success!");
        filename = strdup(outPath);
    }
    else if ( result == NFD_CANCEL )
    {
        puts("User pressed cancel.");
        exit(-1);
    }
    else
    {
        printf("Error: %s\n", NFD_GetError() );
        exit(-1);
    }
  } else {
    filename = argv[1];
    depthFilename = argv[2];
  }
#else
  if (argc < 3) {
    printf("Usage: exrview input.exr depth.exr\n");
    exit(-1);
  }
  filename = argv[1];
  depthFilename = argv[2];
#endif

  {
    bool ret = exrio::LoadEXRRGBA(&gExrRGBA, &gExrWidth, &gExrHeight, filename);
    if (!ret) {
      exit(-1);
    }
    ret = exrio::LoadEXRRGBA(&gInitialExrRGBA, &gExrWidth, &gExrHeight, filename);

    ret = exrio::LoadEXRRGBA(&gDepthExrRGBA, &gExrWidth, &gExrHeight, depthFilename);
    if (!ret) {
      exit(-1);
    }
  }
  printf("Loaded\n");

  window = new b3gDefaultOpenGLWindow;
  b3gWindowConstructionInfo ci;
#ifdef USE_OPENGL2
  ci.m_openglVersion = 2;
#endif
  ci.m_width = gExrWidth;
  ci.m_height = gExrHeight;
  window->createWindow(ci);

  char title[1024];
  sprintf(title, "%s (%d x %d)", filename, gExrWidth, gExrHeight);
  window->setWindowTitle(title);

#ifndef __APPLE__
#ifndef _WIN32
  //some Linux implementations need the 'glewExperimental' to be true
  glewExperimental = GL_TRUE;
#endif
  if (glewInit() != GLEW_OK) {
	  fprintf(stderr, "Failed to initialize GLEW\n");
	  exit(-1);
  }

  if (!GLEW_VERSION_2_1) {
	  fprintf(stderr, "OpenGL 2.1 is not available\n");
	  exit(-1);
  }
#endif


  checkErrors("init");

  window->setMouseButtonCallback(mouseButtonCallback);
  window->setMouseMoveCallback(mouseMoveCallback);
  checkErrors("mouse");
  window->setKeyboardCallback(keyboardCallback);
  checkErrors("keyboard");
  window->setResizeCallback(resizeCallback);
  checkErrors("resize");

  struct nk_color background;
  background = nk_rgb(28,48,62);


  {
    // Upload EXR image to OpenGL texture.
    gTexId = GenTexture(gExrWidth, gExrHeight, gExrRGBA);
    if (gTexId == 0) {
      fprintf(stderr, "OpenGL texture error\n");
      exit(-1);
    }
  }


  /* GUI */
  ctx = nk_btgui_init(window, NK_BTGUI3_DEFAULT);
  /* Load Fonts: if none of these are loaded a default font will be used  */
  {
    struct nk_font_atlas* atlas;
    nk_btgui_font_stash_begin(&atlas);
    /*struct nk_font *droid = nk_font_atlas_add_from_file(atlas,
     * "../../../extra_font/DroidSans.ttf", 14, 0);*/
    /*struct nk_font *roboto = nk_font_atlas_add_from_file(atlas,
     * "../../../extra_font/Roboto-Regular.ttf", 14, 0);*/
    /*struct nk_font *future = nk_font_atlas_add_from_file(atlas,
     * "../../../extra_font/kenvector_future_thin.ttf", 13, 0);*/
    /*struct nk_font *clean = nk_font_atlas_add_from_file(atlas,
     * "../../../extra_font/ProggyClean.ttf", 12, 0);*/
    /*struct nk_font *tiny = nk_font_atlas_add_from_file(atlas,
     * "../../../extra_font/ProggyTiny.ttf", 10, 0);*/
    /*struct nk_font *cousine = nk_font_atlas_add_from_file(atlas,
     * "../../../extra_font/Cousine-Regular.ttf", 13, 0);*/
    struct nk_font *droid = nk_font_atlas_add_from_file(atlas,
     "./DroidSans.ttf", 14, 0);
    nk_btgui_font_stash_end();
    if (droid) {
      nk_style_set_font(ctx, &droid->handle);
    }

    // Color
    struct nk_color table[NK_COLOR_COUNT];
    table[NK_COLOR_TEXT] = nk_rgba(210, 210, 210, 255);
    table[NK_COLOR_WINDOW] = nk_rgba(57, 67, 71, 245);
    table[NK_COLOR_HEADER] = nk_rgba(51, 51, 56, 230);
    table[NK_COLOR_BORDER] = nk_rgba(46, 46, 46, 255);
    table[NK_COLOR_BUTTON] = nk_rgba(48, 48, 48, 255);
    table[NK_COLOR_BUTTON_HOVER] = nk_rgba(58, 93, 121, 255);
    table[NK_COLOR_BUTTON_ACTIVE] = nk_rgba(63, 98, 126, 255);
    table[NK_COLOR_TOGGLE] = nk_rgba(50, 58, 61, 255);
    table[NK_COLOR_TOGGLE_HOVER] = nk_rgba(45, 53, 56, 255);
    table[NK_COLOR_TOGGLE_CURSOR] = nk_rgba(48, 83, 111, 255);
    table[NK_COLOR_SELECT] = nk_rgba(57, 67, 61, 255);
    table[NK_COLOR_SELECT_ACTIVE] = nk_rgba(48, 83, 111, 255);
    table[NK_COLOR_SLIDER] = nk_rgba(50, 58, 61, 255);
    table[NK_COLOR_SLIDER_CURSOR] = nk_rgba(48, 83, 111, 245);
    table[NK_COLOR_SLIDER_CURSOR_HOVER] = nk_rgba(53, 88, 116, 255);
    table[NK_COLOR_SLIDER_CURSOR_ACTIVE] = nk_rgba(58, 93, 121, 255);
    table[NK_COLOR_PROPERTY] = nk_rgba(50, 58, 61, 255);
    table[NK_COLOR_EDIT] = nk_rgba(50, 58, 61, 225);
    table[NK_COLOR_EDIT_CURSOR] = nk_rgba(210, 210, 210, 255);
    table[NK_COLOR_COMBO] = nk_rgba(50, 58, 61, 255);
    table[NK_COLOR_CHART] = nk_rgba(50, 58, 61, 255);
    table[NK_COLOR_CHART_COLOR] = nk_rgba(48, 83, 111, 255);
    table[NK_COLOR_CHART_COLOR_HIGHLIGHT] = nk_rgba(255, 0, 0, 255);
    table[NK_COLOR_SCROLLBAR] = nk_rgba(50, 58, 61, 255);
    table[NK_COLOR_SCROLLBAR_CURSOR] = nk_rgba(48, 83, 111, 255);
    table[NK_COLOR_SCROLLBAR_CURSOR_HOVER] = nk_rgba(53, 88, 116, 255);
    table[NK_COLOR_SCROLLBAR_CURSOR_ACTIVE] = nk_rgba(58, 93, 121, 255);
    table[NK_COLOR_TAB_HEADER] = nk_rgba(48, 83, 111, 255);
    nk_style_from_table(ctx, table);
  }

  checkErrors("start");

  GLuint vert_id = 0, frag_id = 0, prog_id = 0;
  {
    bool ret = LoadShader(GL_VERTEX_SHADER, vert_id, "shader.vert");
    if (!ret) {
      fprintf(stderr, "Failed to compile vertex shader.\n");
      exit(-1);
    }
  }
  checkErrors("vertex shader load");

  {
    bool ret = LoadShader(GL_FRAGMENT_SHADER, frag_id, "shader.frag");
    if (!ret) {
      fprintf(stderr, "Failed to compile fragment shader.\n");
      exit(-1);
    }
  }
  checkErrors("fragment shader load");

  {
    bool ret = LinkShader(prog_id, vert_id, frag_id);
    if (!ret) {
      fprintf(stderr, "Failed to link shader.\n");
      exit(-1);
    }
  }
  checkErrors("link shader");

  while (!window->requestedExit()) {
    window->startRendering();

    glClear(GL_COLOR_BUFFER_BIT);

    checkErrors("begin frame");
    nk_btgui_new_frame();

    float pixel[4];
    InspectPixel(pixel, gMousePosX, gMousePosY);

    /* GUI */
    {
      //struct nk_panel layout;
      if (nk_begin(ctx, "UI", nk_rect(50, 50, 350, 250),
                   NK_WINDOW_BORDER | NK_WINDOW_MOVABLE | NK_WINDOW_SCALABLE |
                       NK_WINDOW_MINIMIZABLE | NK_WINDOW_TITLE)) {
        nk_layout_row_static(ctx, 30, 300, 1);
        //if (nk_button_label(ctx, "button", NK_BUTTON_DEFAULT))
        //  fprintf(stdout, "button pressed\n");

        nk_label(ctx, "Intensity", NK_TEXT_LEFT);
        if (nk_slider_float(ctx, 0, &gIntensityScale, 10.0, 0.1f)) {
            fprintf(stdout, "Intensity: %f\n", gIntensityScale);
        }
        nk_label(ctx, "Display gamma", NK_TEXT_LEFT);
        if (nk_slider_float(ctx, 0, &gGamma, 10.0, 0.01f)) {
            fprintf(stdout, "Gamma: %f\n", gGamma);
        }
        nk_label(ctx, "Bokeh", NK_TEXT_LEFT);
        if (nk_slider_float(ctx, 0, &gBokeh, 2.0, 0.01f)) {
            fprintf(stdout, "Bokeh: %f\n", gBokeh);

            applyBokeh(gBokeh, gFocusDepth, gExrWidth, gExrHeight);

            glBindTexture(GL_TEXTURE_2D, gTexId);
            glTexImage2D(GL_TEXTURE_2D, 0, GL_RGBA, gExrWidth, gExrHeight,
                         0, GL_RGBA, GL_FLOAT, gExrRGBA);
        }

        nk_label(ctx, "FocusDepth", NK_TEXT_LEFT);
        if (nk_slider_float(ctx, 0.0, &gFocusDepth, 1.0, 0.01f)) {
            fprintf(stdout, "FocusDepth: %f\n", gFocusDepth);

            applyBokeh(gBokeh, gFocusDepth, gExrWidth, gExrHeight);

            glBindTexture(GL_TEXTURE_2D, gTexId);
            glTexImage2D(GL_TEXTURE_2D, 0, GL_RGBA, gExrWidth, gExrHeight,
                         0, GL_RGBA, GL_FLOAT, gExrRGBA);
        }

        nk_label(ctx, "RAW pixel value", NK_TEXT_LEFT);
        char txt[1024];
        sprintf(txt, "(%d, %d) = %f, %f, %f, %f",
                gMousePosX, gMousePosY,
                pixel[0], pixel[1], pixel[2], pixel[3]);
        nk_text(ctx, txt, strlen(txt), NK_TEXT_LEFT);

#if 0
        nk_layout_row_dynamic(ctx, 25, 1);
        nk_property_int(ctx, "Compression:", 0, &property, 100, 10, 1);

        {
          struct nk_panel combo;
          nk_layout_row_dynamic(ctx, 20, 1);
          nk_label(ctx, "background:", NK_TEXT_LEFT);
          nk_layout_row_dynamic(ctx, 25, 1);
          if (nk_combo_begin_color(ctx, &combo, background, 400)) {
            nk_layout_row_dynamic(ctx, 120, 1);
            background = nk_color_picker(ctx, background, NK_RGBA);
            nk_layout_row_dynamic(ctx, 25, 1);
            background.r =
                (nk_byte)nk_propertyi(ctx, "#R:", 0, background.r, 255, 1, 1);
            background.g =
                (nk_byte)nk_propertyi(ctx, "#G:", 0, background.g, 255, 1, 1);
            background.b =
                (nk_byte)nk_propertyi(ctx, "#B:", 0, background.b, 255, 1, 1);
            background.a =
                (nk_byte)nk_propertyi(ctx, "#A:", 0, background.a, 255, 1, 1);
            nk_combo_end(ctx);
          }
        }
#endif
      }
      nk_end(ctx);
    }

    /* Draw */
    {
      float bg[4];
      nk_color_fv(bg, background);
      glViewport(0, 0, window->getWidth(), window->getHeight());
      glClear(GL_COLOR_BUFFER_BIT);
      glClearColor(bg[0], bg[1], bg[2], bg[3]);

      Render(prog_id, window->getWidth(), window->getHeight());

      /* IMPORTANT: `nk_glfw_render` modifies some global OpenGL state
       * with blending, scissor, face culling and depth test and defaults
       * everything
       * back into a default state. Make sure to either save and restore or
       * reset your own state after drawing rendering the UI. */
      nk_btgui_render(NK_ANTI_ALIASING_ON, MAX_VERTEX_BUFFER,
                      MAX_ELEMENT_BUFFER);
    }

    window->endRendering();
  }

  nk_btgui_shutdown();

  delete window;

  return EXIT_SUCCESS;
}
