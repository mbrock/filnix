#include <GL/glu.h>
#include <assert.h>
#include <stdio.h>

static unsigned vertices;
static GLdouble square[4][3] = {{0, 0, 0}, {1, 0, 0}, {1, 1, 0}, {0, 1, 0}};

static void vertex(void *value) {
  assert(value == square[0] || value == square[1] ||
         value == square[2] || value == square[3]);
  ++vertices;
}

static void error(GLenum code) {
  fprintf(stderr, "Tessellation: %s\n", gluErrorString(code));
  assert(0);
}

int main(void) {
  const GLdouble identity[16] = {1, 0, 0, 0, 0, 1, 0, 0,
                                0, 0, 1, 0, 0, 0, 0, 1};
  const GLint viewport[4] = {10, 20, 640, 480};
  GLdouble x, y, z, ox, oy, oz;
  assert(gluProject(.25, -.5, .125, identity, identity, viewport, &x, &y, &z));
  assert(x == 410 && y == 140 && z == .5625);
  assert(gluUnProject(x, y, z, identity, identity, viewport, &ox, &oy, &oz));
  assert(ox == .25 && oy == -.5 && oz == .125);

  GLUtesselator *tess = gluNewTess();
  assert(tess);
  gluTessCallback(tess, GLU_TESS_VERTEX, (_GLUfuncptr)vertex);
  gluTessCallback(tess, GLU_TESS_ERROR, (_GLUfuncptr)error);
  gluTessBeginPolygon(tess, NULL);
  gluTessBeginContour(tess);
  for (unsigned i = 0; i < 4; ++i) gluTessVertex(tess, square[i], square[i]);
  gluTessEndContour(tess);
  gluTessEndPolygon(tess);
  assert(vertices >= 4);
  gluDeleteTess(tess);
  puts("GLU projection, inverse projection and tessellation passed");
}
