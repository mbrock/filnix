#include <FL/Fl.H>
#include <FL/Fl_Image.H>
#include <FL/Fl_Device.H>
#include <FL/fl_draw.H>
#include <cassert>
#include <cmath>
#include <cstdio>

int main() {
  // Matrix operations use libm but need no window or display server.
  Fl_Display_Device::display_device()->set_current();
  fl_push_matrix();
  fl_translate(3, 4);
  fl_rotate(30);
  assert(std::fabs(fl_transform_x(2, 0) - (3 + std::sqrt(3.0))) < 1e-9);
  // FLTK's screen coordinates increase downward.
  assert(std::fabs(fl_transform_y(2, 0) - 3) < 1e-9);
  fl_pop_matrix();

  const unsigned char rgb[] = {255, 0, 0, 0, 255, 0, 0, 0, 255, 255, 255, 255};
  Fl_RGB_Image original(rgb, 2, 2, 3);
  Fl_Image::RGB_scaling(FL_RGB_SCALING_NEAREST);
  Fl_Image *scaled = original.copy(4, 4);
  assert(scaled && scaled->w() == 4 && scaled->h() == 4 && scaled->d() == 3);
  const auto *pixels = reinterpret_cast<const unsigned char *>(scaled->data()[0]);
  for (int y = 0; y < 4; y++)
    for (int x = 0; x < 4; x++)
      for (int c = 0; c < 3; c++)
        assert(pixels[(y * 4 + x) * 3 + c] == rgb[((y / 2) * 2 + x / 2) * 3 + c]);
  delete scaled;
  std::puts("FLTK installed consumer: matrix and image operations passed");
}
