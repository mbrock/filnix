#include <dav1d/dav1d.h>
#include <assert.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

int main(int argc, char **argv) {
  assert(argc == 3);
  int bits = atoi(argv[2]);
  assert(bits == 8 || bits == 10);
  FILE *file = fopen(argv[1], "rb");
  assert(file);
  assert(fseek(file, 0, SEEK_END) == 0);
  long size = ftell(file);
  assert(size > 0);
  rewind(file);
  Dav1dData data = {0};
  uint8_t *bytes = dav1d_data_create(&data, (size_t)size);
  assert(bytes && fread(bytes, 1, size, file) == (size_t)size);
  fclose(file);
  Dav1dSettings settings;
  dav1d_default_settings(&settings);
  settings.n_threads = 1;
  settings.max_frame_delay = 1;
  Dav1dContext *context = NULL;
  assert(dav1d_open(&context, &settings) == 0);
  assert(dav1d_send_data(context, &data) == 0);
  Dav1dPicture picture = {0};
  assert(dav1d_get_picture(context, &picture) == 0);
  assert(picture.p.w == 16 && picture.p.h == 16 && picture.p.bpc == bits);
  assert(picture.p.layout == DAV1D_PIXEL_LAYOUT_I420);
  for (int plane = 0; plane < 3; ++plane) {
    int width = plane ? 8 : 16;
    for (int y = 0; y < width; ++y) {
      const uint8_t *row = (const uint8_t *)picture.data[plane] +
                           y * picture.stride[plane != 0];
      for (int x = 0; x < width; ++x) {
        int expected = plane == 0 ? (x * 13 + y * 7) * ((1 << bits) - 1) / 300
                                  : (plane == 1 ? 1 : 3) << (bits - 2);
        int actual = bits == 8 ? row[x] : ((const uint16_t *)row)[x];
        assert(actual == expected);
      }
    }
  }
  dav1d_picture_unref(&picture);
  dav1d_data_unref(&data);
  dav1d_close(&context);
  printf("dav1d %d-bit lossless frame: every Y/U/V sample verified\n", bits);
}
