#pragma once
#include <string.h>

struct rep {
  union {
    struct { unsigned char size; char data[23]; } s;
    struct { unsigned long cap, size; char *data; } l;
  } u;
};
