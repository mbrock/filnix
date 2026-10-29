// error: the C23 attribute [[gnu::vector_size]] is not supported
// Dropped, the typedef was int; clang makes it a 16-byte vector.
typedef int v4 [[gnu::vector_size(16)]];
