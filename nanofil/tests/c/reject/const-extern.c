// error: initializer is not a constant
/* Only a visible definition with a constant initializer is a constant:
   an extern declaration alone, or a volatile object, is not. */
extern const int K;
static int v = K;
