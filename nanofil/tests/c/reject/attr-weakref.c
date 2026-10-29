// error: weakref declaration of g must have internal linkage
/* weakref names another symbol from a static declaration; clang refuses
   it on an extern one (c_lower weakref_item/3). */
int g(void) __attribute__((weakref("h")));
