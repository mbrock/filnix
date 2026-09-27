#include <dlfcn.h>
#include <stdio.h>
int which(void);
int main(int argc, char **argv) {
  void *h = dlopen(argv[1], RTLD_LOCAL | RTLD_NOW);
  if (!h) { printf("dlopen: %s\n", dlerror()); return 2; }
  int (*f)(void) = (int (*)(void))dlsym(h, "which");
  int (*cw)(void) = (int (*)(void))dlsym(h, "callwhich");
  int (*(*wp)(void))(void) = (int (*(*)(void))(void))dlsym(h, "whichptr");
  printf("which()=%d dlsym(which)()=%d callwhich()=%d whichptr()()=%d\n", which(), f(), cw(), wp()());
  return 0;
}
