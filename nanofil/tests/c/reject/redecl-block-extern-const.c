// error: :5: redeclaration of 'y' with a different type
/* The block-scope declaration's scope has ended, but it declared the
   same object (C11 6.2.7p2); clang refuses the file-scope one. */
int use(void) { extern const int y; return y; }
int y;
