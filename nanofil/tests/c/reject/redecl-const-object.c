// error: :4: redeclaration of 'x' with a different type
/* C11 6.7.3p10, 6.2.7p2: const int and int are not compatible; clang refuses. */
extern const int x;
int x = 5;
