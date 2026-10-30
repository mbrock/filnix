// error: :4: redeclaration of 's' with a different type
/* A pointer's target qualifiers are part of its type (C11 6.7.6.1p2). */
extern const char *s;
char *s;
