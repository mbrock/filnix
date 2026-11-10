// The smallest honest glibc-using program: main returns the length of
// a string by glibc's own strlen, linked in as nanofil's IR of user
// glibc's string/strlen.c, not called through a contract.
// Proved never to panic in rocq/glibc/LenLogic.v.
#include <string.h>

static const char msg[] = "hello, glibc";

int main(void) { return (int)strlen(msg); }
