#include <stdio.h>
void pass_rows(char *a, char *b);
void use_rows(char **rows) { printf("%s %s\n", rows[0], rows[1]); }
int main(void) { char a[] = "hello", b[] = "world"; pass_rows(a, b); return 0; }
