/* A backslash, then spaces or tabs, then a newline splices lines, as in
   clang and GCC: the comment and the macro below each continue onto
   their next line. (The trailing whitespace after each backslash is
   the test; keep it.) */
#include <stdio.h>
#define TWO 1 + \  
    1
int main(void) {
    int x = 1;
    // note \	 
    x = 2;
    printf("%d %d\n", x, TWO);
    return 0;
}
