/* Direct calls of more than 16 words have no fast signature. Each such
   call to one callee still needs a weak thunk sized for its own words:
   here printf gets 18 and then 24, which a shared thunk would truncate. */
#include <stdio.h>

int main(void)
{
    printf("%d %d %d %d %d %d %d %d %d %d %d %d %d %d %d %d %d\n",
           1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17);
    printf("%d %d %d %d %d %d %d %d %d %d %d %d %d %d %d %d %d %d %d %d %d %d %d\n",
           1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23);
    return 0;
}
