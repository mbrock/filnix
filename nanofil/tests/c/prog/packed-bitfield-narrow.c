/* A packed bit-field wider than its struct (parted's one-byte
   FatClusterInfo: unsigned int:6 and an enum :2) is accessed in a
   narrower integer of its sign, as clang does, so an array of them
   never reads past its end. */
#include <stdio.h>
#include <stdlib.h>
enum F { F0 = 0, F1, F2, F3 };
typedef enum F FatClusterFlag;
struct __attribute__((packed)) CI { unsigned int units_used:6; FatClusterFlag flag:2; };
struct __attribute__((packed)) S2 { char c; int s:11; unsigned u:3; };
int main(void)
{
    struct CI *c = calloc(4, sizeof *c);
    c[3].units_used = 300; c[3].flag = 5; c[1].flag = F2;
    struct S2 *s = calloc(1, sizeof *s);
    s->s = -700; s->u = 9; s->c = 'k';
    static struct CI g = { 33, F3 };
    struct CI l = { 61, F1 };
    printf("%zu %zu %d %d %d %d %d %u %c %d %d %d %d\n", sizeof *c, sizeof *s, c[3].units_used, c[3].flag, c[1].flag,
           c[3].units_used - 50, s->s, s->u, s->c, g.units_used, g.flag, l.units_used, l.flag);
    c[3].units_used += 2;
    printf("%d %d\n", c[3].units_used, c[3].flag);
    return 0;
}
