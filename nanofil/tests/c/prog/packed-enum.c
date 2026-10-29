/* GNU packed on an enum gives it the smallest integer type that holds
   its constants, unsigned unless one is negative (svt-av1's
   EbSvtAv1Enc.h, libepoxy, elfutils' color.h). nanofil refused it, and
   before that made every such enum 4 bytes. */
#include <stdio.h>
#include <stddef.h>
typedef enum __attribute__((packed)) { A0, A1, A2 } small;
enum __attribute__((__packed__)) wide { W0, W1 = 300 };
enum neg { N0 = -1, N1 = 100 } __attribute__((packed));
enum neg2 { M0 = -1, M1 = 200 } __attribute__((packed, unused));
enum __attribute__((packed)) big { B0 = 70000 };
enum __attribute__((packed)) nbig { C0 = -40000 };
enum __attribute__((packed)) empty_ish { E0 };
typedef enum { T0, T1 } __attribute__((packed)) tdp;
struct s { char c; small a; enum wide w; enum neg n; tdp t; int i; };
int main(void) {
    printf("%zu %zu %zu %zu %zu %zu %zu %zu\n", sizeof(small), sizeof(enum wide), sizeof(enum neg),
           sizeof(enum neg2), sizeof(enum big), sizeof(enum nbig), sizeof(enum empty_ish), sizeof(tdp));
    printf("%zu %zu %zu %zu %zu %zu\n", sizeof(struct s), offsetof(struct s, a), offsetof(struct s, w),
           offsetof(struct s, n), offsetof(struct s, t), _Alignof(enum wide));
    enum neg x = N0; small y = A2; enum wide z = W1;
    printf("%d %d %d %d\n", x, y, z, (enum neg)255 == N0);
    struct s v = { 1, A1, W1, N0, T1, 9 };
    unsigned char *p = (unsigned char *)&v;
    for (size_t i = 0; i < sizeof v; i++) printf("%02x", p[i]);
    printf("\n");
    return 0;
}
