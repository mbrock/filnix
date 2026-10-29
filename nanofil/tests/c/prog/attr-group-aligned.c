/* An aligned attribute listed with others in one __attribute__((...))
   (c_types alignment_requests/3): GLib's generated resources declare
   their data with section(...) and aligned(...) together, and the other
   items still apply. Each alignment is stricter than the type's, so a
   dropped request shows in the offsets and addresses. */
#include <stdio.h>
#include <stddef.h>
#include <stdint.h>

#define SECTION __attribute__ ((section (".gresource.test"), aligned (sizeof(void *) > 8 ? sizeof(void *) : 64)))
static const SECTION union { const unsigned char data[5]; const double alignment; void * const ptr; }
    resource = { { 1, 2, 3, 4, 5 } };

struct s {
    char c;
    int x __attribute__((unused, aligned(16)));
    char d __attribute__((__aligned__(32), deprecated));
};

static char buf[3] __attribute__((used, aligned(128), unused));

int main(void) {
    printf("%d %d %d\n", resource.data[2], (int)((uintptr_t)&resource % 64), (int)_Alignof(struct s));
    printf("%zu %zu %zu\n", offsetof(struct s, x), offsetof(struct s, d), sizeof(struct s));
    printf("%d\n", (int)((uintptr_t)buf % 128));
    return 0;
}
