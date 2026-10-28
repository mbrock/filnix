// cflags: -std=c23
// The C23 spellings gnulib's headers use under -std=gnu23 (GNU sed):
// bool, true, false, nullptr, static_assert (also without a message),
// alignas, alignof, thread_local and standard attributes.
#include <stddef.h>
#include <stdio.h>

typedef typeof(nullptr) my_nullptr_t;
static_assert(sizeof(bool) == 1);
static_assert(alignof(long) == 8, "long");

[[deprecated]] int old_api(int);
static thread_local int counter;
struct s { char c; bool flag; };

static int pick(int k, [[maybe_unused]] int unused) {
    int r = 0;
    switch (k) {
    case 0: r += 1; [[fallthrough]];
    case 1: r += 10; break;
    default: unreachable();
    }
    return r;
}

static bool is_null(const void *p [[maybe_unused]]) { return p == nullptr; }

int main(void) {
    bool b = 256, z = 0.25, f = false;
    my_nullptr_t np = nullptr;
    char *cp = nullptr;
    printf("%d %d %d %zu %zu\n", b, z, f, sizeof true, sizeof(struct s));
    printf("%d %d %d\n", _Generic(true, bool: 1, int: 2, default: 3),
           true + true, (int)false - 1);
    printf("%d %d %d\n", is_null(np), is_null(cp), is_null(&counter));
    printf("%d %d %zu\n", pick(0, 0), pick(1, 0), alignof(struct s));
    counter += true;
    return counter - 1;
}
