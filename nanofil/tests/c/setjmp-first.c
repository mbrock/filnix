// The first return of setjmp stores the runtime's jmpbuf into the
// caller's buffer with a checked 8-byte pointer store and returns 0; the
// interpreter models only that return (docs/setjmp.md). A buffer the
// store cannot write traps, out of bounds or misaligned. The stored
// pointer is not null, and free through it traps.
#include <setjmp.h>
#include <stdlib.h>

// run: $global_buf
// run: $local_buf 13
// run: $small_buf
// run: $misaligned_buf
// run: $stored_not_null
// run: $free_stored

static jmp_buf b;
static char small[16];
static long words[8];

int global_buf(void) {
    if (setjmp(b))
        return 1;
    return 42;
}

int local_buf(int x) {
    jmp_buf lb;
    int y = x * 3;
    if (_setjmp(lb) != 0)
        return -1;
    return y + 1;
}

int small_buf(void) {
    return _setjmp(*(jmp_buf *)(small + 12));
}

int misaligned_buf(void) {
    return _setjmp(*(jmp_buf *)((char *)words + 4));
}

int stored_not_null(void) {
    static jmp_buf c;
    setjmp(c);
    return *(void **)c != NULL;
}

int free_stored(void) {
    static jmp_buf c;
    setjmp(c);
    free(*(void **)c);
    return 7;
}
