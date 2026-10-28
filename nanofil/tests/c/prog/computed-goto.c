// GNU labels as values: a threaded bytecode interpreter as oniguruma
// (jq's regex engine) and Lua's jump table write it. A static table of
// label addresses, direct threading through addresses stored in heap
// operations, label comparisons, and a second function whose labels
// are numbered independently.
#include <stdio.h>
#include <stdlib.h>

enum { PUSH, ADD, MUL, DUP, JNZ, DEC, PRINT, HALT };
struct op { int code; long arg; const void *addr; };

static long run(struct op *prog, size_t n, int direct) {
    static const void *const table[] = {
        &&L_PUSH, &&L_ADD, &&L_MUL, &&L_DUP, &&L_JNZ, &&L_DEC, &&L_PRINT, &&L_HALT,
    };
    long stack[64];
    int sp = 0;
    struct op *p = prog;
    if (direct)
        for (size_t i = 0; i < n; i++)
            prog[i].addr = table[prog[i].code];
#define NEXT do { if (direct) goto *(p->addr); goto *table[p->code]; } while (0)
    NEXT;
L_PUSH: stack[sp++] = p->arg; p++; NEXT;
L_ADD:  sp--; stack[sp - 1] += stack[sp]; p++; NEXT;
L_MUL:  sp--; stack[sp - 1] *= stack[sp]; p++; NEXT;
L_DUP:  stack[sp] = stack[sp - 1]; sp++; p++; NEXT;
L_JNZ:  if (stack[--sp]) p = prog + p->arg; else p++; NEXT;
L_DEC:  stack[sp - 1]--; p++; NEXT;
L_PRINT: printf("%ld\n", stack[sp - 1]); p++; NEXT;
L_HALT: return sp ? stack[sp - 1] : -1;
}

static int classify(int n) {
    void *where = n < 0 ? &&negative : n == 0 ? &&zero : &&positive;
    if (where == &&zero) return 0;
    goto *where;
negative: return -1;
zero: return 100;
positive: return 1;
}

int main(void) {
    // acc = 1; n = 10; do { acc *= n; print acc; n--; } while (n)
    struct op prog[] = {
        { PUSH, 1 }, { PUSH, 10 },
        { DUP, 0 }, { PRINT, 0 },          // 2: print n
        { DUP, 0 }, { JNZ, 7 }, { HALT, 0 },
        { DEC, 0 }, { DUP, 0 }, { JNZ, 2 }, { HALT, 0 },
    };
    size_t n = sizeof prog / sizeof prog[0];
    struct op *heap = malloc(sizeof prog);
    for (size_t i = 0; i < n; i++) heap[i] = prog[i];
    printf("%ld\n", run(prog, n, 0));
    printf("%ld\n", run(heap, n, 1));
    struct op sum[] = { { PUSH, 6 }, { PUSH, 7 }, { MUL, 0 }, { PUSH, 3 }, { ADD, 0 }, { HALT, 0 } };
    printf("%ld %ld\n", run(sum, 6, 0), run(sum, 6, 1));
    printf("%d %d %d\n", classify(-5), classify(0), classify(9));
    free(heap);
    return 0;
}
