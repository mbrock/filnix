// trap-reason
/* The asm that filcc certainly compiles to a run-time error, each run in
   its own child: nanofil must report the same reason (c_lower
   asm_runtime_reason/6). GLib's G_BREAKPOINT is case 0. The asm that
   filcc may accept, or that only its validator's full table refuses
   (cpuid, an unknown mnemonic), nanofil refuses at compile time:
   reject/asm-cpuid.c and reject/asm-unknown-mnemonic.c. */
#include <stdio.h>
#include <unistd.h>
#include <sys/wait.h>

static int x = 1;
static unsigned short cw;
static int *p = &x;

static void run(int i) {
    switch (i) {
    case 0: __asm__ __volatile__ ("int $03"); break;
    case 1: __asm__ volatile ("int $3" : : "r"(p)); break;
    case 2: __asm__ volatile ("fnstcw %0" : "=m"(cw)); break;
    case 3: __asm__ volatile ("nop" : "=r"(p)); break;
    case 4: __asm__ goto ("jmp %l0" : : : : out); break;
    case 5: __asm__ volatile ("lock; incl %0" : "+r"(x) : : "memory", "cc"); break;
    case 6: __asm__ volatile ("\n\t  INT $3"); break;
    case 7: __asm__ volatile ("syscall" : "=a"(x) : "a"(39)); break;
    case 8: __asm__ volatile ("rep movsb"); break;
    case 9: __asm__ volatile ("hlt\n\tnop"); break;
    /* longlong.h's umul_ppmm and sub_ddmmss (coreutils' factor), whose
       register-or-memory inputs clang passes by value: the validator
       refuses the constraint. */
    case 10: { unsigned long h, l, u = 5, v = 6;
        __asm__ ("mulq %3" : "=a"(l), "=d"(h) : "%0"(u), "rm"(v)); x = (int)(h + l); break; }
    case 11: { unsigned long h, l, a = 1, b = 2, c = 3, d = 4;
        __asm__ ("subq %5,%q1\n\tsbbq %3,%q0" : "=r"(h), "=&r"(l) : "0"(a), "rme"(c), "1"(b), "rme"(d));
        x = (int)(h + l); break; }
    case 12: __asm__ volatile ("nop" : "+r"(x) : "g"(x)); break;
    case 13: __asm__ volatile ("bswap %0" : "=r"(x) : "0"(x), "i"(3)); break;
    }
out:
    printf("case %d ran on\n", i);
}

int main(void) {
    for (int i = 0; i < 14; i++) {
        fflush(stdout);
        pid_t pid = fork();
        if (pid == 0) { run(i); _exit(0); }
        int st;
        waitpid(pid, &st, 0);
        printf("case %d: %s\n", i, WIFSIGNALED(st) ? "signal" : "exit");
    }
    return 0;
}
