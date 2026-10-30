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
static int arr[4];
/* The operands of an asm that traps are evaluated first, as clang's
   EmitAsmStmt does: case 14 prints h, then g. */
static int g(void) { printf("g\n"); fflush(stdout); return 1; }
static int *h(void) { printf("h\n"); fflush(stdout); return &arr[1]; }

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
    case 14: __asm__ volatile ("hlt" : "=r"(*h()) : "r"(g())); break;
    /* Port I/O with fixed registers (kbd's resizecons, util-linux's
       lscpu-virt) and glibc's sys/io.h, whose "Nd" is N{dx} in the IR. */
    case 15: { unsigned char v = 1; unsigned short port = 0x80;
        __asm__ volatile ("outb %0,%1" : : "a"(v), "d"(port)); break; }
    case 16: { unsigned char v; unsigned short port = 0x80;
        __asm__ volatile ("inb %1,%0" : "=a"(v) : "d"(port)); x = v; break; }
    case 17: { unsigned char v; unsigned short port = 0x80;
        __asm__ volatile ("inb %w1,%0" : "=a"(v) : "Nd"(port)); x = v; break; }
    case 18: { unsigned a = 0x564d5868, b = 0, c = 10, d = 0x5658;
        __asm__ volatile ("inl (%%dx), %%eax;" : "=b"(b), "=a"(a), "=c"(c), "=d"(d)
                          : "0"(b), "1"(a), "2"(c), "3"(d) : "memory");
        x = (int)(a ^ b); break; }
    /* zlib-ng's xgetbv as bytes, and sljit's (pcre2) with clang's
       {AT&T|Intel} alternatives. */
    case 19: { unsigned a, d, c = 0;
        __asm__ volatile (".byte 0x0f, 0x01, 0xd0" : "=a"(a), "=d"(d) : "c"(c)); x = (int)(a + d); break; }
    case 20: { unsigned a;
        __asm__ ("xor{l %%ecx, %%ecx | ecx, ecx}\nxgetbv\n" : "=a"(a) : : "rcx", "rdx"); x = (int)a; break; }
    /* nettle-benchmark's cycle counter: the xorl and the mov pass, then
       cpuid writes ebx, which no output or clobber covers. */
    case 21: { unsigned a, d;
        __asm__ volatile ("xorl %%eax,%%eax\nmov %%rbx, %%r10\ncpuid\nrdtsc\nmov %%r10, %%rbx\n"
                          : "=a"(a), "=d"(d) : : "%r10", "%rcx", "cc"); x = (int)(a + d); break; }
    case 22: { unsigned a, b;
        __asm__ volatile ("cpuid" : "=a"(a), "=b"(b) : : "edx"); x = (int)(a + b); break; }
    /* A literal register that the line writes must be covered too; an
       input does not cover it. */
    case 23: { unsigned a, c = 0;
        __asm__ volatile ("xorl %%ecx,%%ecx\nint3" : "=a"(a) : "c"(c)); x = (int)a; break; }
    case 24: { unsigned a;
        __asm__ volatile ("movl %%ebx, %%r8d\n\tINB %%dx,%%al" : "=a"(a) : : "r8"); x = (int)a; break; }
    }
out:
    printf("case %d ran on\n", i);
}

int main(void) {
    for (int i = 0; i < 25; i++) {
        fflush(stdout);
        pid_t pid = fork();
        if (pid == 0) { run(i); _exit(0); }
        int st;
        waitpid(pid, &st, 0);
        printf("case %d: %s\n", i, WIFSIGNALED(st) ? "signal" : "exit");
    }
    return 0;
}
