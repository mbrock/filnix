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
    }
out:
    printf("case %d ran on\n", i);
}

int main(void) {
    for (int i = 0; i < 10; i++) {
        fflush(stdout);
        pid_t pid = fork();
        if (pid == 0) { run(i); _exit(0); }
        int st;
        waitpid(pid, &st, 0);
        printf("case %d: %s\n", i, WIFSIGNALED(st) ? "signal" : "exit");
    }
    return 0;
}
