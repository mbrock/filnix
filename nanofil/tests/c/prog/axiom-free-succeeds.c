// Runtime axiom "Free succeeds" (docs/runtime-axioms.md): free of the null
// pointer returns and changes nothing, and free of the base pointer of a
// live heap object returns, for every way a heap object is made (malloc of
// 0 bytes to 1 MiB, calloc, realloc, aligned_alloc, posix_memalign, strdup),
// before and after collections, and changes no other object: a neighbour's
// bytes and the pointer it stores read as before, and a pointer stored to
// the freed object loads back at its address. The freed object's bounds are
// then empty: its capability traps. The model's other heap objects free
// too: an escaping local, a VLA and an alloca, which nanofil keeps on the
// heap, and the startup objects argv and argv[0]. The obvious wrong
// strengthenings are false: a second free traps (the object must be live),
// and a global's base, an mmap'd object and an interior pointer trap (it
// must be a heap object's base).
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <fcntl.h>
#include <signal.h>
#include <sys/wait.h>
#include <sys/mman.h>
#include <stdfil.h>
static char *volatile target;
static long global[4];
static void free_target(void) { free(target); }
static void read_target(void) { volatile char x = target[0]; (void)x; }
static void free_twice(void) { free(target); free(target); }
static void free_local(void) { long x = 7; target = (char *)&x; free(target); }
static volatile int vla_size = 24;
static void free_vla(void) { char v[vla_size]; target = v; free(target); }
static void free_alloca(void) { target = __builtin_alloca(16); free(target); }
// trapped(f): f, run in a child whose stderr is closed, ends in a Fil-C
// trap (SIGTRAP), not a normal exit.
static int trapped(void (*f)(void)) {
    fflush(stdout);
    pid_t c = fork();
    if (c == 0) { dup2(open("/dev/null", O_WRONLY), 2); f(); _exit(0); }
    int st;
    waitpid(c, &st, 0);
    return WIFSIGNALED(st) && WTERMSIG(st) == SIGTRAP;
}
static const char *yes(int b) { return b ? "yes" : "no"; }
// A neighbour: 64 bytes reading i * 3 + 1 at i, then a stored pointer to
// a live object holding "kept".
struct neighbour { char bytes[64]; char *ptr; };
static struct neighbour *nb;
static char *kept;
static int neighbour_intact(void) {
    for (int i = 0; i < 64; i++)
        if (nb->bytes[i] != (char)(i * 3 + 1)) return 0;
    return nb->ptr == kept && strcmp(nb->ptr, "kept") == 0;
}
// frees(p): free of p returns, the neighbour is intact, and p's capability
// then traps.
static int frees(char *p) {
    target = p;
    int returned = !trapped(free_target);
    free(p);
    int intact = neighbour_intact();
    target = p;
    return returned && intact && trapped(read_target);
}
int main(int argc, char **argv) {
    (void)argc;
    kept = strdup("kept");
    nb = malloc(sizeof *nb);
    for (int i = 0; i < 64; i++) nb->bytes[i] = (char)(i * 3 + 1);
    nb->ptr = kept;
    target = 0;
    printf("free of null returns: %s\n", yes(!trapped(free_target)));
    free(0);
    printf("and changes nothing: %s\n", yes(neighbour_intact()));
    // A zero-byte object traps on every read already, so only its free
    // returning and the neighbour are tested.
    target = malloc(0);
    printf("malloc(0): %s\n", yes(!trapped(free_target) && neighbour_intact()));
    printf("malloc(1): %s\n", yes(frees(malloc(1))));
    printf("malloc(16): %s\n", yes(frees(malloc(16))));
    printf("malloc(4096): %s\n", yes(frees(malloc(4096))));
    printf("malloc(1 MiB): %s\n", yes(frees(malloc(1 << 20))));
    printf("calloc: %s\n", yes(frees(calloc(8, 8))));
    char *r = malloc(8);
    r = realloc(r, 1000);
    printf("realloc: %s\n", yes(frees(r)));
    printf("aligned_alloc: %s\n", yes(frees(aligned_alloc(64, 128))));
    void *pm = 0;
    posix_memalign(&pm, 256, 512);
    printf("posix_memalign: %s\n", yes(frees(pm)));
    printf("strdup: %s\n", yes(frees(strdup("hello"))));
    char *aged = malloc(48);
    zgc_request_and_wait();
    zgc_request_and_wait();
    printf("after collections: %s\n", yes(frees(aged)));
    // An object that stores a pointer to the one freed: the stored pointer
    // loads back at the freed object's address, and traps.
    char *q = malloc(32);
    char **holder = malloc(sizeof(char *));
    *holder = q;
    printf("an object storing a pointer to it: %s\n", yes(frees(q)));
    target = *holder;
    printf("its stored pointer loads back: %s\n", yes(*holder == q && trapped(read_target)));
    // Freeing the holder leaves the object it points to live.
    char *held = malloc(32);
    strcpy(held, "held");
    *holder = held;
    printf("free of a holder: %s\n", yes(frees((char *)holder)));
    printf("leaves what it points to: %s\n", yes(strcmp(held, "held") == 0));
    printf("an escaping local: %s\n", yes(!trapped(free_local)));
    printf("a VLA: %s\n", yes(!trapped(free_vla)));
    printf("an alloca: %s\n", yes(!trapped(free_alloca)));
    target = argv[0];
    printf("argv[0]: %s\n", yes(!trapped(free_target)));
    target = (char *)argv;
    printf("argv: %s\n", yes(!trapped(free_target)));
    target = malloc(32);
    printf("a second free traps: %s\n", yes(trapped(free_twice)));
    target = mmap(0, 4096, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
    printf("free of an mmap'd object traps: %s\n", yes(target != MAP_FAILED && trapped(free_target)));
    target = (char *)global;
    printf("free of a global traps: %s\n", yes(trapped(free_target)));
    target = (char *)malloc(32) + 8;
    printf("free of an interior pointer traps: %s\n", yes(trapped(free_target)));
    return 0;
}
