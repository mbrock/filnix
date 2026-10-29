/* GNU's cleanup attribute: f(&v) runs when v's scope ends, on every way
   out of it (falling off the block, return, break, continue, goto), in
   reverse order of declaration, after a return's value is computed.
   GLib's g_autoptr and g_autofree are built on it (dconf's leak tests
   leaked a GDBusConnection reference when nanofil ignored it). */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static char trace[512];
static int refs;

static void note(const char *s) { strcat(trace, s); }
static void drop(int *p) { char b[16]; snprintf(b, sizeof b, "~%d ", *p); note(b); }
static void unref(char **p) { if (*p) { refs--; free(*p); } }
static char *ref(const char *s) { refs++; return strdup(s); }
static void *steal(void *pp) { void **p = pp; void *r = *p; *p = NULL; return r; }

static int block_exit(void) {
    {
        int a __attribute__((cleanup(drop))) = 1;
        int b __attribute__((cleanup(drop))) = 2;
        note("body ");
    }
    note("after ");
    return 0;
}

static int early(int k) {
    int a __attribute__((cleanup(drop))) = 10;
    if (k) {
        int b __attribute__((cleanup(drop))) = 11;
        return a + b;              /* the value is read before the cleanups */
    }
    a = 12;
    return a;
}

static int loops(void) {
    int sum = 0;
    for (int i = 0; i < 4; i++) {
        int v __attribute__((cleanup(drop))) = 20 + i;
        if (i == 1) continue;
        if (i == 3) break;
        sum += v;
    }
    int j = 0;
    while (1) {
        int w __attribute__((cleanup(drop))) = 30 + j;
        switch (j) {
        case 0: { int s __attribute__((cleanup(drop))) = 40; j++; break; }
        default: goto out;
        }
    }
out:
    note("out ");
    return sum;
}

static int backward(void) {
    int n = 0;
again:
    {
        int v __attribute__((cleanup(drop))) = 50 + n;
        if (++n < 3) goto again;
    }
    return n;
}

static char *keep(void) {
    __attribute__((cleanup(unref))) char *s = NULL;
    s = ref("kept");
    return steal(&s);
}

static int lose(void) {
    __attribute__((cleanup(unref))) char *s = ref("lost");
    return (int)strlen(s);
}

static int stmt_expr(void) {
    int r = ({ int t __attribute__((cleanup(drop))) = 60; t + 1; });
    note("se ");
    return r;
}

static int for_init(void) {
    int n = 0;
    for (int k __attribute__((cleanup(drop))) = 70; n < 2; n++)
        note("f ");
    return n;
}

int main(void) {
    block_exit(); printf("%s\n", trace); trace[0] = 0;
    printf("%d ", early(1)); printf("%d ", early(0)); printf("%s\n", trace); trace[0] = 0;
    printf("%d %s\n", loops(), trace); trace[0] = 0;
    printf("%d %s\n", backward(), trace); trace[0] = 0;
    char *k = keep();
    printf("%s %d ", k, refs); free(k); refs--;
    printf("%d %d\n", lose(), refs);
    printf("%d %s\n", stmt_expr(), trace); trace[0] = 0;
    printf("%d %s\n", for_init(), trace);
    return 0;
}
