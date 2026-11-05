// Wide inlining (docs/perf.md item 20) and what it leans on: callees
// that call other functions, always_inline and noinline, a callee with
// one call site holding a local array indexed by a variable, a 12-byte
// struct returned in two words and copied as a long and a word,
// out-parameters that stop escaping once their callee is inlined, and
// double locals, read after a store on every path or only on the paths
// the program takes. Each result goes through printf, so a wrong value
// shows as a mismatch with filcc.
#include <stdio.h>
#include <string.h>

typedef struct { int off, len, back; } match;

static inline __attribute__((always_inline)) unsigned get_varint(const unsigned char *p,
                                                                 unsigned *v) {
    unsigned x = 0, shift = 0, n = 0;
    do {
        x |= (unsigned)(p[n] & 0x7f) << shift;
        shift += 7;
    } while (p[n++] & 0x80);
    *v = x;
    return n;
}

static int __attribute__((noinline)) cold(int x) { return x * 3 + 1; }

static unsigned decode(const unsigned char *p, int count, unsigned *sum) {
    unsigned s = 0, at = 0;
    for (int i = 0; i < count; i++) {
        unsigned v;
        at += get_varint(p + at, &v);
        s += v;
    }
    *sum = s;
    return at;
}

static inline __attribute__((always_inline)) match widest(const char *s, int n, int from) {
    match m = {from, 0, 0};
    for (int i = from; i < n; i++) {
        int len = 0;
        while (i + len < n && s[i + len] == s[from + len] && len < 16) len++;
        if (len > m.len && i != from) { m.off = i; m.len = len; m.back = i - from; }
    }
    return m;
}

// One call site: an array of 100 ints indexed by a variable (a heap
// object either way) and a nested call.
static int sorted_sum(const int *xs, int n) {
    int stack[100];
    int sp = 0;
    for (int i = 0; i < n && sp < 100; i++) stack[sp++] = xs[i];
    for (int i = 1; i < sp; i++)
        for (int j = i; j > 0 && stack[j - 1] > stack[j]; j--) {
            int t = stack[j]; stack[j] = stack[j - 1]; stack[j - 1] = t;
        }
    int s = 0;
    for (int i = 0; i < sp; i++) s = s * 7 + stack[i];
    return s + cold(sp);
}

static double mean(const double *xs, int n) {
    double sum = 0.0;
    for (int i = 0; i < n; i++) sum += xs[i];
    return n ? sum / n : 0.0;
}

// The double is stored only when the test that guards its read holds.
static double guarded(const double *xs, int n, int k) {
    double out = -1.0;
    for (int i = 0; i < n; i++) {
        double v;
        int ok = 0;
        if (xs[i] > 0.0) { v = xs[i] * k; ok = 1; }
        if (ok) out += v;
    }
    return out;
}

int main(void) {
    unsigned char buf[] = {0x05, 0x96, 0x01, 0xff, 0x7f, 0x80, 0x80, 0x01, 0x2a};
    unsigned sum = 0;
    unsigned used = decode(buf, 5, &sum);
    printf("decode: used %u sum %u\n", used, sum);

    const char *text = "abcabcabcxabcabcab";
    int n = (int)strlen(text);
    match best = {0, 0, 0};
    for (int from = 0; from < 4; from++) {
        match m = widest(text, n, from);
        match copy;
        memcpy(&copy, &m, sizeof m);
        if (copy.len > best.len) best = copy;
        printf("widest %d: %d %d %d\n", from, m.off, m.len, m.back);
    }
    printf("best: %d %d %d\n", best.off, best.len, best.back);

    int xs[] = {9, -2, 7, 7, 0, 31, -8, 4};
    printf("sorted_sum: %d\n", sorted_sum(xs, 8));

    double ds[] = {1.5, -2.25, 4.0, 0.0, 8.125};
    printf("mean: %.6f\n", mean(ds, 5));
    printf("guarded: %.6f\n", guarded(ds, 5, 3));
    printf("cold: %d\n", cold(14));
    return 0;
}
