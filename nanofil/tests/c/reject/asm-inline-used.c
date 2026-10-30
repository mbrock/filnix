// error: inline asm "rdtsc; lfence" is not supported
static inline unsigned ticks(void) {
    unsigned lo, hi;
    __asm__ volatile("rdtsc; lfence" : "=a"(lo), "=d"(hi));
    return lo ^ hi;
}
unsigned f(void) { return ticks(); }
