// error: inline asm "rdtsc" is not supported
static inline unsigned ticks(void) {
    unsigned lo, hi;
    __asm__ volatile("rdtsc" : "=a"(lo), "=d"(hi));
    return lo ^ hi;
}
unsigned f(void) { return ticks(); }
