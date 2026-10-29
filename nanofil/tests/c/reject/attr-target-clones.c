// error: attribute target_clones is not supported
__attribute__((target_clones("avx2", "default"))) int f(void) { return 1; }
