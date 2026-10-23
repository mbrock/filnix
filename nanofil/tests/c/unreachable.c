int reachable(int n) {
    if (n) return 42;
    __builtin_unreachable();
}
// run: $reachable 1
