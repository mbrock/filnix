/* Source lines in the IR: tests/unit.pl's source_locations. */
long fib(int n) {
    return n < 2 ? n : fib(n - 1) + fib(n - 2);
}

long sum(int n) {
    long s = 0;
    for (int i = 0; i < n; i++)
        s += fib(i);
    return s;
}
// run: $sum 10
// run: $fib 7
