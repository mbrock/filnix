int constants(int n) {
    int side = 0;
    int a = __builtin_constant_p(2 * 3);
    int b = __builtin_constant_p(side++);
    int c = __builtin_constant_p(n);
    return a + side + b + c;
}
// run: $constants 7
