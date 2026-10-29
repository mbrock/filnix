// error: bypasses the initialization of a variable with __attribute__((cleanup))
/* clang: "cannot jump from this goto statement to its label". */
static void drop(int *p) { (void)p; }
int f(int k) {
    if (k) goto in;
    {
        int v __attribute__((cleanup(drop))) = 1;
    in:
        return v;
    }
}
