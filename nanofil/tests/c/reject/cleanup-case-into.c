// error: cannot jump from switch statement to this case label
static void drop(int *p) { (void)p; }
int f(int k) {
    switch (k) {
    case 0: {
        int v __attribute__((cleanup(drop))) = 1;
    case 1:
        return v;
    }
    }
    return 0;
}
