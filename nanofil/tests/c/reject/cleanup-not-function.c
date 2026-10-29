// error: 'cleanup' argument drop is not a function
int drop;
int f(void) {
    int v __attribute__((cleanup(drop))) = 1;
    return v;
}
