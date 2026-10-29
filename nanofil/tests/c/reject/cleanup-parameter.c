// error: incompatible
/* clang: "'cleanup' function 'drop' parameter has type 'char *' which is
   incompatible with type 'int *'". */
static void drop(char *p) { (void)p; }
int f(void) {
    int v __attribute__((cleanup(drop))) = 1;
    return v;
}
