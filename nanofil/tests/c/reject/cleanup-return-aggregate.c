// error: returning the aggregate cleanup variable r is not supported
// clang runs z on the returned object (r is its named-return-value
// candidate), so mk().a is 0; copying r before the cleanup gives 1.
struct S { int a, b; };
static void z(struct S *s) { s->a = 0; }
struct S mk(void) {
    __attribute__((cleanup(z))) struct S r = {1, 2};
    return r;
}
