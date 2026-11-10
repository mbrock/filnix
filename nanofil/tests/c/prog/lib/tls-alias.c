/* clang's side of tls-alias.c: the alias, through its getter. */
extern __thread int lerr;

int clang_side(int v)
{
    int old = lerr;
    lerr = v;
    return old * 100 + lerr;
}
