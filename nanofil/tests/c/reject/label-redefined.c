// error: :8: redefinition of label again
/* A label is defined once in a function (C11 6.8.1p3), even in an inner
   block; clang refuses the second definition. */
int f(int x)
{
again:
    if (x-- > 3) goto again;
    { again: x++; }
    return x;
}
