// error: duplicate case value 5
/* Overlapping case ranges are duplicate cases (GCC and clang: "duplicate
   case value"). */
int f(int c)
{
    switch (c) {
    case 1 ... 5: return 1;
    case 5 ... 9: return 2;
    }
    return 0;
}
