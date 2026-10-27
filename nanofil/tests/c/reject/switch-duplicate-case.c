// error: duplicate case value 0
// 0x100000000 converts to the int 0 (C11 6.8.4.2p3, 6.3.1.3p3).
int f(int x) {
    switch (x) {
    case 0: return 1;
    case 0x100000000: return 2;
    }
    return 3;
}
