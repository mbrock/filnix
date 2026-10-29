// error: inline asm "frobnicate %0" is not supported: nanofil cannot check its instructions
/* filcc's validator refuses an unknown mnemonic at run time, but only
   its full table says a mnemonic is unknown; nanofil knows the refused
   mnemonics it has probed (c_types filcc_refused_mnemonic/1) and refuses
   any other asm at compile time. */
int main(void) {
    int x = 1;
    __asm__ volatile ("frobnicate %0" : "+r"(x));
    return x - 1;
}
