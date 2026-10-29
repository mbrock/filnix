// error: attribute ms_abi is not supported
/* Calling: the Windows convention. */
int __attribute__((ms_abi)) f(int a, int b) { return a + b; }
