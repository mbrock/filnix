// error: an asm operand must have integer or floating type
/* filcc analyses an empty asm with pointer operands; nanofil refuses it. */
int f(int *p) { __asm__("" : "+r"(p)); return *p; }
