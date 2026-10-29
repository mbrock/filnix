// error: a case range of more than 4096 values is not supported
/* nanofil expands a GNU case range into its values, and refuses one
   too large to expand. */
int f(int x) { switch (x) { case 0 ... 0x7fffffff: return 1; } return 0; }
