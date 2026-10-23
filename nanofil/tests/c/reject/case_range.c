// error: GNU case ranges are not supported
int f(int x) { switch (x) { case 1 ... 3: return 1; } return 0; }
