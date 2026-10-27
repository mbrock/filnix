// error: a is a variable length array with static storage
int f(int n) { static int a[n]; return a[0]; }
