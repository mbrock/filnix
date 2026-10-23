// error: cannot assign ptr(func(int,[int],fixed)) to ptr(func(void,[],fixed))
int g(int);
void f(void) { void (*fp)(void) = 0; fp = g; (void)fp; }
