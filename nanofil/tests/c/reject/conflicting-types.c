// error: conflicting types for 'f'
/* C11 6.7p4: declarations of one function in a scope must have
   compatible types; long and int are not. */
int f(int);
long f(int);
