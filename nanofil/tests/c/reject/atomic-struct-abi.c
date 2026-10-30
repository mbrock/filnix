// error: a function with external linkage or called through a pointer cannot take or return an _Atomic struct or union
/* filcc passes a struct holding an _Atomic struct by its own rules (it
   returns this one through memory), so it cannot cross to code nanofil
   did not compile. */
typedef struct { char a, b, c; } t3;
struct w3 { _Atomic(t3) v; };
struct w3 give3(void);
int f(void) { struct w3 r = give3(); t3 v = r.v; return v.a; }
