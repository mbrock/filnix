// error: compound assignment += to an _Atomic object is an atomic read-modify-write
_Atomic(int) counter;
void bump(void) { counter += 2; }
