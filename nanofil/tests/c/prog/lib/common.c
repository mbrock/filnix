int shared;
int counted = 5;
struct rec { long n; int *p; } rec;
static int own = 9;
void bump(void) { shared += 1; counted += 1; rec.n = 7; *rec.p += 2; }
int lib_own(void) { return own; }
