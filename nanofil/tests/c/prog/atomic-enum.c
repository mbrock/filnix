/* _Atomic of an enum type (bind's adb.h _Atomic(dns_adbstatus_t)): an
   enum is not a qualified type (C11 6.7.2.4p3), though c_types records
   its identity among its reflected qualifiers. */
#include <stdatomic.h>
#include <stdio.h>
typedef enum { IDLE = 0, BUSY = 1, DONE = 7 } status_t;
enum color { RED, GREEN = 5 };
struct find { int id; _Atomic(status_t) status; _Atomic(enum color) c; _Atomic(enum { X = 3, Y }) anon; };
int main(void) {
    struct find f = { 1, BUSY, GREEN, Y };
    atomic_store(&f.status, DONE);
    status_t old = atomic_exchange(&f.status, IDLE);
    f.c = RED;
    f.anon++;
    printf("%d %d %d %d %d %zu\n", f.id, (int)old, (int)atomic_load(&f.status), (int)f.c, (int)f.anon, sizeof f);
    return 0;
}
