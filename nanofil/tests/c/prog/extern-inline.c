// link: lib/extern-inline.c
// C99 external definitions, including declarations after the body.
extern inline int direct(int x) { return x + 1; }
int before(int);
inline int before(int x) { return x + 2; }
inline int after(int x) { return x + 3; }
int after(int);
inline int later_extern(int x) { return x + 4; }
extern inline int later_extern(int);

// These must NOT emit external definitions: the companion supplies them.
inline int c99_only(int x) { return x + 5; }
int gnu_extern(int);
extern inline __attribute__((gnu_inline)) int gnu_extern(int x) { return x + 6; }
extern inline int gnu_suffix(int x) __attribute__((__gnu_inline__));
extern inline int gnu_suffix(int x) __attribute__((__gnu_inline__)) { return x + 7; }

// GNU plain inline is an external definition (unlike C99 plain inline).
inline __attribute__((gnu_inline)) int gnu_plain(int x) { return x + 8; }
static inline int local(int x) { return x + 9; }
int check_external(void);
int main(void) {
    return check_external() || local(1) != 10 || c99_only(1) != 6
        || gnu_extern(1) != 7 || gnu_suffix(1) != 8;
}
