// error: packed pointers
/* Under #pragma pack(4) the pointer would be 4-aligned, where Fil-C
   keeps no capability. */
#pragma pack(4)
struct S { char c; int *p; };
#pragma pack()
int f(struct S *s) { return *s->p; }
