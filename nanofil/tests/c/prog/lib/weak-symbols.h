/* Weak symbols shared by nanofil's and clang's objects
   (weak-symbols.c, lib/weak-symbols.c). n_ names are defined by
   nanofil's object, c_ ones by clang's. */
int n_weak_alone(int x);      /* nanofil, weak, nothing overrides it */
int c_weak_alone(int x);      /* clang, weak */
int n_weak_overridden(int x); /* nanofil weak, clang strong */
int c_weak_overridden(int x); /* clang weak, nanofil strong */
extern int n_wdata_overridden; /* nanofil weak, clang strong */
extern int c_wdata_overridden; /* clang weak, nanofil strong */
int both_weak(void);          /* weak in both: the linker keeps one */
int both_weak_from_c(void);
int n_pragma(void);           /* nanofil, #pragma weak */
int n_alias(int x);           /* nanofil, weak alias of a static */
int c_alias(int x);           /* clang, #pragma weak c_alias = ... */
int n_strong_for_c(int x);    /* nanofil strong; clang refers weakly */
long c_probe(void);           /* clang's view of the weak symbols */
