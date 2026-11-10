int foo(int), __GI_foo(int), wfn(void), __GI_wfn(void), q(void), qq(void);
int __GI_r0(void), r1(void), shown(void), soft(void);
extern int counter, __GI_counter;
extern const int table0[3];
int ext(void) { return 100; }
__attribute__((weak)) int wq(void) { return 99; }
int __GI_ext(void) { return 200; }
int from_clang(void)
{
    return foo(10) + __GI_foo(20) * 100 + counter + (&counter == &__GI_counter)
        + wfn() + __GI_wfn() + q() + qq() + __GI_r0() + r1() + shown() + soft()
        + table0[2] * 1000;
}
