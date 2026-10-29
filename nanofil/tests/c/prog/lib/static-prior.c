/* The other unit of static-prior.c: the same internal functions, each
   its own. */
static inline int heap_size(const int *s);
int heap_size(const int *s) { return s[0] * 100; }
static int helper(void);
extern int helper(void) { return 2; }
int other_unit(void)
{
    int s[1] = {4};
    return heap_size(s) + helper();
}
