extern int counter_alias, table_alias[4], weak_obj_alias;
extern const char *greeting_alias;
int sum_alias(int n, ...);
int sum_weak(int n, ...);
int triple_alias(int);
int target_alias(int);
int from_clang(void)
{
    table_alias[0] += 10;
    return counter_alias * 1000 + table_alias[0] + sum_alias(2, 20, 30) + sum_weak(1, 400)
        + triple_alias(7) + greeting_alias[1] + weak_obj_alias;
}
int same_from_clang(int (*f)(int), int *p)
{
    counter_alias = 42;
    return (f == target_alias) * 10 + (p == &counter_alias) + target_alias(1) * 100;
}
