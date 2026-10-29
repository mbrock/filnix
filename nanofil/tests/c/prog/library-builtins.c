/* GCC and clang declare __builtin_F for library functions F whether or
   not a header declares F: bison's parsers call __builtin_memcpy without
   <string.h> (netcdf's dcetab.c). No header is included here. */
int printf(const char *, ...);

int main(void)
{
    char *p = __builtin_malloc(32);
    __builtin_memset(p, 0, 32);
    __builtin_strcpy(p, "hello");
    __builtin_strcat(p, ", world");
    char *q = __builtin_calloc(4, 8);
    __builtin_memcpy(q, p, __builtin_strlen(p) + 1);
    __builtin_memmove(q + 1, q, 5);
    printf("%s|%s|%d %d %d|%s|%s\n", p, q, __builtin_strcmp(p, q) > 0, __builtin_memcmp(p, q, 1),
           __builtin_strncmp(p, "help", 3), __builtin_strchr(p, 'w'), __builtin_strstr(p, "lo"));
    p = __builtin_realloc(p, 64);
    printf("%zu %d %ld\n", __builtin_strlen(p), __builtin_abs(-3), __builtin_labs(-4L));
    __builtin_free(q);
    __builtin_free(p);
    if (__builtin_strlen("x") != 1)
        __builtin_abort();
    return 0;
}
