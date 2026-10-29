// error: cannot convert double to union
/* A cast to a union needs a member of the operand's type; clang:
   "cast to union type from type 'double' not present in union". */
typedef union {
    long num;
    const char *str;
} op_t;

long f(void) { return ((op_t)1.5).num; }
