import sys

# A JIT-trace-shaped function: N blocks of type guards and an overflow-checked add.
n = int(sys.argv[1])
print("""typedef struct { long v; int type; } zval;
typedef struct { zval *vars; void *ip; } ed;
extern void *helper_add(ed *fp, zval *a, zval *b, zval *r);
extern void *exit_to_interp(ed *fp, int which);
void *trace(ed *fp) {
  zval *v = fp->vars;""")
for i in range(n):
    a, b, c = i % 7, (i * 3 + 1) % 7, (i * 5 + 2) % 7
    print(f"""  {{
    zval *x{i} = &v[{a}]; zval *y{i} = &v[{b}]; zval *r{i} = &v[{c}];
    if (x{i}->type != 4) return exit_to_interp(fp, {2 * i});
    if (y{i}->type != 4) return exit_to_interp(fp, {2 * i + 1});
    long s{i};
    if (__builtin_add_overflow(x{i}->v, y{i}->v, &s{i})) {{
      void *ret{i} = helper_add(fp, x{i}, y{i}, r{i});
      if (ret{i}) return ret{i};
    }} else {{ r{i}->v = s{i}; r{i}->type = 4; }}
  }}""")
print("  return fp->ip;\n}")
