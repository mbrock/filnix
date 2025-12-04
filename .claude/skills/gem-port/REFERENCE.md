# Fil-C Ruby Porting Reference

## Type System

In Fil-C Ruby:
- `VALUE` = `struct rb_value_unit_struct *` (pointer)
- `ID` = `unsigned long` (integer)
- `Qnil`, `Qtrue`, `Qfalse` = VALUE constants (pointers)

## Common Error Patterns

### 1. Qfalse/Qtrue passed where int expected

**Error:**
```
error: incompatible pointer to integer conversion passing 'VALUE' to parameter of type 'int'
```

**Pattern:** Functions like `rb_attr` take `int` for boolean flags, not VALUE.

**Fix with ast-grep:**
```bash
ast-grep run -p 'rb_attr($A, $B, $C, $D, Qfalse)' \
             -r 'rb_attr($A, $B, $C, $D, 0)' \
             -l c --selector call_expression -U .

ast-grep run -p 'rb_cstr_to_inum($A, $B, Qtrue)' \
             -r 'rb_cstr_to_inum($A, $B, 1)' \
             -l c --selector call_expression -U .
```

### 2. int literal passed where VALUE expected

**Error:**
```
error: incompatible integer to pointer conversion passing 'int' to parameter of type 'VALUE'
```

**Example:** `SHIFT(v, act, ERROR_TOKEN, val)` where ERROR_TOKEN is `#define ERROR_TOKEN 1`

**Fix:** Use `INT2FIX()` wrapper or existing VALUE version (e.g., `vERROR_TOKEN`).

### 3. VALUE stored in int variable

**Error:**
```
error: incompatible pointer to integer conversion initializing 'int' with expression of type 'VALUE'
```

**Example:** `int i, ret = Qnil;`

**Fix:** Change variable type or initial value:
- `int i, ret = -1;` (if ret is used as int)
- `int i; VALUE ret = Qnil;` (if ret should be VALUE)

### 4. VALUE stored in ID variable (or vice versa)

**Error:**
```
error: incompatible integer to pointer conversion assigning to 'VALUE' from 'ID'
```

**Example:**
```c
VALUE ret;
ret = ID_compressed;  // ID assigned to VALUE
return ID2SYM(ret);   // then passed to ID2SYM which wants ID
```

**Fix:** Change `VALUE ret;` to `ID ret;`

### 5. rb_protect with wrong argument type

**Error:**
```
error: incompatible integer to pointer conversion passing 'long' to parameter of type 'VALUE'
```

**Example:** `rb_protect(func, len, &state)` where `len` is `long`

**Fix:** Cast: `rb_protect(func, (VALUE)(uintptr_t)len, &state)`

And in the callback:
```c
// Before
return rb_str_new(NULL, (long)size);
// After
return rb_str_new(NULL, (long)(uintptr_t)size);
```

### 6. Bitwise operations on VALUE

**Error:**
```
error: invalid operands to binary expression ('VALUE' and 'int')
```

**Example:** `((sym) >> 8) & 0xff`

**Fix:** Cast to uintptr_t first: `(((uintptr_t)(sym)) >> 8) & 0xff`

### 7. RTEST with non-VALUE

**Error:** RTEST expects VALUE but gets something else.

**Fix:** Cast to VALUE: `RTEST((VALUE)ret)`

## ast-grep Tips

1. **Always use `--selector call_expression`** for function calls in C
2. Use `$A`, `$B`, etc. for single-node captures
3. Use `$$$ARGS` for variadic captures
4. Test patterns with `--debug-query=cst` to see AST structure
5. Dry run without `-U` first to see matches

## rubyports.nix Helpers

```nix
# Force native build
native = use { dontBuild = false; };

# String replacement
(replace "path/file.c" "old" "new")

# ast-grep pattern (uses --selector call_expression)
(astGrep "pattern($A)" "replacement($A)")

# Add compiler flag
(addCFlag "-DSOME_DEFINE")
```
