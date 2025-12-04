# ast-grep Reference for C Code

## Quick Start

```bash
# Find patterns
ast-grep run -p 'pattern' -l c .

# Replace patterns
ast-grep run -p 'pattern' -r 'replacement' -l c -U .

# With selector for function calls
ast-grep run -p 'func($A)' -r 'other($A)' -l c --selector call_expression -U .

# Debug how pattern parses
ast-grep run -p 'pattern' -l c --debug-query=ast
ast-grep run -p 'pattern' -l c --debug-query=cst
```

## How ast-grep Parses C

ast-grep uses tree-sitter to parse code into an AST. Key insights:

### 1. Preprocessor Directives

`#define` macros ARE matchable:
- Parsed as `preproc_def` nodes
- Macro body is `preproc_arg` (raw text, not parsed as C code)
- **Must match exact whitespace** in the pattern

```bash
# Match a specific #define macro
ast-grep run -p '#define ECB_MEMORY_FENCE         __asm__ __volatile__ ("mfence"   : : : "memory")' -l c .
```

### 2. Function Calls

Plain `test($A)` may be ambiguous - tree-sitter-c parses differently based on context:
- Fragment `test(a)` → `macro_type_specifier`
- Statement `test(a);` → `expression_statement` → `call_expression`

**Solution**: Use selector:
```bash
ast-grep run -p 'test($A)' -l c --selector call_expression -U .
```

Or provide context in pattern:
```bash
ast-grep run -p 'test($A);' -l c -U .
```

### 3. Inline ASM

`__asm__ __volatile__ (...)` parses as `gnu_asm_expression`:

```
gnu_asm_expression
  gnu_asm_qualifier: __volatile__
  assembly_code: string_literal
  output_operands: gnu_asm_output_operand_list
  input_operands: gnu_asm_input_operand_list
  clobbers: gnu_asm_clobber_list
```

## Meta-Variables

| Syntax | Meaning |
|--------|---------|
| `$A` | Match single named AST node |
| `$$$ARGS` | Match zero or more nodes (spread) |
| `$$OP` | Match unnamed node (like operators) |

## Common Selectors for C

| Selector | Use Case |
|----------|----------|
| `call_expression` | Function calls |
| `switch_statement` | Switch blocks |
| `case_statement` | Individual case labels |
| `declaration` | Variable declarations |
| `assignment_expression` | Assignments |
| `preproc_def` | #define macros |

## YAML Rule Format

For complex rules, use YAML config:

```yaml
id: match-function-call
language: c
rule:
  pattern:
    context: $M($$$);     # Full context for parsing
    selector: call_expression  # What to actually match
fix: replacement($$$)
```

## C Catalog Examples

### 1. Match Function Call

```yaml
id: match-function-call
language: c
rule:
  pattern:
    context: $M($$$);
    selector: call_expression
```

### 2. Rewrite Method to Function Call

```yaml
id: method_receiver
language: c
rule:
  pattern: $R.$METHOD($$$ARGS)
transform:
  MAYBE_COMMA:
    replace:
      source: $$$ARGS
      replace: '^.+'
      by: ', '
fix:
  $METHOD(&$R$MAYBE_COMMA$$$ARGS)
```

Transforms: `some_struct->field.method(1, 2)` → `method(&some_struct->field, 1, 2)`

### 3. Yoda Conditions

```yaml
id: may-the-force-be-with-you
language: c
rule:
  pattern: $A == $B
  inside:
    kind: parenthesized_expression
    inside: {kind: if_statement}
constraints:
  B: { kind: number_literal }
fix: $B == $A
```

Transforms: `if (x == 42)` → `if (42 == x)`

## Our Nix Helpers

In rubyports.nix:

```nix
# With call_expression selector (for function calls)
astGrep = pattern: rewrite: ...

# Without selector (for switch/case, #define, etc.)
astGrepAny = pattern: rewrite: ...

# With custom selector
astGrepSel = selector: pattern: rewrite: ...
```

## Fil-C Specific Patterns

### VALUE Switch to If-Else

VALUE is a pointer in Fil-C, can't be switch case label:

```nix
(astGrepSel "switch_statement"
  "switch (expr) { case Qfalse: ...; case Qnil: ...; default: ...; }"
  "{ VALUE r = expr; if (r == Qfalse) { ... } else if (r == Qnil) { ... } else { ... } }")
```

### VALUE Switch with uintptr_t Cast

Alternative: cast to integer for switch:

```nix
(astGrepAny "switch ($X)" "switch ((uintptr_t)$X)")
(astGrepAny "case Qtrue:" "case (uintptr_t)Qtrue:")
```

### Preprocessor Macro Replacement

```nix
(astGrepAny
  "#define ECB_MEMORY_FENCE         __asm__ __volatile__ (\"mfence\"   : : : \"memory\")"
  "#define ECB_MEMORY_FENCE         __atomic_thread_fence(__ATOMIC_SEQ_CST)")
```

### Function Argument Type Fix

```nix
(astGrep "rb_attr($A, $B, $C, $D, Qfalse)" "rb_attr($A, $B, $C, $D, 0)")
(astGrep "rb_cstr_to_inum($A, $B, Qtrue)" "rb_cstr_to_inum($A, $B, 1)")
```

## Debugging Tips

1. **Use --debug-query**: See how your pattern parses
   ```bash
   ast-grep run -p 'your_pattern' -l c --debug-query=ast
   ```

2. **Check CST for exact tokens**:
   ```bash
   ast-grep run -p 'your_pattern' -l c --debug-query=cst
   ```

3. **Test without -U first**: See what matches before replacing

4. **Whitespace matters for #define**: Match exact spacing

## Resources

- [ast-grep docs](https://ast-grep.github.io/)
- [Pattern syntax](https://ast-grep.github.io/guide/pattern-syntax.html)
- [C language catalog](https://ast-grep.github.io/catalog/c/)
- [Deep dive on patterns](https://ast-grep.github.io/advanced/pattern-parse.html)
- [FAQ](https://ast-grep.github.io/advanced/faq.html)
