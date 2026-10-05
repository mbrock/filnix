# Perl + C Integration with Fil-C Memory Safety

Two concise demos showing **memory-safe C integration in Perl** using Fil-C.

## The Demos

### 1. `demo.pl` - Multiple C Libraries
Shows 4 major C libraries working together with memory safety:
- **JSON::XS** - Fast JSON parsing (C)
- **XML::LibXML** - XML parsing via libxml2 (C)
- **DBD::SQLite** - SQLite database (C)
- **Compress::Zlib** - zlib compression (C)

All in ~50 lines of code.

### 2. `inline-c.pl` - Memory-Safe C in Perl
Write C code directly inside Perl with `Inline::C`:
- Fast factorial computation
- String reversal with pointers
- Array operations with pointer arithmetic
- Memory allocation with malloc

**All automatically memory-safe** - no buffer overflows, no use-after-free, no undefined behavior.

## Quick Start

### With direnv (automatic):
```bash
cd demo/perl
# Environment loads automatically
perl demo.pl
perl inline-c.pl
```

### With nix develop:
```bash
nix develop .#perl-demos
perl demo.pl
./run-all.sh  # Run both demos
```

### With nix run:
```bash
nix run .#perl-demos        # Runs demo.pl
nix build .#perl-demos      # Builds demo package
result/bin/perl-demo
result/bin/perl-inline-c
result/bin/perl-demos-all   # Runs both
```

## Why This Matters

### The Problem
Perl's XS (eXternal Subroutine) mechanism lets C code interact with Perl internals. Traditionally:
- Bugs in XS modules can crash the interpreter
- Memory corruption can escape C and affect Perl
- 5000+ CPAN XS modules have potential memory safety issues

### The Fil-C Solution
All C code gets **automatic memory safety**:
- ✓ No buffer overflows
- ✓ No use-after-free
- ✓ No type confusion
- ✓ GIMSO: Garbage In, Memory Safety Out

This means:
- **5000+ CPAN XS modules** become memory-safe
- **Inline::C** lets you write provably safe C in Perl
- **C libraries** (OpenSSL, libxml2, SQLite, zlib) are safe

## Technical Details

### How Fil-C Works with Perl

1. **InvisiCap Runtime**: Every pointer becomes `(value, capability)` pair
2. **Bounds Checking**: All array/pointer accesses verified
3. **FUGC**: Garbage collector prevents use-after-free
4. **Type Safety**: Capability metadata tracks types

### Performance
- Typical overhead: 1.5x-4x vs unsafe C
- Still faster than pure Perl for many operations
- Compile with `-O3` for production

## C Libraries Used

All compiled with Fil-C memory safety:
- **libxml2** - XML parsing (~150K lines of C)
- **SQLite** - Database engine (~150K lines of C)
- **zlib** - Compression library
- **JSON-XS** - Fast JSON parser

## Further Reading

- [Fil-C upstream](https://github.com/pizlonator/fil-c)
- [Inline::C on CPAN](https://metacpan.org/pod/Inline::C)
- [perlxs documentation](https://perldoc.perl.org/perlxs)
- [Main filnix README](../../README.md)
