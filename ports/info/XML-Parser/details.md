# XML-Parser v2.47

## Summary
Minimal Perl XS fix to properly decode pointers stored as integers using Fil-C's pointer table mechanism.

## Fil-C Compatibility Changes

### Perl XS Typemap
- **File**: `Expat/typemap`
- **Input type**: `T_ENCOBJ`
- **Change**: Replaced direct cast `$var = ($type) tmp` with `$var = zptrtable_decode(Perl_xsub_ptrtable, tmp)`
- **Why**: Perl XS stores pointers as integers (IV = integer values) for passing across the Perl/C boundary. Under Fil-C, pointers cannot be reconstructed from integers via cast - must use explicit pointer table lookup.
- **Pattern**: Pointer table (`zptrtable`) for integer↔pointer conversion

## Build Artifact Bloat
None - single typemap file change only.

## Assessment
- **Patch quality**: Minimal and precise
- **Actual changes**: Minor - single line fix for Perl XS integration
- **Complexity**: Trivial, uses Fil-C's standard pointer table API for language bindings
