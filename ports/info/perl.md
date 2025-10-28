# Perl 5.40.0

## Summary
Comprehensive Fil-C integration across Perl's XS (eXtension System) interface. Replaces all pointer-to-integer conversions with zptrtable encoding to maintain capability tracking.

## Fil-C Compatibility Changes

### Core Infrastructure
**perl.c** / **perl.h**
- Global `Perl_xsub_ptrtable` declared and initialized
- Constructor creates pointer table for all XS modules to share
- Includes `<stdfil.h>` at top level

### XS Module Modifications
Each XS module creates its own pointer table and converts PTR2IV ↔ INT2PTR:

**builtin.c**
- `builtin_ptrtable` for encoding `BuiltinFuncDescriptor*`
- Used in `ck_builtin_const`, `ck_builtin_func1`, `ck_builtin_funcN`

**Encode.xs** (`cpan/Encode/`)
- `encode_ptrtable` for `encode_t*` encoding
- Affects encode/decode operations across character sets

**Compress-Raw-Zlib/typemap**
- Converts typemap `INT2PTR` → `zptrtable_decode(Perl_xsub_ptrtable, ...)`

**Storable.xs** (`dist/Storable/`)
- `perinterp_ptrtable` for per-interpreter context encoding
- Complex macro rewrites for `dSTCXT_PTR`, `INIT_STCXT`, `SET_STCXT`

**threads-shared/shared.xs**
- `sharedsv_ptrtable` for shared SV encoding
- `SHAREDSV_FROM_OBJ` macro rewritten

**threads.xs** (`dist/threads/`)
- `threads_ptrtable` for thread management
- Affects `ithread_mg_get`, `S_ithread_to_SV`, `S_SV_to_ithread`, etc.

### Directory Handle Management
**doio.c**
- `dir_ptrtable` for `DIR*` encoding in ARGV processing
- `S_argvout_free`, `Perl_nextargv`, `S_argvout_final` updated

### Introspection (B::)
**ext/B/B.xs** + **typemap**
- All OP/SV/MAGIC pointer operations use `Perl_xsub_ptrtable`
- Affects `make_op_object`, `make_sv_object`, `make_mg_object`, etc.
- All `T_OP_OBJ`, `T_SV_OBJ`, `T_MG_OBJ` conversions rewritten

### DynaLoader
**ext/DynaLoader/dl_dlopen.xs**
- `dl_load_file`, `dl_find_symbol` encode dlopen handles

### Regex Engine
**ext/re/re.xs**
- Encodes `my_reg_engine` pointer

### GV/Stash Cache
**gv.c**
- `gvstash_ptrtable` for stash cache (`PL_stashcache`)
- `Perl_gv_stashsvpvn_cached` encodes HV* pointers

### Regex Context Saving
**pp_ctl.c**
- `rxres_save`/`rxres_restore`/`rxres_free` rewritten
- Uses `*(void**)` casts instead of `PTR2UV`/`INT2PTR` for match buffers

### Regex Engine Dispatch
**regcomp.c**
- `Perl_current_re_engine` decodes from `cop_hints_fetch_pvs`

### Public API
**sv.c**
- `Perl_sv_setref_pv` uses `zptrtable_encode` for blessed references

### Performance Optimization
**util.c**
- `Perl_repeatcpy` loop replaced with `memcpy` (unrelated optimization)

### Typemap Defaults
**lib/ExtUtils/typemap**
- Default `T_PTR`, `T_PTRREF`, `T_PTROBJ` conversions use `Perl_xsub_ptrtable`
- Affects all XS modules using standard typemaps

## Build Artifact Bloat
None - this is a clean code-only patch.

## Assessment
- **Patch quality**: Clean, systematic
- **Actual changes**: Substantial - touches ~20 files across core and XS
- **Pattern**: Consistent use of per-module pointer tables with shared fallback
- **Correctness**: Appears sound - maintains Perl's pointer identity semantics while adding capability tracking
