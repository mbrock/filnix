# libpng 1.6.43

## Summary
This patch adds APNG (Animated PNG) support. **NOT Fil-C specific** - it's a feature addition, not a compatibility fix. Unclear why it's in the Fil-C patches.

## Fil-C Compatibility Changes
**None** - this patch has no Fil-C-specific changes.

## Feature Changes (Not Fil-C Related)

**png.h (API Extensions)**:
- Defines `PNG_APNG_SUPPORTED`, `PNG_READ_APNG_SUPPORTED`, `PNG_WRITE_APNG_SUPPORTED`
- Adds APNG chunk constants: `PNG_DISPOSE_OP_*`, `PNG_BLEND_OP_*`
- Adds info flags: `PNG_INFO_acTL`, `PNG_INFO_fcTL`
- Declares ~20 new APNG functions:
  - `png_get/set_acTL`, `png_get/set_next_frame_fcTL`
  - `png_read/write_frame_head`, `png_write_frame_tail`
  - Progressive frame callbacks
  - Getter functions for frame properties

**pnginfo.h (Info Struct)**:
- Adds fields: `num_frames`, `num_plays`, `next_frame_*` (width/height/offsets/delays/ops)

**pngstruct.h (PNG Struct)**:
- Adds fields: `apng_flags`, `next_seq_num`, `first_frame_*`, `num_frames_*`
- Progressive callbacks: `frame_info_fn`, `frame_end_fn`

**Implementation Files**:
- `pngget.c`: Implements 16 getter functions for APNG metadata (~166 lines)
- `pngset.c`: Implements acTL/fcTL validation and setters (~100 lines)
- `pngpread.c`: Progressive APNG chunk handling (acTL, fcTL, fdAT) (~300 lines)
- `pngread.c`: Frame reading logic (~200 lines)
- `pngwrite.c`: Frame writing (fcTL generation, fdAT wrapping) (~200 lines)
- `pngwutil.c`: acTL/fcTL/fdAT chunk writers (~150 lines)
- `pngtest.c`: APNG test code (~150 lines)
- `scripts/symbols.def`: Export 20 new symbols

## Build Artifact Bloat
None - this is a feature addition patch (though unrelated to Fil-C).

## Assessment
- **Patch quality**: Well-structured feature addition
- **Actual changes**: Substantial - full APNG implementation (~1200 lines)
- **Fil-C relevance**: **NONE** - this is a feature patch, not a compatibility patch
- **Mystery**: Why is APNG support in Fil-C patches? Possible reasons:
  - Accidentally included from upstream merge
  - Needed by a specific Fil-C test/demo
  - Used for testing complex PNG workflows
