// error: attribute speculative_load_hardening2 is not supported
/* An unknown attribute of clang's own namespace is refused; one of a
   namespace clang does not know (vendor::x) is ignored, as clang does. */
[[clang::speculative_load_hardening2]] int f(void) { return 1; }
