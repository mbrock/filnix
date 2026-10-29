// error: must point to a defined variable or function
/* clang refuses an alias whose target the unit does not define. */
extern int y __attribute__((alias("nothere")));
