// error: attribute section is not supported
/* Placement: __start_/__stop_ tables would miss it. */
int x __attribute__((section("table"))) = 1;
