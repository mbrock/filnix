// error: loading a bad(address_space) value is not supported yet
// A load through %gs (address_space(256)) is not a Fil-C access.
unsigned get(unsigned __attribute__((address_space(256))) *p) { return *p; }
