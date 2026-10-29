// error: attribute scalar_storage_order is not supported
/* Values: big-endian members. */
struct __attribute__((scalar_storage_order("big-endian"))) s { int a; };
struct s v;
