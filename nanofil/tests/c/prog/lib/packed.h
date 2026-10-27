/* A packed struct with misaligned members: SysV class MEMORY, so it is
   returned through a hidden pointer even though it has 11 bytes. */
struct __attribute__((packed)) pk { char a; long long b; short c; };
struct pk c_pk(long x);
struct pk n_pk(long x);
long c_pk_sum(struct pk *p);
