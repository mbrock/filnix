/* Shared by structs.c (built by nanofil in one build) and lib/structs.c
   (always built by clang). */
struct two { long a, b; };
struct pw { char *p; long n; };
struct pp { char *p, *q; };
struct small { int a; char c; };
struct odd { char a, b, c; };
struct big { long a, b; char *p; long c; };
union up { char *p; long n; };

struct two c_two(long x);
struct pw c_pw(char *p, long n);
struct pp c_pp(char *p);
struct small c_small(int x);
struct odd c_odd(int x);
struct big c_big(char *p, long x);
union up c_up(char *p);
long c_take(struct two t, struct pw w, struct small s, struct odd o);
long c_calls_back(char *buf);
long c_generic(char *buf);

struct two n_two(long x);
struct pw n_pw(char *p, long n);
struct pp n_pp(char *p);
struct small n_small(int x);
struct odd n_odd(int x);
struct big n_big(char *p, long x);
union up n_up(char *p);
long n_take(struct two t, struct pw w, struct small s, struct odd o);
