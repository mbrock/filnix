/* Shared declarations of tests/c/prog/thread-local.c and its clang side
   lib/thread-local.c. */
enum { THREADS = 8, ROUNDS = 3000 };

struct node { struct node *next; long value; char pad[24]; };

/* Defined by nanofil (thread-local.c). */
extern _Thread_local long nf_count;
extern __thread struct node *nf_list;
extern _Thread_local int nf_init;
extern _Thread_local char nf_name[16];

/* Defined by clang (lib/thread-local.c). */
extern _Thread_local long cl_count;
extern _Thread_local struct node *cl_list;
extern _Thread_local int cl_init;
extern _Thread_local struct pairs { long a[4]; const char *s; } cl_pairs;

long clang_round(int id, int i, long *nf_count_ptr);
long clang_check(int id);
long *clang_counter_address(void);
int clang_static_local(void);
