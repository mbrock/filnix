/* The slot two threads share in tests/c/prog/atomic-ptr.c. */
struct obj { long tag; char bytes[]; };
extern struct obj *slot;
extern struct obj *small_obj, *large_obj;
enum { SMALL = 16, LARGE = 4096, ROUNDS = 400000 };
long peer_check(struct obj *q);
void *peer_store(void *arg);
void *peer_load(void *arg);
/* The store-buffer litmus: each side stores its flag, then loads the
   other's, both sequentially consistent, once per round. */
extern int flag_a, flag_b, seen_b, seen_a, round_no, done_a, done_b;
enum { LITMUS = 100000 };
void *peer_litmus(void *arg);
