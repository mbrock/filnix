/* liburcu's lock-free hash table under Fil-C: concurrent adds, lookups and
 * deletes while the table auto-resizes. Deletes set REMOVED_FLAG and the
 * garbage collector unlinks flagged nodes, so this exercises the tagged
 * next pointers that lost their capabilities, and the flag that atomic
 * loads did not see. liburcu's own tests do not cover rculfhash. */
#include <stdio.h>
#include <stdlib.h>
#include <pthread.h>
#include <urcu.h>
#include <urcu/rculfhash.h>
struct item { int key; struct cds_lfht_node node; };
static struct cds_lfht *ht;
static int match(struct cds_lfht_node *n, const void *key) {
  return caa_container_of(n, struct item, node)->key == *(const int *)key;
}
enum { T = 6, N = 3000, ROUNDS = 5 };
static int ok[T];
static unsigned long h(int k) { return (unsigned long)k * 2654435761u; }
static void *worker(void *arg) {
  int t = (int)(long)arg, good = 1;
  rcu_register_thread();
  for (int r = 0; r < ROUNDS; r++) {
    for (int i = 0; i < N; i++) {
      struct item *it = calloc(1, sizeof *it);
      it->key = t * N + i;
      cds_lfht_node_init(&it->node);
      rcu_read_lock();
      cds_lfht_add(ht, h(it->key), &it->node);
      rcu_read_unlock();
    }
    for (int i = 0; i < N; i++) {
      int k = t * N + i;
      struct cds_lfht_iter iter;
      rcu_read_lock();
      cds_lfht_lookup(ht, h(k), match, &k, &iter);
      struct cds_lfht_node *n = cds_lfht_iter_get_node(&iter);
      if (!n || cds_lfht_del(ht, n) != 0) good = 0;
      rcu_read_unlock();
    }
  }
  rcu_unregister_thread();
  ok[t] = good;
  return NULL;
}
int main(void) {
  ht = cds_lfht_new(1, 1, 0, CDS_LFHT_AUTO_RESIZE | CDS_LFHT_ACCOUNTING, NULL);
  pthread_t th[T];
  for (long t = 0; t < T; t++) pthread_create(&th[t], NULL, worker, (void *)t);
  for (int t = 0; t < T; t++) pthread_join(th[t], NULL);
  int all = 1;
  for (int t = 0; t < T; t++) all &= ok[t];
  unsigned long count; long a, b;
  rcu_register_thread(); rcu_read_lock();
  cds_lfht_count_nodes(ht, &a, &count, &b);
  rcu_read_unlock();
  printf("all ok %d, remaining %lu\n", all, count);
  return all && count == 0 ? 0 : 1;
}
