struct node { struct node *next; long v; };

__attribute__((noinline)) long sum(struct node *p) {
  long s = 0;
  while (p) {
    s += p->v;
    p = p->next;
  }
  return s;
}

long listsum(int n) {
  struct node *h = 0;
  for (int i = 0; i < n; i++) {
    struct node *x = __builtin_alloca(sizeof *x);
    x->next = h;
    x->v = i;
    h = x;
  }
  return sum(h);
}
