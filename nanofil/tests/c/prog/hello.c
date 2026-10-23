// args: a b
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
struct node { int v; struct node *next; };
static struct node *push(struct node *l, int v) {
    struct node *n = malloc(sizeof *n);
    n->v = v; n->next = l; return n;
}
static int cmp(const void *a, const void *b) { return *(const int *)a - *(const int *)b; }
int main(int argc, char **argv) {
    struct node *l = 0;
    for (int i = 0; i < 5; i++) l = push(l, i * i);
    int sum = 0;
    for (struct node *p = l; p; p = p->next) sum += p->v;
    printf("hello %s, %d args, sum %d\n", "world", argc, sum);
    char buf[32];
    strcpy(buf, "abc");
    strcat(buf, "def");
    printf("%s %zu %c\n", buf, strlen(buf), buf[2]);
    int xs[6] = {5, 3, 9, 1, 7, 2};
    qsort(xs, 6, sizeof xs[0], cmp);
    for (int i = 0; i < 6; i++) printf("%d%c", xs[i], i == 5 ? '\n' : ' ');
    puts(argv[0] ? "argv ok" : "no argv");
    fputs("to stderr\n", stderr);
    return sum % 7;
}
