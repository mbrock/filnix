#include <stdio.h>
#include <stdlib.h>

/* Structs and the heap: in Fil-C each pointer carries its object's bounds. */
struct node {
    int value;
    struct node *next;
};

static struct node *push(struct node *list, int value) {
    struct node *n = malloc(sizeof *n);
    n->value = value;
    n->next = list;
    return n;
}

int main(void) {
    struct node *list = NULL;
    for (int i = 1; i <= 3; i++)
        list = push(list, i * i);
    for (struct node *n = list; n; n = n->next)
        printf("%d\n", n->value);
    return 0;
}
