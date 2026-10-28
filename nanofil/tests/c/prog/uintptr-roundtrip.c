/* A pointer cast to a 64-bit integer and straight back is the same
   pointer, with its capability, as filcc gives it: at run time and in a
   static initializer (lighttpd's (connection *)(uintptr_t)&queue). */
#include <stdint.h>
#include <stdio.h>
struct node { struct node *next; int v; };
static struct node queue = { 0, 42 };
static struct node *const sentinel = (struct node *)(uintptr_t)&queue;
static int arr[4] = { 1, 2, 3, 4 };
static int *const third = (int *)(unsigned long)(arr + 2);
static const char *const msg = (const char *)(intptr_t)"round trip";
int main(void)
{
    struct node *r = (struct node *)(uintptr_t)&queue;
    printf("%d %d %d\n", sentinel == &queue, sentinel->v, r->v);
    printf("%d %s\n", *third, msg);
    return 0;
}
