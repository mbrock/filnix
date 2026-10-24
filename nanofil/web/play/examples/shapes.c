#include <stdio.h>

/* An enum, a switch and a table of function pointers. */
enum shape { SQUARE, CIRCLE, TRIANGLE };

static double square(double x) { return x * x; }
static double circle(double r) { return 3.14159 * r * r; }
static double triangle(double s) { return 0.433 * s * s; }

static double (*const area[])(double) = { square, circle, triangle };

static const char *name(enum shape s) {
    switch (s) {
    case SQUARE: return "square";
    case CIRCLE: return "circle";
    default: return "triangle";
    }
}

int main(void) {
    for (enum shape s = SQUARE; s <= TRIANGLE; s++)
        printf("%s: %.2f\n", name(s), area[s](2.0));
    return 0;
}
