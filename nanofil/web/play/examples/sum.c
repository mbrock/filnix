/* A loop: compare the IR with and without -O. */
int sum(const int *xs, int n) {
    int total = 0;
    for (int i = 0; i < n; i++)
        total += xs[i] * 2 + 1;
    return total;
}

int main(void) {
    int xs[] = { 3, 1, 4, 1, 5, 9, 2, 6 };
    return sum(xs, sizeof xs / sizeof xs[0]);
}
