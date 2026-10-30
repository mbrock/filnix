struct node {
    int value;
    struct node *next;
};

int sum(struct node *n) {
    int s = 0;
    while (n) {
        s += n->value;
        n = n->next;
    }
    return s;
}

int three(void) {
    struct node c = {3, 0}, b = {2, &c}, a = {1, &b};
    return sum(&a);
}
