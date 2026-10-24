static char slot0[256];
static struct slotvec { unsigned long size; char *val; }
    slotvec0 = {sizeof slot0, slot0};
static char *offset = slot0 + 17;
int slots(void) {
    slotvec0.val[255] = 42;
    return slotvec0.size + slot0[255] + (offset - slot0);
}
int local_slots(void) {
    enum { N = 17 };
    static char buffer[N];
    static struct slotvec local = {sizeof buffer, buffer};
    static int size = N;
    local.val[16] = 42;
    return local.size + size + buffer[16];
}
static int grid[2][3];
static int *cell = &grid[1][2];
static int *none = 0 + 0;
static const char *tail = 1 + "abc";
int cells(void) {
    *cell = 5;
    return grid[1][2] + (cell - &grid[0][0]) + (none == 0) + *tail;
}
// run: $slots
// run: $local_slots
// run: $cells
