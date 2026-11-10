static int two = 2;
int *pick(void) { return &two; }
static void *nothing(int x) { (void)x; return 0; }
void *(*hook)(int) = nothing;
