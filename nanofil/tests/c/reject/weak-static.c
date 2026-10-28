// error: weak declaration of hidden must have external linkage
static int hidden(void) { return 1; }
#pragma weak hidden
int use(void) { return hidden(); }
