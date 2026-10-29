// error: attribute mode on one of several declarators is not supported
// It applied to both, so ga had one byte too.
int ga, gb __attribute__((mode(QI)));
