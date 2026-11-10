// error: calls returning _Complex long double are not supported yet
_Complex long double cexpl(_Complex long double);
long double f(_Complex long double z) { return __real__ cexpl(z); }
