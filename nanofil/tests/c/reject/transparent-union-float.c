// error: cannot assign double to union
/* A floating first member: clang warns that the transparent_union
   attribute is ignored, and then refuses a double argument. */
union __attribute__((__transparent_union__)) D {
    double d;
    long l;
};

long f(union D u);

long g(void) { return f(1.5); }
