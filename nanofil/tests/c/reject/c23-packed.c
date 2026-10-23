// error: alignment attributes
struct [[gnu::packed]] S { char a; int b; };
int main(void) { return sizeof(struct S); }
