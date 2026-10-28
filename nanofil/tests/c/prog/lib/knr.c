int add();
long mix();
int bump();
double scale();
int callers(void)
{
    char c = 10;
    float f = 2.5f;
    return add(c, 1) + (int)mix("B", 1, f, c, 300) + bump(c) + (int)scale(f, c);
}
