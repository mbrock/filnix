int direct(int);
int before(int);
int after(int);
int later_extern(int);
int gnu_plain(int);
int c99_only(int x) { return x + 5; }
int gnu_extern(int x) { return x + 6; }
int gnu_suffix(int x) { return x + 7; }
int check_external(void) {
    return direct(10) != 11 || before(10) != 12 || after(10) != 13
        || later_extern(10) != 14 || gnu_plain(10) != 18;
}
