/* stdio on a file: writing, seeking, reading back, scanning, buffering
   and the error and end-of-file flags. */
#include <stdio.h>
#include <string.h>

int main(void)
{
    const char *path = "stdio-test.txt";
    FILE *f = fopen(path, "w+");
    if (!f) { perror("fopen"); return 2; }
    setvbuf(f, NULL, _IOFBF, 64);
    for (int i = 0; i < 50; i++) fprintf(f, "line %d: %x %s\n", i, i * 37, i % 3 ? "odd" : "even");
    fputs("tail", f); fputc('!', f); fwrite("\nbytes\n", 1, 7, f);
    long len = ftell(f);
    fflush(f);
    rewind(f);
    char line[128]; int n = 0, a, b; char w[8];
    while (fgets(line, sizeof line, f) && n < 3) { printf("got %s", line); n++; }
    fseek(f, 0, SEEK_SET);
    int got = fscanf(f, "line %d: %x %7s", &a, &b, w);
    printf("scan %d %d %d %s len %ld\n", got, a, b, w, len);
    fseek(f, -6, SEEK_END);
    int c = fgetc(f); ungetc('X', f);
    char rest[16] = { 0 };
    size_t r = fread(rest, 1, sizeof rest - 1, f);
    printf("c=%d r=%zu [%s] eof=%d err=%d\n", c, r, rest, feof(f), ferror(f));
    fclose(f);
    f = fopen(path, "r");
    int lines = 0, ch;
    while ((ch = getc(f)) != EOF) lines += ch == '\n';
    printf("lines %d\n", lines);
    fclose(f);
    printf("remove %d %d\n", remove(path), fopen(path, "r") == NULL);
    int x; double y; char z[10];
    printf("sscanf %d", sscanf("17 2.5e3 word", "%d %lf %9s", &x, &y, z));
    printf(" %d %g %s\n", x, y, z);
    fprintf(stderr, "to stderr %d\n", 7);
    return 0;
}
