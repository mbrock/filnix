/* Native (not Fil-C) writer for zmark.c's "native" case: maps the same file
   and writes raw addresses into the marked segment's words. */
#include <fcntl.h>
#include <stdint.h>
#include <stdlib.h>
#include <sys/mman.h>
#include <unistd.h>

int main(int argc, char **argv)
{
    int fd = open(argv[1], O_RDWR);
    size_t words = strtoul(argv[2], 0, 10);
    uintptr_t seg = strtoul(argv[3], 0, 10);
    uintptr_t priv = strtoul(argv[4], 0, 10);
    size_t data = strtoul(argv[5], 0, 10);
    char *m = mmap(0, words + 64 * 8, PROT_READ | PROT_WRITE, MAP_SHARED, fd, 0);
    if (m == MAP_FAILED)
        return 1;
    uintptr_t *w = (uintptr_t *)(m + words);
    w[0] = priv;
    w[1] = seg + data + 8;
    w[2] = seg + data + (1 << 20); /* past the end of the segment */
    return 0;
}
