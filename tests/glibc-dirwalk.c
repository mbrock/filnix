/* glibc's directory walkers open subdirectories with __openat_nocancel:
   nftw and ftw on the first subdirectory, scandirat and fts through
   __opendirat. Each must walk a small tree and count what it saw. */
#define _GNU_SOURCE
#include <dirent.h>
#include <fcntl.h>
#include <fts.h>
#include <ftw.h>
#include <stdio.h>
#include <stdlib.h>
#include <sys/stat.h>
#include <unistd.h>

static int seen;

static int count(const char *path, const struct stat *sb, int flag, struct FTW *ftw)
{
    (void)path; (void)sb; (void)flag; (void)ftw;
    seen++;
    return 0;
}

static int count_ftw(const char *path, const struct stat *sb, int flag)
{
    (void)path; (void)sb; (void)flag;
    seen++;
    return 0;
}

static void expect(const char *what, int got, int want)
{
    printf("%s: %d\n", what, got);
    if (got != want) {
        fprintf(stderr, "%s: expected %d\n", what, want);
        exit(1);
    }
}

int main(void)
{
    /* tree/, tree/a/, tree/a/b/, tree/a/b/f, tree/g: five entries. */
    if (mkdir("tree", 0755) || mkdir("tree/a", 0755) || mkdir("tree/a/b", 0755))
        return 2;
    close(open("tree/a/b/f", O_CREAT | O_WRONLY, 0644));
    close(open("tree/g", O_CREAT | O_WRONLY, 0644));

    seen = 0;
    expect("nftw", nftw("tree", count, 4, FTW_PHYS) ? -1 : seen, 5);
    seen = 0;
    expect("nftw depth chdir", nftw("tree", count, 4, FTW_DEPTH | FTW_CHDIR) ? -1 : seen, 5);
    seen = 0;
    expect("ftw", ftw("tree", count_ftw, 4) ? -1 : seen, 5);

    /* tree/a holds only b: ".", ".." and "b". */
    struct dirent **names;
    int dirfd = open("tree", O_RDONLY | O_DIRECTORY);
    expect("scandirat", scandirat(dirfd, "a", &names, NULL, alphasort), 3);

    char *roots[] = { "tree", NULL };
    FTS *fts = fts_open(roots, FTS_PHYSICAL, NULL);
    int entries = 0;
    for (FTSENT *e; fts && (e = fts_read(fts));)
        if (e->fts_info != FTS_DP)
            entries++;
    expect("fts", fts ? entries : -1, 5);
    return 0;
}
