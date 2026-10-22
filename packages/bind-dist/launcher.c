/* Starts a program of the relocatable BIND distribution.

   bin/NAME runs libexec/NAME through the bundled Fil-C dynamic loader,
   lib/ld-fil1-x86_64.so, because a PT_INTERP path cannot be relative to the
   executable. The loader gets --argv0 so that programs that look at their
   name (tsig-keygen and ddns-confgen, named-checkzone and
   named-compilezone) behave as the name they were started with.

   This is ordinary static C, not Fil-C, so it runs on any x86-64 Linux. */

#define _GNU_SOURCE
#include <limits.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

int main(int argc, char **argv) {
    char root[PATH_MAX];
    ssize_t n = readlink("/proc/self/exe", root, sizeof root - 1);
    if (n < 0) {
        fprintf(stderr, "%s: cannot locate own executable\n", argv[0]);
        return 127;
    }
    root[n] = 0;

    /* root is ROOT/bin/NAME. */
    char *slash = strrchr(root, '/');
    char *name = strdup(slash + 1);
    *slash = 0;
    slash = strrchr(root, '/');
    *slash = 0;

    char *loader, *program, *conf;
    if (asprintf(&loader, "%s/lib/ld-fil1-x86_64.so", root) < 0 ||
        asprintf(&program, "%s/libexec/%s", root, name) < 0 ||
        asprintf(&conf, "%s/etc/ssl/openssl.cnf", root) < 0)
        return 127;
    /* OpenSSL's compiled-in configuration path is in /nix. */
    setenv("OPENSSL_CONF", conf, 0);

    char **args = calloc(argc + 4, sizeof *args);
    int k = 0;
    args[k++] = loader;
    args[k++] = "--argv0";
    args[k++] = argv[0];
    args[k++] = program;
    for (int i = 1; i < argc; i++)
        args[k++] = argv[i];
    args[k] = NULL;

    execv(loader, args);
    fprintf(stderr, "%s: cannot run %s: ", argv[0], loader);
    perror(NULL);
    return 127;
}
