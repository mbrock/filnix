/* Starts a program of the relocatable PHP distribution.

   bin/NAME runs libexec/NAME through the bundled Fil-C dynamic loader,
   lib/ld-fil1-x86_64.so, because a PT_INTERP path cannot be relative to the
   executable. The loader gets --argv0 so that PHP sees the name it was
   started with and derives PHP_BINARY from it, which then points back here.

   This is ordinary static C, not Fil-C, so it runs on any x86-64 Linux. */

#define _GNU_SOURCE
#include <limits.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

static char root[PATH_MAX];

static char *in_root(const char *rel) {
    char *path;
    if (asprintf(&path, "%s/%s", root, rel) < 0) {
        perror("asprintf");
        exit(127);
    }
    return path;
}

static void set_default(const char *name, const char *value) {
    setenv(name, value, 0);
}

int main(int argc, char **argv) {
    char self[PATH_MAX];
    ssize_t n = readlink("/proc/self/exe", self, sizeof self - 1);
    if (n < 0) {
        if (!realpath(argv[0], self)) {
            fprintf(stderr, "%s: cannot locate own executable\n", argv[0]);
            return 127;
        }
    } else {
        self[n] = 0;
    }

    /* self is ROOT/bin/NAME. */
    char *slash = strrchr(self, '/');
    const char *name = slash + 1;
    *slash = 0;
    slash = strrchr(self, '/');
    *slash = 0;
    snprintf(root, sizeof root, "%s", *self ? self : "/");

    /* etc/php.d/extensions.ini finds the extensions through this. */
    setenv("PHP_DIST_DIR", root, 1);
    set_default("PHPRC", in_root("etc"));
    set_default("PHP_INI_SCAN_DIR", in_root("etc/php.d"));
    /* The compiled-in paths of iconv's character set modules and of the
       locales are in /nix. The bundled glibc reads these renamed variables
       instead of GCONV_PATH and LOCPATH, which would also reach host
       programs that PHP runs and make their glibc load these files. */
    set_default("FILC_GCONV", in_root("lib/gconv"));
    set_default("FILCLOC", in_root("lib/locale"));
    set_default("OPENSSL_CONF", in_root("etc/ssl/openssl.cnf"));
    set_default("TERMINFO_DIRS", "/etc/terminfo:/lib/terminfo:/usr/share/terminfo");

    /* OpenSSL's compiled-in certificate locations are in /nix. Prefer the
       host's trust store and fall back to the bundled Mozilla one. */
    if (!getenv("SSL_CERT_FILE") && !getenv("SSL_CERT_DIR")) {
        static const char *const bundles[] = {
            "/etc/ssl/certs/ca-certificates.crt", /* Debian, Ubuntu, Arch, Alpine */
            "/etc/pki/tls/certs/ca-bundle.crt",   /* Fedora, RHEL */
            "/etc/ssl/ca-bundle.pem",             /* openSUSE */
            "/etc/ssl/cert.pem",
        };
        const char *bundle = in_root("etc/ssl/cert.pem");
        for (size_t i = 0; i < sizeof bundles / sizeof *bundles; i++) {
            if (access(bundles[i], R_OK) == 0) {
                bundle = bundles[i];
                break;
            }
        }
        setenv("SSL_CERT_FILE", bundle, 1);
        if (access("/etc/ssl/certs", R_OK) == 0)
            setenv("SSL_CERT_DIR", "/etc/ssl/certs", 1);
    }

    /* php-fpm reads PREFIX/etc/php-fpm.conf and resolves relative paths in
       it against PREFIX; the compiled-in prefix is in /nix. */
    int fpm_prefix = 0;
    if (strcmp(name, "php-fpm") == 0) {
        fpm_prefix = 1;
        for (int i = 1; i < argc; i++)
            if (strcmp(argv[i], "-p") == 0 || strncmp(argv[i], "--prefix", 8) == 0)
                fpm_prefix = 0;
    }

    char **args = calloc(argc + 7, sizeof *args);
    int k = 0;
    char *loader = in_root("lib/ld-fil1-x86_64.so");
    args[k++] = loader;
    args[k++] = "--argv0";
    args[k++] = argv[0];
    char *program;
    if (asprintf(&program, "%s/libexec/%s", root, name) < 0)
        return 127;
    args[k++] = program;
    if (fpm_prefix) {
        args[k++] = "--prefix";
        args[k++] = root;
    }
    for (int i = 1; i < argc; i++)
        args[k++] = argv[i];
    args[k] = NULL;

    execv(loader, args);
    fprintf(stderr, "%s: cannot run %s: ", argv[0], loader);
    perror(NULL);
    return 127;
}
