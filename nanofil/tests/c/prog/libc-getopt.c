// cflags: -D_GNU_SOURCE -fno-builtin
// Independent options contract probe. A failed claim makes the process
// fail too: agreeing implementations cannot hide a false expectation.
#include <getopt.h>
#include <stddef.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <errno.h>

static int failures;
static void check(const char *claim, int ok) {
    printf("%s: %s\n", claim, ok ? "yes" : "no");
    if (!ok) failures++;
}
static void reset(void) { optind = 0; opterr = 0; }

int main(void) {
    struct option opts[] = {
        {"greeting", required_argument, 0, 'g'},
        {"traditional", no_argument, 0, 't'},
        {"help", no_argument, 0, 128},
        {"version", no_argument, 0, 129},
        {0, 0, 0, 0}
    };
    check("option layout", sizeof(struct option) == 32 &&
          offsetof(struct option, name) == 0 && offsetof(struct option, has_arg) == 8 &&
          offsetof(struct option, flag) == 16 && offsetof(struct option, val) == 24);
    unsetenv("POSIXLY_CORRECT");
    char name[] = "probe", operand[] = "operand", greeting[] = "--greeting=abc";
    char help[] = "--help", version[] = "--version";
    char *av[] = {name, operand, greeting, help, version, 0};
    reset();
    int index = -7;
    int r = getopt_long(5, av, "g:t", opts, &index);
    check("greeting interior borrow", r == 'g' && index == 0 && optarg == greeting + 11 &&
          strcmp(optarg, "abc") == 0);
    // Pointer equality alone checks addresses. Dereference the permuted
    // slots and the old borrow under Fil-C to exercise their capabilities.
    char *borrow = optarg;
    check("help result", getopt_long(5, av, "g:t", opts, 0) == 128 && optarg == 0);
    check("version result", getopt_long(5, av, "g:t", opts, 0) == 129 && optarg == 0);
    r = getopt_long(5, av, "g:t", opts, 0);
    check("end and exact permutation", r == -1 && optind == 4 && optarg == 0 &&
          av[0] == name && av[1] == greeting && av[2] == help && av[3] == version &&
          av[4] == operand && av[5] == 0 && strcmp(av[1], "--greeting=abc") == 0 &&
          strcmp(av[4], "operand") == 0 && strcmp(borrow, "abc") == 0);
    check("argument bytes framed", strcmp(greeting, "--greeting=abc") == 0 &&
          strcmp(help, "--help") == 0 && strcmp(version, "--version") == 0);

    char empty[] = "--greeting=", text[] = "separate", shortarg[] = "-ginside";
    char *bv[] = {name, empty, "-g", text, shortarg, 0};
    reset();
    r = getopt_long(5, bv, "g:t", opts, 0);
    check("empty nonnull greeting", r == 'g' && optarg == empty + 11 && *optarg == 0);
    r = getopt_long(5, bv, "g:t", opts, 0);
    check("separate greeting borrow", r == 'g' && optarg == text && strcmp(optarg, "separate") == 0);
    r = getopt_long(5, bv, "g:t", opts, 0);
    check("short interior borrow", r == 'g' && optarg == shortarg + 2 && strcmp(optarg, "inside") == 0);

    char *bad[] = {name, "--unknown", "--greeting", 0};
    reset(); index = -7;
    r = getopt_long(3, bad, "g:t", opts, &index);
    check("unknown is ordinary result", r == '?' && optopt == 0 && optarg == 0 && index == -7);
    r = getopt_long(3, bad, "g:t", opts, &index);
    check("missing required argument", r == '?' && optopt == 'g' && optarg == 0 && index == -7);
    char *missing[] = {name, "-g", 0};
    reset();
    check("colon error mode", getopt_long(2, missing, ":g:t", opts, 0) == ':' && optopt == 'g');
    char *stop[] = {name, "--", "--help", 0};
    reset();
    check("double dash ends options", getopt_long(3, stop, "g:t", opts, 0) == -1 &&
          optind == 2 && optarg == 0 && strcmp(stop[2], "--help") == 0);

    int flag = -9;
    struct option flags[] = {{"set", no_argument, &flag, -17}, {"maybe", optional_argument, 0, 301}, {0, 0, 0, 0}};
    char optional[] = "--maybe=value";
    char *fv[] = {name, "--set", "--maybe", optional, 0};
    reset(); index = -7;
    r = getopt_long(4, fv, "", flags, &index);
    check("optional flag and index cells", r == 0 && flag == -17 && index == 0 && optarg == 0);
    check("optional argument absent", getopt_long(4, fv, "", flags, 0) == 301 && optarg == 0);
    r = getopt_long(4, fv, "", flags, &index);
    check("optional argument interior", r == 301 && index == 1 && optarg == optional + 8 && strcmp(optarg, "value") == 0);

    char *ordered[] = {name, operand, help, 0};
    reset();
    check("require order", getopt_long(3, ordered, "+g:t", opts, 0) == -1 && optind == 1 && ordered[2] == help);
    reset();
    r = getopt_long(3, ordered, "-g:t", opts, 0);
    check("return in order borrow", r == 1 && optarg == operand && strcmp(optarg, "operand") == 0);
    check("return in order continuation", getopt_long(3, ordered, "-g:t", opts, 0) == 128);
    char *previous[] = {name, "--greeting", text, 0};
    reset();
    check("seed private borrow", getopt_long(3, previous, "g:t", opts, 0) == 'g' && optarg == text);
    int saved_optopt = optopt;
    char *zero[] = {0};
    reset(); optarg = 0; optopt = -8;
    r = getopt_long(0, zero, "g:t", opts, 0);
    check("zero argc exports private state", r == -1 && optind == 0 && optarg == text &&
          optopt == saved_optopt && strcmp(optarg, "separate") == 0);
    char high[] = {'-', (char) 255, 0}, highopts[] = {(char) 255, 0};
    char *hv[] = {name, high, 0};
    reset();
    check("signed high short byte", getopt_long(2, hv, highopts, opts, 0) == -1 && optarg == 0);
    return failures != 0;
}
