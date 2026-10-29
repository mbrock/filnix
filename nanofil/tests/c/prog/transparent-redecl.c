/* A function declared with a transparent union parameter may be
   redeclared or defined with one of its members' types, and the other
   way round (clang's mergeTransparentUnionType, a GNU extension):
   torsocks defines connect(int, const struct sockaddr *, socklen_t)
   over glibc's __CONST_SOCKADDR_ARG declaration under _GNU_SOURCE. */
#define _GNU_SOURCE
#include <stdio.h>
#include <string.h>
#include <sys/socket.h>
#include <netinet/in.h>

typedef union {
    const int *ip;
    const char *cp;
} __attribute__((transparent_union)) arg_t;

static int first(arg_t a);
static int second(const int *p);

static int call_before(void) {
    static const int seven = 7;
    return first(&seven) + first("A");     /* any member's pointer */
}

/* defined with a member's type */
static int first(const int *p) { return *p; }

/* declared with the member, defined with the union */
static int second(arg_t a);
static int second(arg_t a) { return a.ip[0] * 2; }

int connect(int fd, const struct sockaddr *addr, socklen_t len) {
    const struct sockaddr_in *in = (const struct sockaddr_in *)addr;
    return fd + (int)len + in->sin_family;
}

int main(void) {
    static const int three = 3;
    struct sockaddr_in sin;
    memset(&sin, 0, sizeof sin);
    sin.sin_family = AF_INET;
    printf("%d %d %d %d\n", call_before(), first(&three), second(&three),
           connect(1, (struct sockaddr *)&sin, sizeof sin));
    return 0;
}
