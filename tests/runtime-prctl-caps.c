/* prctl's capability options (patches/filc-runtime-prctl-caps.patch):
   PR_CAPBSET_READ, PR_CAPBSET_DROP and every PR_CAP_AMBIENT operation must
   reach the kernel and give its answers, not ENOSYS. systemd needs them to
   start any service. Whether a raise or a drop is allowed depends on the
   builder's capabilities, so those cases check that the kernel's answer is
   consistent rather than which one it is. */
#include <errno.h>
#include <linux/capability.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/prctl.h>

static int failed;

static void check(const char *what, int ok, int r)
{
    printf("%-36s = %d (%s)%s\n", what, r, r < 0 ? strerror(errno) : "ok", ok ? "" : "  <-- wrong");
    if (!ok)
        failed = 1;
}

int main(void)
{
    int r;

    errno = 0;
    r = prctl(PR_CAPBSET_READ, CAP_CHOWN);
    check("PR_CAPBSET_READ CAP_CHOWN", r == 0 || r == 1, r);

    errno = 0;
    r = prctl(PR_CAPBSET_READ, 1000);
    check("PR_CAPBSET_READ 1000", r == -1 && errno == EINVAL, r);

    errno = 0;
    r = prctl(PR_CAPBSET_DROP, CAP_SYS_TIME);
    check("PR_CAPBSET_DROP CAP_SYS_TIME", r == 0 ? prctl(PR_CAPBSET_READ, CAP_SYS_TIME) == 0 : errno == EPERM, r);

    errno = 0;
    r = prctl(PR_CAP_AMBIENT, PR_CAP_AMBIENT_CLEAR_ALL, 0, 0, 0);
    check("PR_CAP_AMBIENT CLEAR_ALL", r == 0, r);

    errno = 0;
    r = prctl(PR_CAP_AMBIENT, PR_CAP_AMBIENT_IS_SET, CAP_CHOWN, 0, 0);
    check("PR_CAP_AMBIENT IS_SET CAP_CHOWN", r == 0, r);

    errno = 0;
    r = prctl(PR_CAP_AMBIENT, PR_CAP_AMBIENT_RAISE, CAP_CHOWN, 0, 0);
    check("PR_CAP_AMBIENT RAISE CAP_CHOWN",
          r == 0 ? prctl(PR_CAP_AMBIENT, PR_CAP_AMBIENT_IS_SET, CAP_CHOWN, 0, 0) == 1 : errno == EPERM, r);

    errno = 0;
    r = prctl(PR_CAP_AMBIENT, PR_CAP_AMBIENT_LOWER, CAP_CHOWN, 0, 0);
    check("PR_CAP_AMBIENT LOWER CAP_CHOWN",
          r == 0 && prctl(PR_CAP_AMBIENT, PR_CAP_AMBIENT_IS_SET, CAP_CHOWN, 0, 0) == 0, r);

    errno = 0;
    r = prctl(PR_CAP_AMBIENT, 99, CAP_CHOWN, 0, 0);
    check("PR_CAP_AMBIENT 99", r == -1 && errno == EINVAL, r);

    return failed;
}
