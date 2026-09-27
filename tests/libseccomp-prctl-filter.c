/* libseccomp under Fil-C: the seccomp() syscall is reported as missing, so
 * TSYNC is refused, and filters are loaded through prctl(PR_SET_SECCOMP). */
#include <errno.h>
#include <seccomp.h>
#include <stdio.h>
#include <sys/utsname.h>

int main(void)
{
	struct utsname u;
	scmp_filter_ctx ctx;
	int rc;

	if (seccomp_api_get() != 1)
		return fprintf(stderr, "api level %u\n", seccomp_api_get()), 1;
	ctx = seccomp_init(SCMP_ACT_ALLOW);
	if (!ctx)
		return fprintf(stderr, "seccomp_init failed\n"), 1;
	rc = seccomp_attr_set(ctx, SCMP_FLTATR_CTL_TSYNC, 1);
	if (rc != -EOPNOTSUPP)
		return fprintf(stderr, "TSYNC attr: %d\n", rc), 1;
	if (seccomp_rule_add(ctx, SCMP_ACT_ERRNO(EACCES), SCMP_SYS(uname), 0))
		return fprintf(stderr, "seccomp_rule_add failed\n"), 1;
	if (uname(&u) != 0)
		return fprintf(stderr, "uname failed before the filter\n"), 1;
	rc = seccomp_load(ctx);
	if (rc)
		return fprintf(stderr, "seccomp_load: %d\n", rc), 1;
	seccomp_release(ctx);
	errno = 0;
	if (uname(&u) != -1 || errno != EACCES)
		return fprintf(stderr, "uname not filtered (errno %d)\n", errno), 1;
	printf("filter loaded with prctl; uname fails with EACCES\n");
	return 0;
}
