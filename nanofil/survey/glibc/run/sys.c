/* The syscall stubs nanofil compiles through zargs and zreturn: open,
   fcntl, dup, sysinfo, munmap, with their results and errno, printed so
   that two libcs can be compared. */
#include <errno.h>
#include <fcntl.h>
#include <stdio.h>
#include <string.h>
#include <sys/mman.h>
#include <sys/sysinfo.h>
#include <unistd.h>

int main(void)
{
    int fd = open("sys-test.txt", O_CREAT | O_RDWR | O_TRUNC, 0600);
    printf("open %d\n", fd >= 0);
    printf("write %zd\n", write(fd, "hello\n", 6));
    int flags = fcntl(fd, F_GETFL);
    printf("getfl %d %d\n", flags >= 0, (flags & O_ACCMODE) == O_RDWR);
    printf("setfd %d getfd %d\n", fcntl(fd, F_SETFD, FD_CLOEXEC), fcntl(fd, F_GETFD));
    int fd2 = dup(fd);
    printf("dup %d %d\n", fd2 > fd, close(fd2));
    errno = 0;
    printf("bad open %d %s\n", open("no/such/dir/file", O_RDONLY), strerror(errno));
    errno = 0;
    printf("bad fcntl %d %s\n", fcntl(-1, F_GETFL), strerror(errno));
    errno = 0;
    printf("bad dup %d %s\n", dup(-1), strerror(errno));
    struct sysinfo si;
    printf("sysinfo %d %d %d\n", sysinfo(&si), si.totalram > 0, si.mem_unit > 0);
    char *p = mmap(NULL, 8192, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
    printf("mmap %d\n", p != MAP_FAILED);
    p[0] = 1; p[8191] = 2;
    printf("munmap %d\n", munmap(p, 8192));
    close(fd);
    unlink("sys-test.txt");
    return 0;
}
