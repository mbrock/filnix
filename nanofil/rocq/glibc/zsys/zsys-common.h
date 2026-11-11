// Shared helpers of the zsys-*.c native counterexample probes
// (rocq/glibc/zsys/Os*.v): pipes, draining, and running a case in a
// forked child to see whether Fil-C panics.
#ifndef ZSYS_COMMON_H
#define ZSYS_COMMON_H
#define _GNU_SOURCE
#include <errno.h>
#include <fcntl.h>
#include <pizlonated_runtime.h>
#include <pizlonated_syscalls.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/wait.h>
#include <unistd.h>

static int pipe_nb(int fds[2]) {
  if (pipe(fds))
    return -1;
  return fcntl(fds[1], F_SETFL, O_NONBLOCK);
}

// Read everything in the pipe's read end without blocking.
static long drain(int fd, char *out, long cap) {
  int fl = fcntl(fd, F_GETFL);
  fcntl(fd, F_SETFL, fl | O_NONBLOCK);
  long got = 0;
  for (;;) {
    long r = read(fd, out + got, cap - got);
    if (r <= 0)
      break;
    got += r;
  }
  fcntl(fd, F_SETFL, fl);
  return got;
}

// Run fn(arg) in a child that exits 0 if fn returns; print the case name
// and whether the child died some other way (a Fil-C panic).
static void dies(const char *name, void (*fn)(int), int arg) {
  fflush(stdout);
  pid_t pid = fork();
  if (pid == 0) {
    fn(arg);
    _exit(0);
  }
  int status = 0;
  waitpid(pid, &status, 0);
  printf("%s %d\n", name, !(WIFEXITED(status) && WEXITSTATUS(status) == 0));
}
// The descriptor of libpizlo's log file, or -1: a /proc/self/fd entry
// naming a filc-log-PID.txt.
static int log_fd(void) {
  for (int fd = 0; fd < 64; fd++) {
    char path[64], link[256];
    snprintf(path, sizeof path, "/proc/self/fd/%d", fd);
    long n = readlink(path, link, sizeof link - 1);
    if (n > 0) {
      link[n] = 0;
      if (strstr(link, "filc-log-"))
        return fd;
    }
  }
  return -1;
}

// Re-run this program with FILC_LOG_TO_FILE=1 and the argument mode, in a
// fresh directory for its log file; print name and whether it died.
static void logged(const char *name, const char *mode) {
  char dir[] = "/tmp/zsys-log-XXXXXX";
  char exe[4096];
  long n = readlink("/proc/self/exe", exe, sizeof exe - 1);
  exe[n < 0 ? 0 : n] = 0;
  if (!mkdtemp(dir))
    return;
  fflush(stdout);
  pid_t pid = fork();
  if (pid == 0) {
    chdir(dir);
    char *argv[] = {exe, (char *)mode, NULL};
    char *envp[] = {"FILC_LOG_TO_FILE=1", NULL};
    execve(exe, argv, envp);
    _exit(127);
  }
  int status = 0;
  waitpid(pid, &status, 0);
  printf("%s %d\n", name, !(WIFEXITED(status) && WEXITSTATUS(status) == 0));
  char cmd[128];
  snprintf(cmd, sizeof cmd, "rm -rf %s", dir);
  system(cmd);
}
#endif
