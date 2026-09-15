#include <assert.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

extern ssize_t __real_write(int, const void *, size_t);
extern void *__real_calloc(size_t, size_t);
static int writes, allocations;

ssize_t __wrap_write(int fd, const void *data, size_t size) {
  writes++;
  return __real_write(fd, data, size);
}

void *__wrap_calloc(size_t count, size_t size) {
  allocations++;
  return __real_calloc(count, size);
}

int main(void) {
  int pipefd[2];
  assert(pipe(pipefd) == 0);
  char *buf = calloc(8, 1);
  assert(buf && allocations == 1);
  for (int i = 0; i < 8; i++) assert(buf[i] == 0);
  assert(write(pipefd[1], "wrapped", 7) == 7);
  assert(writes == 1);
  assert(read(pipefd[0], buf, 8) == 7);
  assert(strcmp(buf, "wrapped") == 0);
  free(buf);
  assert(close(pipefd[0]) == 0);
  assert(close(pipefd[1]) == 0);
}
