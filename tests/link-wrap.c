#include <assert.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

extern ssize_t __real_write(int, const void *, size_t);
extern void *__real_calloc(size_t, size_t);
extern void *__real_malloc(size_t);
extern int wrapped_value(int);
extern int __real_wrapped_value(int);
static int writes, allocations;
static int values, mallocs;

int __wrap_wrapped_value(int x) {
  values++;
  return __real_wrapped_value(x) + 1;
}

void *__wrap_malloc(size_t size) {
  mallocs++;
  return __real_malloc(size);
}

ssize_t __wrap_write(int fd, const void *data, size_t size) {
  writes++;
  return __real_write(fd, data, size);
}

void *__wrap_calloc(size_t count, size_t size) {
  allocations++;
  return __real_calloc(count, size);
}

int main(void) {
  /* The real definition comes from another object. Both direct calls and
   * function pointers must reach the wrapper, independent of link order. */
  assert(wrapped_value(7) == 22);
  int (*volatile fn)(int) = wrapped_value;
  assert(fn(9) == 28);
  assert(values == 2);
  char *allocation = malloc(19);
  memset(allocation, 0, 19);
  assert(allocation && mallocs == 1);
  free(allocation);
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
