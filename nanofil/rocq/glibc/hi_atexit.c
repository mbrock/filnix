extern int __fpending(void *);
extern int ferror(void *);
extern int fclose(void *);
extern int puts(const char *);
extern int atexit(void (*)(void));
extern void _exit(int);
extern void exit(int);
extern void *stdout;

static void close_stdout_hi(void) {
  int pending = (__fpending(stdout) != 0);
  int prev_fail = (ferror(stdout) != 0);
  int fclose_fail = (fclose(stdout) != 0);
  if (prev_fail || fclose_fail) {
    if (pending || fclose_fail)
      _exit(1);
  }
}

int main(void) {
  atexit(close_stdout_hi);
  puts("hello");
  exit(0);
}
