/* Compiler experiments, independent of the assembly frontend. In particular,
   volatile reads, calls and stdfil APIs are NOT newly accepted source forms. */
#include <stdint.h>
#include <stdfil.h>
static uint64_t load8(const unsigned char *p) {
  uint64_t value;
  __builtin_memcpy(&value, p, 8);
  return value;
}
uint64_t covering(const unsigned char *p, uint64_t n) {
  uint64_t first = load8(p);
  return first + n + p[3];
}
uint64_t diamond(const unsigned char *p, uint64_t n) {
  uint64_t first = load8(p);
  if (n & 1) first += n; else first ^= n;
  return first + p[3];
}
uint64_t one_path(const unsigned char *p, uint64_t n) {
  uint64_t first = 0;
  if (n & 1) first = load8(p);
  return first + p[3];
}
uint64_t checked(const unsigned char *p, uint64_t n) {
  zcheck_readonly(p, 8);
  return p[n & 7];
}
uint64_t changed(unsigned char *p, uint64_t n) {
  uint64_t first = load8(p);
  p[3] = n;
  return first + p[3];
}
uint64_t retained_loads(const unsigned char *p, uint64_t n) {
  uint64_t first = load8(p);
  return first + n + *(const volatile unsigned char *)(p + 3);
}
extern void check_probe_effect(void *);
uint64_t call_barrier(const unsigned char *p, uint64_t n) {
  uint64_t first = load8(p);
  check_probe_effect((void *)p);
  return first + n + p[3];
}
