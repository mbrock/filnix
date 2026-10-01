#include <assert.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>

/* Private libaom API: link these tests against the installed static archive. */
void *aom_memalign(size_t align, size_t size);
void *aom_malloc(size_t size);
void *aom_calloc(size_t num, size_t size);
void aom_free(void *ptr);

int main(void) {
  const size_t sizes[] = {0, 1, 7, 8, 9, 31, 65, 4097};
  for (size_t align = 1; align <= 4096; align *= 2) {
    for (size_t i = 0; i < sizeof(sizes) / sizeof(sizes[0]); ++i) {
      size_t size = sizes[i];
      unsigned char *ptr = aom_memalign(align, size);
      assert(ptr && (uintptr_t)ptr % align == 0);
      /* Write both edges and the entire payload, without touching the header. */
      for (size_t j = 0; j < size; ++j) ptr[j] = (j * 13 + i) % 251;
      for (size_t j = 0; j < size; ++j) assert(ptr[j] == (j * 13 + i) % 251);
      aom_free(ptr);
    }
  }
  unsigned char *ptr = aom_malloc(513);
  assert(ptr && (uintptr_t)ptr % (2 * sizeof(void *)) == 0);
  memset(ptr, 0xa5, 513);
  assert(ptr[0] == 0xa5 && ptr[512] == 0xa5);
  aom_free(ptr);
  ptr = aom_calloc(17, 31);
  assert(ptr && (uintptr_t)ptr % (2 * sizeof(void *)) == 0);
  for (size_t i = 0; i < 17 * 31; ++i) assert(ptr[i] == 0);
  memset(ptr, 0x3b, 17 * 31);
  aom_free(ptr);
  assert(aom_malloc(SIZE_MAX) == NULL);
  assert(aom_memalign(64, SIZE_MAX - 64) == NULL);
  assert(aom_calloc(32, SIZE_MAX / 32) == NULL);
  assert(aom_calloc(SIZE_MAX, 2) == NULL);
  aom_free(NULL);
  puts("libaom allocator: 104 aligned allocation/free cases, malloc, calloc and overflow checks passed");
}
