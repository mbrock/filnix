#define _POSIX_C_SOURCE 200809L
#include "evaluation.h"
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

static double now(void) {
  struct timespec t;
  assert(clock_gettime(CLOCK_MONOTONIC, &t) == 0);
  return (double)t.tv_sec + (double)t.tv_nsec * 1e-9;
}
static uint64_t word(const unsigned char *p) {
  return (uint64_t)p[0] | (uint64_t)p[1] << 8 | (uint64_t)p[2] << 16 | (uint64_t)p[3] << 24;
}
static FILE *control, *ack;
static void counters(const char *command) {
  if (!control) return;
  assert(fputs(command, control) >= 0 && fflush(control) == 0);
  /* Allow a NUL terminator after the acknowledgement line. */
  int first;
  do { first = fgetc(ack); } while (first == 0);
  assert(first == 'a' && fgetc(ack) == 'c' && fgetc(ack) == 'k' && fgetc(ack) == '\n');
}
int main(int argc, char **argv) {
  assert(argc == 3);
  const char *mode = argv[1];
  uint64_t iterations = strtoull(argv[2], NULL, 10);
  assert(iterations > 0);
  unsigned char *table = malloc(272), *input = malloc(65536), *output = malloc(262144);
  assert(table && input && output);
  uint64_t rng = 42;
  for (unsigned i = 0; i < 272; i++) table[i] = (unsigned char)(i * 179 + 31);
  for (unsigned i = 0; i < 65536; i++) {
    rng = rng * UINT64_C(6364136223846793005) + 1;
    input[i] = (unsigned char)((rng >> 32) & 63);
  }
  memset(output, 0, 262144);
  if (!strcmp(mode, "table-check") || !strcmp(mode, "unaligned")) {
    unsigned alignment = !strcmp(mode, "unaligned");
    for (unsigned trial = 0; trial < 256; trial++) {
      for (unsigned i = 0; i < 272; i++) table[i] = (unsigned char)(i * 179 + trial);
      for (unsigned i = 0; i < 64; i++)
        assert(table_entry(table + alignment, i) == word(table + alignment + 4 * i));
    }
    puts("table evaluation: 16384 cases passed");
    return 0;
  }
  if (!strcmp(mode, "table-tail")) {
    void *short_table = calloc(1, 16);
    return table_entry(short_table, 4);
  }
  if (!strcmp(mode, "table-freed")) {
    free(table);
    return table_entry(table, 0);
  }
  if (!strcmp(mode, "table-null")) return table_entry(NULL, 0);

  unsigned count = !strcmp(mode, "decode-small") ? 64 : 65536;
  struct node *nodes[4096];
  uint64_t node_sum = 0;
  if (!strcmp(mode, "walk")) {
    for (unsigned i = 0; i < 4096; i++) {
      nodes[i] = malloc(sizeof *nodes[i]);
      nodes[i]->value = i * 31 + 7;
      node_sum += nodes[i]->value;
    }
    for (unsigned i = 0; i < 4096; i++) nodes[i]->next = nodes[(i + 179) & 4095];
  } else assert(!strcmp(mode, "table") || !strcmp(mode, "decode") || !strcmp(mode, "decode-small"));

  /* Warm the exact workload before enabling counters/timing. */
  for (unsigned i = 0; i < 64; i++) {
    if (!strcmp(mode, "table")) assert(table_entry(table, i) == word(table + 4 * i));
    else if (!strcmp(mode, "walk")) assert(loop_walk(nodes[0], 4096) == node_sum);
    else {
      struct decoder s = {table, input, output, 0};
      assert(tiny_decode(&s, count) == 0 && s.consumed == count);
    }
  }
  const char *ctl_path = getenv("SP_PERF_CONTROL"), *ack_path = getenv("SP_PERF_ACK");
  if (ctl_path) {
    assert(ack_path);
    control = fopen(ctl_path, "w"); ack = fopen(ack_path, "r");
    assert(control && ack);
  }
  uint64_t checksum = 0;
  unsigned kind = !strcmp(mode, "table") ? 0 : !strcmp(mode, "walk") ? 1 : 2;
  counters("enable\n");
  double start = now();
  if (kind == 0) {
    for (uint64_t i = 0; i < iterations; i++) checksum += table_entry(table, i & 63);
  } else if (kind == 1) {
    for (uint64_t i = 0; i < iterations; i++) checksum += loop_walk(nodes[0], 4096);
  } else {
    for (uint64_t i = 0; i < iterations; i++) {
      struct decoder s = {table, input, output, 0};
      checksum += tiny_decode(&s, count) + s.consumed;
      assert(s.input == input + count && s.output == output + 4 * count);
    }
  }
  double elapsed = now() - start;
  counters("disable\n");
  if (kind == 2) {
    assert(checksum == iterations * count);
    for (unsigned i = 0; i < count; i++)
      for (unsigned j = 0; j < 4; j++) assert(output[4 * i + j] == table[4 * input[i] + j]);
  } else if (kind == 1) assert(checksum == iterations * node_sum);
  else {
    uint64_t full = 0, partial = 0;
    for (unsigned i = 0; i < 64; i++) {
      full += word(table + 4 * i);
      if (i < iterations % 64) partial += word(table + 4 * i);
    }
    assert(checksum == (iterations / 64) * full + partial);
  }
  printf("{\"seconds\":%.9f,\"iterations\":%llu,\"checksum\":%llu}\n",
         elapsed, (unsigned long long)iterations, (unsigned long long)checksum);
  if (control) { fclose(control); fclose(ack); }
  if (kind == 1) for (unsigned i = 0; i < 4096; i++) free(nodes[i]);
  free(table); free(input); free(output);
}
