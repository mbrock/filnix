#include <sys/resource.h>
#include "const_strs.h"
#include <errno.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "gc_stack.h"
#include "glue.h"
#include "nb.h"

#define is_ptr(x) Is_block(x)

static value ascii_blocks[256][9];
value ascii_vals[256];

static void init_ascii_table(void) {
  for (unsigned int c = 0; c < 256; c++) {
    ascii_blocks[c][0] = 8192LL;
    for (int b = 0; b < 8; b++) {
      ascii_blocks[c][1 + b] = ((c >> b) & 1u) ? 3LL : 1LL;
    }
    ascii_vals[c] = (value)(&ascii_blocks[c][1]);
  }
}

static unsigned char decode_ascii(value ch) {
  unsigned char c = 0;
  for (int b = 0; b < 8; b++) {
    if (Field(ch, b) == 3LL) c |= (unsigned char)(1u << b);
  }
  return c;
}

static void fprint_gallina_string(FILE *out, value s) {
  char buf[4096];
  size_t k = 0;
  while (is_ptr(s)) {
    buf[k++] = (char)decode_ascii(Field(s, 0));
    if (k == sizeof(buf)) {
      fwrite(buf, 1, k, out);
      k = 0;
    }
    s = Field(s, 1);
  }
  if (k > 0) fwrite(buf, 1, k, out);
}

static void stop_c(int code, const char *why) {
  fflush(stdout);
  fprintf(stderr, "nanofil-backend: %s\n", why);
  exit(code);
}

static void stop_gallina(int code, const char *prefix, value why) {
  fflush(stdout);
  fprintf(stderr, "nanofil-backend: %s", prefix);
  fprint_gallina_string(stderr, why);
  fputc('\n', stderr);
  exit(code);
}

static FILE *src_file = NULL;
static unsigned char *src_buf = NULL;
static size_t src_buf_size = 0;

static value next_piece_code(struct thread_info *tinfo, value env, value unit_arg);
static value next_piece_clo_block[3] = {
  2048LL,
  (value)next_piece_code,
  1LL
};
#define NEXT_PIECE_CLO ((value)(&next_piece_clo_block[1]))

static value next_piece_code(struct thread_info *tinfo, value env, value unit_arg) {
  (void)env;
  (void)unit_arg;
  if (!src_file) return make_Backend_IrText_chunked_TextEnd();
  size_t n = fread(src_buf, 1, src_buf_size, src_file);
  if (n == 0) {
    fclose(src_file);
    src_file = NULL;
    return make_Backend_IrText_chunked_TextEnd();
  }
  value roots[1] = { make_Corelib_Init_Datatypes_list_nil() };
  struct stack_frame frame = { .next = roots + 1, .root = roots, .prev = tinfo->fp };
  tinfo->fp = &frame;
  for (size_t i = n; i-- > 0;) {
    if (tinfo->limit - tinfo->alloc < 6) {
      tinfo->nalloc = 6;
      garbage_collect(tinfo);
    }
    roots[0] = alloc_make_Corelib_Init_Datatypes_list_cons(
        tinfo, ascii_vals[src_buf[i]], roots[0]);
  }
  if (tinfo->limit - tinfo->alloc < 6) {
    tinfo->nalloc = 6;
    garbage_collect(tinfo);
  }
  value res = alloc_make_Backend_IrText_chunked_TextPiece(tinfo, roots[0], NEXT_PIECE_CLO);
  tinfo->fp = frame.prev;
  return res;
}

static value open_file_text(struct thread_info *tinfo, const char *path) {
  const char *piece = getenv("NANOFIL_BACKEND_PIECE");
  src_buf_size = piece ? (size_t)strtoull(piece, NULL, 10) : ((size_t)1 << 20);
  if (src_buf_size == 0) src_buf_size = 1;
  src_file = fopen(path, "rb");
  if (!src_file) {
    fflush(stdout);
    fprintf(stderr, "nanofil-backend: %s: %s\n", path, strerror(errno));
    exit(2);
  }
  src_buf = (unsigned char *)malloc(src_buf_size);
  if (!src_buf) stop_c(2, "out of memory");
  return next_piece_code(tinfo, 1LL, 1LL);
}

enum {
  R_ENTRIES = 0,
  R_READ_TEXT,
  R_COMPILE,
  R_COMPILE_PROMOTED,
  R_COMPILE_ALLOCATED,
  R_REV_LINES_PARTS,
  R_FIRST_TODO,
  R_TMP,
  R_PIECES,
  R_LISTS,
  R_LINES,
  R_REV,
  R_PARTS,
  NUM_ROOTS
};

int main(int argc, char **argv) {
  int plain = (argc == 3 && strcmp(argv[1], "compile") == 0);
  int promoted = (argc == 3 && strcmp(argv[1], "compile-promoted") == 0);
  int allocated = (argc == 3 && strcmp(argv[1], "compile-allocated") == 0);
  if (!(plain || promoted || allocated)) {
    fputs("usage: nanofil-backend-c compile FILE.ir, compile-promoted FILE.ir, "
          "or compile-allocated FILE.ir\n", stderr);
    return 2;
  }

  { struct rlimit rl; if (getrlimit(RLIMIT_STACK, &rl) == 0 && rl.rlim_cur < (64ULL << 20)) { rl.rlim_cur = 64ULL << 20; if (rl.rlim_max != RLIM_INFINITY && rl.rlim_cur > rl.rlim_max) rl.rlim_cur = rl.rlim_max; setrlimit(RLIMIT_STACK, &rl); } }
  init_ascii_table(); init_const_strs();
  struct thread_info *tinfo = make_tinfo();
  value roots[NUM_ROOTS];
  for (int i = 0; i < NUM_ROOTS; i++) roots[i] = 1LL;
  struct stack_frame frame = { .next = roots + NUM_ROOTS, .root = roots, .prev = tinfo->fp };
  tinfo->fp = &frame;

  roots[R_ENTRIES] = body(tinfo);
  roots[R_READ_TEXT] = Field(roots[R_ENTRIES], 0);
  roots[R_COMPILE] = Field(roots[R_ENTRIES], 1);
  roots[R_COMPILE_PROMOTED] = Field(roots[R_ENTRIES], 2);
  roots[R_COMPILE_ALLOCATED] = Field(roots[R_ENTRIES], 3);
  roots[R_REV_LINES_PARTS] = Field(roots[R_ENTRIES], 4);
  roots[R_FIRST_TODO] = Field(roots[R_ENTRIES], 5);

  roots[R_TMP] = open_file_text(tinfo, argv[2]);
  roots[R_TMP] = call(tinfo, roots[R_READ_TEXT], roots[R_TMP]);
  free(src_buf);
  src_buf = NULL;
  if (!is_ptr(roots[R_TMP])) stop_c(1, "the IR text is not read");
  roots[R_TMP] = Field(roots[R_TMP], 0); /* Some m -> m */

  value compiler = allocated  ? roots[R_COMPILE_ALLOCATED]
                 : promoted   ? roots[R_COMPILE_PROMOTED]
                              : roots[R_COMPILE];
  roots[R_TMP] = call(tinfo, compiler, roots[R_TMP]);

  unsigned long long ctag = get_Backend_Compile_compiled_tag(roots[R_TMP]);
  if (ctag == 0) stop_gallina(1, "", Field(roots[R_TMP], 0)); /* Refused */
  if (ctag == 1) stop_gallina(3, "", Field(roots[R_TMP], 0)); /* Outside */

  roots[R_PIECES] = Field(roots[R_TMP], 0);
  roots[R_TMP] = 1LL;

  while (is_ptr(roots[R_PIECES])) {
    roots[R_TMP] = Field(roots[R_PIECES], 0); /* piece : unit -> option (list (list line)) */
    roots[R_PIECES] = Field(roots[R_PIECES], 1);
    roots[R_TMP] = call(tinfo, roots[R_TMP], make_Corelib_Init_Datatypes_unit_tt());
    if (!is_ptr(roots[R_TMP])) {
      stop_c(3, "a function is outside the subset or has no plan");
    }
    roots[R_LISTS] = Field(roots[R_TMP], 0); /* Some lists -> lists */
    roots[R_TMP] = 1LL;

    while (is_ptr(roots[R_LISTS])) {
      roots[R_LINES] = Field(roots[R_LISTS], 0);
      roots[R_LISTS] = Field(roots[R_LISTS], 1);

      roots[R_TMP] = call(tinfo, roots[R_FIRST_TODO], roots[R_LINES]);
      if (is_ptr(roots[R_TMP])) {
        stop_gallina(3, "not ported: ", Field(roots[R_TMP], 0));
      }

      while (is_ptr(roots[R_LINES])) {
        roots[R_REV] = make_Corelib_Init_Datatypes_list_nil();
        int k = 0;
        while (k < 64 && is_ptr(roots[R_LINES])) {
          if (tinfo->limit - tinfo->alloc < 6) {
            tinfo->nalloc = 6;
            garbage_collect(tinfo);
          }
          value line = Field(roots[R_LINES], 0);
          roots[R_LINES] = Field(roots[R_LINES], 1);
          roots[R_REV] = alloc_make_Corelib_Init_Datatypes_list_cons(tinfo, line, roots[R_REV]);
          k++;
        }
        roots[R_TMP] = call(tinfo, roots[R_REV_LINES_PARTS], roots[R_REV]);
        roots[R_REV] = 1LL;
        roots[R_PARTS] = call(tinfo, roots[R_TMP], make_Corelib_Init_Datatypes_list_nil());
        roots[R_TMP] = 1LL;
        while (is_ptr(roots[R_PARTS])) {
          fprint_gallina_string(stdout, Field(roots[R_PARTS], 0));
          roots[R_PARTS] = Field(roots[R_PARTS], 1);
        }
      }
    }
  }

  fflush(stdout);
  return 0;
}
