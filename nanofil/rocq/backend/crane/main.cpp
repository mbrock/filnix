// The driver of the Crane extraction of the nanofil backend: the
// standalone compiler of extraction/main.ml, with the same commands,
// messages and exit codes.
//
//   nanofil-backend-cpp compile FILE.ir
//   nanofil-backend-cpp compile-promoted FILE.ir
//   nanofil-backend-cpp compile-allocated FILE.ir
//
// IrText.v reads the text and Compile.v compiles the module. Exits 1
// for a text that is not read or a module that is not valid, and 3,
// with its output cut short, for a module the backend does not take.
// One translation unit: Crane defines a few functions in nb.h without
// `inline`, so the header cannot be included twice in a program.
#include "nb.cpp"

#include <cerrno>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <memory>
#include <string>
#include <vector>

namespace {

[[noreturn]] void stop(int code, const std::string &why) {
  std::fflush(stdout);
  std::fprintf(stderr, "nanofil-backend: %s\n", why.c_str());
  std::exit(code);
}

// The bytes of a file as the text IrText.v reads: pieces of
// NANOFIL_BACKEND_PIECE bytes (default 1 MB), each a list of
// characters made when the reader asks for it.
struct Source {
  std::FILE *file;
  std::vector<char> buf;
};

Chunked next_piece(const std::shared_ptr<Source> &src) {
  size_t n = std::fread(src->buf.data(), 1, src->buf.size(), src->file);
  if (n == 0) {
    std::fclose(src->file);
    return Chunked::textend();
  }
  List<char> cs = List<char>::nil();
  for (size_t i = n; i-- > 0;) cs = List<char>::cons(src->buf[i], std::move(cs));
  return Chunked::textpiece(std::move(cs),
                            [src](std::monostate) { return next_piece(src); });
}

Chunked file_text(const char *path) {
  const char *piece = std::getenv("NANOFIL_BACKEND_PIECE");
  size_t size = piece ? std::strtoull(piece, nullptr, 10) : (size_t{1} << 20);
  std::FILE *f = std::fopen(path, "rb");
  if (!f) stop(2, std::string(path) + ": " + std::strerror(errno));
  auto src = std::make_shared<Source>(Source{f, std::vector<char>(size)});
  return next_piece(src);
}

// A chunk of lines is printed at a time, as in main.ml.
constexpr int chunk = 64;

void print_lines(const List<Line> &lines) {
  const List<Line> *at = &lines;
  for (;;) {
    List<Line> rev = List<Line>::nil();
    int k = 0;
    while (k < chunk) {
      auto *cell = std::get_if<List<Line>::Cons>(&at->v());
      if (!cell) break;
      rev = List<Line>::cons(cell->a, std::move(rev));
      at = cell->l.get();
      ++k;
    }
    if (k == 0) return;
    List<std::string> parts = Asm::rev_lines_parts(rev, List<std::string>::nil());
    for (const List<std::string> *p = &parts;;) {
      auto *cell = std::get_if<List<std::string>::Cons>(&p->v());
      if (!cell) break;
      std::fwrite(cell->a.data(), 1, cell->a.size(), stdout);
      p = cell->l.get();
    }
  }
}

template <class A, class F> void each(const List<A> &xs, F f) {
  for (const List<A> *p = &xs;;) {
    auto *cell = std::get_if<typename List<A>::Cons>(&p->v());
    if (!cell) return;
    f(cell->a);
    p = cell->l.get();
  }
}

void print_pieces(const List<crane::fn<std::optional<List<List<Line>>>(std::monostate)>> &pieces) {
  each(pieces, [](const auto &piece) {
    std::optional<List<List<Line>>> lists = piece(std::monostate{});
    if (!lists) stop(3, "a function is outside the subset or has no plan");
    each(*lists, [](const List<Line> &ls) {
      if (auto what = Layout::first_todo(ls)) stop(3, "not ported: " + *what);
      print_lines(ls);
    });
  });
}

} // namespace

int main(int argc, char **argv) {
  auto command = [&](const char *name) { return argc == 3 && !std::strcmp(argv[1], name); };
  bool promoted = command("compile-promoted"), allocated = command("compile-allocated");
  if (!(promoted || allocated || command("compile"))) {
    std::fputs("usage: nanofil-backend-cpp compile FILE.ir, compile-promoted FILE.ir, "
               "or compile-allocated FILE.ir\n", stderr);
    return 2;
  }
  std::optional<Term> m = read_text(file_text(argv[2]));
  if (!m) stop(1, "the IR text is not read");
  Compiled c = allocated  ? Compile::compile_allocated(*m)
               : promoted ? Compile::compile_promoted(*m)
                          : Compile::compile(*m);
  if (auto *r = std::get_if<Compiled::Refused>(&c.v())) stop(1, r->why);
  if (auto *o = std::get_if<Compiled::Outside>(&c.v())) stop(3, o->why);
  print_pieces(std::get<Compiled::Pieces>(c.v()).ps);
  std::fflush(stdout);
  return 0;
}
