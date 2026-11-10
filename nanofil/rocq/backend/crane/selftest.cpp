#include "st.cpp"
#include <cstdio>
int main() {
  auto ts = tests(std::monostate{});
  const List<std::string> *e = &expected;
  int bad = 0, n = 0;
  for (auto *p = &ts;;) {
    auto *cell = std::get_if<List<std::pair<std::string, std::string>>::Cons>(&p->v());
    if (!cell) break;
    auto *ec = std::get_if<List<std::string>::Cons>(&e->v());
    ++n;
    if (cell->a.second != ec->a) {
      ++bad;
      // first differing word
      const std::string &a = cell->a.second, &b = ec->a;
      size_t i = 0; int w = 0;
      while (i < a.size() && i < b.size() && a[i] == b[i]) { if (a[i] == ' ') ++w; ++i; }
      size_t s = a.rfind(' ', i == 0 ? 0 : i - 1); s = s == std::string::npos ? 0 : s + 1;
      std::printf("got  [%s]\nwant [%s]\n", a.c_str(), b.c_str()); std::printf("BAD %s at word %d: got '%s' want '%s'\n", cell->a.first.c_str(), w,
                  a.substr(s, a.find(' ', i) - s).c_str(), b.substr(s, b.find(' ', i) - s).c_str());
    }
    p = cell->l.get(); e = ec->l.get();
  }
  std::printf("%d tests, %d bad\n", n, bad);
  return bad != 0;
}
