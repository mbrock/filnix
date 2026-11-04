#include "loc.hh"

__attribute__((noinline)) static void report(const char *name, CodeLocation loc) {
  std::printf("%s %s:%d\n", name, loc.file.c_str(), loc.line);
}

// An 18-character literal fits libc++'s short string, which starts at offset 1
// of the record, so the literal's bytes 7..14 fill its second pointer word.
static int registered = (report("BuildResultJSON", CodeLocation("../build-result.cc", 41)), 0);

int main() { return registered; }
