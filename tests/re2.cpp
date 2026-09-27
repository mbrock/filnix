// Use re2 (and through it abseil) from a Fil-C program.
#include <cstdio>
#include <cstdlib>
#include <string>

#include <re2/re2.h>
#include <re2/set.h>

#define CHECK(cond)                                                    \
  do {                                                                 \
    if (!(cond)) {                                                     \
      std::fprintf(stderr, "%s:%d: check failed: %s\n", __FILE__,      \
                   __LINE__, #cond);                                   \
      std::exit(1);                                                    \
    }                                                                  \
  } while (0)

int main() {
  std::string user, host;
  int port = 0;
  RE2 re("(\\w+)@([\\w.]+):(\\d+)");
  CHECK(re.ok());
  CHECK(RE2::FullMatch("alice@example.org:8080", re, &user, &host, &port));
  CHECK(user == "alice" && host == "example.org" && port == 8080);

  std::string s = "one two  three";
  CHECK(RE2::GlobalReplace(&s, "\\s+", "_") == 2);
  CHECK(s == "one_two_three");

  // A long input run through the DFA (re2/dfa.cc was the file that crashed).
  std::string big(1 << 20, 'a');
  big += "needle";
  CHECK(RE2::PartialMatch(big, "a+needle$"));
  CHECK(!RE2::PartialMatch(big, "b"));

  RE2::Set set(RE2::DefaultOptions, RE2::UNANCHORED);
  CHECK(set.Add("foo", nullptr) == 0);
  CHECK(set.Add("ba+r", nullptr) == 1);
  CHECK(set.Compile());
  std::vector<int> hits;
  CHECK(set.Match("xx baaar yy", &hits) && hits.size() == 1 && hits[0] == 1);

  // An invalid pattern reports an error string instead of crashing.
  RE2 bad("(unclosed", RE2::Quiet);
  CHECK(!bad.ok() && !bad.error().empty());

  std::printf("ok: re2 matched %s@%s:%d\n", user.c_str(), host.c_str(), port);
  return 0;
}
