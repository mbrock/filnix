#pragma once
#include <cstdio>
#include <string>

// Like googletest's CodeLocation: a by-value record whose std::string member
// is a union with pointers.
struct CodeLocation {
  CodeLocation(std::string f, int l) : file(std::move(f)), line(l) {}
  std::string file;
  int line;
};
