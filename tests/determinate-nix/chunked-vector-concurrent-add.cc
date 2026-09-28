// ChunkedVector.ConcurrentAdd from Determinate Nix's libutil-tests, standalone.
#include "nix/util/chunked-vector.hh"
#include <thread>
#include <set>
#include <cstdio>
using namespace nix;
int main() {
  ChunkedVector<uint64_t, 17, 8192> v;
  constexpr int nThreads = 8, perThread = 8192;
  std::vector<std::thread> threads;
  std::vector<std::vector<uint32_t>> indices(nThreads);
  for (int t = 0; t < nThreads; t++)
    threads.emplace_back([&, t]() {
      for (int i = 0; i < perThread; ++i) {
        auto [val, idx] = v.add(static_cast<uint64_t>(t * perThread + i));
        indices[t].push_back(idx);
      }
    });
  for (auto & t : threads) t.join();
  std::set<uint32_t> all;
  for (auto & vec : indices) for (auto idx : vec) if (!all.insert(idx).second) return 2;
  for (int t = 0; t < nThreads; t++) for (int i = 0; i < perThread; i++)
    if (v[indices[t][i]] != static_cast<uint64_t>(t * perThread + i)) return 3;
  std::puts("ok");
}
