#include <array>
#include <atomic>
#include <cstdio>
#include <thread>
#include <vector>
#ifdef __FILC__
#include <stdfil.h>
#endif

struct Item {
    unsigned tag;
    unsigned check;
};

static bool valid(Item *p) {
#ifdef __FILC__
    if (!zhasvalidcap(p))
        return false;
#endif
    return p && p->tag >= 1 && p->tag <= 8 && p->check == 3 * p->tag + 11;
}

int main() {
    constexpr unsigned rounds = 16, slots = 512, workers = 8;
    unsigned failures = 0;
    std::atomic<unsigned> bad{0}, failed_cas{0};
    for (unsigned round = 0; round < rounds; ++round) {
        // Each round starts with fresh, unboxed slots: reusing already boxed
        // atomics would miss the primary/shadow publication race.
        std::array<std::atomic<Item *>, slots> values{};
        std::atomic<unsigned> ready{0};
        std::atomic<bool> start{false};
        std::vector<std::thread> threads;
        for (unsigned t = 0; t < workers; ++t) {
            threads.emplace_back([&, t] {
                ready.fetch_add(1, std::memory_order_release);
                while (!start.load(std::memory_order_acquire)) {}
                for (auto &slot : values) {
                    Item *item = new Item{t + 1, 3 * (t + 1) + 11};
                    Item *expected = nullptr;
                    if (!slot.compare_exchange_strong(expected, item,
                            std::memory_order_acq_rel, std::memory_order_acquire)) {
                        failed_cas.fetch_add(1, std::memory_order_relaxed);
                        if (!valid(expected))
                            bad.fetch_add(1, std::memory_order_relaxed);
                        delete item;
                    }
                }
            });
        }
        while (ready.load(std::memory_order_acquire) != workers) {}
        start.store(true, std::memory_order_release);
        for (auto &thread : threads)
            thread.join();
        for (auto &slot : values) {
            Item *item = slot.load(std::memory_order_acquire);
            if (!valid(item))
                ++failures;
            delete item;
        }
    }
    if (failed_cas.load() != rounds * slots * (workers - 1) || bad.load() || failures) {
        std::fprintf(stderr, "failed CAS: %u, bad writebacks: %u, bad loads: %u\n",
                     failed_cas.load(), bad.load(), failures);
        return 1;
    }
    std::puts("57344 failed CAS writebacks and 8192 loads retained valid objects");
}
