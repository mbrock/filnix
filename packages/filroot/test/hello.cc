#include <iostream>
#include <map>
#include <stdexcept>
#include <string>
#include <thread>
#include <vector>

int main() {
    std::map<std::string, int> counts;
    for (std::string w : {"fil", "c", "fil", "safe"})
        counts[w]++;
    std::vector<std::thread> threads;
    int sums[4] = {0};
    for (int t = 0; t < 4; t++)
        threads.emplace_back([&sums, t] {
            for (int i = 0; i <= 1000; i++)
                sums[t] += i;
        });
    for (auto &t : threads)
        t.join();
    try {
        throw std::runtime_error("caught");
    } catch (const std::exception &e) {
        std::cout << e.what() << " fil=" << counts["fil"] << " sum=" << sums[3] << "\n";
    }
}
