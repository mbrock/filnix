#include <boost/json.hpp>
#include <boost/unordered/unordered_flat_map.hpp>
#include <boost/coroutine2/all.hpp>
#include <boost/multi_index_container.hpp>
#include <boost/multi_index/ordered_index.hpp>
#include <boost/multi_index/identity.hpp>
#include <cassert>
#include <memory>
#include <stdexcept>
#include <stdfil.h>

struct Guard {
    int &destroyed;
    ~Guard() { ++destroyed; }
};

int main() {
    auto json = boost::json::parse("{\"answer\":42}");
    assert(json.as_object().at("answer").as_int64() == 42);
    boost::unordered_flat_map<int, std::string> values;
    values.emplace(42, "answer");
    zgc_request_and_wait();
    assert(values.at(42) == "answer");

    using Coroutine = boost::coroutines2::coroutine<int *>;
    int destroyed = 0;
    {
        Coroutine::pull_type source([&](Coroutine::push_type &yield) {
            Guard guard{destroyed};
            auto value = std::make_unique<int>(41);
            yield(value.get());
            assert(*value == 42);
            zgc_request_and_wait();
            ++*value;
            yield(value.get());
        });
        assert(source && *source.get() == 41);
        ++*source.get();
        zgc_request_and_wait();
        source();
        assert(source && *source.get() == 43);
        source();
        assert(!source);
    }
    assert(destroyed == 1);
    {
        Coroutine::pull_type source([&](Coroutine::push_type &yield) {
            Guard guard{destroyed};
            int value = 7;
            yield(&value);
            assert(false); // Destroying a suspended coroutine must unwind it.
        });
        assert(*source.get() == 7);
    }
    assert(destroyed == 2);
    {
        Coroutine::pull_type source([&](Coroutine::push_type &yield) {
            Guard guard{destroyed};
            int value = 11;
            yield(&value);
            throw std::runtime_error("coroutine exception");
        });
        bool caught = false;
        try { source(); } catch (const std::runtime_error &) { caught = true; }
        assert(caught);
    }
    assert(destroyed == 3);

    namespace mi = boost::multi_index;
    mi::multi_index_container<int, mi::indexed_by<mi::ordered_unique<mi::identity<int>>>> index;
    for (int i = 199; i >= 0; --i) assert(index.insert(i).second);
    for (int i = 0; i < 200; i += 2) assert(index.erase(i) == 1);
    zgc_request_and_wait();
    int expected = 1;
    for (int value : index) { assert(value == expected); expected += 2; }
    assert(expected == 201 && index.find(99) != index.end());
}
