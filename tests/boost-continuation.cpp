// Boost's two ucontext APIs define different detail::forced_unwind types.
// Exercise the continuation API in its own executable.
#include <boost/context/continuation.hpp>
#include <cassert>
#include <memory>
#include <stdfil.h>

int main() {
    int resumed = 0;
    auto context = boost::context::callcc([&](boost::context::continuation &&caller) {
        auto live = std::make_unique<int>(99);
        caller = caller.resume();
        assert(*live == 99);
        resumed++;
        return std::move(caller);
    });
    zgc_request_and_wait();
    context = context.resume();
    assert(!context && resumed == 1);

}
