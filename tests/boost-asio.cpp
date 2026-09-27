// io_context executors keep the context pointer with flag bits; posting
// through a strand and a tracked executor must reach the context.
#include <boost/asio.hpp>
#include <cstdio>

int main()
{
    boost::asio::io_context ioc;
    auto tracked = boost::asio::require(ioc.get_executor(), boost::asio::execution::outstanding_work.tracked);
    auto strand = boost::asio::make_strand(ioc);
    int n = 0;
    boost::asio::post(strand, [&] { n++; });
    boost::asio::post(ioc, [&] { n++; });
    { auto moved = std::move(tracked); }
    ioc.run();
    std::printf("n=%d\n", n);
    return n == 2 ? 0 : 1;
}
