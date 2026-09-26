// error_code used to keep its source_location as an integer, so what() on
// an error with a location dereferenced a pointer without a capability.
#include <boost/system/system_error.hpp>
#include <boost/assert/source_location.hpp>
#include <cstdio>
#include <cstring>

int main()
{
    static constexpr boost::source_location loc = BOOST_CURRENT_LOCATION;
    boost::system::error_code ec(EINVAL, boost::system::generic_category(), &loc);
    try {
        throw boost::system::system_error(ec);
    } catch (boost::system::system_error const & e) {
        if (!std::strstr(e.what(), "Invalid argument"))
            return 1;
        std::puts(e.what());
    }
    return 0;
}
