// Boost.Test's execution monitor under Fil-C: the runner must start, report
// a failed check, turn a timeout (SIGALRM) and an exception into test
// failures, and keep running the remaining cases. (Fil-C's abort() stops
// the process itself rather than raising SIGABRT.)
#define BOOST_TEST_MODULE FilcBoostTest
#include <boost/test/unit_test.hpp>
#include <boost/function.hpp>
#include <memory>
#include <string>
#include <stdexcept>
#include <unistd.h>

BOOST_AUTO_TEST_CASE(passes)
{
  BOOST_TEST(1 + 1 == 2);
  BOOST_CHECK_CLOSE(0.1 + 0.2, 0.3, 1e-9);
}

// boost::function tags the vtable pointer of trivially copyable functors.
BOOST_AUTO_TEST_CASE(function_objects)
{
  int base = 40;
  boost::function<int(int)> small = [base](int x) { return base + x; };
  auto shared = std::make_shared<std::string>("fil-c");
  boost::function<std::size_t()> heap = [shared] { return shared->size(); };
  boost::function<int(int)> small_copy = small;
  boost::function<std::size_t()> heap_copy = heap;
  small.clear();
  heap.clear();
  BOOST_TEST(small.empty());
  BOOST_TEST(small_copy(2) == 42);
  BOOST_TEST(heap_copy() == 5u);
  BOOST_TEST(shared.use_count() == 2);
}

BOOST_AUTO_TEST_CASE(expected_check_failure, *boost::unit_test::expected_failures(1))
{
  BOOST_CHECK_EQUAL(2 + 2, 5);
}

BOOST_AUTO_TEST_CASE(times_out, *boost::unit_test::timeout(1))
{
  sleep(5);
}

BOOST_AUTO_TEST_CASE(throws)
{
  throw std::runtime_error("from a test case");
}

BOOST_AUTO_TEST_CASE(passes_after_failures)
{
  BOOST_TEST(std::string("fil") + "-c" == "fil-c");
}
