/* A real C++ unwind frame between the cancellation point and C cleanup. */
#include <cstdlib>
#ifdef __FILC__
#include <stdfil.h>
#endif

extern "C" void filc_cancel_cxx_scope(void (*body)(void *), void *arg,
                                      void (*destroy)(void *))
{
    struct Guard {
        void *arg;
        void (*destroy)(void *);
        ~Guard() {
            // An inner handler must not overwrite the forced unwind's state.
            try {
                throw 73;
            } catch (int value) {
                if (value != 73)
                    std::abort();
#ifdef __FILC__
                zgc_request_and_wait();
#endif
            }
            destroy(arg);
        }
    } guard { arg, destroy };
    body(arg);
}
