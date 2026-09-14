/* A real C++ unwind frame between the cancellation point and C cleanup. */
extern "C" void filc_cancel_cxx_scope(void (*body)(void *), void *arg,
                                      void (*destroy)(void *))
{
    struct Guard {
        void *arg;
        void (*destroy)(void *);
        ~Guard() { destroy(arg); }
    } guard { arg, destroy };
    body(arg);
}
