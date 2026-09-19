/* TPM2-TSS 4.x uses cmocka's legacy integer/pointer-polymorphic macros.
 * Cmocka 2 provides pointer-valued storage: select that member at each old
 * call site instead of discarding pointer capabilities through uintmax_t.
 * Only C integer and pointer values are supported by this compatibility shim.
 */
#ifndef FILNIX_CMOCKA_POINTER_MOCKS_H
#define FILNIX_CMOCKA_POINTER_MOCKS_H
/* This adapter intentionally uses the supported legacy integer assertions. */
#define CMOCKA_DISABLE_DEPRECATION_WARNINGS
#include <cmocka.h>

#define filnix_mock_value(value) \
    __builtin_choose_expr(__builtin_classify_type(value) == 5, \
        ((CMockaValueData){.const_ptr = (const void *)(uintptr_t)(value)}), \
        ((CMockaValueData){.uint_val = (uintmax_t)(value)}))

#undef will_return_count
#define will_return_count(function, value, count) \
    _will_return(#function, __FILE__, __LINE__, NULL, \
                 filnix_mock_value(value), count)
#undef will_return
#define will_return(function, value) will_return_count(function, value, 1)
#undef will_return_always
#define will_return_always(function, value) \
    will_return_count(function, value, WILL_RETURN_ALWAYS)
#undef will_return_maybe
#define will_return_maybe(function, value) \
    will_return_count(function, value, WILL_RETURN_ONCE)

#undef mock_type
#define mock_type(type) \
    ((type)__builtin_choose_expr(__builtin_classify_type((type)0) == 5, \
        _mock(__func__, __FILE__, __LINE__, NULL).ptr, \
        _mock(__func__, __FILE__, __LINE__, NULL).uint_val))

#undef check_expected
#define check_expected(parameter) \
    _check_expected(__func__, #parameter, __FILE__, __LINE__, \
                    filnix_mock_value(parameter))
#endif
