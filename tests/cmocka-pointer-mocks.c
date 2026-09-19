#include "cmocka-pointer-mocks.h"
#include <stdlib.h>
#include <string.h>

static char *pointer_mock(void) { return mock_type(char *); }
static void *explicit_pointer_mock(void) { return mock_ptr_type(void *); }
static int integer_mock(void) { return mock_type(int); }

static void parameters(const char *text, int number) {
    check_expected(text);
    check_expected(number);
}

static void legacy_mocks(void **state) {
    (void)state;
    char local[] = "stack";
    char *heap = malloc(32);
    assert_non_null(heap);
    strcpy(heap, "heap");

    will_return(pointer_mock, local);
    /* Dereference after cmocka frees its queue entry: equality alone cannot
     * prove that the returned pointer still has the object's capability. */
    assert_string_equal(pointer_mock(), "stack");
    will_return_count(pointer_mock, heap, 2);
    char *returned = pointer_mock();
    returned[0] = 'H';
    assert_string_equal(pointer_mock(), "Heap");
    will_return(explicit_pointer_mock, heap);
    assert_memory_equal(explicit_pointer_mock(), "Heap", 5);
    free(heap);

    will_return(pointer_mock, NULL);
    assert_null(pointer_mock());
    int value = -7;
    will_return(integer_mock, value++);
    assert_int_equal(value, -6);
    assert_int_equal(integer_mock(), -7);
    will_return_always(integer_mock, 42);
    assert_int_equal(integer_mock(), 42);
    assert_int_equal(integer_mock(), 42);
    will_return_maybe(explicit_pointer_mock, local);
    assert_memory_equal(explicit_pointer_mock(), "stack", 6);

    expect_string(parameters, text, "stack");
    expect_value(parameters, number, -3);
    parameters(local, -3);
}

int main(void) {
    const struct CMUnitTest tests[] = {cmocka_unit_test(legacy_mocks)};
    return cmocka_run_group_tests(tests, NULL, NULL);
}
