#include <assert.h>
#include <ffi.h>
#include <stdarg.h>
#include <stdio.h>

static int add(int a, int b) { return a + b; }
static void *identity(void *p) { return p; }
static double sum(int count, ...) {
    va_list ap;
    va_start(ap, count);
    double result = 0;
    for (int i = 0; i < count; ++i) result += va_arg(ap, double);
    va_end(ap);
    return result;
}
static void callback(ffi_cif *cif, void *result, void **args, void *data) {
    (void)cif;
    *(ffi_arg *)result = *(int *)args[0] + *(int *)args[1] + *(int *)data;
}
int main(void) {
    ffi_cif cif;
    ffi_type *ints[] = { &ffi_type_sint, &ffi_type_sint };
    int a = 19, b = 23;
    void *args[] = { &a, &b };
    ffi_arg result = 0;
    assert(ffi_prep_cif(&cif, FFI_DEFAULT_ABI, 2, &ffi_type_sint, ints) == FFI_OK);
    ffi_call(&cif, FFI_FN(add), &result, args);
    assert(result == 42);

    /* The writable closure record and callable code have distinct roles. */
    void *code;
    ffi_closure *closure = ffi_closure_alloc(sizeof(*closure), &code);
    int extra = 7;
    assert(closure && code);
    assert(ffi_prep_closure_loc(closure, &cif, callback, &extra, code) == FFI_OK);
    assert(((int (*)(int, int))code)(a, b) == 49);
    ffi_closure_free(closure);

    /* Both the returned pointer and its capability must survive ffi_call. */
    ffi_type *ptrs[] = { &ffi_type_pointer };
    int value = 41;
    void *pointer = &value, *returned = NULL;
    void *pargs[] = { &pointer };
    assert(ffi_prep_cif(&cif, FFI_DEFAULT_ABI, 1, &ffi_type_pointer, ptrs) == FFI_OK);
    ffi_call(&cif, FFI_FN(identity), &returned, pargs);
    ++*(int *)returned;
    assert(value == 42);

    ffi_type *var_types[] = { &ffi_type_sint, &ffi_type_double, &ffi_type_double };
    int count = 2;
    double x = 19.25, y = 22.75, total = 0;
    void *vargs[] = { &count, &x, &y };
    assert(ffi_prep_cif_var(&cif, FFI_DEFAULT_ABI, 1, 3, &ffi_type_double, var_types) == FFI_OK);
    ffi_call(&cif, FFI_FN(sum), &total, vargs);
    assert(total == 42);
    puts("libffi: calls, closures, pointer capabilities and variadic arguments passed");
}
