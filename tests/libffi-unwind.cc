#include <ffi.h>
#include <cstdio>
static int throwing() { throw 9; }
int main() {
  ffi_cif cif;
  if (ffi_prep_cif(&cif, FFI_DEFAULT_ABI, 0, &ffi_type_sint, nullptr) != FFI_OK) return 2;
  ffi_arg result;
  try { ffi_call(&cif, FFI_FN(throwing), &result, nullptr); }
  catch (int x) { std::printf("caught %d\n", x); return x == 9 ? 0 : 3; }
  return 4;
}
