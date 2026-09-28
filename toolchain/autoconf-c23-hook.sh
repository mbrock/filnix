# Autoconf 2.73 selects -std=gnu23 when Clang supports it, and C23 rejects
# K&R function definitions, which GCC still accepts there. Many autoreconf'd
# packages (libtirpc, rpcbind, Ruby, ...) have them; keep the compiler's
# default C standard unless a package asks for another.
export ac_cv_prog_cc_c23="${ac_cv_prog_cc_c23-no}"
