- syscalls in ENUMERATE_SYSCALLS: 158
- with a sys$ declaration in Process.h: 158
- without one: none
- sys$ declarations that are not syscalls: beep
- params structs: 49, of which the generic marshaller covers 43
- params structs needing hand-written marshalling: SC_mmap_params, SC_mremap_params, SC_futex_params, SC_create_thread_params, SC_set_mmap_name_params, SC_ptrace_params

| class | syscalls |
|---|---|
| SCALARS | 50 |
| POINTERS | 38 |
| PARAMS | 40 |
| VARIADIC | 4 |
| RUNTIME_OWNED | 26 |

| params field kind | fields |
|---|---|
| SCALAR | 92 |
| STRING | 35 |
| ADDRESS | 6 |
| OUT_ARRAY | 6 |
| IN_PTR | 5 |
| OUT_PTR | 5 |
| IN_ARRAY | 5 |
| OUT_BYTES_INDIRECT | 4 |
| INOUT_PTR | 4 |
| OUT_BUFFER | 4 |
| STRING_LIST | 4 |
| IN_BYTES | 3 |
| ATOMIC_U32 | 2 |
| INOUT_ARRAY | 1 |
| FUTEX_TIMEOUT | 1 |
| CODE | 1 |
| OPAQUE_PTR | 1 |
| SCALAR_OR_PTR | 1 |

Pointer arguments of POINTERS syscalls, by inferred kind:

- OUT_PTR: 18
- IN_PTR: 9
- IN_BYTES: 8
- OUT_BYTES: 6
- OUT_ARRAY: 1
- OUT_IOVEC: 1
- INOUT_MSGHDR: 1
- IN_MSGHDR: 1
- IN_ARRAY: 1
- IN_IOVEC: 1
