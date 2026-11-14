/* Expansion C: trusted marshallers for SerenityOS params structs, in libpizlo.

   A pizlonated program passes a pointer to an SC_foo_params struct. The struct
   lives in Fil-C memory, so the address words of its pointer fields are in the
   struct while their capabilities are kept by the runtime. This file expands
   each SC_foo_FIELDS X-macro from SyscallParams.h into a function that

     1. checks that the struct itself is readable and copies it,
     2. reloads every pointer field with filc_load_ptr_at, so the runtime gets
        the capability, and checks it against the extent the descriptor names,
     3. replaces the copy's pointer fields with checked raw pointers, deep
        copies of strings, or runtime-owned copies of in/out words,
     4. calls trap(), the yolo function that enters the kernel with the copy,
     5. copies in/out words back to the program.

   Strings and string lists are copied because the kernel reads them after
   the check, and another thread could otherwise change them in between. For
   the same reason, an in/out word that bounds another buffer, such as
   accept4's addrlen, is copied before the check and copied back after the
   call: the kernel then sees the length the runtime checked.

   This header compiles as C (libpizlo) and as C++ (a check against Serenity's
   own headers). It needs filc_thread, filc_ptr, filc_load_ptr_at,
   filc_check_access, filc_ptr_ptr, filc_ptr_with_offset, filc_mul_size,
   filc_bmalloc_allocate_tmp, memcpy, StringArgument and StringListArgument. */

#ifndef FILC_SERENITY_MARSHAL_H
#define FILC_SERENITY_MARSHAL_H

static inline void* filc_serenity_checked(filc_ptr ptr, size_t size, filc_access_kind kind)
{
    if (!filc_ptr_ptr(ptr))
        return NULL;
    filc_check_access(ptr, size, kind);
    return filc_ptr_ptr(ptr);
}

static inline const char* filc_serenity_copy_string(filc_thread* my_thread, filc_ptr chars, size_t length)
{
    char* copy;
    if (!filc_ptr_ptr(chars) && !length)
        return NULL;
    filc_check_access(chars, length, filc_read_access);
    copy = (char*)filc_bmalloc_allocate_tmp(my_thread, length + 1);
    memcpy(copy, filc_ptr_ptr(chars), length);
    copy[length] = 0; /* Serenity does not need this; the Linux emulation does. */
    return copy;
}

static inline StringArgument* filc_serenity_copy_string_list(filc_thread* my_thread, filc_ptr list, size_t count)
{
    StringArgument* copy;
    size_t index;
    filc_check_access(list, filc_mul_size(count, sizeof(StringArgument)), filc_read_access);
    copy = (StringArgument*)filc_bmalloc_allocate_tmp(my_thread, filc_mul_size(count, sizeof(StringArgument)));
    for (index = 0; index < count; ++index) {
        filc_ptr entry = filc_ptr_with_offset(list, index * sizeof(StringArgument));
        StringArgument* user = (StringArgument*)filc_ptr_ptr(entry);
        size_t length = user->length;
        copy[index].characters = filc_serenity_copy_string(
            my_thread, filc_load_ptr_at(my_thread, entry, &user->characters), length);
        copy[index].length = length;
    }
    return copy;
}

/* The pointer field `name` of the program's struct, with its capability. */
#define FILC_SC_LOAD(field) filc_load_ptr_at(my_thread, user, &src->field)
#define FILC_SC_SIZE_OF_FIELD(name) sizeof(*p->name)

/* Locals: one slot per in/out word, to copy it back after the call. */
#define FILC_SC_LOCALS(kind, type, name, extent, ...) FILC_SC_LOCALS_##kind(name)
#define FILC_SC_LOCALS_INOUT_PTR(name) void* user_##name = NULL;
#define FILC_SC_LOCALS_SCALAR(name)
#define FILC_SC_LOCALS_STRING(name)
#define FILC_SC_LOCALS_STRING_LIST(name)
#define FILC_SC_LOCALS_OUT_BUFFER(name)
#define FILC_SC_LOCALS_IN_PTR(name)
#define FILC_SC_LOCALS_OUT_PTR(name)
#define FILC_SC_LOCALS_IN_ARRAY(name)
#define FILC_SC_LOCALS_OUT_ARRAY(name)
#define FILC_SC_LOCALS_INOUT_ARRAY(name)
#define FILC_SC_LOCALS_IN_BYTES(name)
#define FILC_SC_LOCALS_OUT_BYTES_INDIRECT(name)

/* Pass 1: everything whose extent is in the struct copy itself. */
#define FILC_SC_PASS1(kind, type, name, extent, ...) FILC_SC_##kind(name, extent)
#define FILC_SC_SCALAR(name, extent)
#define FILC_SC_STRING(name, extent) \
    p->name.characters = filc_serenity_copy_string(my_thread, FILC_SC_LOAD(name.characters), p->name.length);
#define FILC_SC_STRING_LIST(name, extent) \
    p->name.strings = filc_serenity_copy_string_list(my_thread, FILC_SC_LOAD(name.strings), p->name.length);
#define FILC_SC_OUT_BUFFER(name, extent)                                                                     \
    *(void**)&p->name.data = filc_serenity_checked(                                                          \
        FILC_SC_LOAD(name.data), filc_mul_size(p->name.size, sizeof(*p->name.data)), filc_write_access);
#define FILC_SC_IN_PTR(name, extent) \
    *(void**)&p->name = filc_serenity_checked(FILC_SC_LOAD(name), FILC_SC_SIZE_OF_FIELD(name), filc_read_access);
#define FILC_SC_OUT_PTR(name, extent) \
    *(void**)&p->name = filc_serenity_checked(FILC_SC_LOAD(name), FILC_SC_SIZE_OF_FIELD(name), filc_write_access);
#define FILC_SC_INOUT_PTR(name, extent)                                                                        \
    user_##name = filc_serenity_checked(FILC_SC_LOAD(name), FILC_SC_SIZE_OF_FIELD(name), filc_write_access);   \
    if (user_##name) {                                                                                         \
        *(void**)&p->name = filc_bmalloc_allocate_tmp(my_thread, FILC_SC_SIZE_OF_FIELD(name));                 \
        memcpy((void*)p->name, user_##name, FILC_SC_SIZE_OF_FIELD(name));                                      \
    }
#define FILC_SC_IN_ARRAY(name, extent) \
    *(void**)&p->name = filc_serenity_checked(FILC_SC_LOAD(name), filc_mul_size((extent), FILC_SC_SIZE_OF_FIELD(name)), filc_read_access);
#define FILC_SC_OUT_ARRAY(name, extent) \
    *(void**)&p->name = filc_serenity_checked(FILC_SC_LOAD(name), filc_mul_size((extent), FILC_SC_SIZE_OF_FIELD(name)), filc_write_access);
#define FILC_SC_INOUT_ARRAY FILC_SC_OUT_ARRAY
#define FILC_SC_IN_BYTES(name, extent) \
    *(void**)&p->name = filc_serenity_checked(FILC_SC_LOAD(name), (extent), filc_read_access);
#define FILC_SC_OUT_BYTES_INDIRECT(name, extent)

/* Pass 2: buffers bounded by an in/out word, which pass 1 has copied. */
#define FILC_SC_PASS2(kind, type, name, extent, ...) FILC_SC_PASS2_##kind(name, extent)
#define FILC_SC_PASS2_OUT_BYTES_INDIRECT(name, extent) \
    *(void**)&p->name = filc_serenity_checked(FILC_SC_LOAD(name), (extent) ? *(extent) : 0, filc_write_access);
#define FILC_SC_PASS2_SCALAR(name, extent)
#define FILC_SC_PASS2_STRING(name, extent)
#define FILC_SC_PASS2_STRING_LIST(name, extent)
#define FILC_SC_PASS2_OUT_BUFFER(name, extent)
#define FILC_SC_PASS2_IN_PTR(name, extent)
#define FILC_SC_PASS2_OUT_PTR(name, extent)
#define FILC_SC_PASS2_INOUT_PTR(name, extent)
#define FILC_SC_PASS2_IN_ARRAY(name, extent)
#define FILC_SC_PASS2_OUT_ARRAY(name, extent)
#define FILC_SC_PASS2_INOUT_ARRAY(name, extent)
#define FILC_SC_PASS2_IN_BYTES(name, extent)

/* After the call: copy in/out words back. */
#define FILC_SC_COPY_BACK(kind, type, name, extent, ...) FILC_SC_COPY_BACK_##kind(name)
#define FILC_SC_COPY_BACK_INOUT_PTR(name) \
    if (user_##name)                      \
        memcpy(user_##name, (void*)p->name, FILC_SC_SIZE_OF_FIELD(name));
#define FILC_SC_COPY_BACK_SCALAR(name)
#define FILC_SC_COPY_BACK_STRING(name)
#define FILC_SC_COPY_BACK_STRING_LIST(name)
#define FILC_SC_COPY_BACK_OUT_BUFFER(name)
#define FILC_SC_COPY_BACK_IN_PTR(name)
#define FILC_SC_COPY_BACK_OUT_PTR(name)
#define FILC_SC_COPY_BACK_IN_ARRAY(name)
#define FILC_SC_COPY_BACK_OUT_ARRAY(name)
#define FILC_SC_COPY_BACK_INOUT_ARRAY(name)
#define FILC_SC_COPY_BACK_IN_BYTES(name)
#define FILC_SC_COPY_BACK_OUT_BYTES_INDIRECT(name)

/* Kinds the generic marshaller refuses: a struct with one of these fields
   fails to compile here and needs hand-written code in the runtime. */
#define FILC_SC_REFUSE(kind, name) \
    _Static_assert(0, #kind " field " #name " needs a hand-written marshaller");
#define FILC_SC_ADDRESS(name, extent) FILC_SC_REFUSE(ADDRESS, name)
#define FILC_SC_CODE(name, extent) FILC_SC_REFUSE(CODE, name)
#define FILC_SC_OPAQUE_PTR(name, extent) FILC_SC_REFUSE(OPAQUE_PTR, name)
#define FILC_SC_FUTEX_TIMEOUT(name, extent) FILC_SC_REFUSE(FUTEX_TIMEOUT, name)
#define FILC_SC_SCALAR_OR_PTR(name, extent) FILC_SC_REFUSE(SCALAR_OR_PTR, name)
#define FILC_SC_ATOMIC_U32(name, extent) FILC_SC_REFUSE(ATOMIC_U32, name)
#define FILC_SC_LOCALS_ADDRESS(name)
#define FILC_SC_LOCALS_CODE(name)
#define FILC_SC_LOCALS_OPAQUE_PTR(name)
#define FILC_SC_LOCALS_FUTEX_TIMEOUT(name)
#define FILC_SC_LOCALS_SCALAR_OR_PTR(name)
#define FILC_SC_LOCALS_ATOMIC_U32(name)
#define FILC_SC_PASS2_ADDRESS(name, extent)
#define FILC_SC_PASS2_CODE(name, extent)
#define FILC_SC_PASS2_OPAQUE_PTR(name, extent)
#define FILC_SC_PASS2_FUTEX_TIMEOUT(name, extent)
#define FILC_SC_PASS2_SCALAR_OR_PTR(name, extent)
#define FILC_SC_PASS2_ATOMIC_U32(name, extent)
#define FILC_SC_COPY_BACK_ADDRESS(name)
#define FILC_SC_COPY_BACK_CODE(name)
#define FILC_SC_COPY_BACK_OPAQUE_PTR(name)
#define FILC_SC_COPY_BACK_FUTEX_TIMEOUT(name)
#define FILC_SC_COPY_BACK_SCALAR_OR_PTR(name)
#define FILC_SC_COPY_BACK_ATOMIC_U32(name)

/* filc_serenity_marshal_<sc>(my_thread, user, trap): marshal, call, copy back.
   trap receives the runtime's copy and returns the kernel's result. */
#define FILC_SC_DEFINE_MARSHALLER(sc)                                                           \
    static long filc_serenity_marshal_##sc(                                                     \
        filc_thread* my_thread, filc_ptr user, long (*trap)(filc_thread*, SC_##sc##_params*))   \
    {                                                                                           \
        SC_##sc##_params copy;                                                                  \
        SC_##sc##_params* p = &copy;                                                            \
        const SC_##sc##_params* src;                                                            \
        long result;                                                                            \
        SC_##sc##_FIELDS(FILC_SC_LOCALS)                                                        \
        filc_check_access(user, sizeof(copy), filc_read_access);                                \
        src = (const SC_##sc##_params*)filc_ptr_ptr(user);                                      \
        memcpy((void*)&copy, (const void*)src, sizeof(copy));                                   \
        SC_##sc##_FIELDS(FILC_SC_PASS1)                                                         \
        SC_##sc##_FIELDS(FILC_SC_PASS2)                                                         \
        result = trap(my_thread, p);                                                            \
        SC_##sc##_FIELDS(FILC_SC_COPY_BACK)                                                     \
        return result;                                                                          \
    }

#endif /* FILC_SERENITY_MARSHAL_H */
