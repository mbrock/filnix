// Compile-only check: expand the trusted marshaller for every generic params
// struct against SerenityOS's own Kernel/API headers, with the libpizlo API
// stubbed out. -DREFUSED=<sc> expands one of the structs the generic
// marshaller must refuse, which has to fail to compile.

#include <AK/Types.h>
#include <Kernel/API/Syscall.h>
#include <poll.h>
#include <signal.h>
#include <string.h>
#include <sys/socket.h>
#include <sys/stat.h>
#include <sys/statvfs.h>
#include <time.h>

using namespace Kernel::Syscall;

struct filc_thread;
struct filc_ptr {
    void* ptr;
    void* lower;
};
enum filc_access_kind {
    filc_read_access,
    filc_write_access,
};
void* filc_ptr_ptr(filc_ptr);
filc_ptr filc_load_ptr_at(filc_thread*, filc_ptr, void const*);
filc_ptr filc_ptr_with_offset(filc_ptr, uintptr_t);
void filc_check_access(filc_ptr, size_t, filc_access_kind);
size_t filc_mul_size(size_t, size_t);
void* filc_bmalloc_allocate_tmp(filc_thread*, size_t);

#include "filc_serenity_marshal.h"

ENUMERATE_GENERIC_PARAMS_STRUCTS(FILC_SC_DEFINE_MARSHALLER)

#ifdef REFUSED
#    define __DEFINE(sc) FILC_SC_DEFINE_MARSHALLER(sc)
__DEFINE(REFUSED)
#endif

// Instantiate them so the compiler checks every body.
#define __USE(sc) (void*)&filc_serenity_marshal_##sc,
void* all_marshallers[] = { ENUMERATE_GENERIC_PARAMS_STRUCTS(__USE) };
