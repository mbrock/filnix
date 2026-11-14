// Just enough of a pizlonated Serenity userland to run typed syscalls on
// Linux against libpizlo-spike.nix. It expands the same generated
// descriptors as the Serenity headers: the SC_*_params structs from
// SyscallParams.h and the Function enum from SyscallSignatures.h, so the
// syscall numbers match Kernel/API/Syscall.h. Only the natives the spike
// implements are declared. The dispatch and the syscall macro are the same
// as in LibSystem/syscall.h.

#pragma once

#include <cstddef>
#include <cstdint>
#include <sys/socket.h>
#include <sys/stat.h>

using u16 = uint16_t;
using u32 = uint32_t;

namespace Syscall {

struct StringArgument {
    char const* characters;
    size_t length { 0 };
};

template<typename DataType, typename SizeType>
struct MutableBufferArgument {
    DataType* data { nullptr };
    SizeType size { 0 };
};

#define SC_MUTABLE_BUFFER(T, S) MutableBufferArgument<T, S>
#define SC_USERSPACE(T) T
#include "../generated/SyscallParams.h"
#include "../generated/SyscallSignatures.h"

#define __SC_FIELD_DECL(kind, type, name, extent, ...) type name __VA_OPT__(= __VA_ARGS__);
#define __SC_PARAMS_STRUCT(sc) struct SC_##sc##_params { SC_##sc##_FIELDS(__SC_FIELD_DECL) };
__SC_PARAMS_STRUCT(open)
__SC_PARAMS_STRUCT(readlink)
__SC_PARAMS_STRUCT(stat)
__SC_PARAMS_STRUCT(getsockname)

enum Function {
#define __SC_ENUM(name, ...) SC_##name,
    ENUMERATE_SYSCALL_SIGNATURES(__SC_ENUM, )
    __Count
};

extern "C" {
long zsys_serenity_getpid();
long zsys_serenity_write(int, void const*, size_t);
long zsys_serenity_read(int, void*, size_t);
long zsys_serenity_open(SC_open_params const*);
long zsys_serenity_readlink(SC_readlink_params const*);
long zsys_serenity_stat(SC_stat_params const*);
long zsys_serenity_getsockname(SC_getsockname_params const*);
}

template<Function F>
struct Native;
#define __SC_NATIVE(name)                                       \
    template<>                                                  \
    struct Native<SC_##name> {                                  \
        static constexpr auto call = &zsys_serenity_##name;     \
    };
__SC_NATIVE(getpid)
__SC_NATIVE(write)
__SC_NATIVE(read)
__SC_NATIVE(open)
__SC_NATIVE(readlink)
__SC_NATIVE(stat)
__SC_NATIVE(getsockname)

}

using namespace Syscall;

template<Syscall::Function F, typename... Args>
inline uintptr_t serenity_syscall(Args... args)
{
    return static_cast<uintptr_t>(Syscall::Native<F>::call(args...));
}

#define syscall(fn, ...) serenity_syscall<fn>(__VA_ARGS__)
