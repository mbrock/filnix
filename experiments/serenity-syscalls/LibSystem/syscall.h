/*
 * Copyright (c) 2021, Andreas Kling <kling@serenityos.org>
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

// Userland/Libraries/LibSystem/syscall.h with a typed path for Fil-C.
//
// The upper half is upstream's header unchanged. Under __FILC__ the lower half
// declares one native per syscall, zsys_serenity_<name>, with the argument
// types the kernel's sys$<name> declares in Kernel/Tasks/Process.h, and turns
// syscall(SC_foo, args...) into a direct call of zsys_serenity_foo(args...).
// The compiler then checks every call site against the kernel's signature,
// and pointer arguments reach libpizlo with their capabilities. All checking
// of memory happens in libpizlo; this header only supplies types.

#pragma once

#include <Kernel/API/Syscall.h>
#include <sys/types.h>

extern "C" {

uintptr_t syscall0(uintptr_t function);
uintptr_t syscall1(uintptr_t function, uintptr_t arg0);
uintptr_t syscall2(uintptr_t function, uintptr_t arg0, uintptr_t arg1);
uintptr_t syscall3(uintptr_t function, uintptr_t arg0, uintptr_t arg1, uintptr_t arg2);
uintptr_t syscall4(uintptr_t function, uintptr_t arg0, uintptr_t arg1, uintptr_t arg2, uintptr_t arg3);
}

#ifdef __cplusplus

inline uintptr_t syscall(auto function)
{
    return syscall0(function);
}

inline uintptr_t syscall(auto function, auto arg0)
{
    return syscall1((uintptr_t)function, (uintptr_t)arg0);
}

inline uintptr_t syscall(auto function, auto arg0, auto arg1)
{
    return syscall2((uintptr_t)function, (uintptr_t)arg0, (uintptr_t)arg1);
}

inline uintptr_t syscall(auto function, auto arg0, auto arg1, auto arg2)
{
    return syscall3((uintptr_t)function, (uintptr_t)arg0, (uintptr_t)arg1, (uintptr_t)arg2);
}

inline uintptr_t syscall(auto function, auto arg0, auto arg1, auto arg2, auto arg3)
{
    return syscall4((uintptr_t)function, (uintptr_t)arg0, (uintptr_t)arg1, (uintptr_t)arg2, (uintptr_t)arg3);
}

#endif

#if defined(__FILC__) && defined(__cplusplus)

#    include <Kernel/API/SyscallSignatures.h>
// The prototypes name POSIX types (stack_t, sigset_t, siginfo_t, timespec,
// msghdr, ...), so this half needs their declarations.
#    include <signal.h>
#    include <sys/resource.h>
#    include <sys/socket.h>
#    include <sys/stat.h>
#    include <sys/statvfs.h>
#    include <sys/times.h>
#    include <sys/uio.h>
#    include <sys/utsname.h>
#    include <time.h>
#    include <utime.h>

namespace Kernel::Syscall {

// One native per syscall. VARIADIC syscalls take their polymorphic last
// argument as "..." so a pointer keeps its capability, as zsys_ioctl does on
// Linux; their rows are skipped here and declared by hand below.
#    define __SC_ARG_TYPE(kind, type, extent) type
#    define __SC_DECLARE_SCALARS(name, ...) extern "C" long zsys_serenity_##name(__VA_ARGS__);
#    define __SC_DECLARE_POINTERS __SC_DECLARE_SCALARS
#    define __SC_DECLARE_PARAMS __SC_DECLARE_SCALARS
#    define __SC_DECLARE_RUNTIME_OWNED __SC_DECLARE_SCALARS
#    define __SC_DECLARE_VARIADIC(name, ...)
#    define __SC_DECLARE(name, cls, ...) __SC_DECLARE_##cls(name __VA_OPT__(, ) __VA_ARGS__)
ENUMERATE_SYSCALL_SIGNATURES(__SC_DECLARE, __SC_ARG_TYPE)

extern "C" long zsys_serenity_ioctl(int fd, unsigned request, ...);
extern "C" long zsys_serenity_fcntl(int fd, int cmd, ...);
extern "C" long zsys_serenity_prctl(int option, ...);
extern "C" long zsys_serenity_archctl(int option, ...);

// Native<SC_foo>::call is zsys_serenity_foo. A syscall without a row has no
// specialization, so naming it is a compile error.
template<Function F>
struct Native;
#    define __SC_NATIVE(name, cls, ...)                                 \
        template<>                                                      \
        struct Native<SC_##name> {                                      \
            static constexpr auto call = &zsys_serenity_##name;         \
        };
ENUMERATE_SYSCALL_SIGNATURES(__SC_NATIVE, __SC_ARG_TYPE)

}

template<Kernel::Syscall::Function F, typename... Args>
inline uintptr_t serenity_syscall(Args... args)
{
    return static_cast<uintptr_t>(Kernel::Syscall::Native<F>::call(args...));
}

// Must come after the overloads above, which it would otherwise rewrite. The
// expansion has no leading "::" so that "::syscall(...)" call sites, as in
// LibCore/System.cpp, become "::serenity_syscall<...>(...)". A
// syscall number that is not a constant expression fails to compile here;
// such callers (Utilities/syscall.cpp, Tests/Kernel/fuzz-syscalls.cpp) need
// the explicit dynamic path, zsys_serenity_dynamic, instead.
#    define syscall(fn, ...) serenity_syscall<fn>(__VA_ARGS__)

extern "C" long zsys_serenity_dynamic(int function, uintptr_t arg1, uintptr_t arg2, uintptr_t arg3, uintptr_t arg4);

#endif
