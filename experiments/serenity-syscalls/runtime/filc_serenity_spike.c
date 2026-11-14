/* SerenityOS typed syscalls, emulated on Linux inside libpizlo (spike).

   libpizlo-spike.nix appends an #include of this file to filc_runtime.c, so it
   sees the runtime's internals (check_fd, filc_exit, ...). It defines the
   zsys_serenity_* natives that runtime/addsig.rb registers. Each one checks
   its arguments the way a Serenity port would, then calls a "trap" that, on
   Serenity, would enter the kernel with Syscall::invoke. Here the trap runs
   the closest Linux call instead, so the checking half can run under real
   Fil-C today.

   Errors come back Serenity-style, as a negative errno, and the runtime
   leaves errno alone: Serenity's LibC sets errno itself. */

#include <sys/socket.h>
#include <sys/stat.h>

typedef uint16_t u16;
typedef uint32_t u32;
typedef struct sockaddr sockaddr;

typedef struct {
    const char* characters;
    size_t length;
} StringArgument;

typedef struct {
    StringArgument* strings;
    size_t length;
} StringListArgument;

#define SC_MUTABLE_BUFFER(T, S) struct { T* data; S size; }
#define SC_USERSPACE(T) T

#include "SyscallParams.h"

/* Expansion A, in C, for the structs this spike implements. */
#define FILC_SC_FIELD_DECL(kind, type, name, extent, ...) type name;
#define FILC_SC_STRUCT(sc) typedef struct { SC_##sc##_FIELDS(FILC_SC_FIELD_DECL) } SC_##sc##_params;
FILC_SC_STRUCT(open)
FILC_SC_STRUCT(readlink)
FILC_SC_STRUCT(stat)
FILC_SC_STRUCT(getsockname)

#include "filc_serenity_marshal.h"

FILC_SC_DEFINE_MARSHALLER(open)
FILC_SC_DEFINE_MARSHALLER(readlink)
FILC_SC_DEFINE_MARSHALLER(stat)
FILC_SC_DEFINE_MARSHALLER(getsockname)

/* Leave the runtime around a blocking call and return -errno on failure. */
#define FILC_SERENITY_TRAP(my_thread, call) ({ \
        filc_exit(my_thread);                  \
        long trap_result = (call);             \
        int trap_errno = errno;                \
        filc_enter(my_thread);                 \
        trap_result < 0 ? -(long)trap_errno : trap_result; \
    })

/* Serenity's open flags, from Kernel/API/POSIX/fcntl.h, to Linux's. */
static int filc_serenity_open_flags(int options)
{
    int flags = 0;
    switch (options & 3) {
    case 1: flags = O_RDONLY; break;
    case 2: flags = O_WRONLY; break;
    case 3: flags = O_RDWR; break;
    }
    if (options & (1 << 3)) flags |= O_CREAT;
    if (options & (1 << 4)) flags |= O_EXCL;
    if (options & (1 << 6)) flags |= O_TRUNC;
    if (options & (1 << 7)) flags |= O_APPEND;
    if (options & (1 << 9)) flags |= O_DIRECTORY;
    if (options & (1 << 10)) flags |= O_NOFOLLOW;
    if (options & (1 << 11)) flags |= O_CLOEXEC;
    return flags;
}

static long filc_serenity_trap_open(filc_thread* my_thread, SC_open_params* p)
{
    return FILC_SERENITY_TRAP(
        my_thread, openat(p->dirfd, p->path.characters, filc_serenity_open_flags(p->options), (mode_t)p->mode));
}

static long filc_serenity_trap_readlink(filc_thread* my_thread, SC_readlink_params* p)
{
    return FILC_SERENITY_TRAP(
        my_thread, readlinkat(p->dirfd, p->path.characters, p->buffer.data, p->buffer.size));
}

static long filc_serenity_trap_stat(filc_thread* my_thread, SC_stat_params* p)
{
    return FILC_SERENITY_TRAP(
        my_thread,
        fstatat(p->dirfd, p->path.characters, p->statbuf, p->follow_symlinks ? 0 : AT_SYMLINK_NOFOLLOW));
}

static long filc_serenity_trap_getsockname(filc_thread* my_thread, SC_getsockname_params* p)
{
    check_fd(p->sockfd);
    return FILC_SERENITY_TRAP(my_thread, getsockname(p->sockfd, p->addr, p->addrlen));
}

long filc_native_zsys_serenity_open(filc_thread* my_thread, filc_ptr params)
{
    return filc_serenity_marshal_open(my_thread, params, filc_serenity_trap_open);
}

long filc_native_zsys_serenity_readlink(filc_thread* my_thread, filc_ptr params)
{
    return filc_serenity_marshal_readlink(my_thread, params, filc_serenity_trap_readlink);
}

long filc_native_zsys_serenity_stat(filc_thread* my_thread, filc_ptr params)
{
    return filc_serenity_marshal_stat(my_thread, params, filc_serenity_trap_stat);
}

long filc_native_zsys_serenity_getsockname(filc_thread* my_thread, filc_ptr params)
{
    return filc_serenity_marshal_getsockname(my_thread, params, filc_serenity_trap_getsockname);
}

/* Raw-pointer syscalls: the extent is another argument (Process.h's
   sys$write(int, Userspace<u8 const*>, size_t)), so the check is direct. */
long filc_native_zsys_serenity_write(filc_thread* my_thread, int fd, filc_ptr data, size_t size)
{
    check_fd(fd);
    filc_check_access(data, size, filc_read_access);
    return FILC_SERENITY_TRAP(my_thread, write(fd, filc_ptr_ptr(data), size));
}

long filc_native_zsys_serenity_read(filc_thread* my_thread, int fd, filc_ptr data, size_t size)
{
    check_fd(fd);
    filc_check_access(data, size, filc_write_access);
    return FILC_SERENITY_TRAP(my_thread, read(fd, filc_ptr_ptr(data), size));
}

long filc_native_zsys_serenity_getpid(filc_thread* my_thread)
{
    return FILC_SERENITY_TRAP(my_thread, getpid());
}
