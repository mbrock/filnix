// Runs typed Serenity syscalls through libpizlo-spike's checked natives.
//
//   demo            well-formed calls; prints what each returned
//   demo <attack>   one malformed call that libpizlo must stop with a Fil-C
//                   safety error; see the attacks table below
//
// Call sites are written the way Serenity's LibC writes them.

#include <cerrno>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <string_view>
#include <sys/un.h>
#include <unistd.h>

// Last: its syscall() macro would also rewrite unistd.h's syscall declaration.
#include "serenity_on_linux.h"

static constexpr int AT_FDCWD_SERENITY = -100;
static constexpr int O_RDONLY_SERENITY = 1 << 0;

static int well_formed()
{
    long pid = syscall(SC_getpid);
    std::printf("getpid: %ld (libc says %d)\n", pid, getpid());

    char exe[256];
    std::string_view self = "/proc/self/exe";
    SC_readlink_params rl { { self.data(), self.size() }, { exe, sizeof(exe) - 1 }, AT_FDCWD_SERENITY };
    long n = syscall(SC_readlink, &rl);
    if (n < 0)
        return std::printf("readlink failed: %ld\n", n), 1;
    exe[n] = 0;
    std::printf("readlink: %s\n", exe);

    struct stat st;
    SC_stat_params sp { { exe, std::strlen(exe) }, &st, AT_FDCWD_SERENITY, 1 };
    long rc = syscall(SC_stat, &sp);
    std::printf("stat: rc=%ld size=%lld\n", rc, (long long)st.st_size);

    SC_open_params op { AT_FDCWD_SERENITY, { exe, std::strlen(exe) }, O_RDONLY_SERENITY, 0 };
    long fd = syscall(SC_open, &op);
    char magic[4] {};
    long got = syscall(SC_read, (int)fd, magic, sizeof(magic));
    std::printf("open+read: fd=%ld got=%ld magic=%s\n", fd, got, std::memcmp(magic, "\x7f" "ELF", 4) ? "no" : "\\x7fELF");
    close((int)fd);

    std::string_view missing = "/nonexistent/serenity";
    SC_open_params bad { AT_FDCWD_SERENITY, { missing.data(), missing.size() }, O_RDONLY_SERENITY, 0 };
    std::printf("open missing: %ld (-ENOENT is %d)\n", (long)syscall(SC_open, &bad), -ENOENT);

    // getsockname: addrlen is in/out and bounds addr, so libpizlo copies it.
    int s = socket(AF_UNIX, SOCK_DGRAM, 0);
    sockaddr_un bound {};
    bound.sun_family = AF_UNIX;
    std::memcpy(bound.sun_path, "\0filc-serenity-spike", 21);
    bind(s, (sockaddr*)&bound, offsetof(sockaddr_un, sun_path) + 21);
    sockaddr_un name {};
    socklen_t namelen = sizeof(name);
    SC_getsockname_params gp { s, (sockaddr*)&name, &namelen };
    rc = syscall(SC_getsockname, &gp);
    std::printf("getsockname: rc=%ld namelen=%u name=@%s\n", rc, (unsigned)namelen, name.sun_path + 1);

    std::string_view msg = "write: hello from a typed Serenity syscall\n";
    syscall(SC_write, 1, msg.data(), msg.size());
    return 0;
}

static int attack(std::string_view which)
{
    static char exe[16];
    if (which == "string-length") {
        // StringArgument claims 4096 bytes of a 15-byte string.
        SC_open_params op { AT_FDCWD_SERENITY, { "/proc/self/exe", 4096 }, O_RDONLY_SERENITY, 0 };
        return (int)syscall(SC_open, &op);
    }
    if (which == "string-freed") {
        char* path = (char*)std::malloc(16);
        std::strcpy(path, "/proc/self/exe");
        std::free(path);
        SC_open_params op { AT_FDCWD_SERENITY, { path, 14 }, O_RDONLY_SERENITY, 0 };
        return (int)syscall(SC_open, &op);
    }
    if (which == "out-buffer") {
        // MutableBufferArgument claims 4096 bytes of a 16-byte array.
        SC_readlink_params rl { { "/proc/self/exe", 14 }, { exe, 4096 }, AT_FDCWD_SERENITY };
        return (int)syscall(SC_readlink, &rl);
    }
    if (which == "out-ptr") {
        // statbuf points at 16 bytes, not a struct stat.
        SC_stat_params sp { { "/proc/self/exe", 14 }, (struct stat*)exe, AT_FDCWD_SERENITY, 1 };
        return (int)syscall(SC_stat, &sp);
    }
    if (which == "forged-params") {
        // The params pointer is rebuilt from an integer, so it has no capability.
        // The volatile keeps LLVM from folding the round trip back into &op.
        SC_open_params op { AT_FDCWD_SERENITY, { "/proc/self/exe", 14 }, O_RDONLY_SERENITY, 0 };
        uintptr_t volatile address = (uintptr_t)&op;
        auto forged = (SC_open_params const*)address;
        return (int)syscall(SC_open, forged);
    }
    if (which == "indirect-length") {
        // addrlen claims 4096 bytes; addr is a 16-byte array.
        int s = socket(AF_UNIX, SOCK_DGRAM, 0);
        socklen_t len = 4096;
        SC_getsockname_params gp { s, (sockaddr*)exe, &len };
        return (int)syscall(SC_getsockname, &gp);
    }
    if (which == "raw-buffer") {
        // write's length argument exceeds its buffer.
        return (int)syscall(SC_write, 1, exe, 4096);
    }
    std::fprintf(stderr, "unknown attack %.*s\n", (int)which.size(), which.data());
    return 2;
}

int main(int argc, char** argv)
{
    if (argc < 2)
        return well_formed();
    int rc = attack(argv[1]);
    std::printf("attack %s was NOT stopped (rc=%d)\n", argv[1], rc);
    return 1;
}
