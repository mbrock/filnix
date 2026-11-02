/* FilLLVMJIT_EnableSharedObjectCache: processes forked after it share
   compiled code. A child's compile of a module serves its siblings and its
   parent, but only when every mapped pointer is the same: a module whose
   mapping points elsewhere compiles anew and writes where its own mapping
   says. Values that differ between processes go in globals of the module,
   filled after compiling. An object bigger than the region is refused
   without harm, and Fil-C code cannot open /proc/self/mem for writing,
   which would reach the region without a capability. */
#include <errno.h>
#include <fcntl.h>
#include <filc_llvm_jit.h>
#include <string.h>
#include <stdbool.h>
#include <stdfil.h>
#include <stdio.h>
#include <stdlib.h>
#include <sys/wait.h>
#include <unistd.h>

static long a, b;
static long other;

/* put(v): *target = v; get(): return slot (a global of the module) */
static void compile(long* target, bool expect_hit, void (**put)(long), long* (**get)(void),
                    long*** slot)
{
    LLVMContextRef c = LLVMContextCreate();
    LLVMModuleRef m = LLVMModuleCreateWithNameInContext("shared", c);
    LLVMTypeRef i64 = LLVMInt64TypeInContext(c);
    LLVMTypeRef ptr = LLVMPointerTypeInContext(c, 0);
    LLVMTypeRef voidTy = LLVMVoidTypeInContext(c);
    LLVMBuilderRef bld = LLVMCreateBuilderInContext(c);
    LLVMValueRef targetG = LLVMAddGlobal(m, i64, "target");
    LLVMValueRef slotG = LLVMAddGlobal(m, ptr, "slot");
    LLVMSetInitializer(slotG, LLVMConstNull(ptr));

    LLVMValueRef putF = LLVMAddFunction(m, "put", LLVMFunctionType(voidTy, &i64, 1, false));
    LLVMPositionBuilderAtEnd(bld, LLVMAppendBasicBlockInContext(c, putF, "entry"));
    LLVMBuildStore(bld, LLVMGetParam(putF, 0), targetG);
    LLVMBuildRetVoid(bld);

    LLVMValueRef getF = LLVMAddFunction(m, "get", LLVMFunctionType(ptr, NULL, 0, false));
    LLVMPositionBuilderAtEnd(bld, LLVMAppendBasicBlockInContext(c, getF, "entry"));
    LLVMBuildRet(bld, LLVMBuildLoad2(bld, ptr, slotG, ""));

    FilLLVMJITRef jit = FilLLVMJIT_Create();
    FilLLVMJIT_SetGlobalMapping(jit, "target", target);
    unsigned long long hits = FilLLVMJIT_SharedObjectCacheHits();
    FilLLVMJITModuleRef compiled = FilLLVMJIT_CompileModule(jit, m);
    ZASSERT(compiled);
    ZASSERT(FilLLVMJIT_SharedObjectCacheHits() - hits == (expect_hit ? 1 : 0));
    *put = FilLLVMJIT_GetPointerToGlobal(compiled, "put");
    *get = FilLLVMJIT_GetPointerToGlobal(compiled, "get");
    *slot = FilLLVMJIT_GetPointerToGlobal(compiled, "slot");
    ZASSERT(*put && *get && *slot);
}

/* Compile in a child, run the code there, and check what it did. */
static void child(long* target, bool expect_hit, long value)
{
    pid_t pid = fork();
    ZASSERT(pid >= 0);
    if (!pid) {
        void (*put)(long);
        long* (*get)(void);
        long** slot;
        compile(target, expect_hit, &put, &get, &slot);
        put(value);
        ZASSERT(*target == value);
        ZASSERT(a + b == value);
        ZASSERT(!get());
        *slot = &other;
        ZASSERT(get() == &other);
        _exit(0);
    }
    int status;
    ZASSERT(waitpid(pid, &status, 0) == pid);
    ZASSERT(WIFEXITED(status) && !WEXITSTATUS(status));
}

/* A module with megabytes of initialized data, more than a small region holds. */
static void compile_big(void)
{
    enum { size = 3 << 20 };
    char* bytes = malloc(size);
    memset(bytes, 'x', size);
    LLVMContextRef c = LLVMContextCreate();
    LLVMModuleRef m = LLVMModuleCreateWithNameInContext("big", c);
    LLVMValueRef data = LLVMConstStringInContext(c, bytes, size, true);
    LLVMValueRef g = LLVMAddGlobal(m, LLVMTypeOf(data), "big");
    LLVMSetInitializer(g, data);
    free(bytes);
    FilLLVMJITRef jit = FilLLVMJIT_Create();
    unsigned long long hits = FilLLVMJIT_SharedObjectCacheHits();
    FilLLVMJITModuleRef compiled = FilLLVMJIT_CompileModule(jit, m);
    ZASSERT(compiled);
    ZASSERT(FilLLVMJIT_SharedObjectCacheHits() == hits);
    char* p = FilLLVMJIT_GetPointerToGlobal(compiled, "big");
    ZASSERT(p && p[0] == 'x' && p[size - 1] == 'x');
}

static void check_proc_mem(void)
{
    int fd = open("/proc/self/mem", O_RDWR);
    ZASSERT(fd < 0 && errno == EACCES);
    int dir = open("/proc/self", O_RDONLY | O_DIRECTORY);
    ZASSERT(dir >= 0);
    fd = openat(dir, "task/../mem", O_WRONLY);
    ZASSERT(fd < 0 && errno == EACCES);
    char link[64];
    snprintf(link, sizeof(link), "%s/procmem-%d", getenv("TMPDIR") ? getenv("TMPDIR") : "/tmp",
             getpid());
    ZASSERT(!symlink("/proc/self/mem", link));
    fd = open(link, O_RDWR);
    ZASSERT(fd < 0 && errno == EACCES);
    unlink(link);
    fd = open("/proc/self/mem", O_RDONLY);
    ZASSERT(fd >= 0);
    char path[64];
    snprintf(path, sizeof(path), "/proc/self/fd/%d", fd);
    int fd2 = open(path, O_RDWR);
    ZASSERT(fd2 < 0 && errno == EACCES);
    close(fd);
    close(dir);
}

int main()
{
    check_proc_mem();

    /* In a child with a region of its own just above the minimum size. */
    pid_t pid = fork();
    ZASSERT(pid >= 0);
    if (!pid) {
        ZASSERT(!FilLLVMJIT_EnableSharedObjectCache((1 << 20) + (64 << 10)));
        compile_big();
        compile_big(); /* not cached */
        _exit(0);
    }
    int status;
    ZASSERT(waitpid(pid, &status, 0) == pid);
    ZASSERT(WIFEXITED(status) && !WEXITSTATUS(status));

    ZASSERT(!FilLLVMJIT_EnableSharedObjectCache(16 << 20));
    ZASSERT(!FilLLVMJIT_EnableSharedObjectCache(16 << 20));

    child(&a, false, 5);   /* compiles */
    child(&a, true, 7);    /* the sibling's code */
    child(&b, false, 9);   /* another mapping: compiles, writes b */
    child(&b, true, 11);

    /* The parent forked them, so it shares their code too. */
    void (*put)(long);
    long* (*get)(void);
    long** slot;
    compile(&a, true, &put, &get, &slot);
    put(13);
    ZASSERT(a == 13 && !b);
    printf("ok\n");
    return 0;
}
