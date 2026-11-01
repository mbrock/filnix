/* JIT code that touches what Fil-C instruments: a loop (pollchecks), a host
   global bound with FilLLVMJIT_SetGlobalMapping, calls back into the host,
   pointer stores (GC store barriers) and a pointer compare-and-swap. Each
   round compiles a fresh module and runs it while the GC collects. */
#include <filc_llvm_jit.h>
#include <stdbool.h>
#include <stdfil.h>
#include <stdio.h>
#include <stdlib.h>

long counter;
static long calls;

static void bump(long by)
{
    calls += by;
}

struct node { long value; struct node* next; };

/* add(n): for (i = 0; i < n; i++) { counter += i; bump(1); }
   link(head, fresh): fresh->next = head; return cmpxchg(&fresh->next, head, head) ? fresh : 0 */
static void build(void (**add)(long), struct node* (**link)(struct node*, struct node*))
{
    LLVMContextRef c = LLVMContextCreate();
    LLVMModuleRef m = LLVMModuleCreateWithNameInContext("global", c);
    LLVMTypeRef i64 = LLVMInt64TypeInContext(c);
    LLVMTypeRef ptr = LLVMPointerTypeInContext(c, 0);
    LLVMTypeRef voidTy = LLVMVoidTypeInContext(c);
    LLVMTypeRef addTy = LLVMFunctionType(voidTy, &i64, 1, false);
    LLVMTypeRef linkParams[] = { ptr, ptr };
    LLVMTypeRef linkTy = LLVMFunctionType(ptr, linkParams, 2, false);
    LLVMValueRef counterG = LLVMAddGlobal(m, i64, "counter");
    LLVMValueRef bumpF = LLVMAddFunction(m, "bump", addTy);
    LLVMBuilderRef b = LLVMCreateBuilderInContext(c);

    LLVMValueRef addF = LLVMAddFunction(m, "add", addTy);
    LLVMBasicBlockRef entry = LLVMAppendBasicBlockInContext(c, addF, "entry");
    LLVMBasicBlockRef loop = LLVMAppendBasicBlockInContext(c, addF, "loop");
    LLVMBasicBlockRef body = LLVMAppendBasicBlockInContext(c, addF, "body");
    LLVMBasicBlockRef done = LLVMAppendBasicBlockInContext(c, addF, "done");
    LLVMPositionBuilderAtEnd(b, entry);
    LLVMBuildBr(b, loop);
    LLVMPositionBuilderAtEnd(b, loop);
    LLVMValueRef i = LLVMBuildPhi(b, i64, "i");
    LLVMValueRef more = LLVMBuildICmp(b, LLVMIntSLT, i, LLVMGetParam(addF, 0), "more");
    LLVMBuildCondBr(b, more, body, done);
    LLVMPositionBuilderAtEnd(b, body);
    LLVMValueRef old = LLVMBuildLoad2(b, i64, counterG, "old");
    LLVMBuildStore(b, LLVMBuildAdd(b, old, i, "new"), counterG);
    LLVMValueRef one = LLVMConstInt(i64, 1, false);
    LLVMBuildCall2(b, addTy, bumpF, &one, 1, "");
    LLVMValueRef next = LLVMBuildAdd(b, i, one, "next");
    LLVMBuildBr(b, loop);
    LLVMValueRef incoming[] = { LLVMConstInt(i64, 0, false), next };
    LLVMBasicBlockRef from[] = { entry, body };
    LLVMAddIncoming(i, incoming, from, 2);
    LLVMPositionBuilderAtEnd(b, done);
    LLVMBuildRetVoid(b);

    LLVMValueRef linkF = LLVMAddFunction(m, "link", linkTy);
    LLVMPositionBuilderAtEnd(b, LLVMAppendBasicBlockInContext(c, linkF, "entry"));
    LLVMValueRef head = LLVMGetParam(linkF, 0);
    LLVMValueRef fresh = LLVMGetParam(linkF, 1);
    LLVMValueRef nextField = LLVMBuildStructGEP2(
        b, LLVMStructTypeInContext(c, (LLVMTypeRef[]){ i64, ptr }, 2, false), fresh, 1, "nextp");
    LLVMBuildStore(b, head, nextField);
    LLVMValueRef cas = LLVMBuildAtomicCmpXchg(
        b, nextField, head, head, LLVMAtomicOrderingSequentiallyConsistent,
        LLVMAtomicOrderingSequentiallyConsistent, false);
    LLVMValueRef ok = LLVMBuildExtractValue(b, cas, 1, "ok");
    LLVMBuildRet(b, LLVMBuildSelect(b, ok, fresh, LLVMConstNull(ptr), "result"));

    FilLLVMJITRef jit = FilLLVMJIT_Create();
    FilLLVMJIT_SetGlobalMapping(jit, "counter", &counter);
    FilLLVMJIT_SetGlobalMapping(jit, "bump", bump);
    FilLLVMJITModuleRef compiled = FilLLVMJIT_CompileModule(jit, m);
    ZASSERT(compiled);
    *add = FilLLVMJIT_GetPointerToGlobal(compiled, "add");
    *link = FilLLVMJIT_GetPointerToGlobal(compiled, "link");
    ZASSERT(*add && *link);
}

int main(void)
{
    struct node* list = NULL;
    for (int round = 0; round < 20; round++) {
        void (*add)(long);
        struct node* (*link)(struct node*, struct node*);
        build(&add, &link);
        zgc_request_and_wait();
        add(100);
        for (long k = 0; k < 1000; k++) {
            struct node* fresh = malloc(sizeof(struct node));
            fresh->value = k;
            list = link(list, fresh);
            ZASSERT(list == fresh);
            if (!(k % 250))
                zgc_request_and_wait();
        }
    }
    long length = 0, sum = 0;
    for (struct node* n = list; n; n = n->next) {
        length++;
        sum += n->value;
    }
    printf("counter %ld calls %ld length %ld sum %ld\n", counter, calls, length, sum);
    return 0;
}
