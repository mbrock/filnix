// Verify the reader's pointer-table lookup and exact backing-store lifetime.
#include <assert.h>
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "quickjs.h"

typedef struct {
    int refs;
    uint8_t data[];
} Buffer;

static int live, duplicates;

static Buffer *header(void *data)
{
    return (Buffer *)((uint8_t *)data - offsetof(Buffer, data));
}

static void *allocate(void *opaque, size_t size)
{
    Buffer *b = malloc(sizeof(*b) + size);
    assert(b);
    b->refs = 1;
    live++;
    return b->data;
}

static void duplicate(void *opaque, void *data)
{
    Buffer *b = header(data);
    assert(b->refs > 0);
    b->refs++;
    duplicates++;
}

static void release(void *opaque, void *data)
{
    Buffer *b = header(data);
    assert(b->refs > 0);
    if (--b->refs == 0) {
        live--;
        free(b);
    }
}

static void expect_exception(JSContext *ctx, JSValue value)
{
    assert(JS_IsException(value));
    JS_FreeValue(ctx, JS_GetException(ctx));
}

int main(void)
{
    JSSharedArrayBufferFunctions sf = { allocate, release, duplicate, NULL };
    JSRuntime *sender = JS_NewRuntime(), *receiver = JS_NewRuntime();
    assert(sender && receiver);
    JS_SetSharedArrayBufferFunctions(sender, &sf);
    JS_SetSharedArrayBufferFunctions(receiver, &sf);
    JSContext *src = JS_NewContext(sender), *dst = JS_NewContext(receiver);
    assert(src && dst);
    const char script[] = "(()=>{const a=new SharedArrayBuffer(23),"
                          "b=new SharedArrayBuffer(7);return [a,b,a];})()";
    JSValue original = JS_Eval(src, script, strlen(script), "sab-test",
                               JS_EVAL_TYPE_GLOBAL);
    assert(!JS_IsException(original));
    assert(live == 2);
    size_t size, count;
    uint8_t **table;
    uint8_t *bytes = JS_WriteObject2(src, &size, original,
                                    JS_WRITE_OBJ_SAB | JS_WRITE_OBJ_REFERENCE,
                                    &table, &count);
    assert(bytes && count == 2);
    // Simulate the worker's allocator-independent message and queue refs.
    uint8_t *data = malloc(size);
    assert(data);
    memcpy(data, bytes, size);
    uint8_t *stores[2];
    memcpy(stores, table, sizeof(stores));
    duplicate(NULL, stores[0]);
    duplicate(NULL, stores[1]);
    js_free(src, bytes);
    js_free(src, table);
    JS_FreeValue(src, original);
    JS_FreeContext(src);
    JS_FreeRuntime(sender);
    assert(live == 2);
    assert(header(stores[0])->refs == 1 && header(stores[1])->refs == 1);
    int flags = JS_READ_OBJ_SAB | JS_READ_OBJ_REFERENCE;
    int before = duplicates;
    // Address absent from the table: do not touch any refcounts.
    expect_exception(dst, JS_ReadObject2(dst, data, size, flags, stores + 1, 1));
    assert(duplicates == before);
    // First clone succeeds, second fails: the partial clone must be freed.
    expect_exception(dst, JS_ReadObject2(dst, data, size, flags, stores, 1));
    assert(duplicates == before + 1);
    assert(header(stores[0])->refs == 1 && header(stores[1])->refs == 1);
#ifdef __PIZLONATOR_WAS_HERE__
    // The legacy byte-only API cannot reconstruct a capability.
    expect_exception(dst, JS_ReadObject(dst, data, size, flags));
    assert(duplicates == before + 1);
#endif
    // Deliberately reorder the table: lookup must use the serialized address,
    // not the first entry or serialization order.
    uint8_t *reversed[] = { stores[1], stores[0] };
    JSValue clone = JS_ReadObject2(dst, data, size, flags, reversed, 2);
    assert(!JS_IsException(clone));
    assert(header(stores[0])->refs == 2 && header(stores[1])->refs == 2);
    release(NULL, stores[0]);
    release(NULL, stores[1]);
    free(data);
    JSValue a = JS_GetPropertyUint32(dst, clone, 0);
    JSValue b = JS_GetPropertyUint32(dst, clone, 1);
    JSValue alias = JS_GetPropertyUint32(dst, clone, 2);
    size_t len;
    assert(JS_GetArrayBuffer(dst, &len, a) == stores[0] && len == 23);
    assert(JS_GetArrayBuffer(dst, &len, b) == stores[1] && len == 7);
    assert(JS_VALUE_GET_PTR(a) == JS_VALUE_GET_PTR(alias));
    stores[0][22] = 91;
    assert(JS_GetArrayBuffer(dst, &len, alias)[22] == 91);
    JS_FreeValue(dst, a);
    JS_FreeValue(dst, b);
    JS_FreeValue(dst, alias);
    JS_FreeValue(dst, clone);
    assert(live == 0);
    JS_FreeContext(dst);
    JS_FreeRuntime(receiver);
    puts("quickjs SAB reader/lifetime ok");
    return 0;
}
