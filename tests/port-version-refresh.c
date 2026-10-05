#define PCRE2_CODE_UNIT_WIDTH 8
#include <assert.h>
#include <crypt.h>
#include <event2/event.h>
#include <krb5.h>
#include <pcre2.h>
#include <stdio.h>
#include <string.h>
#include <uv.h>
#include <zlib.h>

static void event_callback(evutil_socket_t fd, short what, void *arg) {
    (void)fd;
    (void)what;
    ++*(int *)arg;
}

static void uv_callback(uv_timer_t *timer) {
    ++*(int *)timer->data;
    uv_close((uv_handle_t *)timer, NULL);
}

int main(void) {
    unsigned char input[4096], compressed[8192], restored[4096];
    for (size_t i = 0; i < sizeof input; ++i)
        input[i] = (unsigned char)(i * 17);
    uLongf compressed_size = sizeof compressed, restored_size = sizeof restored;
    assert(compress2(compressed, &compressed_size, input, sizeof input, 9) == Z_OK);
    assert(uncompress(restored, &restored_size, compressed, compressed_size) == Z_OK);
    assert(restored_size == sizeof input && !memcmp(input, restored, sizeof input));
    puts("zlib compression roundtrip passed");

    int events = 0;
    struct event_base *base = event_base_new();
    assert(base);
    struct event *event = evtimer_new(base, event_callback, &events);
    assert(event);
    struct timeval delay = { 0, 1000 };
    assert(evtimer_add(event, &delay) == 0);
    int event_result = event_base_dispatch(base);
    /* A completed one-shot timer leaves no pending events (return value 1). */
    assert((event_result == 0 || event_result == 1) && events == 1);
    event_free(event);
    event_base_free(base);
    puts("libevent timer passed");

    uv_loop_t loop;
    uv_timer_t timer;
    events = 0;
    assert(uv_loop_init(&loop) == 0);
    assert(uv_timer_init(&loop, &timer) == 0);
    timer.data = &events;
    assert(uv_timer_start(&timer, uv_callback, 1, 0) == 0);
    assert(uv_run(&loop, UV_RUN_DEFAULT) == 0 && events == 1);
    assert(uv_loop_close(&loop) == 0);
    puts("libuv timer passed");

    struct crypt_data crypt_state = { 0 };
    char *hash = crypt_r("password", "$6$salt$", &crypt_state);
    assert(hash && !strcmp(hash,
        "$6$salt$IxDD3jeSOb5eB1CX5LBsqZFVkJdido3OUILO5Ifz5iwM"
        "uTS4XMS130MTSuDDl3aCI6WouIL9AjRbLCelDCy.g."));
    puts("libxcrypt SHA-512 known-answer test passed");

    int error;
    PCRE2_SIZE offset;
    pcre2_code *code = pcre2_compile((PCRE2_SPTR)"^(?<word>\\p{L}+)([0-9]+)$",
                                   PCRE2_ZERO_TERMINATED, PCRE2_UTF, &error, &offset, NULL);
    assert(code);
    pcre2_match_data *match = pcre2_match_data_create_from_pattern(code, NULL);
    assert(match);
    assert(pcre2_match(code, (PCRE2_SPTR)"safe42", 6, 0, 0, match, NULL) == 3);
    PCRE2_SIZE *captures = pcre2_get_ovector_pointer(match);
    assert(captures[2] == 0 && captures[3] == 4);
    pcre2_match_data_free(match);
    pcre2_code_free(code);
    puts("PCRE2 Unicode properties and captures passed");

    krb5_context context;
    krb5_principal principal;
    char *name;
    assert(krb5_init_context(&context) == 0);
    assert(krb5_parse_name(context, "test@EXAMPLE.COM", &principal) == 0);
    assert(krb5_unparse_name(context, principal, &name) == 0);
    assert(!strcmp(name, "test@EXAMPLE.COM"));
    krb5_free_unparsed_name(context, name);
    krb5_free_principal(context, principal);
    krb5_free_context(context);
    puts("Kerberos principal roundtrip passed");
    return 0;
}
