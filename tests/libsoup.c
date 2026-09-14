#include <libsoup/soup.h>
#include <string.h>

static void changed(SoupCookieJar *jar, SoupCookie *old_cookie,
                    SoupCookie *new_cookie, gpointer data) {
    (void)jar;
    if (old_cookie) g_assert_cmpstr(soup_cookie_get_name(old_cookie), ==, "filnix");
    if (new_cookie) g_assert_cmpstr(soup_cookie_get_name(new_cookie), ==, "filnix");
    ++*(int *)data;
}

static void request(SoupSession *session, const char *url, gboolean cookies) {
    SoupMessage *message = soup_message_new("GET", url);
    if (!cookies) soup_message_disable_feature(message, SOUP_TYPE_COOKIE_JAR);
#if SOUP_MAJOR_VERSION >= 3
    GError *error = NULL;
    GBytes *body = soup_session_send_and_read(session, message, NULL, &error);
    g_assert_no_error(error);
    g_assert_cmpuint(soup_message_get_status(message), ==, 200);
    gsize length;
    const char *data = g_bytes_get_data(body, &length);
    g_assert_cmpuint(length, ==, 6);
    g_assert_true(memcmp(data, "filnix", length) == 0);
    g_bytes_unref(body);
#else
    g_assert_cmpuint(soup_session_send_message(session, message), ==, 200);
    g_assert_cmpuint(message->response_body->length, ==, 6);
    g_assert_true(memcmp(message->response_body->data, "filnix", 6) == 0);
#endif
    g_object_unref(message);
}

int main(int argc, char **argv) {
    g_assert_cmpint(argc, ==, 2);
    SoupSession *session = soup_session_new();
    SoupCookieJar *jar = soup_cookie_jar_new();
    int changes = 0;
    g_signal_connect(jar, "changed", G_CALLBACK(changed), &changes);
    soup_session_add_feature(session, SOUP_SESSION_FEATURE(jar));
    soup_cookie_jar_add_cookie(jar, soup_cookie_new("filnix", "first", "127.0.0.1", "/", 3600));
    soup_cookie_jar_add_cookie(jar, soup_cookie_new("filnix", "42", "127.0.0.1", "/", 3600));
    g_assert_cmpint(changes, ==, 2);
    request(session, argv[1], TRUE);
    char *plain = g_strconcat(argv[1], "plain", NULL);
    request(session, plain, FALSE);
    g_free(plain);
    soup_session_abort(session);
    g_object_unref(session);
    g_object_unref(jar);
}
