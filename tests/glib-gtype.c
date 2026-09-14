#include <glib-object.h>

typedef struct _FilnixFace FilnixFace;
typedef struct { GTypeInterface parent; } FilnixFaceInterface;
G_DEFINE_INTERFACE(FilnixFace, filnix_face, G_TYPE_OBJECT)
static void filnix_face_default_init(FilnixFaceInterface *iface) { (void)iface; }

typedef struct { GObject parent; int value; } FilnixProbe;
typedef struct { GObjectClass parent; } FilnixProbeClass;
G_DEFINE_TYPE_WITH_CODE(FilnixProbe, filnix_probe, G_TYPE_OBJECT,
                       G_IMPLEMENT_INTERFACE(filnix_face_get_type(), NULL))
static void filnix_probe_class_init(FilnixProbeClass *klass) { (void)klass; }
static void filnix_probe_init(FilnixProbe *self) { self->value = 42; }

typedef struct { int *value; } FilnixBox;
static FilnixBox *filnix_box_copy(FilnixBox *box) {
    FilnixBox *copy = g_new(FilnixBox, 1);
    copy->value = g_new(int, 1);
    *copy->value = *box->value;
    return copy;
}
static void filnix_box_free(FilnixBox *box) { g_free(box->value); g_free(box); }
G_DEFINE_BOXED_TYPE(FilnixBox, filnix_box, filnix_box_copy, filnix_box_free)

#if GLIB_VERSION_MAX_ALLOWED >= GLIB_VERSION_2_74
G_DEFINE_ENUM_TYPE(FilnixEnum, filnix_enum,
                  G_DEFINE_ENUM_VALUE(7, "seven"))
G_DEFINE_FLAGS_TYPE(FilnixFlags, filnix_flags,
                   G_DEFINE_ENUM_VALUE(1, "first"))
#endif

static gpointer exercise(gpointer unused) {
    (void)unused;
    for (int i = 0; i < 50; ++i) {
        FilnixProbe *p = (FilnixProbe *)g_object_new(filnix_probe_get_type(), NULL);
        g_assert_cmpint(p->value, ==, 42);
        g_assert_true(G_TYPE_CHECK_INSTANCE_TYPE(p, filnix_probe_get_type()));
        g_assert_true(g_type_is_a(filnix_probe_get_type(), filnix_face_get_type()));
        g_object_unref(p);
        int value = 123;
        FilnixBox box = { &value };
        GValue boxed = G_VALUE_INIT;
        g_value_init(&boxed, filnix_box_get_type());
        g_value_set_boxed(&boxed, &box);
        FilnixBox *copy = (FilnixBox *)g_value_get_boxed(&boxed);
        g_assert_true(copy->value != box.value);
        g_assert_cmpint(*copy->value, ==, 123);
        g_value_unset(&boxed);
#if GLIB_VERSION_MAX_ALLOWED >= GLIB_VERSION_2_74
        GEnumClass *en = (GEnumClass *)g_type_class_ref(filnix_enum_get_type());
        g_assert_cmpint(g_enum_get_value_by_nick(en, "seven")->value, ==, 7);
        g_type_class_unref(en);
        GFlagsClass *flags = (GFlagsClass *)g_type_class_ref(filnix_flags_get_type());
        g_assert_cmpuint(g_flags_get_value_by_nick(flags, "first")->value, ==, 1);
        g_type_class_unref(flags);
#endif
    }
    return NULL;
}
int main(void) {
    GThread *threads[4];
    for (int i = 0; i < 4; ++i) threads[i] = g_thread_new("type-check", exercise, NULL);
    for (int i = 0; i < 4; ++i) g_thread_join(threads[i]);
    return 0;
}
