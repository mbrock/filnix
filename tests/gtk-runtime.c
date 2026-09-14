#include <gtk/gtk.h>
#include <string.h>

static void clicked(GtkButton *button, gpointer data)
{
    g_assert_true(GTK_IS_BUTTON(button));
    ++*(int *)data;
}

int main(void)
{
#if GTK_MAJOR_VERSION >= 4
    if (!gtk_init_check())
        return 77;
#else
    if (!gtk_init_check(NULL, NULL))
        return 77;
#endif
    /* Builder type lookup, properties and signal marshaling exercise the
       pointer-valued GType ABI across GTK, GLib and this downstream program. */
    GtkBuilder *builder = gtk_builder_new_from_string(
        "<interface><object class='GtkBox' id='box'><child>"
        "<object class='GtkButton' id='button'>"
        "<property name='label'>Fil-C</property>"
        "</object></child></object></interface>", -1);
    GtkWidget *box = GTK_WIDGET(gtk_builder_get_object(builder, "box"));
    GtkWidget *button = GTK_WIDGET(gtk_builder_get_object(builder, "button"));
    g_assert_true(GTK_IS_BOX(box));
    g_assert_true(GTK_IS_BUTTON(button));
    g_assert_true(g_type_is_a(G_OBJECT_TYPE(button), GTK_TYPE_WIDGET));
    int count = 0;
    g_signal_connect(button, "clicked", G_CALLBACK(clicked), &count);
    g_signal_emit_by_name(button, "clicked");
    g_assert_cmpint(count, ==, 1);
    g_object_set(button, "label", "Memory-safe GTK", NULL);
    char *label = NULL;
    g_object_get(button, "label", &label, NULL);
    g_assert_cmpstr(label, ==, "Memory-safe GTK");
    g_free(label);

    /* Force text shaping and font lookup through Pango, HarfBuzz and Cairo. */
    PangoLayout *layout = gtk_widget_create_pango_layout(button, "Hello, Fil-C!");
    int width, height;
    pango_layout_get_pixel_size(layout, &width, &height);
    g_assert_cmpint(width, >, 0);
    g_assert_cmpint(height, >, 0);
    g_object_unref(layout);

    /* Encode/decode an image through the installed GdkPixbuf loaders. */
    GdkPixbuf *pixbuf = gdk_pixbuf_new(GDK_COLORSPACE_RGB, TRUE, 8, 2, 2);
    gdk_pixbuf_fill(pixbuf, 0x123456ff);
    char *png = NULL;
    gsize size = 0;
    GError *error = NULL;
    g_assert_true(gdk_pixbuf_save_to_buffer(pixbuf, &png, &size, "png", &error, NULL));
    g_assert_no_error(error);
    GInputStream *stream = g_memory_input_stream_new_from_data(png, size, g_free);
    GdkPixbuf *decoded = gdk_pixbuf_new_from_stream(stream, NULL, &error);
    g_assert_no_error(error);
    g_assert_nonnull(decoded);
    g_assert_cmpint(gdk_pixbuf_get_width(decoded), ==, 2);
    g_assert_cmpint(gdk_pixbuf_get_pixels(decoded)[0], ==, 0x12);
    g_object_unref(decoded);
    g_object_unref(stream);
    g_object_unref(pixbuf);

#if GTK_MAJOR_VERSION >= 4
    GtkWidget *window = gtk_window_new();
    gtk_window_set_child(GTK_WINDOW(window), box);
    gtk_window_present(GTK_WINDOW(window));
#else
    GtkWidget *window = gtk_window_new(GTK_WINDOW_TOPLEVEL);
    gtk_container_add(GTK_CONTAINER(window), box);
    gtk_widget_show_all(window);
#endif
    for (int i = 0; i < 100 && g_main_context_pending(NULL); ++i)
        g_main_context_iteration(NULL, FALSE);
#if GTK_MAJOR_VERSION >= 4
    gtk_window_destroy(GTK_WINDOW(window));
#else
    gtk_widget_destroy(window);
#endif
    g_object_unref(builder);
    g_print("GTK %d: builder, signals, text, image loaders and Broadway passed\n",
            GTK_MAJOR_VERSION);
    return 0;
}
