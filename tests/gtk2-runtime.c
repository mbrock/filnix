#include <gtk/gtk.h>
#include <gdk/gdkkeysyms.h>
#include <string.h>

static void count(gpointer data)
{
    ++*(int *)data;
}

static void clicked(GtkButton *button, gpointer data)
{
    g_assert_true(GTK_IS_BUTTON(button));
    count(data);
}

/* "insert-text" and "row-inserted" take GTypes flagged with
   G_SIGNAL_TYPE_STATIC_SCOPE, which GTK 2 used to OR into the type ID. */
static void insert_text(GtkTextBuffer *buffer, GtkTextIter *location,
                        gchar *text, gint len, gpointer data)
{
    g_assert_true(gtk_text_iter_get_buffer(location) == buffer);
    g_assert_cmpint(len, ==, (int)strlen(text));
    count(data);
}

static void row_inserted(GtkTreeModel *model, GtkTreePath *path,
                         GtkTreeIter *iter, gpointer data)
{
    g_assert_cmpint(gtk_tree_path_get_depth(path), ==, 1);
    count(data);
}

static gboolean mapped(GtkWidget *widget, GdkEvent *event, gpointer data)
{
    g_assert_cmpint(event->type, ==, GDK_MAP);
    count(data);
    return FALSE;
}

static gboolean quit(gpointer data)
{
    count(data);
    gtk_main_quit();
    return FALSE;
}

int main(void)
{
    if (!gtk_init_check(NULL, NULL))
        return 77;

    /* Builder type lookup, properties and signal marshaling exercise the
       pointer-valued GType ABI across GTK, GLib and this downstream program. */
    GtkBuilder *builder = gtk_builder_new();
    GError *error = NULL;
    gtk_builder_add_from_string(builder,
        "<interface><object class='GtkVBox' id='box'>"
        "<child><object class='GtkButton' id='button'>"
        "<property name='label'>Fil-C</property></object></child>"
        "<child><object class='GtkEntry' id='entry'>"
        "<property name='text'>memory safe</property></object></child>"
        "<child><object class='GtkHScale' id='scale'>"
        "<property name='adjustment'>adjustment</property></object></child>"
        "</object>"
        "<object class='GtkAdjustment' id='adjustment'>"
        "<property name='upper'>10</property></object>"
        "</interface>", -1, &error);
    g_assert_no_error(error);
    GtkWidget *box = GTK_WIDGET(gtk_builder_get_object(builder, "box"));
    GtkWidget *button = GTK_WIDGET(gtk_builder_get_object(builder, "button"));
    GtkWidget *entry = GTK_WIDGET(gtk_builder_get_object(builder, "entry"));
    GtkWidget *scale = GTK_WIDGET(gtk_builder_get_object(builder, "scale"));
    g_assert_true(GTK_IS_VBOX(box));
    g_assert_true(GTK_IS_BUTTON(button));
    g_assert_true(GTK_IS_ENTRY(entry));
    g_assert_true(g_type_is_a(G_OBJECT_TYPE(button), GTK_TYPE_WIDGET));
    g_assert_true(g_type_is_a(G_OBJECT_TYPE(button), GTK_TYPE_OBJECT));

    /* GTK_MODULES=gail loads the accessibility module, whose factories
       register their types with g_once_init. */
    AtkObject *accessible = gtk_widget_get_accessible(button);
    g_assert_cmpstr(G_OBJECT_TYPE_NAME(accessible), ==, "GailButton");
    g_assert_cmpint(atk_object_get_role(accessible), ==, ATK_ROLE_PUSH_BUTTON);

    int clicks = 0;
    g_signal_connect(button, "clicked", G_CALLBACK(clicked), &clicks);
    g_signal_emit_by_name(button, "clicked");
    gtk_button_clicked(GTK_BUTTON(button));
    g_assert_cmpint(clicks, ==, 2);
    g_object_set(button, "label", "Memory-safe GTK", NULL);
    char *label = NULL;
    g_object_get(button, "label", &label, NULL);
    g_assert_cmpstr(label, ==, "Memory-safe GTK");
    g_free(label);

    /* Scale marks are kept sorted with a GCompareDataFunc. */
    gtk_scale_add_mark(GTK_SCALE(scale), 7, GTK_POS_TOP, NULL);
    gtk_scale_add_mark(GTK_SCALE(scale), 3, GTK_POS_TOP, "three");

    /* Key bindings copy GtkArgs by fundamental type, then marshal them. */
    GtkBindingSet *bindings =
        gtk_binding_set_by_class(GTK_ENTRY_GET_CLASS(entry));
    gtk_binding_entry_add_signal(bindings, GDK_KEY_F5, 0, "move-cursor", 3,
                                 G_TYPE_ENUM, GTK_MOVEMENT_BUFFER_ENDS,
                                 G_TYPE_INT, -1, G_TYPE_BOOLEAN, FALSE);
    gtk_editable_set_position(GTK_EDITABLE(entry), -1);
    g_assert_true(gtk_bindings_activate(GTK_OBJECT(entry), GDK_KEY_F5, 0));
    g_assert_cmpint(gtk_editable_get_position(GTK_EDITABLE(entry)), ==, 0);

    /* RC-file bindings take the parser path through the same code. */
    gtk_rc_parse_string(
        "binding \"filc\" { bind \"F6\" { \"move-cursor\" "
        "(buffer-ends, 1, 0) } }\n"
        "class \"GtkEntry\" binding \"filc\"\n");
    gtk_widget_reset_rc_styles(entry);

    /* Tree data is stored and copied by fundamental GType. */
    GtkListStore *store = gtk_list_store_new(4, G_TYPE_STRING, G_TYPE_INT,
                                             G_TYPE_DOUBLE, G_TYPE_BOOLEAN);
    int rows = 0;
    g_signal_connect(store, "row-inserted", G_CALLBACK(row_inserted), &rows);
    GtkTreeIter iter;
    gtk_list_store_insert_with_values(store, &iter, -1, 0, "Fil-C", 1, 42,
                                      2, 1.5, 3, TRUE, -1);
    gtk_list_store_insert_with_values(store, &iter, -1, 0, "GTK", 1, 2,
                                      2, 2.5, 3, FALSE, -1);
    g_assert_cmpint(rows, ==, 2);
    gtk_tree_sortable_set_sort_column_id(GTK_TREE_SORTABLE(store), 1,
                                         GTK_SORT_ASCENDING);
    g_assert_true(gtk_tree_model_get_iter_first(GTK_TREE_MODEL(store), &iter));
    char *name;
    int number;
    double real;
    gtk_tree_model_get(GTK_TREE_MODEL(store), &iter, 0, &name, 1, &number,
                       2, &real, -1);
    g_assert_cmpstr(name, ==, "GTK");
    g_assert_cmpint(number, ==, 2);
    g_assert_cmpfloat(real, ==, 2.5);
    g_free(name);
    GtkWidget *view = gtk_tree_view_new_with_model(GTK_TREE_MODEL(store));
    gtk_tree_view_insert_column_with_attributes(
        GTK_TREE_VIEW(view), -1, "Name", gtk_cell_renderer_text_new(),
        "text", 0, NULL);
    gtk_box_pack_start(GTK_BOX(box), view, TRUE, TRUE, 0);
    g_object_unref(store);

    /* Combo box text checks its model's column GType. */
    GtkWidget *combo = gtk_combo_box_text_new_with_entry();
    gtk_combo_box_text_append_text(GTK_COMBO_BOX_TEXT(combo), "one");
    gtk_combo_box_text_prepend_text(GTK_COMBO_BOX_TEXT(combo), "zero");
    gtk_combo_box_set_active(GTK_COMBO_BOX(combo), 1);
    char *active = gtk_combo_box_text_get_active_text(GTK_COMBO_BOX_TEXT(combo));
    g_assert_cmpstr(active, ==, "one");
    g_free(active);
    gtk_box_pack_start(GTK_BOX(box), combo, FALSE, FALSE, 0);

    GtkTextBuffer *text = gtk_text_buffer_new(NULL);
    int inserts = 0;
    g_signal_connect(text, "insert-text", G_CALLBACK(insert_text), &inserts);
    gtk_text_buffer_set_text(text, "Hello, ", -1);
    GtkTextIter end;
    gtk_text_buffer_get_end_iter(text, &end);
    gtk_text_buffer_insert(text, &end, "Fil-C!", -1);
    g_assert_cmpint(inserts, ==, 2);
    GtkWidget *textview = gtk_text_view_new_with_buffer(text);
    gtk_box_pack_start(GTK_BOX(box), textview, TRUE, TRUE, 0);
    g_object_unref(text);

    /* GtkSettings converts values by fundamental GType. */
    gint double_click = 0;
    g_object_get(gtk_settings_get_default(), "gtk-double-click-time",
                 &double_click, NULL);
    g_assert_cmpint(double_click, >, 0);

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
    g_assert_true(gdk_pixbuf_save_to_buffer(pixbuf, &png, &size, "png", &error, NULL));
    g_assert_no_error(error);
    GInputStream *stream = g_memory_input_stream_new_from_data(png, size, g_free);
    GdkPixbuf *decoded = gdk_pixbuf_new_from_stream(stream, NULL, &error);
    g_assert_no_error(error);
    g_assert_nonnull(decoded);
    g_assert_cmpint(gdk_pixbuf_get_width(decoded), ==, 2);
    g_assert_cmpint(gdk_pixbuf_get_pixels(decoded)[0], ==, 0x12);
    g_object_unref(stream);
    g_object_unref(pixbuf);

    /* A theme engine is a GTypeModule that registers its style types when
       the RC parser loads it (GTK_PATH points at Murrine here); the main
       loop below then draws every widget through it. */
    gtk_rc_parse_string("style \"filc\" { engine \"murrine\" { } }\n"
                        "widget_class \"*\" style \"filc\"\n");

    /* Show everything on the X server, draw, and run the real main loop. */
    GtkWidget *window = gtk_window_new(GTK_WINDOW_TOPLEVEL);
    gtk_window_set_default_size(GTK_WINDOW(window), 320, 240);
    gtk_box_pack_start(GTK_BOX(box), gtk_image_new_from_pixbuf(decoded),
                       FALSE, FALSE, 0);
    g_object_unref(decoded);
    gtk_container_add(GTK_CONTAINER(window), box);
    int maps = 0, quits = 0;
    g_signal_connect(window, "map-event", G_CALLBACK(mapped), &maps);
    gtk_widget_show_all(window);
    GtkRequisition requisition;
    gtk_widget_size_request(window, &requisition);
    g_assert_cmpint(requisition.width, >, 0);
    g_assert_cmpstr(G_OBJECT_TYPE_NAME(gtk_widget_get_style(button)), ==,
                    "MurrineStyle");
    g_timeout_add(200, quit, &quits);
    gtk_main();
    g_assert_cmpint(quits, ==, 1);
    g_assert_cmpint(maps, ==, 1);
    g_assert_true(gtk_widget_get_mapped(textview));
    gdk_window_process_all_updates();

    gtk_widget_grab_focus(entry);
    g_assert_true(gtk_bindings_activate(GTK_OBJECT(entry), GDK_KEY_F6, 0));
    g_assert_cmpint(gtk_editable_get_position(GTK_EDITABLE(entry)), ==,
                    (int)strlen("memory safe"));

    gtk_widget_destroy(window);
    g_object_unref(builder);
    g_print("GTK 2: builder, signals, bindings, tree/text models, "
            "settings, GAIL, Murrine, text, image loaders and X11 main loop passed\n");
    return 0;
}
