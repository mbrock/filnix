/* A dbus-glib service using dbus-binding-tool's server glue. */
#include <stdlib.h>
#include <string.h>
#include "probe.h"

typedef struct { GObject parent; } Probe;
typedef struct { GObjectClass parent; } ProbeClass;

static GType probe_get_type (void);
G_DEFINE_TYPE (Probe, probe, G_TYPE_OBJECT)

static guint announced_signal;

static gboolean
probe_scalars (Probe *self, gint i, guint u, gint64 x, gdouble d,
               gboolean b, guchar y, char **summary, GError **error)
{
  *summary = g_strdup_printf ("%d %u %" G_GINT64_FORMAT " %.2f %s %u",
                              i, u, x, d, b ? "true" : "false", y);
  return TRUE;
}

static void
append_prop (gpointer key, gpointer value, gpointer user_data)
{
  GPtrArray *entries = user_data;
  GValue *v = value;
  g_ptr_array_add (entries,
                   g_strdup_printf ("%s=%s:%s", (char *) key,
                                    G_VALUE_TYPE_NAME (v),
                                    G_VALUE_HOLDS_STRING (v)
                                        ? g_value_get_string (v)
                                        : G_VALUE_HOLDS_INT (v)
                                        ? g_strdup_printf ("%d", g_value_get_int (v))
                                        : G_VALUE_HOLDS_BOOLEAN (v)
                                        ? (g_value_get_boolean (v) ? "true" : "false")
                                        : "?"));
}

static gint
compare_strings (gconstpointer a, gconstpointer b)
{
  return strcmp (*(char *const *) a, *(char *const *) b);
}

static gboolean
probe_collections (Probe *self, char **words, GArray *numbers,
                   GHashTable *props, char **summary, GValueArray **pair,
                   GHashTable **table, GError **error)
{
  GString *out = g_string_new (NULL);
  GPtrArray *entries = g_ptr_array_new ();
  gint total = 0;
  guint n;
  GValue v = G_VALUE_INIT;

  for (n = 0; n < numbers->len; n++)
    total += g_array_index (numbers, gint, n);
  g_hash_table_foreach (props, append_prop, entries);
  g_ptr_array_sort (entries, compare_strings);
  g_ptr_array_add (entries, NULL);

  g_string_append_printf (out, "words=%s sum=%d props=%s",
                          g_strjoinv (",", words), total,
                          g_strjoinv (",", (char **) entries->pdata));
  *summary = g_string_free (out, FALSE);

  *pair = g_value_array_new (2);
  g_value_init (&v, G_TYPE_STRING);
  g_value_set_string (&v, words[0]);
  g_value_array_append (*pair, &v);
  g_value_unset (&v);
  g_value_init (&v, G_TYPE_UINT);
  g_value_set_uint (&v, g_strv_length (words));
  g_value_array_append (*pair, &v);
  g_value_unset (&v);

  *table = g_hash_table_new_full (g_str_hash, g_str_equal, g_free, g_free);
  g_hash_table_insert (*table, g_strdup ("first"), g_strdup (words[0]));
  g_hash_table_insert (*table, g_strdup ("count"),
                       g_strdup_printf ("%u", g_strv_length (words)));
  return TRUE;
}

static gboolean
probe_announce (Probe *self, const char *text, GError **error)
{
  g_signal_emit (self, announced_signal, 0, text, (guint) strlen (text));
  return TRUE;
}

#include "probe-server.h"

static void
probe_init (Probe *self)
{
}

static void
probe_class_init (ProbeClass *klass)
{
  announced_signal =
    g_signal_new ("announced", G_TYPE_FROM_CLASS (klass), G_SIGNAL_RUN_LAST,
                  0, NULL, NULL, NULL, G_TYPE_NONE, 2, G_TYPE_STRING,
                  G_TYPE_UINT);
  dbus_g_object_type_install_info (G_TYPE_FROM_CLASS (klass),
                                   &dbus_glib_probe_object_info);
}

int
main (void)
{
  GError *error = NULL;
  DBusGConnection *bus;
  DBusGProxy *driver;
  guint result;
  GMainLoop *loop = g_main_loop_new (NULL, FALSE);

  bus = dbus_g_bus_get (DBUS_BUS_SESSION, &error);
  if (!bus)
    g_error ("bus: %s", error->message);
  dbus_g_connection_register_g_object (bus, PROBE_PATH,
                                       g_object_new (probe_get_type (), NULL));
  driver = dbus_g_proxy_new_for_name (bus, DBUS_SERVICE_DBUS, DBUS_PATH_DBUS,
                                      DBUS_INTERFACE_DBUS);
  if (!dbus_g_proxy_call (driver, "RequestName", &error,
                          G_TYPE_STRING, PROBE_NAME, G_TYPE_UINT, 0,
                          G_TYPE_INVALID, G_TYPE_UINT, &result,
                          G_TYPE_INVALID))
    g_error ("RequestName: %s", error->message);
  g_main_loop_run (loop);
  return 0;
}
