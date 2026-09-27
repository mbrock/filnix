/* Calls the probe service through dbus-binding-tool's client glue. */
#include <stdio.h>
#include <string.h>
#include "probe.h"
#include "probe-client.h"

static GMainLoop *loop;

static void
on_announced (DBusGProxy *proxy, const char *text, guint length,
              gpointer user_data)
{
  printf ("signal %s %u\n", text, length);
  g_main_loop_quit (loop);
}

static void
check (gboolean ok, GError *error, const char *what)
{
  if (!ok)
    g_error ("%s: %s", what, error ? error->message : "failed");
}

int
main (void)
{
  GError *error = NULL;
  DBusGConnection *bus;
  DBusGProxy *proxy;
  char *summary = NULL;
  const char *words[] = { "alpha", "beta", "gamma", NULL };
  gint ints[] = { 1, 2, 39 };
  GArray *numbers = g_array_new (FALSE, FALSE, sizeof (gint));
  GHashTable *props = g_hash_table_new (g_str_hash, g_str_equal);
  GValue name = G_VALUE_INIT, count = G_VALUE_INIT, flag = G_VALUE_INIT;
  GValueArray *pair = NULL;
  GHashTable *table = NULL;

  loop = g_main_loop_new (NULL, FALSE);
  bus = dbus_g_bus_get (DBUS_BUS_SESSION, &error);
  check (bus != NULL, error, "bus");
  proxy = dbus_g_proxy_new_for_name (bus, PROBE_NAME, PROBE_PATH, PROBE_NAME);

  check (org_filnix_Probe_scalars (proxy, -7, 4000000000u, -G_GINT64_CONSTANT (1099511627776),
                                   2.5, TRUE, 200, &summary, &error),
         error, "Scalars");
  printf ("scalars %s\n", summary);

  g_array_append_vals (numbers, ints, G_N_ELEMENTS (ints));
  g_value_init (&name, G_TYPE_STRING);
  g_value_set_string (&name, "filnix");
  g_value_init (&count, G_TYPE_INT);
  g_value_set_int (&count, 42);
  g_value_init (&flag, G_TYPE_BOOLEAN);
  g_value_set_boolean (&flag, TRUE);
  g_hash_table_insert (props, "name", &name);
  g_hash_table_insert (props, "count", &count);
  g_hash_table_insert (props, "flag", &flag);
  check (org_filnix_Probe_collections (proxy, words, numbers, props, &summary,
                                       &pair, &table, &error),
         error, "Collections");
  printf ("collections %s\n", summary);
  printf ("pair %s %u\n", g_value_get_string (g_value_array_get_nth (pair, 0)),
          g_value_get_uint (g_value_array_get_nth (pair, 1)));
  printf ("table first=%s count=%s\n",
          (char *) g_hash_table_lookup (table, "first"),
          (char *) g_hash_table_lookup (table, "count"));

  dbus_g_proxy_add_signal (proxy, "Announced", G_TYPE_STRING, G_TYPE_UINT,
                           G_TYPE_INVALID);
  dbus_g_proxy_connect_signal (proxy, "Announced", G_CALLBACK (on_announced),
                               NULL, NULL);
  check (org_filnix_Probe_announce (proxy, "memory safety", &error), error,
         "Announce");
  g_main_loop_run (loop);
  return 0;
}
