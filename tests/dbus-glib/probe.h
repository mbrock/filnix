#include <dbus/dbus-glib.h>

#define PROBE_NAME "org.filnix.Probe"
#define PROBE_PATH "/org/filnix/Probe"

#define PAIR_TYPE \
  dbus_g_type_get_struct ("GValueArray", G_TYPE_STRING, G_TYPE_UINT, G_TYPE_INVALID)
#define STRING_TABLE_TYPE \
  dbus_g_type_get_map ("GHashTable", G_TYPE_STRING, G_TYPE_STRING)
