#include "types.h"
int main(void) {
  GType type = filnix_choice_get_type();
  g_assert_true(type == filnix_choice_get_type());
  GEnumClass *klass = g_type_class_ref(type);
  g_assert_cmpint(g_enum_get_value_by_nick(klass, "second")->value, ==, 11);
  g_type_class_unref(klass);
  return 0;
}
