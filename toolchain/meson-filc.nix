# Meson's mkenums_simple supplies its own template instead of using a package's
# .c.template file. Keep GType and its once-initialized storage pointer-valued.
{ pkgs }:
pkgs.meson.overrideAttrs (old: {
  postPatch = (if old.postPatch == null then "" else old.postPatch) + ''
    substituteInPlace mesonbuild/modules/gnome.py \
      --replace-fail 'static gsize gtype_id = 0;' 'static gpointer gtype_id = NULL;' \
      --replace-fail 'g_once_init_enter (&gtype_id)' 'g_once_init_enter_pointer (&gtype_id)' \
      --replace-fail 'g_once_init_leave (&gtype_id, new_type)' 'g_once_init_leave_pointer (&gtype_id, (gpointer) new_type)'
  '';
})
