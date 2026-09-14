project('filc-meson-enums', 'c', default_options: ['werror=true'])
add_project_arguments('-DGLIB_VERSION_MIN_REQUIRED=GLIB_VERSION_2_38',
                      '-DGLIB_VERSION_MAX_ALLOWED=GLIB_VERSION_2_38', language: 'c')
gobject = dependency('gobject-2.0')
enums = import('gnome').mkenums_simple('types', sources: 'values.h')
executable('gtype-enums-check', ['check.c', enums], dependencies: gobject, install: true)
