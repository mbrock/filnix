# Fil-C is a cross target (host x86_64-unknown-linux-gnufilc0), so libtool's
# "whether a program can dlopen itself" run test reports "cross". Libtool
# then implements `-dlopen self` with a preloaded symbol table instead of
# --export-dynamic, and plugins that call back into the executable fail:
# slapd's pwmods/argon2.so could not resolve pizlonated_lutil_passwd_add.
# Fil-C programs run on the build machine and can dlopen themselves.
export lt_cv_dlopen_self="${lt_cv_dlopen_self-yes}"
