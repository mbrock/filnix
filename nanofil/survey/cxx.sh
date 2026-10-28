#!@bash@
# The survey's CXX: C++ is not nanofil's, so filcc compiles it, and each
# C++ compile is logged as "cxx" in $NANOFIL_LOG for the survey to count.
case " $* " in *" -c "*) echo "cxx $PWD: $*" >>"${NANOFIL_LOG:-/dev/null}" ;; esac
exec @filcc@/bin/clang++ "$@"
