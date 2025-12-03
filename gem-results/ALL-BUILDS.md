# Ruby Gem Build Results (Fil-C)

**16 succeeded**, **34 failed**

---

<details>
<summary>❌ <strong>charlock_holmes</strong>: ../../lib/libicuuc.so: error: undefined reference to 'pizlonated_icudt76_dat'</summary>

```
clang++ -O2 -W -Wall -pedantic -Wpointer-arith -Wwrite-strings -Wno-long-long -std=c++17  -Qunused-arguments -Wno-parentheses-equality   -o ../../bin/gendict gendict.o -L../../lib -licutu -L../../lib -licui18n -L../../lib -licuuc -L../../stubdata -licudata -lpthread -lm  
make[2]: Leaving directory '/build/icu/source/tools/gendict'
make[1]: Making `all' in `icuexportdata'
make[2]: Entering directory '/build/icu/source/tools/icuexportdata'
   (deps)        icuexportdata.cpp
cd ../.. \
 && CONFIG_FILES=tools/icuexportdata/icuexportdata.1 CONFIG_HEADERS= /nix/store/cfqbabpc7xwg8akbcchqbq3cai6qq2vs-bash-5.2p37/bin/bash ./config.status
   clang++       ...  icuexportdata.cpp
config.status: creating tools/icuexportdata/icuexportdata.1
clang++ -O2 -W -Wall -pedantic -Wpointer-arith -Wwrite-strings -Wno-long-long -std=c++17  -Qunused-arguments -Wno-parentheses-equality   -o ../../bin/icuexportdata icuexportdata.o -L../../lib -licutu -L../../lib -licui18n -L../../lib -licuuc -L../../stubdata -licudata -lpthread -lm  
make[2]: Leaving directory '/build/icu/source/tools/icuexportdata'
make[1]: Making `all' in `escapesrc'
make[2]: Entering directory '/build/icu/source/tools/escapesrc'
   (deps)        escapesrc.cpp
   clang++       ...  escapesrc.cpp
clang++ -O2 -W -Wall -pedantic -Wpointer-arith -Wwrite-strings -Wno-long-long -std=c++17  -Qunused-arguments -Wno-parentheses-equality   -o ../../bin/escapesrc escapesrc.o -lpthread -lm  
make[2]: Leaving directory '/build/icu/source/tools/escapesrc'
make[2]: Entering directory '/build/icu/source/tools'
make[2]: Nothing to be done for 'all-local'.
make[2]: Leaving directory '/build/icu/source/tools'
make[1]: Leaving directory '/build/icu/source/tools'
make[0]: Making `all' in `data'
make[1]: Entering directory '/build/icu/source/data'
make -f pkgdataMakefile
/nix/store/cfqbabpc7xwg8akbcchqbq3cai6qq2vs-bash-5.2p37/bin/bash ../mkinstalldirs ./out/tmp ./out/build/icudt76l
make[2]: Entering directory '/build/icu/source/data'
rm -rf icupkg.inc
mkdir ./out
mkdir ./out/tmp
mkdir ./out/build
mkdir ./out/build/icudt76l
Unpacking ./in/icudt76l.dat and generating out/tmp/icudata.lst (list of data files)
LD_LIBRARY_PATH=/nix/store/picm2hyv7mxa0s0q6v2vm8fxy1dcgfwv-icu4c-build-root-76.1/lib:/nix/store/picm2hyv7mxa0s0q6v2vm8fxy1dcgfwv-icu4c-build-root-76.1/stubdata:/nix/store/picm2hyv7mxa0s0q6v2vm8fxy1dcgfwv-icu4c-build-root-76.1/tools/ctestfw:$LD_LIBRARY_PATH /nix/store/picm2hyv7mxa0s0q6v2vm8fxy1dcgfwv-icu4c-build-root-76.1/bin/icupkg -d ./out/build/icudt76l --list -x \* ./in/icudt76l.dat -o out/tmp/icudata.lst
make[2]: Leaving directory '/build/icu/source/data'
echo timestamp > build-local
LD_LIBRARY_PATH=/nix/store/picm2hyv7mxa0s0q6v2vm8fxy1dcgfwv-icu4c-build-root-76.1/stubdata:/nix/store/picm2hyv7mxa0s0q6v2vm8fxy1dcgfwv-icu4c-build-root-76.1/tools/ctestfw:/nix/store/picm2hyv7mxa0s0q6v2vm8fxy1dcgfwv-icu4c-build-root-76.1/lib:$LD_LIBRARY_PATH  /nix/store/picm2hyv7mxa0s0q6v2vm8fxy1dcgfwv-icu4c-build-root-76.1/bin/pkgdata -O ../data/icupkg.inc -q -c -s /build/icu/source/data/out/build/icudt76l -d ../lib -e icudt76  -T ./out/tmp -p icudt76l -m dll -r 76.1 -L icudata ./out/tmp/icudata.lst
pkgdata: clang -D_REENTRANT  -DU_HAVE_ELF_H=1 -DU_HAVE_STRTOD_L=1 -DU_HAVE_XLOCALE_H=0  -DU_ALL_IMPLEMENTATION -DU_ATTRIBUTE_DEPRECATED= -O2 -std=c11 -Wall -pedantic -Wshadow -Wpointer-arith -Wmissing-prototypes -Wwrite-strings  -Qunused-arguments -Wno-parentheses-equality -c -I../common -I../common -DPIC -fPIC -o ./out/tmp/icudt76l_dat.o ./out/tmp/icudt76l_dat.S
pkgdata: clang -O2 -std=c11 -Wall -pedantic -Wshadow -Wpointer-arith -Wmissing-prototypes -Wwrite-strings  -Qunused-arguments -Wno-parentheses-equality  -shared -Wl,-Bsymbolic -nodefaultlibs -nostdlib -o ../lib/libicudata.so.76.1 ./out/tmp/icudt76l_dat.o -Wl,-soname -Wl,libicudata.so.76  -Wl,-Bsymbolic
pkgdata: cd ../lib/ && rm -f libicudata.so.76 && ln -s libicudata.so.76.1 libicudata.so.76
pkgdata: cd ../lib/ && rm -f libicudata.so && ln -s libicudata.so.76.1 libicudata.so
echo timestamp > packagedata
make[1]: Leaving directory '/build/icu/source/data'
make[0]: Making `all' in `extra'
make[1]: Entering directory '/build/icu/source/extra'
make[1]: Making `all' in `scrptrun'
make[2]: Entering directory '/build/icu/source/extra/scrptrun'
   (deps)        scrptrun.cpp
   (deps)        srtest.cpp
   clang++       ...  scrptrun.cpp
   clang++       ...  srtest.cpp
clang++ -O2 -W -Wall -pedantic -Wpointer-arith -Wwrite-strings -Wno-long-long -std=c++17  -Qunused-arguments -Wno-parentheses-equality   -o srtest scrptrun.o srtest.o -L../../lib -licuuc -L../../stubdata -licudata 
make[2]: Leaving directory '/build/icu/source/extra/scrptrun'
make[1]: Making `all' in `uconv'
make[2]: Entering directory '/build/icu/source/extra/uconv'
make -f pkgdataMakefile
   clang++       ...  uconv.cpp
   clang         ...  uwmsg.c
mkdir uconvmsg
make[3]: Entering directory '/build/icu/source/extra/uconv'
rm -rf pkgdata.inc
LD_LIBRARY_PATH=/nix/store/picm2hyv7mxa0s0q6v2vm8fxy1dcgfwv-icu4c-build-root-76.1/lib:/nix/store/picm2hyv7mxa0s0q6v2vm8fxy1dcgfwv-icu4c-build-root-76.1/stubdata:/nix/store/picm2hyv7mxa0s0q6v2vm8fxy1dcgfwv-icu4c-build-root-76.1/tools/ctestfw:$LD_LIBRARY_PATH /nix/store/picm2hyv7mxa0s0q6v2vm8fxy1dcgfwv-icu4c-build-root-76.1/bin/genrb -e UTF-8 -s resources -d uconvmsg root.txt
LD_LIBRARY_PATH=/nix/store/picm2hyv7mxa0s0q6v2vm8fxy1dcgfwv-icu4c-build-root-76.1/lib:/nix/store/picm2hyv7mxa0s0q6v2vm8fxy1dcgfwv-icu4c-build-root-76.1/stubdata:/nix/store/picm2hyv7mxa0s0q6v2vm8fxy1dcgfwv-icu4c-build-root-76.1/tools/ctestfw:$LD_LIBRARY_PATH /nix/store/picm2hyv7mxa0s0q6v2vm8fxy1dcgfwv-icu4c-build-root-76.1/bin/genrb -e UTF-8 -s resources -d uconvmsg fr.txt
make[3]: Leaving directory '/build/icu/source/extra/uconv'
LD_LIBRARY_PATH=/nix/store/picm2hyv7mxa0s0q6v2vm8fxy1dcgfwv-icu4c-build-root-76.1/lib:/nix/store/picm2hyv7mxa0s0q6v2vm8fxy1dcgfwv-icu4c-build-root-76.1/stubdata:/nix/store/picm2hyv7mxa0s0q6v2vm8fxy1dcgfwv-icu4c-build-root-76.1/tools/ctestfw:$LD_LIBRARY_PATH  /nix/store/picm2hyv7mxa0s0q6v2vm8fxy1dcgfwv-icu4c-build-root-76.1/bin/pkgdata -p uconvmsg -O pkgdata.inc -m static -s uconvmsg -d uconvmsg -T uconvmsg uconvmsg/uconvmsg.lst
cd ../.. \
 && CONFIG_FILES=extra/uconv/uconv.1 CONFIG_HEADERS= /nix/store/cfqbabpc7xwg8akbcchqbq3cai6qq2vs-bash-5.2p37/bin/bash ./config.status
pkgdata: clang -D_REENTRANT  -DU_HAVE_ELF_H=1 -DU_HAVE_STRTOD_L=1 -DU_HAVE_XLOCALE_H=0  -DU_ALL_IMPLEMENTATION -DU_ATTRIBUTE_DEPRECATED= -O2 -std=c11 -Wall -pedantic -Wshadow -Wpointer-arith -Wmissing-prototypes -Wwrite-strings  -Qunused-arguments -Wno-parentheses-equality -c -I../../common -I../../common -DPIC -fPIC -o uconvmsg/uconvmsg_dat.o uconvmsg/uconvmsg_dat.S
config.status: creating extra/uconv/uconv.1
pkgdata: ar r uconvmsg/libuconvmsg.a uconvmsg/uconvmsg_dat.o
ar: creating uconvmsg/libuconvmsg.a
pkgdata: ranlib uconvmsg/libuconvmsg.a
clang++ -O2 -W -Wall -pedantic -Wpointer-arith -Wwrite-strings -Wno-long-long -std=c++17  -Qunused-arguments -Wno-parentheses-equality   -o ../../bin/uconv uconv.o uwmsg.o -L../../lib -licui18n -L../../lib -licuuc -L../../stubdata -licudata -lpthread -lm   uconvmsg/libuconvmsg.a
../../lib/libicuuc.so: error: undefined reference to 'pizlonated_icudt76_dat'
uconv.o:uconv.cpp:function pizlonatedFI__ZL7initMsgPKc:(.text+0xc0c4): error: undefined reference to 'pizlonated_uconvmsg_dat'
clang-20: error: linker command failed with exit code 1 (use -v to see invocation)
make[2]: *** [Makefile:148: ../../bin/uconv] Error 1
make[2]: Leaving directory '/build/icu/source/extra/uconv'
make[1]: *** [Makefile:49: all-recursive] Error 2
make[1]: Leaving directory '/build/icu/source/extra'
make: *** [Makefile:153: all-recursive] Error 2
```

</details>

<details>
<summary>❌ <strong>cld3</strong>: build failed</summary>

```
shrinking /nix/store/fbpmvkkbxif1d2y48f1y7746n6ky10rc-abseil-cpp-x86_64-unknown-linux-gnufilc0-20250127.1/lib/libabsl_symbolize.so.2501.0.0
shrinking /nix/store/fbpmvkkbxif1d2y48f1y7746n6ky10rc-abseil-cpp-x86_64-unknown-linux-gnufilc0-20250127.1/lib/libabsl_examine_stack.so.2501.0.0
shrinking /nix/store/fbpmvkkbxif1d2y48f1y7746n6ky10rc-abseil-cpp-x86_64-unknown-linux-gnufilc0-20250127.1/lib/libabsl_failure_signal_handler.so.2501.0.0
shrinking /nix/store/fbpmvkkbxif1d2y48f1y7746n6ky10rc-abseil-cpp-x86_64-unknown-linux-gnufilc0-20250127.1/lib/libabsl_debugging_internal.so.2501.0.0
shrinking /nix/store/fbpmvkkbxif1d2y48f1y7746n6ky10rc-abseil-cpp-x86_64-unknown-linux-gnufilc0-20250127.1/lib/libabsl_demangle_internal.so.2501.0.0
shrinking /nix/store/fbpmvkkbxif1d2y48f1y7746n6ky10rc-abseil-cpp-x86_64-unknown-linux-gnufilc0-20250127.1/lib/libabsl_decode_rust_punycode.so.2501.0.0
shrinking /nix/store/fbpmvkkbxif1d2y48f1y7746n6ky10rc-abseil-cpp-x86_64-unknown-linux-gnufilc0-20250127.1/lib/libabsl_demangle_rust.so.2501.0.0
shrinking /nix/store/fbpmvkkbxif1d2y48f1y7746n6ky10rc-abseil-cpp-x86_64-unknown-linux-gnufilc0-20250127.1/lib/libabsl_utf8_for_code_point.so.2501.0.0
shrinking /nix/store/fbpmvkkbxif1d2y48f1y7746n6ky10rc-abseil-cpp-x86_64-unknown-linux-gnufilc0-20250127.1/lib/libabsl_leak_check.so.2501.0.0
shrinking /nix/store/fbpmvkkbxif1d2y48f1y7746n6ky10rc-abseil-cpp-x86_64-unknown-linux-gnufilc0-20250127.1/lib/libabsl_flags_program_name.so.2501.0.0
shrinking /nix/store/fbpmvkkbxif1d2y48f1y7746n6ky10rc-abseil-cpp-x86_64-unknown-linux-gnufilc0-20250127.1/lib/libabsl_flags_config.so.2501.0.0
shrinking /nix/store/fbpmvkkbxif1d2y48f1y7746n6ky10rc-abseil-cpp-x86_64-unknown-linux-gnufilc0-20250127.1/lib/libabsl_flags_marshalling.so.2501.0.0
shrinking /nix/store/fbpmvkkbxif1d2y48f1y7746n6ky10rc-abseil-cpp-x86_64-unknown-linux-gnufilc0-20250127.1/lib/libabsl_flags_commandlineflag_internal.so.2501.0.0
shrinking /nix/store/fbpmvkkbxif1d2y48f1y7746n6ky10rc-abseil-cpp-x86_64-unknown-linux-gnufilc0-20250127.1/lib/libabsl_flags_commandlineflag.so.2501.0.0
shrinking /nix/store/fbpmvkkbxif1d2y48f1y7746n6ky10rc-abseil-cpp-x86_64-unknown-linux-gnufilc0-20250127.1/lib/libabsl_flags_private_handle_accessor.so.2501.0.0
shrinking /nix/store/fbpmvkkbxif1d2y48f1y7746n6ky10rc-abseil-cpp-x86_64-unknown-linux-gnufilc0-20250127.1/lib/libabsl_flags_reflection.so.2501.0.0
shrinking /nix/store/fbpmvkkbxif1d2y48f1y7746n6ky10rc-abseil-cpp-x86_64-unknown-linux-gnufilc0-20250127.1/lib/libabsl_flags_internal.so.2501.0.0
shrinking /nix/store/fbpmvkkbxif1d2y48f1y7746n6ky10rc-abseil-cpp-x86_64-unknown-linux-gnufilc0-20250127.1/lib/libabsl_flags_usage_internal.so.2501.0.0
shrinking /nix/store/fbpmvkkbxif1d2y48f1y7746n6ky10rc-abseil-cpp-x86_64-unknown-linux-gnufilc0-20250127.1/lib/libabsl_flags_usage.so.2501.0.0
shrinking /nix/store/fbpmvkkbxif1d2y48f1y7746n6ky10rc-abseil-cpp-x86_64-unknown-linux-gnufilc0-20250127.1/lib/libabsl_flags_parse.so.2501.0.0
shrinking /nix/store/fbpmvkkbxif1d2y48f1y7746n6ky10rc-abseil-cpp-x86_64-unknown-linux-gnufilc0-20250127.1/lib/libabsl_hash.so.2501.0.0
shrinking /nix/store/fbpmvkkbxif1d2y48f1y7746n6ky10rc-abseil-cpp-x86_64-unknown-linux-gnufilc0-20250127.1/lib/libabsl_city.so.2501.0.0
shrinking /nix/store/fbpmvkkbxif1d2y48f1y7746n6ky10rc-abseil-cpp-x86_64-unknown-linux-gnufilc0-20250127.1/lib/libabsl_low_level_hash.so.2501.0.0
shrinking /nix/store/fbpmvkkbxif1d2y48f1y7746n6ky10rc-abseil-cpp-x86_64-unknown-linux-gnufilc0-20250127.1/lib/libabsl_log_internal_check_op.so.2501.0.0
shrinking /nix/store/fbpmvkkbxif1d2y48f1y7746n6ky10rc-abseil-cpp-x86_64-unknown-linux-gnufilc0-20250127.1/lib/libabsl_log_internal_conditions.so.2501.0.0
shrinking /nix/store/fbpmvkkbxif1d2y48f1y7746n6ky10rc-abseil-cpp-x86_64-unknown-linux-gnufilc0-20250127.1/lib/libabsl_log_internal_format.so.2501.0.0
shrinking /nix/store/fbpmvkkbxif1d2y48f1y7746n6ky10rc-abseil-cpp-x86_64-unknown-linux-gnufilc0-20250127.1/lib/libabsl_log_internal_globals.so.2501.0.0
shrinking /nix/store/fbpmvkkbxif1d2y48f1y7746n6ky10rc-abseil-cpp-x86_64-unknown-linux-gnufilc0-20250127.1/lib/libabsl_log_internal_proto.so.2501.0.0
shrinking /nix/store/fbpmvkkbxif1d2y48f1y7746n6ky10rc-abseil-cpp-x86_64-unknown-linux-gnufilc0-20250127.1/lib/libabsl_log_internal_message.so.2501.0.0
shrinking /nix/store/fbpmvkkbxif1d2y48f1y7746n6ky10rc-abseil-cpp-x86_64-unknown-linux-gnufilc0-20250127.1/lib/libabsl_log_internal_log_sink_set.so.2501.0.0
shrinking /nix/store/fbpmvkkbxif1d2y48f1y7746n6ky10rc-abseil-cpp-x86_64-unknown-linux-gnufilc0-20250127.1/lib/libabsl_log_internal_nullguard.so.2501.0.0
shrinking /nix/store/fbpmvkkbxif1d2y48f1y7746n6ky10rc-abseil-cpp-x86_64-unknown-linux-gnufilc0-20250127.1/lib/libabsl_die_if_null.so.2501.0.0
shrinking /nix/store/fbpmvkkbxif1d2y48f1y7746n6ky10rc-abseil-cpp-x86_64-unknown-linux-gnufilc0-20250127.1/lib/libabsl_log_flags.so.2501.0.0
shrinking /nix/store/fbpmvkkbxif1d2y48f1y7746n6ky10rc-abseil-cpp-x86_64-unknown-linux-gnufilc0-20250127.1/lib/libabsl_log_globals.so.2501.0.0
shrinking /nix/store/fbpmvkkbxif1d2y48f1y7746n6ky10rc-abseil-cpp-x86_64-unknown-linux-gnufilc0-20250127.1/lib/libabsl_log_initialize.so.2501.0.0
shrinking /nix/store/fbpmvkkbxif1d2y48f1y7746n6ky10rc-abseil-cpp-x86_64-unknown-linux-gnufilc0-20250127.1/lib/libabsl_log_entry.so.2501.0.0
shrinking /nix/store/fbpmvkkbxif1d2y48f1y7746n6ky10rc-abseil-cpp-x86_64-unknown-linux-gnufilc0-20250127.1/lib/libabsl_log_sink.so.2501.0.0
shrinking /nix/store/fbpmvkkbxif1d2y48f1y7746n6ky10rc-abseil-cpp-x86_64-unknown-linux-gnufilc0-20250127.1/lib/libabsl_scoped_mock_log.so.2501.0.0
shrinking /nix/store/fbpmvkkbxif1d2y48f1y7746n6ky10rc-abseil-cpp-x86_64-unknown-linux-gnufilc0-20250127.1/lib/libabsl_log_internal_structured_proto.so.2501.0.0
shrinking /nix/store/fbpmvkkbxif1d2y48f1y7746n6ky10rc-abseil-cpp-x86_64-unknown-linux-gnufilc0-20250127.1/lib/libabsl_vlog_config_internal.so.2501.0.0
shrinking /nix/store/fbpmvkkbxif1d2y48f1y7746n6ky10rc-abseil-cpp-x86_64-unknown-linux-gnufilc0-20250127.1/lib/libabsl_log_internal_fnmatch.so.2501.0.0
shrinking /nix/store/fbpmvkkbxif1d2y48f1y7746n6ky10rc-abseil-cpp-x86_64-unknown-linux-gnufilc0-20250127.1/lib/libabsl_int128.so.2501.0.0
shrinking /nix/store/fbpmvkkbxif1d2y48f1y7746n6ky10rc-abseil-cpp-x86_64-unknown-linux-gnufilc0-20250127.1/lib/libabsl_exponential_biased.so.2501.0.0
shrinking /nix/store/fbpmvkkbxif1d2y48f1y7746n6ky10rc-abseil-cpp-x86_64-unknown-linux-gnufilc0-20250127.1/lib/libabsl_periodic_sampler.so.2501.0.0
shrinking /nix/store/fbpmvkkbxif1d2y48f1y7746n6ky10rc-abseil-cpp-x86_64-unknown-linux-gnufilc0-20250127.1/lib/libabsl_random_distributions.so.2501.0.0
shrinking /nix/store/fbpmvkkbxif1d2y48f1y7746n6ky10rc-abseil-cpp-x86_64-unknown-linux-gnufilc0-20250127.1/lib/libabsl_random_seed_gen_exception.so.2501.0.0
shrinking /nix/store/fbpmvkkbxif1d2y48f1y7746n6ky10rc-abseil-cpp-x86_64-unknown-linux-gnufilc0-20250127.1/lib/libabsl_random_seed_sequences.so.2501.0.0
shrinking /nix/store/fbpmvkkbxif1d2y48f1y7746n6ky10rc-abseil-cpp-x86_64-unknown-linux-gnufilc0-20250127.1/lib/libabsl_random_internal_seed_material.so.2501.0.0
shrinking /nix/store/fbpmvkkbxif1d2y48f1y7746n6ky10rc-abseil-cpp-x86_64-unknown-linux-gnufilc0-20250127.1/lib/libabsl_random_internal_pool_urbg.so.2501.0.0
shrinking /nix/store/fbpmvkkbxif1d2y48f1y7746n6ky10rc-abseil-cpp-x86_64-unknown-linux-gnufilc0-20250127.1/lib/libabsl_random_internal_platform.so.2501.0.0
shrinking /nix/store/fbpmvkkbxif1d2y48f1y7746n6ky10rc-abseil-cpp-x86_64-unknown-linux-gnufilc0-20250127.1/lib/libabsl_random_internal_randen.so.2501.0.0
shrinking /nix/store/fbpmvkkbxif1d2y48f1y7746n6ky10rc-abseil-cpp-x86_64-unknown-linux-gnufilc0-20250127.1/lib/libabsl_random_internal_randen_slow.so.2501.0.0
shrinking /nix/store/fbpmvkkbxif1d2y48f1y7746n6ky10rc-abseil-cpp-x86_64-unknown-linux-gnufilc0-20250127.1/lib/libabsl_random_internal_randen_hwaes.so.2501.0.0
shrinking /nix/store/fbpmvkkbxif1d2y48f1y7746n6ky10rc-abseil-cpp-x86_64-unknown-linux-gnufilc0-20250127.1/lib/libabsl_random_internal_randen_hwaes_impl.so.2501.0.0
shrinking /nix/store/fbpmvkkbxif1d2y48f1y7746n6ky10rc-abseil-cpp-x86_64-unknown-linux-gnufilc0-20250127.1/lib/libabsl_random_internal_distribution_test_util.so.2501.0.0
shrinking /nix/store/fbpmvkkbxif1d2y48f1y7746n6ky10rc-abseil-cpp-x86_64-unknown-linux-gnufilc0-20250127.1/lib/libabsl_status.so.2501.0.0
shrinking /nix/store/fbpmvkkbxif1d2y48f1y7746n6ky10rc-abseil-cpp-x86_64-unknown-linux-gnufilc0-20250127.1/lib/libabsl_statusor.so.2501.0.0
shrinking /nix/store/fbpmvkkbxif1d2y48f1y7746n6ky10rc-abseil-cpp-x86_64-unknown-linux-gnufilc0-20250127.1/lib/libabsl_status_matchers.so.2501.0.0
shrinking /nix/store/fbpmvkkbxif1d2y48f1y7746n6ky10rc-abseil-cpp-x86_64-unknown-linux-gnufilc0-20250127.1/lib/libabsl_string_view.so.2501.0.0
shrinking /nix/store/fbpmvkkbxif1d2y48f1y7746n6ky10rc-abseil-cpp-x86_64-unknown-linux-gnufilc0-20250127.1/lib/libabsl_strings.so.2501.0.0
shrinking /nix/store/fbpmvkkbxif1d2y48f1y7746n6ky10rc-abseil-cpp-x86_64-unknown-linux-gnufilc0-20250127.1/lib/libabsl_strings_internal.so.2501.0.0
shrinking /nix/store/fbpmvkkbxif1d2y48f1y7746n6ky10rc-abseil-cpp-x86_64-unknown-linux-gnufilc0-20250127.1/lib/libabsl_str_format_internal.so.2501.0.0
shrinking /nix/store/fbpmvkkbxif1d2y48f1y7746n6ky10rc-abseil-cpp-x86_64-unknown-linux-gnufilc0-20250127.1/lib/libabsl_cord_internal.so.2501.0.0
shrinking /nix/store/fbpmvkkbxif1d2y48f1y7746n6ky10rc-abseil-cpp-x86_64-unknown-linux-gnufilc0-20250127.1/lib/libabsl_cordz_functions.so.2501.0.0
shrinking /nix/store/fbpmvkkbxif1d2y48f1y7746n6ky10rc-abseil-cpp-x86_64-unknown-linux-gnufilc0-20250127.1/lib/libabsl_cordz_handle.so.2501.0.0
shrinking /nix/store/fbpmvkkbxif1d2y48f1y7746n6ky10rc-abseil-cpp-x86_64-unknown-linux-gnufilc0-20250127.1/lib/libabsl_cordz_info.so.2501.0.0
shrinking /nix/store/fbpmvkkbxif1d2y48f1y7746n6ky10rc-abseil-cpp-x86_64-unknown-linux-gnufilc0-20250127.1/lib/libabsl_cordz_sample_token.so.2501.0.0
shrinking /nix/store/fbpmvkkbxif1d2y48f1y7746n6ky10rc-abseil-cpp-x86_64-unknown-linux-gnufilc0-20250127.1/lib/libabsl_cord.so.2501.0.0
shrinking /nix/store/fbpmvkkbxif1d2y48f1y7746n6ky10rc-abseil-cpp-x86_64-unknown-linux-gnufilc0-20250127.1/lib/libabsl_graphcycles_internal.so.2501.0.0
shrinking /nix/store/fbpmvkkbxif1d2y48f1y7746n6ky10rc-abseil-cpp-x86_64-unknown-linux-gnufilc0-20250127.1/lib/libabsl_kernel_timeout_internal.so.2501.0.0
shrinking /nix/store/fbpmvkkbxif1d2y48f1y7746n6ky10rc-abseil-cpp-x86_64-unknown-linux-gnufilc0-20250127.1/lib/libabsl_synchronization.so.2501.0.0
shrinking /nix/store/fbpmvkkbxif1d2y48f1y7746n6ky10rc-abseil-cpp-x86_64-unknown-linux-gnufilc0-20250127.1/lib/libabsl_time.so.2501.0.0
shrinking /nix/store/fbpmvkkbxif1d2y48f1y7746n6ky10rc-abseil-cpp-x86_64-unknown-linux-gnufilc0-20250127.1/lib/libabsl_civil_time.so.2501.0.0
shrinking /nix/store/fbpmvkkbxif1d2y48f1y7746n6ky10rc-abseil-cpp-x86_64-unknown-linux-gnufilc0-20250127.1/lib/libabsl_time_zone.so.2501.0.0
shrinking /nix/store/fbpmvkkbxif1d2y48f1y7746n6ky10rc-abseil-cpp-x86_64-unknown-linux-gnufilc0-20250127.1/lib/libabsl_bad_any_cast_impl.so.2501.0.0
shrinking /nix/store/fbpmvkkbxif1d2y48f1y7746n6ky10rc-abseil-cpp-x86_64-unknown-linux-gnufilc0-20250127.1/lib/libabsl_bad_optional_access.so.2501.0.0
shrinking /nix/store/fbpmvkkbxif1d2y48f1y7746n6ky10rc-abseil-cpp-x86_64-unknown-linux-gnufilc0-20250127.1/lib/libabsl_bad_variant_access.so.2501.0.0
checking for references to /build/ in /nix/store/fbpmvkkbxif1d2y48f1y7746n6ky10rc-abseil-cpp-x86_64-unknown-linux-gnufilc0-20250127.1...
patching script interpreter paths in /nix/store/fbpmvkkbxif1d2y48f1y7746n6ky10rc-abseil-cpp-x86_64-unknown-linux-gnufilc0-20250127.1
stripping (with command strip and flags -S -p) in  /nix/store/fbpmvkkbxif1d2y48f1y7746n6ky10rc-abseil-cpp-x86_64-unknown-linux-gnufilc0-20250127.1/lib
```

```
[ 39%] Linking CXX executable protoc-gen-upbdefs
/nix/store/fbpmvkkbxif1d2y48f1y7746n6ky10rc-abseil-cpp-x86_64-unknown-linux-gnufilc0-20250127.1/lib/libabsl_strings.so.2501.0.0: error: undefined reference to 'pizlonated_nan'
/nix/store/fbpmvkkbxif1d2y48f1y7746n6ky10rc-abseil-cpp-x86_64-unknown-linux-gnufilc0-20250127.1/lib/libabsl_strings.so.2501.0.0: error: undefined reference to 'pizlonated_nanf'
/nix/store/fbpmvkkbxif1d2y48f1y7746n6ky10rc-abseil-cpp-x86_64-unknown-linux-gnufilc0-20250127.1/lib/libabsl_exponential_biased.so.2501.0.0: error: undefined reference to 'pizlonated_log2'
CMakeFiles/protoc-gen-upbdefs.dir/src/google/protobuf/generated_message_util.cc.o:generated_message_util.cc:function pizlonatedFI__ZN6google8protobuf8internal24InitProtobufDefaultsSlowEv:(.text+0x50e): error: undefined reference to 'pizlonated___stop_pb_defaults'
CMakeFiles/protoc-gen-upbdefs.dir/src/google/protobuf/generated_message_util.cc.o:generated_message_util.cc:function pizlonatedFI__ZN6google8protobuf8internal24InitProtobufDefaultsSlowEv:(.text+0x524): error: undefined reference to 'pizlonated___start_pb_defaults'
CMakeFiles/protoc-gen-upbdefs.dir/src/google/protobuf/generated_message_util.cc.o:generated_message_util.cc:function pizlonatedFI__ZN6google8protobuf8internal24InitProtobufDefaultsSlowEv:(.text+0x621): error: undefined reference to 'pizlonated___start_pb_defaults'
CMakeFiles/protoc-gen-upbdefs.dir/src/google/protobuf/generated_message_util.cc.o:generated_message_util.cc:function pizlonatedFI__GLOBAL__I_000101:(.text+0x3c4e): error: undefined reference to 'pizlonated___stop_pb_defaults'
CMakeFiles/protoc-gen-upbdefs.dir/src/google/protobuf/generated_message_util.cc.o:generated_message_util.cc:function pizlonatedFI__GLOBAL__I_000101:(.text+0x3c64): error: undefined reference to 'pizlonated___start_pb_defaults'
CMakeFiles/protoc-gen-upbdefs.dir/src/google/protobuf/generated_message_util.cc.o:generated_message_util.cc:function pizlonatedFI__GLOBAL__I_000101:(.text+0x3d61): error: undefined reference to 'pizlonated___start_pb_defaults'
libupb.a(extension_registry.c.o):extension_registry.c:function pizlonatedFI_upb_ExtensionRegistry_AddAllLinkedExtensions:(.text+0x1449): error: undefined reference to 'pizlonated___start_linkarr_upb_AllExts'
libupb.a(extension_registry.c.o):extension_registry.c:function pizlonatedFI_upb_ExtensionRegistry_AddAllLinkedExtensions:(.text+0x1468): error: undefined reference to 'pizlonated___stop_linkarr_upb_AllExts'
libupb.a(extension_registry.c.o):extension_registry.c:function pizlonatedFI_upb_ExtensionRegistry_AddAllLinkedExtensions:(.text+0x1914): error: undefined reference to 'pizlonated___stop_linkarr_upb_AllExts'
clang-20: error: linker command failed with exit code 1 (use -v to see invocation)
make[2]: *** [CMakeFiles/protoc-gen-upbdefs.dir/build.make:1192: protoc-gen-upbdefs-30.2.0] Error 1
make[1]: *** [CMakeFiles/Makefile2:322: CMakeFiles/protoc-gen-upbdefs.dir/all] Error 2
[ 39%] Linking CXX shared library libprotobuf.so
Failed to parse version script: {
  global:
    extern "C++" {
      *google*;
      *pb::*;
    };
    scc_info_*;
    descriptor_table_*;

  local:
    *;
};

Failed at byte index 23
Reason: Expected ;
Output so far:  { global:
Failed to parse version script.
UNREACHABLE executed at /build/fil-c-b71bd6a/clang/lib/Driver/ToolChains/Gnu.cpp:371!
PLEASE submit a bug report to https://github.com/llvm/llvm-project/issues/ and include the crash backtrace, preprocessed source, and associated run script.
Stack dump:
0.      Program arguments: /nix/store/vgskqs0704cixafnd126s6jjis2jwmyl-filc0-git/bin/clang-20 -Wno-unused-command-line-argument --gcc-toolchain=/nix/store/kxm6wzygmj1439ylqdgyl9zqjgf10dy7-gcc-14.3.0 -resource-dir /nix/store/kmdxr31ifkqpfymppmakb17666rc6dai-filc0-resource-dir/lib/clang/20 --filc-dynamic-linker=/nix/store/gcgh62nhmd12bf9vzsbwa9gkpypr1jvg-filc-crt-lib/ld-yolo-x86_64.so --filc-crt-path=/nix/store/gcgh62nhmd12bf9vzsbwa9gkpypr1jvg-filc-crt-lib --filc-stdfil-include=/nix/store/lxc3z3cvbmsc0nbx7if9rl7jazyvgf56-fil-c-b71bd6a/filc/include --filc-os-include=/nix/store/lp9agkj5pykd83ndmijvpxcdg0lfvzis-linux-headers-6.12.7/include --filc-include=/nix/store/mrm9palka8aff58vj1f2pqv98hyhn325-yolo-glibc-impl-2.40/include -isystem /nix/store/r50h8fzrcx4h59jspwrfy08iicvp1vlg-filc-glibc-2.40/include -L/nix/store/r50h8fzrcx4h59jspwrfy08iicvp1vlg-filc-glibc-2.40/lib -nostdinc++ -I/nix/store/jxw48plk32hg0gy3b2dgji2p55jg7ss2-filc-libcxx-git/include/c++ -L/nix/store/jxw48plk32hg0gy3b2dgji2p55jg7ss2-filc-libcxx-git/lib -Wl,-dynamic-linker=/nix/store/6ql65jl6flp8qbikcpjn15hycghvqg29-filc-sysroot-with-metadata/lib/ld-yolo-x86_64.so -fPIC -O3 -DNDEBUG --version-script=/build/source/src/libprotobuf.map -shared -Wl,-soname,libprotobuf.so.30.2.0 -o libprotobuf.so.30.2.0 CMakeFiles/libprotobuf.dir/src/google/protobuf/any.pb.cc.o CMakeFiles/libprotobuf.dir/src/google/protobuf/api.pb.cc.o CMakeFiles/libprotobuf.dir/src/google/protobuf/duration.pb.cc.o CMakeFiles/libprotobuf.dir/src/google/protobuf/empty.pb.cc.o CMakeFiles/libprotobuf.dir/src/google/protobuf/field_mask.pb.cc.o CMakeFiles/libprotobuf.dir/src/google/protobuf/source_context.pb.cc.o CMakeFiles/libprotobuf.dir/src/google/protobuf/struct.pb.cc.o CMakeFiles/libprotobuf.dir/src/google/protobuf/timestamp.pb.cc.o CMakeFiles/libprotobuf.dir/src/google/protobuf/type.pb.cc.o CMakeFiles/libprotobuf.dir/src/google/protobuf/wrappers.pb.cc.o CMakeFiles/libprotobuf.dir/src/google/protobuf/any.cc.o CMakeFiles/libprotobuf.dir/src/google/protobuf/any_lite.cc.o CMakeFiles/libprotobuf.dir/src/google/protobuf/arena.cc.o CMakeFiles/libprotobuf.dir/src/google/protobuf/arena_align.cc.o CMakeFiles/libprotobuf.dir/src/google/protobuf/arenastring.cc.o CMakeFiles/libprotobuf.dir/src/google/protobuf/arenaz_sampler.cc.o CMakeFiles/libprotobuf.dir/src/google/protobuf/compiler/importer.cc.o CMakeFiles/libprotobuf.dir/src/google/protobuf/compiler/parser.cc.o CMakeFiles/libprotobuf.dir/src/google/protobuf/cpp_features.pb.cc.o CMakeFiles/libprotobuf.dir/src/google/protobuf/descriptor.cc.o CMakeFiles/libprotobuf.dir/src/google/protobuf/descriptor.pb.cc.o CMakeFiles/libprotobuf.dir/src/google/protobuf/descriptor_database.cc.o CMakeFiles/libprotobuf.dir/src/google/protobuf/dynamic_message.cc.o CMakeFiles/libprotobuf.dir/src/google/protobuf/extension_set.cc.o CMakeFiles/libprotobuf.dir/src/google/protobuf/extension_set_heavy.cc.o CMakeFiles/libprotobuf.dir/src/google/protobuf/feature_resolver.cc.o CMakeFiles/libprotobuf.dir/src/google/protobuf/generated_enum_util.cc.o CMakeFiles/libprotobuf.dir/src/google/protobuf/generated_message_bases.cc.o CMakeFiles/libprotobuf.dir/src/google/protobuf/generated_message_reflection.cc.o CMakeFiles/libprotobuf.dir/src/google/protobuf/generated_message_tctable_full.cc.o CMakeFiles/libprotobuf.dir/src/google/protobuf/generated_message_tctable_gen.cc.o CMakeFiles/libprotobuf.dir/src/google/protobuf/generated_message_tctable_lite.cc.o CMakeFiles/libprotobuf.dir/src/google/protobuf/generated_message_util.cc.o CMakeFiles/libprotobuf.dir/src/google/protobuf/implicit_weak_message.cc.o CMakeFiles/libprotobuf.dir/src/google/protobuf/inlined_string_field.cc.o CMakeFiles/libprotobuf.dir/src/google/protobuf/io/coded_stream.cc.o CMakeFiles/libprotobuf.dir/src/google/protobuf/io/gzip_stream.cc.o CMakeFiles/libprotobuf.dir/src/google/protobuf/io/io_win32.cc.o CMakeFiles/libprotobuf.dir/src/google/protobuf/io/printer.cc.o CMakeFiles/libprotobuf.dir/src/google/protobuf/io/strtod.cc.o CMakeFiles/libprotobuf.dir/src/google/protobuf/io/tokenizer.cc.o CMakeFiles/libprotobuf.dir/src/google/protobuf/io/zero_copy_sink.cc.o CMakeFiles/libprotobuf.dir/src/google/protobuf/io/zero_copy_stream.cc.o CMakeFiles/libprotobuf.dir/src/google/protobuf/io/zero_copy_stream_impl.cc.o CMakeFiles/libprotobuf.dir/src/google/protobuf/io/zero_copy_stream_impl_lite.cc.o CMakeFiles/libprotobuf.dir/src/google/protobuf/json/internal/lexer.cc.o CMakeFiles/libprotobuf.dir/src/google/protobuf/json/internal/message_path.cc.o CMakeFiles/libprotobuf.dir/src/google/protobuf/json/internal/parser.cc.o CMakeFiles/libprotobuf.dir/src/google/protobuf/json/internal/unparser.cc.o CMakeFiles/libprotobuf.dir/src/google/protobuf/json/internal/untyped_message.cc.o CMakeFiles/libprotobuf.dir/src/google/protobuf/json/internal/writer.cc.o CMakeFiles/libprotobuf.dir/src/google/protobuf/json/internal/zero_copy_buffered_stream.cc.o CMakeFiles/libprotobuf.dir/src/google/protobuf/json/json.cc.o CMakeFiles/libprotobuf.dir/src/google/protobuf/map.cc.o CMakeFiles/libprotobuf.dir/src/google/protobuf/map_field.cc.o CMakeFiles/libprotobuf.dir/src/google/protobuf/message.cc.o CMakeFiles/libprotobuf.dir/src/google/protobuf/message_lite.cc.o CMakeFiles/libprotobuf.dir/src/google/protobuf/parse_context.cc.o CMakeFiles/libprotobuf.dir/src/google/protobuf/port.cc.o CMakeFiles/libprotobuf.dir/src/google/protobuf/raw_ptr.cc.o CMakeFiles/libprotobuf.dir/src/google/protobuf/reflection_mode.cc.o CMakeFiles/libprotobuf.dir/src/google/protobuf/reflection_ops.cc.o CMakeFiles/libprotobuf.dir/src/google/protobuf/repeated_field.cc.o CMakeFiles/libprotobuf.dir/src/google/protobuf/repeated_ptr_field.cc.o CMakeFiles/libprotobuf.dir/src/google/protobuf/service.cc.o CMakeFiles/libprotobuf.dir/src/google/protobuf/stubs/common.cc.o CMakeFiles/libprotobuf.dir/src/google/protobuf/text_format.cc.o CMakeFiles/libprotobuf.dir/src/google/protobuf/unknown_field_set.cc.o CMakeFiles/libprotobuf.dir/src/google/protobuf/util/delimited_message_util.cc.o CMakeFiles/libprotobuf.dir/src/google/protobuf/util/field_comparator.cc.o CMakeFiles/libprotobuf.dir/src/google/protobuf/util/field_mask_util.cc.o CMakeFiles/libprotobuf.dir/src/google/protobuf/util/message_differencer.cc.o CMakeFiles/libprotobuf.dir/src/google/protobuf/util/time_util.cc.o CMakeFiles/libprotobuf.dir/src/google/protobuf/util/type_resolver_util.cc.o CMakeFiles/libprotobuf.dir/src/google/protobuf/wire_format.cc.o CMakeFiles/libprotobuf.dir/src/google/protobuf/wire_format_lite.cc.o -Wl,-rpath,/build/source/build/third_party/utf8_range: /nix/store/ksm9abcghbc5smqy0n0v1jcn5s148sw4-zlib-1.3-x86_64-unknown-linux-gnufilc0/lib/libz.so /nix/store/fbpmvkkbxif1d2y48f1y7746n6ky10rc-abseil-cpp-x86_64-unknown-linux-gnufilc0-20250127.1/lib/libabsl_die_if_null.so.2501.0.0 /nix/store/fbpmvkkbxif1d2y48f1y7746n6ky10rc-abseil-cpp-x86_64-unknown-linux-gnufilc0-20250127.1/lib/libabsl_log_initialize.so.2501.0.0 /nix/store/fbpmvkkbxif1d2y48f1y7746n6ky10rc-abseil-cpp-x86_64-unknown-linux-gnufilc0-20250127.1/lib/libabsl_statusor.so.2501.0.0 third_party/utf8_range/libutf8_validity.so.30.2.0 /nix/store/fbpmvkkbxif1d2y48f1y7746n6ky10rc-abseil-cpp-x86_64-unknown-linux-gnufilc0-20250127.1/lib/libabsl_log_internal_check_op.so.2501.0.0 /nix/store/fbpmvkkbxif1d2y48f1y7746n6ky10rc-abseil-cpp-x86_64-unknown-linux-gnufilc0-20250127.1/lib/libabsl_log_internal_conditions.so.2501.0.0 /nix/store/fbpmvkkbxif1d2y48f1y7746n6ky10rc-abseil-cpp-x86_64-unknown-linux-gnufilc0-20250127.1/lib/libabsl_log_internal_message.so.2501.0.0 /nix/store/fbpmvkkbxif1d2y48f1y7746n6ky10rc-abseil-cpp-x86_64-unknown-linux-gnufilc0-20250127.1/lib/libabsl_log_internal_nullguard.so.2501.0.0 /nix/store/fbpmvkkbxif1d2y48f1y7746n6ky10rc-abseil-cpp-x86_64-unknown-linux-gnufilc0-20250127.1/lib/libabsl_examine_stack.so.2501.0.0 /nix/store/fbpmvkkbxif1d2y48f1y7746n6ky10rc-abseil-cpp-x86_64-unknown-linux-gnufilc0-20250127.1/lib/libabsl_log_internal_format.so.2501.0.0 /nix/store/fbpmvkkbxif1d2y48f1y7746n6ky10rc-abseil-cpp-x86_64-unknown-linux-gnufilc0-20250127.1/lib/libabsl_log_internal_structured_proto.so.2501.0.0 /nix/store/fbpmvkkbxif1d2y48f1y7746n6ky10rc-abseil-cpp-x86_64-unknown-linux-gnufilc0-20250127.1/lib/libabsl_log_internal_proto.so.2501.0.0 /nix/store/fbpmvkkbxif1d2y48f1y7746n6ky10rc-abseil-cpp-x86_64-unknown-linux-gnufilc0-20250127.1/lib/libabsl_log_internal_log_sink_set.so.2501.0.0 /nix/store/fbpmvkkbxif1d2y48f1y7746n6ky10rc-abseil-cpp-x86_64-unknown-linux-gnufilc0-20250127.1/lib/libabsl_log_sink.so.2501.0.0 /nix/store/fbpmvkkbxif1d2y48f1y7746n6ky10rc-abseil-cpp-x86_64-unknown-linux-gnufilc0-20250127.1/lib/libabsl_log_entry.so.2501.0.0 /nix/store/fbpmvkkbxif1d2y48f1y7746n6ky10rc-abseil-cpp-x86_64-unknown-linux-gnufilc0-20250127.1/lib/libabsl_flags_internal.so.2501.0.0 /nix/store/fbpmvkkbxif1d2y48f1y7746n6ky10rc-abseil-cpp-x86_64-unknown-linux-gnufilc0-20250127.1/lib/libabsl_flags_marshalling.so.2501.0.0 /nix/store/fbpmvkkbxif1d2y48f1y7746n6ky10rc-abseil-cpp-x86_64-unknown-linux-gnufilc0-20250127.1/lib/libabsl_flags_reflection.so.2501.0.0 /nix/store/fbpmvkkbxif1d2y48f1y7746n6ky10rc-abseil-cpp-x86_64-unknown-linux-gnufilc0-20250127.1/lib/libabsl_flags_config.so.2501.0.0 /nix/store/fbpmvkkbxif1d2y48f1y7746n6ky10rc-abseil-cpp-x86_64-unknown-linux-gnufilc0-20250127.1/lib/libabsl_flags_program_name.so.2501.0.0 /nix/store/fbpmvkkbxif1d2y48f1y7746n6ky10rc-abseil-cpp-x86_64-unknown-linux-gnufilc0-20250127.1/lib/libabsl_flags_private_handle_accessor.so.2501.0.0 /nix/store/fbpmvkkbxif1d2y48f1y7746n6ky10rc-abseil-cpp-x86_64-unknown-linux-gnufilc0-20250127.1/lib/libabsl_flags_commandlineflag.so.2501.0.0 /nix/store/fbpmvkkbxif1d2y48f1y7746n6ky10rc-abseil-cpp-x86_64-unknown-linux-gnufilc0-20250127.1/lib/libabsl_flags_commandlineflag_internal.so.2501.0.0 /nix/store/fbpmvkkbxif1d2y48f1y7746n6ky10rc-abseil-cpp-x86_64-unknown-linux-gnufilc0-20250127.1/lib/libabsl_log_globals.so.2501.0.0 /nix/store/fbpmvkkbxif1d2y48f1y7746n6ky10rc-abseil-cpp-x86_64-unknown-linux-gnufilc0-20250127.1/lib/libabsl_vlog_config_internal.so.2501.0.0 /nix/store/fbpmvkkbxif1d2y48f1y7746n6ky10rc-abseil-cpp-x86_64-unknown-linux-gnufilc0-20250127.1/lib/libabsl_log_internal_fnmatch.so.2501.0.0 /nix/store/fbpmvkkbxif1d2y48f1y7746n6ky10rc-abseil-cpp-x86_64-unknown-linux-gnufilc0-20250127.1/lib/libabsl_log_internal_globals.so.2501.0.0 /nix/store/fbpmvkkbxif1d2y48f1y7746n6ky10rc-abseil-cpp-x86_64-unknown-linux-gnufilc0-20250127.1/lib/libabsl_raw_hash_set.so.2501.0.0 /nix/store/fbpmvkkbxif1d2y48f1y7746n6ky10rc-abseil-cpp-x86_64-unknown-linux-gnufilc0-20250127.1/lib/libabsl_hash.so.2501.0.0 /nix/store/fbpmvkkbxif1d2y48f1y7746n6ky10rc-abseil-cpp-x86_64-unknown-linux-gnufilc0-20250127.1/lib/libabsl_city.so.2501.0.0 /nix/store/fbpmvkkbxif1d2y48f1y7746n6ky10rc-abseil-cpp-x86_64-unknown-linux-gnufilc0-20250127.1/lib/libabsl_low_level_hash.so.2501.0.0 /nix/store/fbpmvkkbxif1d2y48f1y7746n6ky10rc-abseil-cpp-x86_64-unknown-linux-gnufilc0-20250127.1/lib/libabsl_hashtablez_sampler.so.2501.0.0 /nix/store/fbpmvkkbxif1d2y48f1y7746n6ky10rc-abseil-cpp-x86_64-unknown-linux-gnufilc0-20250127.1/lib/libabsl_random_distributions.so.2501.0.0 /nix/store/fbpmvkkbxif1d2y48f1y7746n6ky10rc-abseil-cpp-x86_64-unknown-linux-gnufilc0-20250127.1/lib/libabsl_random_seed_sequences.so.2501.0.0 /nix/store/fbpmvkkbxif1d2y48f1y7746n6ky10rc-abseil-cpp-x86_64-unknown-linux-gnufilc0-20250127.1/lib/libabsl_random_internal_pool_urbg.so.2501.0.0 /nix/store/fbpmvkkbxif1d2y48f1y7746n6ky10rc-abseil-cpp-x86_64-unknown-linux-gnufilc0-20250127.1/lib/libabsl_random_internal_randen.so.2501.0.0 /nix/store/fbpmvkkbxif1d2y48f1y7746n6ky10rc-abseil-cpp-x86_64-unknown-linux-gnufilc0-20250127.1/lib/libabsl_random_internal_randen_hwaes.so.2501.0.0 /nix/store/fbpmvkkbxif1d2y48f1y7746n6ky10rc-abseil-cpp-x86_64-unknown-linux-gnufilc0-20250127.1/lib/libabsl_random_internal_randen_hwaes_impl.so.2501.0.0 /nix/store/fbpmvkkbxif1d2y48f1y7746n6ky10rc-abseil-cpp-x86_64-unknown-linux-gnufilc0-20250127.1/lib/libabsl_random_internal_randen_slow.so.2501.0.0 /nix/store/fbpmvkkbxif1d2y48f1y7746n6ky10rc-abseil-cpp-x86_64-unknown-linux-gnufilc0-20250127.1/lib/libabsl_random_internal_platform.so.2501.0.0 /nix/store/fbpmvkkbxif1d2y48f1y7746n6ky10rc-abseil-cpp-x86_64-unknown-linux-gnufilc0-20250127.1/lib/libabsl_random_internal_seed_material.so.2501.0.0 /nix/store/fbpmvkkbxif1d2y48f1y7746n6ky10rc-abseil-cpp-x86_64-unknown-linux-gnufilc0-20250127.1/lib/libabsl_random_seed_gen_exception.so.2501.0.0 /nix/store/fbpmvkkbxif1d2y48f1y7746n6ky10rc-abseil-cpp-x86_64-unknown-linux-gnufilc0-20250127.1/lib/libabsl_status.so.2501.0.0 /nix/store/fbpmvkkbxif1d2y48f1y7746n6ky10rc-abseil-cpp-x86_64-unknown-linux-gnufilc0-20250127.1/lib/libabsl_cord.so.2501.0.0 /nix/store/fbpmvkkbxif1d2y48f1y7746n6ky10rc-abseil-cpp-x86_64-unknown-linux-gnufilc0-20250127.1/lib/libabsl_cordz_info.so.2501.0.0 /nix/store/fbpmvkkbxif1d2y48f1y7746n6ky10rc-abseil-cpp-x86_64-unknown-linux-gnufilc0-20250127.1/lib/libabsl_cord_internal.so.2501.0.0 /nix/store/fbpmvkkbxif1d2y48f1y7746n6ky10rc-abseil-cpp-x86_64-unknown-linux-gnufilc0-20250127.1/lib/libabsl_cordz_functions.so.2501.0.0 /nix/store/fbpmvkkbxif1d2y48f1y7746n6ky10rc-abseil-cpp-x86_64-unknown-linux-gnufilc0-20250127.1/lib/libabsl_exponential_biased.so.2501.0.0 /nix/store/fbpmvkkbxif1d2y48f1y7746n6ky10rc-abseil-cpp-x86_64-unknown-linux-gnufilc0-20250127.1/lib/libabsl_cordz_handle.so.2501.0.0 /nix/store/fbpmvkkbxif1d2y48f1y7746n6ky10rc-abseil-cpp-x86_64-unknown-linux-gnufilc0-20250127.1/lib/libabsl_synchronization.so.2501.0.0 /nix/store/fbpmvkkbxif1d2y48f1y7746n6ky10rc-abseil-cpp-x86_64-unknown-linux-gnufilc0-20250127.1/lib/libabsl_graphcycles_internal.so.2501.0.0 /nix/store/fbpmvkkbxif1d2y48f1y7746n6ky10rc-abseil-cpp-x86_64-unknown-linux-gnufilc0-20250127.1/lib/libabsl_kernel_timeout_internal.so.2501.0.0 /nix/store/fbpmvkkbxif1d2y48f1y7746n6ky10rc-abseil-cpp-x86_64-unknown-linux-gnufilc0-20250127.1/lib/libabsl_time.so.2501.0.0 /nix/store/fbpmvkkbxif1d2y48f1y7746n6ky10rc-abseil-cpp-x86_64-unknown-linux-gnufilc0-20250127.1/lib/libabsl_civil_time.so.2501.0.0 /nix/store/fbpmvkkbxif1d2y48f1y7746n6ky10rc-abseil-cpp-x86_64-unknown-linux-gnufilc0-20250127.1/lib/libabsl_time_zone.so.2501.0.0 /nix/store/fbpmvkkbxif1d2y48f1y7746n6ky10rc-abseil-cpp-x86_64-unknown-linux-gnufilc0-20250127.1/lib/libabsl_tracing_internal.so.2501.0.0 /nix/store/fbpmvkkbxif1d2y48f1y7746n6ky10rc-abseil-cpp-x86_64-unknown-linux-gnufilc0-20250127.1/lib/libabsl_crc_cord_state.so.2501.0.0 /nix/store/fbpmvkkbxif1d2y48f1y7746n6ky10rc-abseil-cpp-x86_64-unknown-linux-gnufilc0-20250127.1/lib/libabsl_crc32c.so.2501.0.0 /nix/store/fbpmvkkbxif1d2y48f1y7746n6ky10rc-abseil-cpp-x86_64-unknown-linux-gnufilc0-20250127.1/lib/libabsl_crc_internal.so.2501.0.0 /nix/store/fbpmvkkbxif1d2y48f1y7746n6ky10rc-abseil-cpp-x86_64-unknown-linux-gnufilc0-20250127.1/lib/libabsl_crc_cpu_detect.so.2501.0.0 /nix/store/fbpmvkkbxif1d2y48f1y7746n6ky10rc-abseil-cpp-x86_64-unknown-linux-gnufilc0-20250127.1/lib/libabsl_bad_optional_access.so.2501.0.0 /nix/store/fbpmvkkbxif1d2y48f1y7746n6ky10rc-abseil-cpp-x86_64-unknown-linux-gnufilc0-20250127.1/lib/libabsl_stacktrace.so.2501.0.0 /nix/store/fbpmvkkbxif1d2y48f1y7746n6ky10rc-abseil-cpp-x86_64-unknown-linux-gnufilc0-20250127.1/lib/libabsl_leak_check.so.2501.0.0 /nix/store/fbpmvkkbxif1d2y48f1y7746n6ky10rc-abseil-cpp-x86_64-unknown-linux-gnufilc0-20250127.1/lib/libabsl_strerror.so.2501.0.0 /nix/store/fbpmvkkbxif1d2y48f1y7746n6ky10rc-abseil-cpp-x86_64-unknown-linux-gnufilc0-20250127.1/lib/libabsl_symbolize.so.2501.0.0 /nix/store/fbpmvkkbxif1d2y48f1y7746n6ky10rc-abseil-cpp-x86_64-unknown-linux-gnufilc0-20250127.1/lib/libabsl_debugging_internal.so.2501.0.0 /nix/store/fbpmvkkbxif1d2y48f1y7746n6ky10rc-abseil-cpp-x86_64-unknown-linux-gnufilc0-20250127.1/lib/libabsl_malloc_internal.so.2501.0.0 /nix/store/fbpmvkkbxif1d2y48f1y7746n6ky10rc-abseil-cpp-x86_64-unknown-linux-gnufilc0-20250127.1/lib/libabsl_demangle_internal.so.2501.0.0 /nix/store/fbpmvkkbxif1d2y48f1y7746n6ky10rc-abseil-cpp-x86_64-unknown-linux-gnufilc0-20250127.1/lib/libabsl_demangle_rust.so.2501.0.0 /nix/store/fbpmvkkbxif1d2y48f1y7746n6ky10rc-abseil-cpp-x86_64-unknown-linux-gnufilc0-20250127.1/lib/libabsl_decode_rust_punycode.so.2501.0.0 /nix/store/fbpmvkkbxif1d2y48f1y7746n6ky10rc-abseil-cpp-x86_64-unknown-linux-gnufilc0-20250127.1/lib/libabsl_utf8_for_code_point.so.2501.0.0 /nix/store/fbpmvkkbxif1d2y48f1y7746n6ky10rc-abseil-cpp-x86_64-unknown-linux-gnufilc0-20250127.1/lib/libabsl_bad_variant_access.so.2501.0.0 /nix/store/fbpmvkkbxif1d2y48f1y7746n6ky10rc-abseil-cpp-x86_64-unknown-linux-gnufilc0-20250127.1/lib/libabsl_str_format_internal.so.2501.0.0 /nix/store/fbpmvkkbxif1d2y48f1y7746n6ky10rc-abseil-cpp-x86_64-unknown-linux-gnufilc0-20250127.1/lib/libabsl_strings.so.2501.0.0 /nix/store/fbpmvkkbxif1d2y48f1y7746n6ky10rc-abseil-cpp-x86_64-unknown-linux-gnufilc0-20250127.1/lib/libabsl_int128.so.2501.0.0 /nix/store/fbpmvkkbxif1d2y48f1y7746n6ky10rc-abseil-cpp-x86_64-unknown-linux-gnufilc0-20250127.1/lib/libabsl_strings_internal.so.2501.0.0 /nix/store/fbpmvkkbxif1d2y48f1y7746n6ky10rc-abseil-cpp-x86_64-unknown-linux-gnufilc0-20250127.1/lib/libabsl_string_view.so.2501.0.0 /nix/store/fbpmvkkbxif1d2y48f1y7746n6ky10rc-abseil-cpp-x86_64-unknown-linux-gnufilc0-20250127.1/lib/libabsl_base.so.2501.0.0 /nix/store/fbpmvkkbxif1d2y48f1y7746n6ky10rc-abseil-cpp-x86_64-unknown-linux-gnufilc0-20250127.1/lib/libabsl_spinlock_wait.so.2501.0.0 /nix/store/fbpmvkkbxif1d2y48f1y7746n6ky10rc-abseil-cpp-x86_64-unknown-linux-gnufilc0-20250127.1/lib/libabsl_throw_delegate.so.2501.0.0 /nix/store/fbpmvkkbxif1d2y48f1y7746n6ky10rc-abseil-cpp-x86_64-unknown-linux-gnufilc0-20250127.1/lib/libabsl_raw_logging_internal.so.2501.0.0 /nix/store/fbpmvkkbxif1d2y48f1y7746n6ky10rc-abseil-cpp-x86_64-unknown-linux-gnufilc0-20250127.1/lib/libabsl_log_severity.so.2501.0.0 -B/nix/store/6ql65jl6flp8qbikcpjn15hycghvqg29-filc-sysroot-with-metadata/lib/ -idirafter /nix/store/6ql65jl6flp8qbikcpjn15hycghvqg29-filc-sysroot-with-metadata/include -B/nix/store/gy2di95906x5rgl25ck3d3xhsp7srz8b-filc-cc/lib -Wno-unused-command-line-argument -gz=none -B/nix/store/bjmp5s6kl068x3vmjg2cbycfwx21hcd2-binutils-wrapper-2.43.1/bin/ -frandom-seed=kqa96llmc5 -isystem /nix/store/jxw48plk32hg0gy3b2dgji2p55jg7ss2-filc-libcxx-git/include -isystem /nix/store/nga4lby01bbxk22y6z3ccr3c7lmsp1r1-gtest-x86_64-unknown-linux-gnufilc0-1.16.0-dev/include -isystem /nix/store/hsxy5sh3imdhnjbp1qrvc862r4rf6ci7-zlib-1.3-x86_64-unknown-linux-gnufilc0-dev/include -isystem /nix/store/fbpmvkkbxif1d2y48f1y7746n6ky10rc-abseil-cpp-x86_64-unknown-linux-gnufilc0-20250127.1/include -Wl,-rpath -Wl,/nix/store/kqa96llmc5wmf1ghbl1p1ch0giws5jgm-protobuf-x86_64-unknown-linux-gnufilc0-30.2/lib -L/nix/store/jxw48plk32hg0gy3b2dgji2p55jg7ss2-filc-libcxx-git/lib -L/nix/store/8vlna318101fgzhdzfpvf71snkvw909w-gtest-x86_64-unknown-linux-gnufilc0-1.16.0/lib -L/nix/store/ksm9abcghbc5smqy0n0v1jcn5s148sw4-zlib-1.3-x86_64-unknown-linux-gnufilc0/lib -L/nix/store/fbpmvkkbxif1d2y48f1y7746n6ky10rc-abseil-cpp-x86_64-unknown-linux-gnufilc0-20250127.1/lib -L/nix/store/6ql65jl6flp8qbikcpjn15hycghvqg29-filc-sysroot-with-metadata/lib -L/nix/store/r50h8fzrcx4h59jspwrfy08iicvp1vlg-filc-glibc-2.40/lib -Wl,-lpizlo -Wl,-lyoloc -Wl,-lyolom -Wl,-lc++ -Wl,-lc++abi -L/nix/store/gy2di95906x5rgl25ck3d3xhsp7srz8b-filc-cc/lib -L/nix/store/jxw48plk32hg0gy3b2dgji2p55jg7ss2-filc-libcxx-git/lib
1.      Compilation construction
2.      Building compilation jobs
3.      Building compilation jobs
Stack dump without symbol names (ensure you have llvm-symbolizer in your PATH or set the environment var `LLVM_SYMBOLIZER_PATH` to point to it):
0  clang-20  0x00000000020c8a4c llvm::sys::PrintStackTrace(llvm::raw_ostream&, int) + 60
1  clang-20  0x00000000020c5f14 llvm::sys::RunSignalHandlers() + 52
2  clang-20  0x00000000020c6344
3  libc.so.6 0x00007ffff7c414b0
4  libc.so.6 0x00007ffff7c9984c
5  libc.so.6 0x00007ffff7c41406 gsignal + 22
6  libc.so.6 0x00007ffff7c2893a abort + 215
7  clang-20  0x000000000202d6da
8  clang-20  0x0000000002b2d2e7
9  clang-20  0x0000000002b45851
10 clang-20  0x0000000002a21f24 clang::driver::Driver::BuildJobsForActionNoCache(clang::driver::Compilation&, clang::driver::Action const*, clang::driver::ToolChain const*, llvm::StringRef, bool, bool, char const*, std::map<std::pair<clang::driver::Action const*, std::__cxx11::basic_string<char, std::char_traits<char>, std::allocator<char>>>, llvm::SmallVector<clang::driver::InputInfo, 4u>, std::less<std::pair<clang::driver::Action const*, std::__cxx11::basic_string<char, std::char_traits<char>, std::allocator<char>>>>, std::allocator<std::pair<std::pair<clang::driver::Action const*, std::__cxx11::basic_string<char, std::char_traits<char>, std::allocator<char>>> const, llvm::SmallVector<clang::driver::InputInfo, 4u>>>>&, clang::driver::Action::OffloadKind) const + 6116
11 clang-20  0x0000000002a23627 clang::driver::Driver::BuildJobsForAction(clang::driver::Compilation&, clang::driver::Action const*, clang::driver::ToolChain const*, llvm::StringRef, bool, bool, char const*, std::map<std::pair<clang::driver::Action const*, std::__cxx11::basic_string<char, std::char_traits<char>, std::allocator<char>>>, llvm::SmallVector<clang::driver::InputInfo, 4u>, std::less<std::pair<clang::driver::Action const*, std::__cxx11::basic_string<char, std::char_traits<char>, std::allocator<char>>>>, std::allocator<std::pair<std::pair<clang::driver::Action const*, std::__cxx11::basic_string<char, std::char_traits<char>, std::allocator<char>>> const, llvm::SmallVector<clang::driver::InputInfo, 4u>>>>&, clang::driver::Action::OffloadKind) const + 423
12 clang-20  0x0000000002a240d9 clang::driver::Driver::BuildJobs(clang::driver::Compilation&) const + 505
13 clang-20  0x0000000002a35835 clang::driver::Driver::BuildCompilation(llvm::ArrayRef<char const*>) + 11605
14 clang-20  0x0000000000c77628 clang_main(int, char**, llvm::ToolContext const&) + 3560
15 clang-20  0x0000000000b83404 main + 100
16 libc.so.6 0x00007ffff7c2a47e
17 libc.so.6 0x00007ffff7c2a539 __libc_start_main + 137
18 clang-20  0x0000000000c741d5 _start + 37
Error running link command: Subprocess abortedmake[2]: *** [CMakeFiles/libprotobuf.dir/build.make:1384: libprotobuf.so.30.2.0] Error 1
make[1]: *** [CMakeFiles/Makefile2:190: CMakeFiles/libprotobuf.dir/all] Error 2
[ 39%] Linking CXX executable protoc-gen-upb
/nix/store/fbpmvkkbxif1d2y48f1y7746n6ky10rc-abseil-cpp-x86_64-unknown-linux-gnufilc0-20250127.1/lib/libabsl_strings.so.2501.0.0: error: undefined reference to 'pizlonated_nan'
/nix/store/fbpmvkkbxif1d2y48f1y7746n6ky10rc-abseil-cpp-x86_64-unknown-linux-gnufilc0-20250127.1/lib/libabsl_strings.so.2501.0.0: error: undefined reference to 'pizlonated_nanf'
/nix/store/fbpmvkkbxif1d2y48f1y7746n6ky10rc-abseil-cpp-x86_64-unknown-linux-gnufilc0-20250127.1/lib/libabsl_exponential_biased.so.2501.0.0: error: undefined reference to 'pizlonated_log2'
CMakeFiles/protoc-gen-upb.dir/src/google/protobuf/generated_message_util.cc.o:generated_message_util.cc:function pizlonatedFI__ZN6google8protobuf8internal24InitProtobufDefaultsSlowEv:(.text+0x50e): error: undefined reference to 'pizlonated___stop_pb_defaults'
CMakeFiles/protoc-gen-upb.dir/src/google/protobuf/generated_message_util.cc.o:generated_message_util.cc:function pizlonatedFI__ZN6google8protobuf8internal24InitProtobufDefaultsSlowEv:(.text+0x524): error: undefined reference to 'pizlonated___start_pb_defaults'
CMakeFiles/protoc-gen-upb.dir/src/google/protobuf/generated_message_util.cc.o:generated_message_util.cc:function pizlonatedFI__ZN6google8protobuf8internal24InitProtobufDefaultsSlowEv:(.text+0x621): error: undefined reference to 'pizlonated___start_pb_defaults'
CMakeFiles/protoc-gen-upb.dir/src/google/protobuf/generated_message_util.cc.o:generated_message_util.cc:function pizlonatedFI__GLOBAL__I_000101:(.text+0x3c4e): error: undefined reference to 'pizlonated___stop_pb_defaults'
CMakeFiles/protoc-gen-upb.dir/src/google/protobuf/generated_message_util.cc.o:generated_message_util.cc:function pizlonatedFI__GLOBAL__I_000101:(.text+0x3c64): error: undefined reference to 'pizlonated___start_pb_defaults'
CMakeFiles/protoc-gen-upb.dir/src/google/protobuf/generated_message_util.cc.o:generated_message_util.cc:function pizlonatedFI__GLOBAL__I_000101:(.text+0x3d61): error: undefined reference to 'pizlonated___start_pb_defaults'
libupb.a(extension_registry.c.o):extension_registry.c:function pizlonatedFI_upb_ExtensionRegistry_AddAllLinkedExtensions:(.text+0x1449): error: undefined reference to 'pizlonated___start_linkarr_upb_AllExts'
libupb.a(extension_registry.c.o):extension_registry.c:function pizlonatedFI_upb_ExtensionRegistry_AddAllLinkedExtensions:(.text+0x1468): error: undefined reference to 'pizlonated___stop_linkarr_upb_AllExts'
libupb.a(extension_registry.c.o):extension_registry.c:function pizlonatedFI_upb_ExtensionRegistry_AddAllLinkedExtensions:(.text+0x1914): error: undefined reference to 'pizlonated___stop_linkarr_upb_AllExts'
clang-20: error: linker command failed with exit code 1 (use -v to see invocation)
make[2]: *** [CMakeFiles/protoc-gen-upb.dir/build.make:1208: protoc-gen-upb-30.2.0] Error 1
make[1]: *** [CMakeFiles/Makefile2:288: CMakeFiles/protoc-gen-upb.dir/all] Error 2
make: *** [Makefile:146: all] Error 2
```

</details>

<details>
<summary>❌ <strong>curb</strong>: curb_easy.c:127:30: error: incompatible pointer to integer conversion passing 'VALUE' (aka 'struct r...</summary>

```
      |                                 ^
/nix/store/za2zv3sp018x807vc5sq1fdc3036jjm1-curl-x86_64-unknown-linux-gnufilc0-8.14.1-dev/include/curl/curl.h:2919:24: note: 'CURLINFO_SIZE_DOWNLOAD' has been explicitly marked deprecated here
 2919 |                        CURL_DEPRECATED(7.55.0, "Use CURLINFO_SIZE_DOWNLOAD_T")
      |                        ^
/nix/store/za2zv3sp018x807vc5sq1fdc3036jjm1-curl-x86_64-unknown-linux-gnufilc0-8.14.1-dev/include/curl/curl.h:44:18: note: expanded from macro 'CURL_DEPRECATED'
   44 |   __attribute__((deprecated("since " # version ". " message)))
      |                  ^
curb_easy.c:3307:33: warning: 'CURLINFO_SPEED_UPLOAD' is deprecated: since 7.55.0. Use CURLINFO_SPEED_UPLOAD_T [-Wdeprecated-declarations]
 3307 |   curl_easy_getinfo(rbce->curl, CURLINFO_SPEED_UPLOAD, &bytes);
      |                                 ^
/nix/store/za2zv3sp018x807vc5sq1fdc3036jjm1-curl-x86_64-unknown-linux-gnufilc0-8.14.1-dev/include/curl/curl.h:2927:24: note: 'CURLINFO_SPEED_UPLOAD' has been explicitly marked deprecated here
 2927 |                        CURL_DEPRECATED(7.55.0, "Use CURLINFO_SPEED_UPLOAD_T")
      |                        ^
/nix/store/za2zv3sp018x807vc5sq1fdc3036jjm1-curl-x86_64-unknown-linux-gnufilc0-8.14.1-dev/include/curl/curl.h:44:18: note: expanded from macro 'CURL_DEPRECATED'
   44 |   __attribute__((deprecated("since " # version ". " message)))
      |                  ^
curb_easy.c:3324:33: warning: 'CURLINFO_SPEED_DOWNLOAD' is deprecated: since 7.55.0. Use CURLINFO_SPEED_DOWNLOAD_T [-Wdeprecated-declarations]
 3324 |   curl_easy_getinfo(rbce->curl, CURLINFO_SPEED_DOWNLOAD, &bytes);
      |                                 ^
/nix/store/za2zv3sp018x807vc5sq1fdc3036jjm1-curl-x86_64-unknown-linux-gnufilc0-8.14.1-dev/include/curl/curl.h:2923:24: note: 'CURLINFO_SPEED_DOWNLOAD' has been explicitly marked deprecated here
 2923 |                        CURL_DEPRECATED(7.55.0, "Use CURLINFO_SPEED_DOWNLOAD_T")
      |                        ^
/nix/store/za2zv3sp018x807vc5sq1fdc3036jjm1-curl-x86_64-unknown-linux-gnufilc0-8.14.1-dev/include/curl/curl.h:44:18: note: expanded from macro 'CURL_DEPRECATED'
   44 |   __attribute__((deprecated("since " # version ". " message)))
      |                  ^
curb_easy.c:3401:33: warning: 'CURLINFO_CONTENT_LENGTH_DOWNLOAD' is deprecated: since 7.55.0. Use CURLINFO_CONTENT_LENGTH_DOWNLOAD_T [-Wdeprecated-declarations]
 3401 |   curl_easy_getinfo(rbce->curl, CURLINFO_CONTENT_LENGTH_DOWNLOAD, &bytes);
      |                                 ^
/nix/store/za2zv3sp018x807vc5sq1fdc3036jjm1-curl-x86_64-unknown-linux-gnufilc0-8.14.1-dev/include/curl/curl.h:2936:24: note: 'CURLINFO_CONTENT_LENGTH_DOWNLOAD' has been explicitly marked deprecated here
 2936 |                        CURL_DEPRECATED(7.55.0,
      |                        ^
/nix/store/za2zv3sp018x807vc5sq1fdc3036jjm1-curl-x86_64-unknown-linux-gnufilc0-8.14.1-dev/include/curl/curl.h:44:18: note: expanded from macro 'CURL_DEPRECATED'
   44 |   __attribute__((deprecated("since " # version ". " message)))
      |                  ^
curb_easy.c:3417:33: warning: 'CURLINFO_CONTENT_LENGTH_UPLOAD' is deprecated: since 7.55.0. Use CURLINFO_CONTENT_LENGTH_UPLOAD_T [-Wdeprecated-declarations]
 3417 |   curl_easy_getinfo(rbce->curl, CURLINFO_CONTENT_LENGTH_UPLOAD, &bytes);
      |                                 ^
/nix/store/za2zv3sp018x807vc5sq1fdc3036jjm1-curl-x86_64-unknown-linux-gnufilc0-8.14.1-dev/include/curl/curl.h:2941:24: note: 'CURLINFO_CONTENT_LENGTH_UPLOAD' has been explicitly marked deprecated here
 2941 |                        CURL_DEPRECATED(7.55.0,
      |                        ^
/nix/store/za2zv3sp018x807vc5sq1fdc3036jjm1-curl-x86_64-unknown-linux-gnufilc0-8.14.1-dev/include/curl/curl.h:44:18: note: expanded from macro 'CURL_DEPRECATED'
   44 |   __attribute__((deprecated("since " # version ". " message)))
      |                  ^
curb_easy.c:3806:8: warning: 'CURLOPT_PROTOCOLS' is deprecated: since 7.85.0. Use CURLOPT_PROTOCOLS_STR [-Wdeprecated-declarations]
 3806 |   case CURLOPT_PROTOCOLS:
      |        ^
/nix/store/za2zv3sp018x807vc5sq1fdc3036jjm1-curl-x86_64-unknown-linux-gnufilc0-8.14.1-dev/include/curl/curl.h:1789:3: note: 'CURLOPT_PROTOCOLS' has been explicitly marked deprecated here
 1789 |   CURLOPTDEPRECATED(CURLOPT_PROTOCOLS, CURLOPTTYPE_LONG, 181,
      |   ^
/nix/store/za2zv3sp018x807vc5sq1fdc3036jjm1-curl-x86_64-unknown-linux-gnufilc0-8.14.1-dev/include/curl/curl.h:1124:43: note: expanded from macro 'CURLOPTDEPRECATED'
 1124 | #define CURLOPTDEPRECATED(na,t,nu,v,m) na CURL_DEPRECATED(v,m) = t + nu
      |                                           ^
/nix/store/za2zv3sp018x807vc5sq1fdc3036jjm1-curl-x86_64-unknown-linux-gnufilc0-8.14.1-dev/include/curl/curl.h:44:18: note: expanded from macro 'CURL_DEPRECATED'
   44 |   __attribute__((deprecated("since " # version ". " message)))
      |                  ^
curb_easy.c:3807:8: warning: 'CURLOPT_REDIR_PROTOCOLS' is deprecated: since 7.85.0. Use CURLOPT_REDIR_PROTOCOLS_STR [-Wdeprecated-declarations]
 3807 |   case CURLOPT_REDIR_PROTOCOLS:
      |        ^
/nix/store/za2zv3sp018x807vc5sq1fdc3036jjm1-curl-x86_64-unknown-linux-gnufilc0-8.14.1-dev/include/curl/curl.h:1795:3: note: 'CURLOPT_REDIR_PROTOCOLS' has been explicitly marked deprecated here
 1795 |   CURLOPTDEPRECATED(CURLOPT_REDIR_PROTOCOLS, CURLOPTTYPE_LONG, 182,
      |   ^
/nix/store/za2zv3sp018x807vc5sq1fdc3036jjm1-curl-x86_64-unknown-linux-gnufilc0-8.14.1-dev/include/curl/curl.h:1124:43: note: expanded from macro 'CURLOPTDEPRECATED'
 1124 | #define CURLOPTDEPRECATED(na,t,nu,v,m) na CURL_DEPRECATED(v,m) = t + nu
      |                                           ^
/nix/store/za2zv3sp018x807vc5sq1fdc3036jjm1-curl-x86_64-unknown-linux-gnufilc0-8.14.1-dev/include/curl/curl.h:44:18: note: expanded from macro 'CURL_DEPRECATED'
   44 |   __attribute__((deprecated("since " # version ". " message)))
      |                  ^
curb_easy.c:3947:10: error: incompatible integer to pointer conversion assigning to 'VALUE' (aka 'struct rb_value_unit_struct *') from 'ID' (aka 'unsigned long') [-Wint-conversion]
 3947 |   idCall = rb_intern("call");
      |          ^ ~~~~~~~~~~~~~~~~~
curb_easy.c:3948:10: error: incompatible integer to pointer conversion assigning to 'VALUE' (aka 'struct rb_value_unit_struct *') from 'ID' (aka 'unsigned long') [-Wint-conversion]
 3948 |   idJoin = rb_intern("join");
      |          ^ ~~~~~~~~~~~~~~~~~
23 warnings and 9 errors generated.
make: *** [Makefile:248: curb_easy.o] Error 1

make failed, exit code 2

Gem files will remain installed in /nix/store/xjn9mfckj0m0m60gx8ymfdh1bjd9svfz-ruby3.3-curb-1.0.9-x86_64-unknown-linux-gnufilc0/lib/ruby/gems/3.3.0/gems/curb-1.0.9 for inspection.
Results logged to /nix/store/xjn9mfckj0m0m60gx8ymfdh1bjd9svfz-ruby3.3-curb-1.0.9-x86_64-unknown-linux-gnufilc0/lib/ruby/gems/3.3.0/extensions/x86_64-linux/3.3.0/curb-1.0.9/gem_make.out
```

</details>

<details>
<summary>✅ <strong>curses</strong>: build failed</summary>

```
Running phase: unpackPhase
Unpacked gem: '/build/container/kxxr5dn0l0zllbfyifgp35003vqnwmsx-curses-1.5.0'
Running phase: patchPhase
Running phase: updateAutotoolsGnuConfigScriptsPhase
Updating Autotools / GNU config script to a newer upstream version: ./vendor/PDCurses/x11/config.sub
Updating Autotools / GNU config script to a newer upstream version: ./vendor/PDCurses/x11/config.guess
Running phase: updateAutotoolsGnuConfigScriptsPhase
Updating Autotools / GNU config script to a newer upstream version: ./vendor/PDCurses/x11/config.sub
Updating Autotools / GNU config script to a newer upstream version: ./vendor/PDCurses/x11/config.guess
Running phase: configurePhase
no configure script, doing nothing
Running phase: buildPhase
WARNING:  expected RubyGems version 3.6.6, was 3.6.2
WARNING:  open-ended dependency on bundler (>= 0, development) is not recommended
  use a bounded requirement, such as "~> x.y"
WARNING:  open-ended dependency on rake (>= 0, development) is not recommended
  use a bounded requirement, such as "~> x.y"
WARNING:  See https://guides.rubygems.org/specification-reference/ for help
  Successfully built RubyGem
  Name: curses
  Version: 1.5.0
  File: curses-1.5.0.gem
gem package built: curses-1.5.0.gem
Running phase: installPhase
buildFlags: 
WARNING:  You build with buildroot.
  Build root: /
  Bin dir: /nix/store/w6f9z4svjr1r71fj60cfbb7qm6p947x3-ruby3.3-curses-1.5.0-x86_64-unknown-linux-gnufilc0/lib/ruby/gems/3.3.0/bin
  Gem home: /nix/store/w6f9z4svjr1r71fj60cfbb7qm6p947x3-ruby3.3-curses-1.5.0-x86_64-unknown-linux-gnufilc0/lib/ruby/gems/3.3.0
  Plugins dir: /nix/store/w6f9z4svjr1r71fj60cfbb7qm6p947x3-ruby3.3-curses-1.5.0-x86_64-unknown-linux-gnufilc0/lib/ruby/gems/3.3.0/plugins
Building native extensions. This could take a while...
Successfully installed curses-1.5.0
1 gem installed
/nix/store/w6f9z4svjr1r71fj60cfbb7qm6p947x3-ruby3.3-curses-1.5.0-x86_64-unknown-linux-gnufilc0/lib/ruby/gems/3.3.0 /build/source
gems/curses-1.5.0/ext/curses/Makefile
extensions/x86_64-linux/3.3.0/curses-1.5.0/mkmf.log
extensions/x86_64-linux/3.3.0/curses-1.5.0/gem_make.out
removed 'cache/curses-1.5.0.gem'
removed directory 'cache'
/build/source
Running phase: fixupPhase
shrinking RPATHs of ELF executables and libraries in /nix/store/w6f9z4svjr1r71fj60cfbb7qm6p947x3-ruby3.3-curses-1.5.0-x86_64-unknown-linux-gnufilc0
shrinking /nix/store/w6f9z4svjr1r71fj60cfbb7qm6p947x3-ruby3.3-curses-1.5.0-x86_64-unknown-linux-gnufilc0/lib/ruby/gems/3.3.0/extensions/x86_64-linux/3.3.0/curses-1.5.0/curses.so
shrinking /nix/store/w6f9z4svjr1r71fj60cfbb7qm6p947x3-ruby3.3-curses-1.5.0-x86_64-unknown-linux-gnufilc0/lib/ruby/gems/3.3.0/gems/curses-1.5.0/lib/curses.so
checking for references to /build/ in /nix/store/w6f9z4svjr1r71fj60cfbb7qm6p947x3-ruby3.3-curses-1.5.0-x86_64-unknown-linux-gnufilc0...
patching script interpreter paths in /nix/store/w6f9z4svjr1r71fj60cfbb7qm6p947x3-ruby3.3-curses-1.5.0-x86_64-unknown-linux-gnufilc0
/nix/store/w6f9z4svjr1r71fj60cfbb7qm6p947x3-ruby3.3-curses-1.5.0-x86_64-unknown-linux-gnufilc0/lib/ruby/gems/3.3.0/gems/curses-1.5.0/sample/addch.rb: interpreter directive changed from "#!/usr/bin/env ruby" to "/nix/store/65in3amyafclxn1lg3yjb1v9a3ngk1rm-ruby-3.3.10-x86_64-unknown-linux-gnufilc0/bin/ruby"
/nix/store/w6f9z4svjr1r71fj60cfbb7qm6p947x3-ruby3.3-curses-1.5.0-x86_64-unknown-linux-gnufilc0/lib/ruby/gems/3.3.0/gems/curses-1.5.0/sample/colors.rb: interpreter directive changed from "#!/usr/bin/env ruby" to "/nix/store/65in3amyafclxn1lg3yjb1v9a3ngk1rm-ruby-3.3.10-x86_64-unknown-linux-gnufilc0/bin/ruby"
/nix/store/w6f9z4svjr1r71fj60cfbb7qm6p947x3-ruby3.3-curses-1.5.0-x86_64-unknown-linux-gnufilc0/lib/ruby/gems/3.3.0/gems/curses-1.5.0/sample/hello.rb: interpreter directive changed from "#!/usr/bin/env ruby" to "/nix/store/65in3amyafclxn1lg3yjb1v9a3ngk1rm-ruby-3.3.10-x86_64-unknown-linux-gnufilc0/bin/ruby"
/nix/store/w6f9z4svjr1r71fj60cfbb7qm6p947x3-ruby3.3-curses-1.5.0-x86_64-unknown-linux-gnufilc0/lib/ruby/gems/3.3.0/gems/curses-1.5.0/sample/menu.rb: interpreter directive changed from "#!/usr/bin/env ruby" to "/nix/store/65in3amyafclxn1lg3yjb1v9a3ngk1rm-ruby-3.3.10-x86_64-unknown-linux-gnufilc0/bin/ruby"
/nix/store/w6f9z4svjr1r71fj60cfbb7qm6p947x3-ruby3.3-curses-1.5.0-x86_64-unknown-linux-gnufilc0/lib/ruby/gems/3.3.0/gems/curses-1.5.0/sample/mouse.rb: interpreter directive changed from "#!/usr/bin/env ruby" to "/nix/store/65in3amyafclxn1lg3yjb1v9a3ngk1rm-ruby-3.3.10-x86_64-unknown-linux-gnufilc0/bin/ruby"
/nix/store/w6f9z4svjr1r71fj60cfbb7qm6p947x3-ruby3.3-curses-1.5.0-x86_64-unknown-linux-gnufilc0/lib/ruby/gems/3.3.0/gems/curses-1.5.0/sample/mouse_move.rb: interpreter directive changed from "#!/usr/bin/env ruby" to "/nix/store/65in3amyafclxn1lg3yjb1v9a3ngk1rm-ruby-3.3.10-x86_64-unknown-linux-gnufilc0/bin/ruby"
/nix/store/w6f9z4svjr1r71fj60cfbb7qm6p947x3-ruby3.3-curses-1.5.0-x86_64-unknown-linux-gnufilc0/lib/ruby/gems/3.3.0/gems/curses-1.5.0/sample/rain.rb: interpreter directive changed from "#!/usr/bin/env ruby" to "/nix/store/65in3amyafclxn1lg3yjb1v9a3ngk1rm-ruby-3.3.10-x86_64-unknown-linux-gnufilc0/bin/ruby"
/nix/store/w6f9z4svjr1r71fj60cfbb7qm6p947x3-ruby3.3-curses-1.5.0-x86_64-unknown-linux-gnufilc0/lib/ruby/gems/3.3.0/gems/curses-1.5.0/sample/view.rb: interpreter directive changed from "#!/usr/bin/env ruby" to "/nix/store/65in3amyafclxn1lg3yjb1v9a3ngk1rm-ruby-3.3.10-x86_64-unknown-linux-gnufilc0/bin/ruby"
/nix/store/w6f9z4svjr1r71fj60cfbb7qm6p947x3-ruby3.3-curses-1.5.0-x86_64-unknown-linux-gnufilc0/lib/ruby/gems/3.3.0/gems/curses-1.5.0/sample/view2.rb: interpreter directive changed from "#!/usr/bin/env ruby" to "/nix/store/65in3amyafclxn1lg3yjb1v9a3ngk1rm-ruby-3.3.10-x86_64-unknown-linux-gnufilc0/bin/ruby"
stripping (with command strip and flags -S -p) in  /nix/store/w6f9z4svjr1r71fj60cfbb7qm6p947x3-ruby3.3-curses-1.5.0-x86_64-unknown-linux-gnufilc0/lib /nix/store/w6f9z4svjr1r71fj60cfbb7qm6p947x3-ruby3.3-curses-1.5.0-x86_64-unknown-linux-gnufilc0/bin
rewriting symlink /nix/store/w6f9z4svjr1r71fj60cfbb7qm6p947x3-ruby3.3-curses-1.5.0-x86_64-unknown-linux-gnufilc0/nix-support/gem-meta/spec to be relative to /nix/store/w6f9z4svjr1r71fj60cfbb7qm6p947x3-ruby3.3-curses-1.5.0-x86_64-unknown-linux-gnufilc0
```

```
created 1 symlinks in user environment
```

```
Running phase: patchPhase
Running phase: updateAutotoolsGnuConfigScriptsPhase
Running phase: updateAutotoolsGnuConfigScriptsPhase
Running phase: configurePhase
no configure script, doing nothing
Running phase: buildPhase
no Makefile or custom buildPhase, doing nothing
Running phase: installPhase
Running phase: fixupPhase
shrinking RPATHs of ELF executables and libraries in /nix/store/9wmns1gzynbcs8k1bqmigsjfrvqfsbg6-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0
shrinking /nix/store/9wmns1gzynbcs8k1bqmigsjfrvqfsbg6-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0/bin/bundle
shrinking /nix/store/9wmns1gzynbcs8k1bqmigsjfrvqfsbg6-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0/bin/bundler
shrinking /nix/store/9wmns1gzynbcs8k1bqmigsjfrvqfsbg6-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0/bin/erb
shrinking /nix/store/9wmns1gzynbcs8k1bqmigsjfrvqfsbg6-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0/bin/gem
shrinking /nix/store/9wmns1gzynbcs8k1bqmigsjfrvqfsbg6-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0/bin/irb
shrinking /nix/store/9wmns1gzynbcs8k1bqmigsjfrvqfsbg6-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0/bin/racc
shrinking /nix/store/9wmns1gzynbcs8k1bqmigsjfrvqfsbg6-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0/bin/rake
shrinking /nix/store/9wmns1gzynbcs8k1bqmigsjfrvqfsbg6-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0/bin/rbs
shrinking /nix/store/9wmns1gzynbcs8k1bqmigsjfrvqfsbg6-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0/bin/rdbg
shrinking /nix/store/9wmns1gzynbcs8k1bqmigsjfrvqfsbg6-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0/bin/rdoc
shrinking /nix/store/9wmns1gzynbcs8k1bqmigsjfrvqfsbg6-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0/bin/ri
shrinking /nix/store/9wmns1gzynbcs8k1bqmigsjfrvqfsbg6-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0/bin/ruby
shrinking /nix/store/9wmns1gzynbcs8k1bqmigsjfrvqfsbg6-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0/bin/syntax_suggest
shrinking /nix/store/9wmns1gzynbcs8k1bqmigsjfrvqfsbg6-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0/bin/typeprof
checking for references to /build/ in /nix/store/9wmns1gzynbcs8k1bqmigsjfrvqfsbg6-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0...
patching script interpreter paths in /nix/store/9wmns1gzynbcs8k1bqmigsjfrvqfsbg6-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0
stripping (with command strip and flags -S -p) in  /nix/store/9wmns1gzynbcs8k1bqmigsjfrvqfsbg6-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0/bin
```

</details>

<details>
<summary>✅ <strong>digest-sha3</strong>: build succeeded</summary>

</details>

<details>
<summary>❌ <strong>do_sqlite3</strong>: do_common.c:481:47: error: incompatible pointer to integer conversion passing 'VALUE' (aka 'struct r...</summary>

```
/nix/store/65in3amyafclxn1lg3yjb1v9a3ngk1rm-ruby-3.3.10-x86_64-unknown-linux-gnufilc0/bin/ruby extconf.rb
checking for sqlite3.h... yes
checking for sqlite3_open() in -lsqlite3... yes
checking for localtime_r()... yes
checking for gmtime_r()... yes
checking for sqlite3_prepare_v2()... yes
checking for sqlite3_open_v2()... yes
checking for sqlite3_enable_load_extension()... yes
creating Makefile

current directory: /nix/store/jhyw6wyivllzlafqqlv1ng27f2kkk4mh-ruby3.3-do_sqlite3-0.10.17-x86_64-unknown-linux-gnufilc0/lib/ruby/gems/3.3.0/gems/do_sqlite3-0.10.17/ext/do_sqlite3
make DESTDIR\= sitearchdir\=./.gem.20251203-36-9fhwdt sitelibdir\=./.gem.20251203-36-9fhwdt clean

current directory: /nix/store/jhyw6wyivllzlafqqlv1ng27f2kkk4mh-ruby3.3-do_sqlite3-0.10.17-x86_64-unknown-linux-gnufilc0/lib/ruby/gems/3.3.0/gems/do_sqlite3-0.10.17/ext/do_sqlite3
make DESTDIR\= sitearchdir\=./.gem.20251203-36-9fhwdt sitelibdir\=./.gem.20251203-36-9fhwdt
compiling do_common.c
do_common.c:64:118: warning: implicit conversion loses integer precision: 'do_int64' (aka 'long long') to 'int' [-Wshorten-64-to-32]
   64 |   message = rb_funcall(cDO_Logger_Message, DO_ID_NEW, 3, string, rb_time_new(start->tv_sec, start->tv_usec), INT2NUM(duration));
      |                                                                                                              ~~~~~~~ ^~~~~~~~
do_common.c:69:127: warning: function 'data_objects_raise_error' could be declared with attribute 'noreturn' [-Wmissing-noreturn]
   69 | void data_objects_raise_error(VALUE self, const struct errcodes *errors, int errnum, VALUE message, VALUE query, VALUE state) {
      |                                                                                                                               ^
do_common.c:443:22: warning: incompatible pointer types passing 'ID *' (aka 'unsigned long *') to parameter of type 'VALUE *' (aka 'struct rb_value_unit_struct **') [-Wincompatible-pointer-types]
  443 |   rb_global_variable(&DO_ID_NEW_DATE);
      |                      ^~~~~~~~~~~~~~~
/nix/store/65in3amyafclxn1lg3yjb1v9a3ngk1rm-ruby-3.3.10-x86_64-unknown-linux-gnufilc0/include/ruby-3.3.0/ruby/internal/gc.h:418:32: note: passing argument to parameter here
  418 | void rb_global_variable(VALUE *);
      |                                ^
do_common.c:444:22: warning: incompatible pointer types passing 'ID *' (aka 'unsigned long *') to parameter of type 'VALUE *' (aka 'struct rb_value_unit_struct **') [-Wincompatible-pointer-types]
  444 |   rb_global_variable(&DO_ID_RATIONAL);
      |                      ^~~~~~~~~~~~~~~
/nix/store/65in3amyafclxn1lg3yjb1v9a3ngk1rm-ruby-3.3.10-x86_64-unknown-linux-gnufilc0/include/ruby-3.3.0/ruby/internal/gc.h:418:32: note: passing argument to parameter here
  418 | void rb_global_variable(VALUE *);
      |                                ^
do_common.c:445:22: warning: incompatible pointer types passing 'ID *' (aka 'unsigned long *') to parameter of type 'VALUE *' (aka 'struct rb_value_unit_struct **') [-Wincompatible-pointer-types]
  445 |   rb_global_variable(&DO_ID_CONST_GET);
      |                      ^~~~~~~~~~~~~~~~
/nix/store/65in3amyafclxn1lg3yjb1v9a3ngk1rm-ruby-3.3.10-x86_64-unknown-linux-gnufilc0/include/ruby-3.3.0/ruby/internal/gc.h:418:32: note: passing argument to parameter here
  418 | void rb_global_variable(VALUE *);
      |                                ^
do_common.c:446:22: warning: incompatible pointer types passing 'ID *' (aka 'unsigned long *') to parameter of type 'VALUE *' (aka 'struct rb_value_unit_struct **') [-Wincompatible-pointer-types]
  446 |   rb_global_variable(&DO_ID_ESCAPE);
      |                      ^~~~~~~~~~~~~
/nix/store/65in3amyafclxn1lg3yjb1v9a3ngk1rm-ruby-3.3.10-x86_64-unknown-linux-gnufilc0/include/ruby-3.3.0/ruby/internal/gc.h:418:32: note: passing argument to parameter here
  418 | void rb_global_variable(VALUE *);
      |                                ^
do_common.c:447:22: warning: incompatible pointer types passing 'ID *' (aka 'unsigned long *') to parameter of type 'VALUE *' (aka 'struct rb_value_unit_struct **') [-Wincompatible-pointer-types]
  447 |   rb_global_variable(&DO_ID_LOG);
      |                      ^~~~~~~~~~
/nix/store/65in3amyafclxn1lg3yjb1v9a3ngk1rm-ruby-3.3.10-x86_64-unknown-linux-gnufilc0/include/ruby-3.3.0/ruby/internal/gc.h:418:32: note: passing argument to parameter here
  418 | void rb_global_variable(VALUE *);
      |                                ^
do_common.c:448:22: warning: incompatible pointer types passing 'ID *' (aka 'unsigned long *') to parameter of type 'VALUE *' (aka 'struct rb_value_unit_struct **') [-Wincompatible-pointer-types]
  448 |   rb_global_variable(&DO_ID_NEW);
      |                      ^~~~~~~~~~
/nix/store/65in3amyafclxn1lg3yjb1v9a3ngk1rm-ruby-3.3.10-x86_64-unknown-linux-gnufilc0/include/ruby-3.3.0/ruby/internal/gc.h:418:32: note: passing argument to parameter here
  418 | void rb_global_variable(VALUE *);
      |                                ^
do_common.c:481:47: error: incompatible pointer to integer conversion passing 'VALUE' (aka 'struct rb_value_unit_struct *') to parameter of type 'int' [-Wint-conversion]
  481 |     return rb_float_new(rb_cstr_to_dbl(value, Qfalse));
      |                                               ^~~~~~
/nix/store/65in3amyafclxn1lg3yjb1v9a3ngk1rm-ruby-3.3.10-x86_64-unknown-linux-gnufilc0/include/ruby-3.3.0/ruby/internal/special_consts.h:59:25: note: expanded from macro 'Qfalse'
   59 | #define Qfalse          RUBY_Qfalse            /**< @old{RUBY_Qfalse} */
      |                         ^~~~~~~~~~~
/nix/store/65in3amyafclxn1lg3yjb1v9a3ngk1rm-ruby-3.3.10-x86_64-unknown-linux-gnufilc0/include/ruby-3.3.0/ruby/internal/special_consts.h:345:21: note: expanded from macro 'RUBY_Qfalse'
  345 | #define RUBY_Qfalse RBIMPL_CAST((VALUE)RUBY_Qfalse)
      |                     ^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
/nix/store/65in3amyafclxn1lg3yjb1v9a3ngk1rm-ruby-3.3.10-x86_64-unknown-linux-gnufilc0/include/ruby-3.3.0/ruby/internal/cast.h:31:28: note: expanded from macro 'RBIMPL_CAST'
   31 | # define RBIMPL_CAST(expr) (expr)
      |                            ^~~~~~
/nix/store/65in3amyafclxn1lg3yjb1v9a3ngk1rm-ruby-3.3.10-x86_64-unknown-linux-gnufilc0/include/ruby-3.3.0/ruby/internal/intern/object.h:486:44: note: passing argument to parameter 'mode' here
  486 | double rb_cstr_to_dbl(const char *str, int mode);
      |                                            ^
8 warnings and 1 error generated.
make: *** [Makefile:248: do_common.o] Error 1

make failed, exit code 2

Gem files will remain installed in /nix/store/jhyw6wyivllzlafqqlv1ng27f2kkk4mh-ruby3.3-do_sqlite3-0.10.17-x86_64-unknown-linux-gnufilc0/lib/ruby/gems/3.3.0/gems/do_sqlite3-0.10.17 for inspection.
Results logged to /nix/store/jhyw6wyivllzlafqqlv1ng27f2kkk4mh-ruby3.3-do_sqlite3-0.10.17-x86_64-unknown-linux-gnufilc0/lib/ruby/gems/3.3.0/extensions/x86_64-linux/3.3.0/do_sqlite3-0.10.17/gem_make.out
```

</details>

<details>
<summary>✅ <strong>ethon</strong>: build failed</summary>

```
copying path '/nix/store/ql3qvx9j0m960ilb28sgv6wbhpr17799-ethon-0.16.0.gem' from 'https://cache.nixos.org'...
Running phase: unpackPhase
Unpacked gem: '/build/container/ql3qvx9j0m960ilb28sgv6wbhpr17799-ethon-0.16.0'
Running phase: patchPhase
substituteStream() in derivation ruby3.3-ethon-0.16.0-x86_64-unknown-linux-gnufilc0: WARNING: '--replace' is deprecated, use --replace-{fail,warn,quiet}. (file 'lib/ethon/curls/settings.rb')
Running phase: updateAutotoolsGnuConfigScriptsPhase
Running phase: updateAutotoolsGnuConfigScriptsPhase
Running phase: configurePhase
no configure script, doing nothing
Running phase: buildPhase
WARNING:  expected RubyGems version 3.6.6, was 3.3.7
WARNING:  open-ended dependency on ffi (>= 1.15.0) is not recommended
  if ffi is semantically versioned, use:
    add_runtime_dependency "ffi", "~> 1.15", ">= 1.15.0"
WARNING:  make sure you specify the oldest ruby version constraint (like ">= 3.0") that you want your gem to support by setting the `required_ruby_version` gemspec attribute
WARNING:  See https://guides.rubygems.org/specification-reference/ for help
  Successfully built RubyGem
  Name: ethon
  Version: 0.16.0
  File: ethon-0.16.0.gem
gem package built: ethon-0.16.0.gem
Running phase: installPhase
buildFlags: 
WARNING:  You build with buildroot.
  Build root: /
  Bin dir: /nix/store/3dx3br9xc3l2156br89dp6xm8khswhhw-ruby3.3-ethon-0.16.0-x86_64-unknown-linux-gnufilc0/lib/ruby/gems/3.3.0/bin
  Gem home: /nix/store/3dx3br9xc3l2156br89dp6xm8khswhhw-ruby3.3-ethon-0.16.0-x86_64-unknown-linux-gnufilc0/lib/ruby/gems/3.3.0
  Plugins dir: /nix/store/3dx3br9xc3l2156br89dp6xm8khswhhw-ruby3.3-ethon-0.16.0-x86_64-unknown-linux-gnufilc0/lib/ruby/gems/3.3.0/plugins
Successfully installed ethon-0.16.0
1 gem installed
/nix/store/3dx3br9xc3l2156br89dp6xm8khswhhw-ruby3.3-ethon-0.16.0-x86_64-unknown-linux-gnufilc0/lib/ruby/gems/3.3.0 /build/source
removed 'cache/ethon-0.16.0.gem'
removed directory 'cache'
/build/source
Running phase: fixupPhase
shrinking RPATHs of ELF executables and libraries in /nix/store/3dx3br9xc3l2156br89dp6xm8khswhhw-ruby3.3-ethon-0.16.0-x86_64-unknown-linux-gnufilc0
checking for references to /build/ in /nix/store/3dx3br9xc3l2156br89dp6xm8khswhhw-ruby3.3-ethon-0.16.0-x86_64-unknown-linux-gnufilc0...
patching script interpreter paths in /nix/store/3dx3br9xc3l2156br89dp6xm8khswhhw-ruby3.3-ethon-0.16.0-x86_64-unknown-linux-gnufilc0
stripping (with command strip and flags -S -p) in  /nix/store/3dx3br9xc3l2156br89dp6xm8khswhhw-ruby3.3-ethon-0.16.0-x86_64-unknown-linux-gnufilc0/lib /nix/store/3dx3br9xc3l2156br89dp6xm8khswhhw-ruby3.3-ethon-0.16.0-x86_64-unknown-linux-gnufilc0/bin
rewriting symlink /nix/store/3dx3br9xc3l2156br89dp6xm8khswhhw-ruby3.3-ethon-0.16.0-x86_64-unknown-linux-gnufilc0/nix-support/gem-meta/spec to be relative to /nix/store/3dx3br9xc3l2156br89dp6xm8khswhhw-ruby3.3-ethon-0.16.0-x86_64-unknown-linux-gnufilc0
```

```
created 5 symlinks in user environment
```

```
Running phase: patchPhase
Running phase: updateAutotoolsGnuConfigScriptsPhase
Running phase: updateAutotoolsGnuConfigScriptsPhase
Running phase: configurePhase
no configure script, doing nothing
Running phase: buildPhase
no Makefile or custom buildPhase, doing nothing
Running phase: installPhase
Running phase: fixupPhase
shrinking RPATHs of ELF executables and libraries in /nix/store/cjf0ri81gpbvqd0zvzsirv94gmsiq9fp-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0
shrinking /nix/store/cjf0ri81gpbvqd0zvzsirv94gmsiq9fp-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0/bin/bundle
shrinking /nix/store/cjf0ri81gpbvqd0zvzsirv94gmsiq9fp-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0/bin/bundler
shrinking /nix/store/cjf0ri81gpbvqd0zvzsirv94gmsiq9fp-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0/bin/erb
shrinking /nix/store/cjf0ri81gpbvqd0zvzsirv94gmsiq9fp-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0/bin/gem
shrinking /nix/store/cjf0ri81gpbvqd0zvzsirv94gmsiq9fp-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0/bin/irb
shrinking /nix/store/cjf0ri81gpbvqd0zvzsirv94gmsiq9fp-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0/bin/racc
shrinking /nix/store/cjf0ri81gpbvqd0zvzsirv94gmsiq9fp-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0/bin/rake
shrinking /nix/store/cjf0ri81gpbvqd0zvzsirv94gmsiq9fp-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0/bin/rbs
shrinking /nix/store/cjf0ri81gpbvqd0zvzsirv94gmsiq9fp-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0/bin/rdbg
shrinking /nix/store/cjf0ri81gpbvqd0zvzsirv94gmsiq9fp-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0/bin/rdoc
shrinking /nix/store/cjf0ri81gpbvqd0zvzsirv94gmsiq9fp-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0/bin/ri
shrinking /nix/store/cjf0ri81gpbvqd0zvzsirv94gmsiq9fp-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0/bin/ruby
shrinking /nix/store/cjf0ri81gpbvqd0zvzsirv94gmsiq9fp-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0/bin/syntax_suggest
shrinking /nix/store/cjf0ri81gpbvqd0zvzsirv94gmsiq9fp-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0/bin/typeprof
checking for references to /build/ in /nix/store/cjf0ri81gpbvqd0zvzsirv94gmsiq9fp-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0...
patching script interpreter paths in /nix/store/cjf0ri81gpbvqd0zvzsirv94gmsiq9fp-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0
stripping (with command strip and flags -S -p) in  /nix/store/cjf0ri81gpbvqd0zvzsirv94gmsiq9fp-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0/bin
```

</details>

<details>
<summary>❌ <strong>eventmachine</strong>: rubymain.cpp:116:4: error: no matching function for call to 'rb_funcall'</summary>

```
/nix/store/65in3amyafclxn1lg3yjb1v9a3ngk1rm-ruby-3.3.10-x86_64-unknown-linux-gnufilc0/include/ruby-3.3.0/ruby/internal/eval.h:131:7: note: candidate function not viable: no known conversion from 'VALUE' (aka 'rb_value_unit_struct *') to 'ID' (aka 'unsigned long') for 2nd argument
  131 | VALUE rb_funcall(VALUE recv, ID mid, int n, ...);
      |       ^                      ~~~~~~
rubymain.cpp:168:4: error: no matching function for call to 'rb_funcall'
  168 |                         rb_funcall (conn, Intern_ssl_handshake_completed, 0);
      |                         ^~~~~~~~~~
/nix/store/65in3amyafclxn1lg3yjb1v9a3ngk1rm-ruby-3.3.10-x86_64-unknown-linux-gnufilc0/include/ruby-3.3.0/ruby/internal/eval.h:131:7: note: candidate function not viable: no known conversion from 'VALUE' (aka 'rb_value_unit_struct *') to 'ID' (aka 'unsigned long') for 2nd argument
  131 | VALUE rb_funcall(VALUE recv, ID mid, int n, ...);
      |       ^                      ~~~~~~
rubymain.cpp:174:26: error: no matching function for call to 'rb_funcall'
  174 |                         VALUE should_accept = rb_funcall (conn, Intern_ssl_verify_peer, 1, rb_str_new(data_str, data_num));
      |                                               ^~~~~~~~~~
/nix/store/65in3amyafclxn1lg3yjb1v9a3ngk1rm-ruby-3.3.10-x86_64-unknown-linux-gnufilc0/include/ruby-3.3.0/ruby/internal/eval.h:131:7: note: candidate function not viable: no known conversion from 'VALUE' (aka 'rb_value_unit_struct *') to 'ID' (aka 'unsigned long') for 2nd argument
  131 | VALUE rb_funcall(VALUE recv, ID mid, int n, ...);
      |       ^                      ~~~~~~
rubymain.cpp:183:4: error: no matching function for call to 'rb_funcall'
  183 |                         rb_funcall (conn, Intern_proxy_target_unbound, 0);
      |                         ^~~~~~~~~~
/nix/store/65in3amyafclxn1lg3yjb1v9a3ngk1rm-ruby-3.3.10-x86_64-unknown-linux-gnufilc0/include/ruby-3.3.0/ruby/internal/eval.h:131:7: note: candidate function not viable: no known conversion from 'VALUE' (aka 'rb_value_unit_struct *') to 'ID' (aka 'unsigned long') for 2nd argument
  131 | VALUE rb_funcall(VALUE recv, ID mid, int n, ...);
      |       ^                      ~~~~~~
rubymain.cpp:189:4: error: no matching function for call to 'rb_funcall'
  189 |                         rb_funcall (conn, Intern_proxy_completed, 0);
      |                         ^~~~~~~~~~
/nix/store/65in3amyafclxn1lg3yjb1v9a3ngk1rm-ruby-3.3.10-x86_64-unknown-linux-gnufilc0/include/ruby-3.3.0/ruby/internal/eval.h:131:7: note: candidate function not viable: no known conversion from 'VALUE' (aka 'rb_value_unit_struct *') to 'ID' (aka 'unsigned long') for 2nd argument
  131 | VALUE rb_funcall(VALUE recv, ID mid, int n, ...);
      |       ^                      ~~~~~~
rubymain.cpp:201:24: error: no matching function for call to 'rb_ivar_get'
  201 |         VALUE error_handler = rb_ivar_get(EmModule, Intern_at_error_handler);
      |                               ^~~~~~~~~~~
/nix/store/65in3amyafclxn1lg3yjb1v9a3ngk1rm-ruby-3.3.10-x86_64-unknown-linux-gnufilc0/include/ruby-3.3.0/ruby/internal/intern/variable.h:228:7: note: candidate function not viable: no known conversion from 'VALUE' (aka 'rb_value_unit_struct *') to 'ID' (aka 'unsigned long') for 2nd argument
  228 | VALUE rb_ivar_get(VALUE obj, ID name);
      |       ^                      ~~~~~~~
rubymain.cpp:202:2: error: no matching function for call to 'rb_funcall'
  202 |         rb_funcall (error_handler, Intern_call, 1, err);
      |         ^~~~~~~~~~
/nix/store/65in3amyafclxn1lg3yjb1v9a3ngk1rm-ruby-3.3.10-x86_64-unknown-linux-gnufilc0/include/ruby-3.3.0/ruby/internal/eval.h:131:7: note: candidate function not viable: no known conversion from 'VALUE' (aka 'rb_value_unit_struct *') to 'ID' (aka 'unsigned long') for 2nd argument
  131 | VALUE rb_funcall(VALUE recv, ID mid, int n, ...);
      |       ^                      ~~~~~~
rubymain.cpp:217:7: error: no matching function for call to 'rb_ivar_defined'
  217 |         if (!rb_ivar_defined(EmModule, Intern_at_error_handler))
      |              ^~~~~~~~~~~~~~~
/nix/store/65in3amyafclxn1lg3yjb1v9a3ngk1rm-ruby-3.3.10-x86_64-unknown-linux-gnufilc0/include/ruby-3.3.0/ruby/internal/intern/variable.h:254:7: note: candidate function not viable: no known conversion from 'VALUE' (aka 'rb_value_unit_struct *') to 'ID' (aka 'unsigned long') for 2nd argument
  254 | VALUE rb_ivar_defined(VALUE obj, ID name);
      |       ^                          ~~~~~~~
rubymain.cpp:220:3: warning: 'rb_rescue' is deprecated: Use of ANYARGS in this function is deprecated [-Wdeprecated-declarations]
  220 |                 rb_rescue((VALUE (*)(ANYARGS))event_callback, (VALUE)&e, (VALUE (*)(ANYARGS))event_error_handler, Qnil);
      |                 ^
/nix/store/65in3amyafclxn1lg3yjb1v9a3ngk1rm-ruby-3.3.10-x86_64-unknown-linux-gnufilc0/include/ruby-3.3.0/ruby/backward/cxxanyargs.hpp:246:1: note: 'rb_rescue' has been explicitly marked deprecated here
  246 | RUBY_CXX_DEPRECATED("Use of ANYARGS in this function is deprecated")
      | ^
/nix/store/65in3amyafclxn1lg3yjb1v9a3ngk1rm-ruby-3.3.10-x86_64-unknown-linux-gnufilc0/include/ruby-3.3.0/ruby/backward/2/attributes.h:79:35: note: expanded from macro 'RUBY_CXX_DEPRECATED'
   79 | #define RUBY_CXX_DEPRECATED(mseg) RBIMPL_ATTR_DEPRECATED((mseg))
      |                                   ^
/nix/store/65in3amyafclxn1lg3yjb1v9a3ngk1rm-ruby-3.3.10-x86_64-unknown-linux-gnufilc0/include/ruby-3.3.0/ruby/internal/attr/deprecated.h:36:53: note: expanded from macro 'RBIMPL_ATTR_DEPRECATED'
   36 | # define RBIMPL_ATTR_DEPRECATED(msg) __attribute__((__deprecated__ msg))
      |                                                     ^
rubymain.cpp:229:16: error: no matching function for call to 'rb_ivar_get'
  229 |         EmConnsHash = rb_ivar_get (EmModule, Intern_at_conns);
      |                       ^~~~~~~~~~~
/nix/store/65in3amyafclxn1lg3yjb1v9a3ngk1rm-ruby-3.3.10-x86_64-unknown-linux-gnufilc0/include/ruby-3.3.0/ruby/internal/intern/variable.h:228:7: note: candidate function not viable: no known conversion from 'VALUE' (aka 'rb_value_unit_struct *') to 'ID' (aka 'unsigned long') for 2nd argument
  228 | VALUE rb_ivar_get(VALUE obj, ID name);
      |       ^                      ~~~~~~~
rubymain.cpp:230:17: error: no matching function for call to 'rb_ivar_get'
  230 |         EmTimersHash = rb_ivar_get (EmModule, Intern_at_timers);
      |                        ^~~~~~~~~~~
/nix/store/65in3amyafclxn1lg3yjb1v9a3ngk1rm-ruby-3.3.10-x86_64-unknown-linux-gnufilc0/include/ruby-3.3.0/ruby/internal/intern/variable.h:228:7: note: candidate function not viable: no known conversion from 'VALUE' (aka 'rb_value_unit_struct *') to 'ID' (aka 'unsigned long') for 2nd argument
  228 | VALUE rb_ivar_get(VALUE obj, ID name);
      |       ^                      ~~~~~~~
rubymain.cpp:1220:8: error: incompatible integer to pointer conversion assigning to 'VALUE' (aka 'rb_value_unit_struct *') from 'int'
 1220 |         arg = (NIL_P(arg)) ? -1 : NUM2INT (arg);
      |               ^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
fatal error: too many errors emitted, stopping now [-ferror-limit=]
1 warning and 20 errors generated.
make: *** [Makefile:240: rubymain.o] Error 1

make failed, exit code 2

Gem files will remain installed in /nix/store/jwnyf8x68ap5vnbgpjicf8fhfqjih1jr-ruby3.3-eventmachine-1.2.7-x86_64-unknown-linux-gnufilc0/lib/ruby/gems/3.3.0/gems/eventmachine-1.2.7 for inspection.
Results logged to /nix/store/jwnyf8x68ap5vnbgpjicf8fhfqjih1jr-ruby3.3-eventmachine-1.2.7-x86_64-unknown-linux-gnufilc0/lib/ruby/gems/3.3.0/extensions/x86_64-linux/3.3.0/eventmachine-1.2.7/gem_make.out
```

</details>

<details>
<summary>✅ <strong>ffi</strong>: build succeeded</summary>

</details>

<details>
<summary>❌ <strong>fiddle</strong>: fiddle.c:682:47: error: incompatible pointer to integer conversion passing 'VALUE' (aka 'struct rb_v...</summary>

```

current directory: /nix/store/3sd6rd7w5xzhh3bnsj7qn8zy1igjb94i-ruby3.3-fiddle-1.1.6-x86_64-unknown-linux-gnufilc0/lib/ruby/gems/3.3.0/gems/fiddle-1.1.6/ext/fiddle
make DESTDIR\= sitearchdir\=./.gem.20251203-36-w2fllb sitelibdir\=./.gem.20251203-36-w2fllb clean

current directory: /nix/store/3sd6rd7w5xzhh3bnsj7qn8zy1igjb94i-ruby3.3-fiddle-1.1.6-x86_64-unknown-linux-gnufilc0/lib/ruby/gems/3.3.0/gems/fiddle-1.1.6/ext/fiddle
make DESTDIR\= sitearchdir\=./.gem.20251203-36-w2fllb sitelibdir\=./.gem.20251203-36-w2fllb
compiling closure.c
closure.c:260:62: warning: format specifies type 'long' but the argument has type 'VALUE' (aka 'struct rb_value_unit_struct *') [-Wformat]
  260 |         rb_raise(rb_eArgError, "already freed: %+"PRIsVALUE, self);
      |                                                ~~~~~~~~~~~~  ^~~~
1 warning generated.
compiling conversions.c
compiling fiddle.c
fiddle.c:682:47: error: incompatible pointer to integer conversion passing 'VALUE' (aka 'struct rb_value_unit_struct *') to parameter of type 'int' [-Wint-conversion]
  682 |     rb_define_const(mFiddle, "Qtrue", INT2NUM(Qtrue));
      |                                               ^~~~~
/nix/store/65in3amyafclxn1lg3yjb1v9a3ngk1rm-ruby-3.3.10-x86_64-unknown-linux-gnufilc0/include/ruby-3.3.0/ruby/internal/special_consts.h:61:25: note: expanded from macro 'Qtrue'
   61 | #define Qtrue           RUBY_Qtrue             /**< @old{RUBY_Qtrue} */
      |                         ^~~~~~~~~~
/nix/store/65in3amyafclxn1lg3yjb1v9a3ngk1rm-ruby-3.3.10-x86_64-unknown-linux-gnufilc0/include/ruby-3.3.0/ruby/internal/special_consts.h:346:21: note: expanded from macro 'RUBY_Qtrue'
  346 | #define RUBY_Qtrue  RBIMPL_CAST((VALUE)RUBY_Qtrue)
      |                     ^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
/nix/store/65in3amyafclxn1lg3yjb1v9a3ngk1rm-ruby-3.3.10-x86_64-unknown-linux-gnufilc0/include/ruby-3.3.0/ruby/internal/cast.h:31:28: note: expanded from macro 'RBIMPL_CAST'
   31 | # define RBIMPL_CAST(expr) (expr)
      |                            ^~~~~~
/nix/store/65in3amyafclxn1lg3yjb1v9a3ngk1rm-ruby-3.3.10-x86_64-unknown-linux-gnufilc0/include/ruby-3.3.0/ruby/internal/arithmetic/int.h:239:23: note: passing argument to parameter 'v' here
  239 | rb_int2num_inline(int v)
      |                       ^
fiddle.c:688:48: error: incompatible pointer to integer conversion passing 'VALUE' (aka 'struct rb_value_unit_struct *') to parameter of type 'int' [-Wint-conversion]
  688 |     rb_define_const(mFiddle, "Qfalse", INT2NUM(Qfalse));
      |                                                ^~~~~~
/nix/store/65in3amyafclxn1lg3yjb1v9a3ngk1rm-ruby-3.3.10-x86_64-unknown-linux-gnufilc0/include/ruby-3.3.0/ruby/internal/special_consts.h:59:25: note: expanded from macro 'Qfalse'
   59 | #define Qfalse          RUBY_Qfalse            /**< @old{RUBY_Qfalse} */
      |                         ^~~~~~~~~~~
/nix/store/65in3amyafclxn1lg3yjb1v9a3ngk1rm-ruby-3.3.10-x86_64-unknown-linux-gnufilc0/include/ruby-3.3.0/ruby/internal/special_consts.h:345:21: note: expanded from macro 'RUBY_Qfalse'
  345 | #define RUBY_Qfalse RBIMPL_CAST((VALUE)RUBY_Qfalse)
      |                     ^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
/nix/store/65in3amyafclxn1lg3yjb1v9a3ngk1rm-ruby-3.3.10-x86_64-unknown-linux-gnufilc0/include/ruby-3.3.0/ruby/internal/cast.h:31:28: note: expanded from macro 'RBIMPL_CAST'
   31 | # define RBIMPL_CAST(expr) (expr)
      |                            ^~~~~~
/nix/store/65in3amyafclxn1lg3yjb1v9a3ngk1rm-ruby-3.3.10-x86_64-unknown-linux-gnufilc0/include/ruby-3.3.0/ruby/internal/arithmetic/int.h:239:23: note: passing argument to parameter 'v' here
  239 | rb_int2num_inline(int v)
      |                       ^
fiddle.c:694:46: error: incompatible pointer to integer conversion passing 'VALUE' (aka 'struct rb_value_unit_struct *') to parameter of type 'int' [-Wint-conversion]
  694 |     rb_define_const(mFiddle, "Qnil", INT2NUM(Qnil));
      |                                              ^~~~
/nix/store/65in3amyafclxn1lg3yjb1v9a3ngk1rm-ruby-3.3.10-x86_64-unknown-linux-gnufilc0/include/ruby-3.3.0/ruby/internal/special_consts.h:60:25: note: expanded from macro 'Qnil'
   60 | #define Qnil            RUBY_Qnil              /**< @old{RUBY_Qnil} */
      |                         ^~~~~~~~~
/nix/store/65in3amyafclxn1lg3yjb1v9a3ngk1rm-ruby-3.3.10-x86_64-unknown-linux-gnufilc0/include/ruby-3.3.0/ruby/internal/special_consts.h:347:21: note: expanded from macro 'RUBY_Qnil'
  347 | #define RUBY_Qnil   RBIMPL_CAST((VALUE)RUBY_Qnil)
      |                     ^~~~~~~~~~~~~~~~~~~~~~~~~~~~~
/nix/store/65in3amyafclxn1lg3yjb1v9a3ngk1rm-ruby-3.3.10-x86_64-unknown-linux-gnufilc0/include/ruby-3.3.0/ruby/internal/cast.h:31:28: note: expanded from macro 'RBIMPL_CAST'
   31 | # define RBIMPL_CAST(expr) (expr)
      |                            ^~~~~~
/nix/store/65in3amyafclxn1lg3yjb1v9a3ngk1rm-ruby-3.3.10-x86_64-unknown-linux-gnufilc0/include/ruby-3.3.0/ruby/internal/arithmetic/int.h:239:23: note: passing argument to parameter 'v' here
  239 | rb_int2num_inline(int v)
      |                       ^
fiddle.c:700:48: error: incompatible pointer to integer conversion passing 'VALUE' (aka 'struct rb_value_unit_struct *') to parameter of type 'int' [-Wint-conversion]
  700 |     rb_define_const(mFiddle, "Qundef", INT2NUM(Qundef));
      |                                                ^~~~~~
/nix/store/65in3amyafclxn1lg3yjb1v9a3ngk1rm-ruby-3.3.10-x86_64-unknown-linux-gnufilc0/include/ruby-3.3.0/ruby/internal/special_consts.h:62:25: note: expanded from macro 'Qundef'
   62 | #define Qundef          RUBY_Qundef            /**< @old{RUBY_Qundef} */
      |                         ^~~~~~~~~~~
/nix/store/65in3amyafclxn1lg3yjb1v9a3ngk1rm-ruby-3.3.10-x86_64-unknown-linux-gnufilc0/include/ruby-3.3.0/ruby/internal/special_consts.h:348:21: note: expanded from macro 'RUBY_Qundef'
  348 | #define RUBY_Qundef RBIMPL_CAST((VALUE)RUBY_Qundef)
      |                     ^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
/nix/store/65in3amyafclxn1lg3yjb1v9a3ngk1rm-ruby-3.3.10-x86_64-unknown-linux-gnufilc0/include/ruby-3.3.0/ruby/internal/cast.h:31:28: note: expanded from macro 'RBIMPL_CAST'
   31 | # define RBIMPL_CAST(expr) (expr)
      |                            ^~~~~~
/nix/store/65in3amyafclxn1lg3yjb1v9a3ngk1rm-ruby-3.3.10-x86_64-unknown-linux-gnufilc0/include/ruby-3.3.0/ruby/internal/arithmetic/int.h:239:23: note: passing argument to parameter 'v' here
  239 | rb_int2num_inline(int v)
      |                       ^
4 errors generated.
make: *** [Makefile:249: fiddle.o] Error 1

make failed, exit code 2

Gem files will remain installed in /nix/store/3sd6rd7w5xzhh3bnsj7qn8zy1igjb94i-ruby3.3-fiddle-1.1.6-x86_64-unknown-linux-gnufilc0/lib/ruby/gems/3.3.0/gems/fiddle-1.1.6 for inspection.
Results logged to /nix/store/3sd6rd7w5xzhh3bnsj7qn8zy1igjb94i-ruby3.3-fiddle-1.1.6-x86_64-unknown-linux-gnufilc0/lib/ruby/gems/3.3.0/extensions/x86_64-linux/3.3.0/fiddle-1.1.6/gem_make.out
```

</details>

<details>
<summary>❌ <strong>google-protobuf</strong>: build failed</summary>

</details>

<details>
<summary>❌ <strong>gpgme</strong>: build failed</summary>

</details>

<details>
<summary>❌ <strong>grpc</strong>: build failed</summary>

</details>

<details>
<summary>❌ <strong>hpricot</strong>: build failed</summary>

```
Running phase: unpackPhase
Unpacked gem: '/build/container/ap4ig7k48cr4a93rjlwc7gg6blrwbg9m-hpricot-0.8.6'
Running phase: patchPhase
applying patch /nix/store/7qfd75b7ysnx2rfqllwqka3cn7fspsq6-hpricot-fix-incompatible-function-pointer-conversion.patch
patching file ext/fast_xs/fast_xs.c
patching file ext/hpricot_scan/hpricot_scan.c
patching file ext/hpricot_scan/hpricot_scan.rl
Running phase: updateAutotoolsGnuConfigScriptsPhase
Running phase: updateAutotoolsGnuConfigScriptsPhase
Running phase: configurePhase
no configure script, doing nothing
Running phase: buildPhase
WARNING:  expected RubyGems version 3.6.6, was 1.8.6
WARNING:  licenses is empty, but is recommended. Use an license identifier from
https://spdx.org/licenses or 'Nonstandard' for a nonstandard license,
or set it to nil if you don't want to specify a license.
WARNING:  description and summary are identical
WARNING:  make sure you specify the oldest ruby version constraint (like ">= 3.0") that you want your gem to support by setting the `required_ruby_version` gemspec attribute
WARNING:  See https://guides.rubygems.org/specification-reference/ for help
  Successfully built RubyGem
  Name: hpricot
  Version: 0.8.6
  File: hpricot-0.8.6.gem
gem package built: hpricot-0.8.6.gem
Running phase: installPhase
buildFlags: 
WARNING:  You build with buildroot.
  Build root: /
  Bin dir: /nix/store/16hdl2i0lwddgcqm3nxsny278m8058sb-ruby3.3-hpricot-0.8.6-x86_64-unknown-linux-gnufilc0/lib/ruby/gems/3.3.0/bin
  Gem home: /nix/store/16hdl2i0lwddgcqm3nxsny278m8058sb-ruby3.3-hpricot-0.8.6-x86_64-unknown-linux-gnufilc0/lib/ruby/gems/3.3.0
  Plugins dir: /nix/store/16hdl2i0lwddgcqm3nxsny278m8058sb-ruby3.3-hpricot-0.8.6-x86_64-unknown-linux-gnufilc0/lib/ruby/gems/3.3.0/plugins
Building native extensions. This could take a while...
```

</details>

<details>
<summary>❌ <strong>iconv</strong>: iconv.c:366:17: error: invalid operands to binary expression ('VALUE' (aka 'struct rb_value_unit_str...</summary>

```
      |                                   ~~~~~~~~~~ ^ ~~
iconv.c:374:27: error: invalid operands to binary expression ('VALUE' (aka 'struct rb_value_unit_struct *') and 'int')
  374 |     if (cd && iconv_close(VALUE2ICONV(cd)) == -1)
      |                           ^~~~~~~~~~~~~~~
iconv.c:146:46: note: expanded from macro 'VALUE2ICONV'
  146 | #define VALUE2ICONV(v) ((iconv_t)((VALUE)(v) ^ -1))
      |                                   ~~~~~~~~~~ ^ ~~
iconv.c:486:5: warning: 'RB_OBJ_INFECT' is deprecated: taintedness turned out to be a wrong idea. [-Wdeprecated-declarations]
  486 |     OBJ_INFECT(ret, str);
      |     ^
/nix/store/65in3amyafclxn1lg3yjb1v9a3ngk1rm-ruby-3.3.10-x86_64-unknown-linux-gnufilc0/include/ruby-3.3.0/ruby/internal/fl_type.h:139:25: note: expanded from macro 'OBJ_INFECT'
  139 | #define OBJ_INFECT      RB_OBJ_INFECT      /**< @old{RB_OBJ_INFECT} */
      |                         ^
/nix/store/65in3amyafclxn1lg3yjb1v9a3ngk1rm-ruby-3.3.10-x86_64-unknown-linux-gnufilc0/include/ruby-3.3.0/ruby/internal/fl_type.h:849:1: note: 'RB_OBJ_INFECT' has been explicitly marked deprecated here
  849 | RBIMPL_ATTR_DEPRECATED(("taintedness turned out to be a wrong idea."))
      | ^
/nix/store/65in3amyafclxn1lg3yjb1v9a3ngk1rm-ruby-3.3.10-x86_64-unknown-linux-gnufilc0/include/ruby-3.3.0/ruby/internal/attr/deprecated.h:36:53: note: expanded from macro 'RBIMPL_ATTR_DEPRECATED'
   36 | # define RBIMPL_ATTR_DEPRECATED(msg) __attribute__((__deprecated__ msg))
      |                                                     ^
iconv.c:579:4: warning: 'RB_OBJ_INFECT' is deprecated: taintedness turned out to be a wrong idea. [-Wdeprecated-declarations]
  579 |                         OBJ_INFECT(ret, str);
      |                         ^
/nix/store/65in3amyafclxn1lg3yjb1v9a3ngk1rm-ruby-3.3.10-x86_64-unknown-linux-gnufilc0/include/ruby-3.3.0/ruby/internal/fl_type.h:139:25: note: expanded from macro 'OBJ_INFECT'
  139 | #define OBJ_INFECT      RB_OBJ_INFECT      /**< @old{RB_OBJ_INFECT} */
      |                         ^
/nix/store/65in3amyafclxn1lg3yjb1v9a3ngk1rm-ruby-3.3.10-x86_64-unknown-linux-gnufilc0/include/ruby-3.3.0/ruby/internal/fl_type.h:849:1: note: 'RB_OBJ_INFECT' has been explicitly marked deprecated here
  849 | RBIMPL_ATTR_DEPRECATED(("taintedness turned out to be a wrong idea."))
      | ^
/nix/store/65in3amyafclxn1lg3yjb1v9a3ngk1rm-ruby-3.3.10-x86_64-unknown-linux-gnufilc0/include/ruby-3.3.0/ruby/internal/attr/deprecated.h:36:53: note: expanded from macro 'RBIMPL_ATTR_DEPRECATED'
   36 | # define RBIMPL_ATTR_DEPRECATED(msg) __attribute__((__deprecated__ msg))
      |                                                     ^
iconv.c:747:30: error: invalid operands to binary expression ('VALUE' (aka 'struct rb_value_unit_struct *') and 'int')
  747 |     DATA_PTR(self) = (void *)ICONV2VALUE(iconv_create(to, from, &opt, &idx));
      |                              ^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
iconv.c:147:36: note: expanded from macro 'ICONV2VALUE'
  147 | #define ICONV2VALUE(c) ((VALUE)(c) ^ -1)
      |                         ~~~~~~~~~~ ^ ~~
iconv.c:771:10: error: invalid operands to binary expression ('VALUE' (aka 'struct rb_value_unit_struct *') and 'int')
  771 |     cd = ICONV2VALUE(iconv_create(to, from, &opt, &idx));
      |          ^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
iconv.c:147:36: note: expanded from macro 'ICONV2VALUE'
  147 | #define ICONV2VALUE(c) ((VALUE)(c) ^ -1)
      |                         ~~~~~~~~~~ ^ ~~
iconv.c:838:64: error: invalid operands to binary expression ('VALUE' (aka 'struct rb_value_unit_struct *') and 'int')
  838 |     return rb_ensure(iconv_s_convert, (VALUE)&arg, iconv_free, ICONV2VALUE(arg.cd));
      |                                                                ^~~~~~~~~~~~~~~~~~~
iconv.c:147:36: note: expanded from macro 'ICONV2VALUE'
  147 | #define ICONV2VALUE(c) ((VALUE)(c) ^ -1)
      |                         ~~~~~~~~~~ ^ ~~
iconv.c:859:64: error: invalid operands to binary expression ('VALUE' (aka 'struct rb_value_unit_struct *') and 'int')
  859 |     return rb_ensure(iconv_s_convert, (VALUE)&arg, iconv_free, ICONV2VALUE(arg.cd));
      |                                                                ^~~~~~~~~~~~~~~~~~~
iconv.c:147:36: note: expanded from macro 'ICONV2VALUE'
  147 | #define ICONV2VALUE(c) ((VALUE)(c) ^ -1)
      |                         ~~~~~~~~~~ ^ ~~
iconv.c:960:18: error: invalid operands to binary expression ('VALUE' (aka 'struct rb_value_unit_struct *') and 'int')
  960 |     iconv_t cd = VALUE2ICONV((VALUE)DATA_PTR(self));
      |                  ^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
iconv.c:146:46: note: expanded from macro 'VALUE2ICONV'
  146 | #define VALUE2ICONV(v) ((iconv_t)((VALUE)(v) ^ -1))
      |                                   ~~~~~~~~~~ ^ ~~
iconv.c:1043:26: error: invalid operands to binary expression ('VALUE' (aka 'struct rb_value_unit_struct *') and 'int')
 1043 |     return iconv_convert(VALUE2ICONV(cd), str, start, length, ICONV_ENCODING_GET(self), NULL);
      |                          ^~~~~~~~~~~~~~~
iconv.c:146:46: note: expanded from macro 'VALUE2ICONV'
  146 | #define VALUE2ICONV(v) ((iconv_t)((VALUE)(v) ^ -1))
      |                                   ~~~~~~~~~~ ^ ~~
iconv.c:1057:18: error: invalid operands to binary expression ('VALUE' (aka 'struct rb_value_unit_struct *') and 'int')
 1057 |     iconv_t cd = VALUE2ICONV(check_iconv(self));
      |                  ^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
iconv.c:146:46: note: expanded from macro 'VALUE2ICONV'
  146 | #define VALUE2ICONV(v) ((iconv_t)((VALUE)(v) ^ -1))
      |                                   ~~~~~~~~~~ ^ ~~
2 warnings and 9 errors generated.
make: *** [Makefile:248: iconv.o] Error 1

make failed, exit code 2

Gem files will remain installed in /nix/store/q10ayfdx21sndwcwgnmnpalvhlq5842y-ruby3.3-iconv-1.1.0-x86_64-unknown-linux-gnufilc0/lib/ruby/gems/3.3.0/gems/iconv-1.1.0 for inspection.
Results logged to /nix/store/q10ayfdx21sndwcwgnmnpalvhlq5842y-ruby3.3-iconv-1.1.0-x86_64-unknown-linux-gnufilc0/lib/ruby/gems/3.3.0/extensions/x86_64-linux/3.3.0/iconv-1.1.0/gem_make.out
```

</details>

<details>
<summary>❌ <strong>libxml-ruby</strong>: ruby_xml_html_parser_context.c:342:11: error: incompatible pointer to integer conversion assigning t...</summary>

```
Running phase: unpackPhase
Running phase: patchPhase
Running phase: updateAutotoolsGnuConfigScriptsPhase
Running phase: updateAutotoolsGnuConfigScriptsPhase
Running phase: configurePhase
no configure script, doing nothing
Running phase: installPhase
buildFlags: --with-xml2-lib=/nix/store/i92z6561z4d29vq69ybkwb2v38zff5nw-libxml2-x86_64-unknown-linux-gnufilc0-2.13.8/lib --with-xml2-include=/nix/store/wpccq3f1256262v4varbm857rnadmmra-libxml2-x86_64-unknown-linux-gnufilc0-2.13.8-dev/include/libxml2
WARNING:  You build with buildroot.
  Build root: /
  Bin dir: /nix/store/qi5d0j2bc0pvrpkwjbx0182yfvqdy8w1-ruby3.3-libxml-ruby-5.0.3-x86_64-unknown-linux-gnufilc0/lib/ruby/gems/3.3.0/bin
  Gem home: /nix/store/qi5d0j2bc0pvrpkwjbx0182yfvqdy8w1-ruby3.3-libxml-ruby-5.0.3-x86_64-unknown-linux-gnufilc0/lib/ruby/gems/3.3.0
  Plugins dir: /nix/store/qi5d0j2bc0pvrpkwjbx0182yfvqdy8w1-ruby3.3-libxml-ruby-5.0.3-x86_64-unknown-linux-gnufilc0/lib/ruby/gems/3.3.0/plugins
Building native extensions with: '--with-xml2-lib=/nix/store/i92z6561z4d29vq69ybkwb2v38zff5nw-libxml2-x86_64-unknown-linux-gnufilc0-2.13.8/lib --with-xml2-include=/nix/store/wpccq3f1256262v4varbm857rnadmmra-libxml2-x86_64-unknown-linux-gnufilc0-2.13.8-dev/include/libxml2'
This could take a while...
ERROR:  Error installing /nix/store/zp83pl2h432q3ljvaplviv24n29w9y7p-libxml-ruby-5.0.3.gem:
        ERROR: Failed to build gem native extension.

    current directory: /nix/store/qi5d0j2bc0pvrpkwjbx0182yfvqdy8w1-ruby3.3-libxml-ruby-5.0.3-x86_64-unknown-linux-gnufilc0/lib/ruby/gems/3.3.0/gems/libxml-ruby-5.0.3/ext/libxml
/nix/store/65in3amyafclxn1lg3yjb1v9a3ngk1rm-ruby-3.3.10-x86_64-unknown-linux-gnufilc0/bin/ruby extconf.rb --with-xml2-lib\=/nix/store/i92z6561z4d29vq69ybkwb2v38zff5nw-libxml2-x86_64-unknown-linux-gnufilc0-2.13.8/lib --with-xml2-include\=/nix/store/wpccq3f1256262v4varbm857rnadmmra-libxml2-x86_64-unknown-linux-gnufilc0-2.13.8-dev/include/libxml2
checking for libxml/xmlversion.h in /opt/include/libxml2,/opt/local/include/libxml2,/opt/homebrew/opt/libxml2/include/libxml2,/usr/local/include/libxml2,/usr/include/libxml2,/usr/local/include,/usr/local/opt/libxml2/include/libxml2... yes
checking for xmlParseDoc() in -lxml2... yes
creating extconf.h
creating Makefile

current directory: /nix/store/qi5d0j2bc0pvrpkwjbx0182yfvqdy8w1-ruby3.3-libxml-ruby-5.0.3-x86_64-unknown-linux-gnufilc0/lib/ruby/gems/3.3.0/gems/libxml-ruby-5.0.3/ext/libxml
make DESTDIR\= sitearchdir\=./.gem.20251203-36-8y1zwn sitelibdir\=./.gem.20251203-36-8y1zwn clean

current directory: /nix/store/qi5d0j2bc0pvrpkwjbx0182yfvqdy8w1-ruby3.3-libxml-ruby-5.0.3-x86_64-unknown-linux-gnufilc0/lib/ruby/gems/3.3.0/gems/libxml-ruby-5.0.3/ext/libxml
make DESTDIR\= sitearchdir\=./.gem.20251203-36-8y1zwn sitelibdir\=./.gem.20251203-36-8y1zwn
compiling libxml.c
compiling ruby_xml.c
compiling ruby_xml_attr.c
compiling ruby_xml_attr_decl.c
compiling ruby_xml_attributes.c
compiling ruby_xml_cbg.c
compiling ruby_xml_document.c
compiling ruby_xml_dtd.c
compiling ruby_xml_encoding.c
compiling ruby_xml_error.c
ruby_xml_error.c:142:26: warning: comparison between pointer and integer ('int' and 'VALUE' (aka 'struct rb_value_unit_struct *')) [-Wpointer-integer-compare]
  142 |   if (rb_block_given_p() == Qfalse)
      |       ~~~~~~~~~~~~~~~~~~ ^  ~~~~~~
1 warning generated.
compiling ruby_xml_html_parser.c
compiling ruby_xml_html_parser_context.c
ruby_xml_html_parser_context.c:342:11: error: incompatible pointer to integer conversion assigning to 'ID' (aka 'unsigned long') from 'VALUE' (aka 'struct rb_value_unit_struct *') [-Wint-conversion]
  342 |   IO_ATTR = ID2SYM(rb_intern("@io"));
      |           ^ ~~~~~~~~~~~~~~~~~~~~~~~~
1 error generated.
make: *** [Makefile:248: ruby_xml_html_parser_context.o] Error 1

make failed, exit code 2

Gem files will remain installed in /nix/store/qi5d0j2bc0pvrpkwjbx0182yfvqdy8w1-ruby3.3-libxml-ruby-5.0.3-x86_64-unknown-linux-gnufilc0/lib/ruby/gems/3.3.0/gems/libxml-ruby-5.0.3 for inspection.
Results logged to /nix/store/qi5d0j2bc0pvrpkwjbx0182yfvqdy8w1-ruby3.3-libxml-ruby-5.0.3-x86_64-unknown-linux-gnufilc0/lib/ruby/gems/3.3.0/extensions/x86_64-linux/3.3.0/libxml-ruby-5.0.3/gem_make.out
```

</details>

<details>
<summary>✅ <strong>magic</strong>: build failed</summary>

```
If you ever happen to want to link against installed libraries
in a given directory, LIBDIR, you must either use libtool, and
specify the full pathname of the library, or use the '-LLIBDIR'
flag during linking and do at least one of the following:
   - add LIBDIR to the 'LD_LIBRARY_PATH' environment variable
     during execution
   - add LIBDIR to the 'LD_RUN_PATH' environment variable
     during linking
   - use the '-Wl,-rpath -Wl,LIBDIR' linker flag
   - have your system administrator run these commands:


See any operating system documentation about shared libraries for
more information, such as the ld(1) and ld.so(8) manual pages.
----------------------------------------------------------------------
 /nix/store/rry6qingvsrqmc7ll7jgaqpybcbdgf5v-coreutils-9.7/bin/mkdir -p '/nix/store/ra9bvc1bzl66mrhbrln5awv0xj1c289r-file-x86_64-unknown-linux-gnufilc0-5.45/bin'
  /nix/store/cfqbabpc7xwg8akbcchqbq3cai6qq2vs-bash-5.2p37/bin/bash ../libtool   --mode=install /nix/store/rry6qingvsrqmc7ll7jgaqpybcbdgf5v-coreutils-9.7/bin/install -c file '/nix/store/ra9bvc1bzl66mrhbrln5awv0xj1c289r-file-x86_64-unknown-linux-gnufilc0-5.45/bin'
libtool: install: /nix/store/rry6qingvsrqmc7ll7jgaqpybcbdgf5v-coreutils-9.7/bin/install -c .libs/file /nix/store/ra9bvc1bzl66mrhbrln5awv0xj1c289r-file-x86_64-unknown-linux-gnufilc0-5.45/bin/file
make[3]: Leaving directory '/build/file-5.45/src'
make[2]: Leaving directory '/build/file-5.45/src'
make[1]: Leaving directory '/build/file-5.45/src'
Making install in magic
make[1]: Entering directory '/build/file-5.45/magic'
make[2]: Entering directory '/build/file-5.45/magic'
make[2]: Nothing to be done for 'install-exec-am'.
 /nix/store/rry6qingvsrqmc7ll7jgaqpybcbdgf5v-coreutils-9.7/bin/mkdir -p '/nix/store/ra9bvc1bzl66mrhbrln5awv0xj1c289r-file-x86_64-unknown-linux-gnufilc0-5.45/share/misc'
 /nix/store/rry6qingvsrqmc7ll7jgaqpybcbdgf5v-coreutils-9.7/bin/install -c -m 644 magic.mgc '/nix/store/ra9bvc1bzl66mrhbrln5awv0xj1c289r-file-x86_64-unknown-linux-gnufilc0-5.45/share/misc'
make[2]: Leaving directory '/build/file-5.45/magic'
make[1]: Leaving directory '/build/file-5.45/magic'
Making install in tests
make[1]: Entering directory '/build/file-5.45/tests'
make[2]: Entering directory '/build/file-5.45/tests'
make[2]: Nothing to be done for 'install-exec-am'.
make[2]: Nothing to be done for 'install-data-am'.
make[2]: Leaving directory '/build/file-5.45/tests'
make[1]: Leaving directory '/build/file-5.45/tests'
Making install in doc
make[1]: Entering directory '/build/file-5.45/doc'
make[2]: Entering directory '/build/file-5.45/doc'
make[2]: Nothing to be done for 'install-exec-am'.
 /nix/store/rry6qingvsrqmc7ll7jgaqpybcbdgf5v-coreutils-9.7/bin/mkdir -p '/nix/store/n6zhinws344ncmhb9pkjxs66bc6nl2sn-file-x86_64-unknown-linux-gnufilc0-5.45-man/share/man/man1'
 /nix/store/rry6qingvsrqmc7ll7jgaqpybcbdgf5v-coreutils-9.7/bin/mkdir -p '/nix/store/n6zhinws344ncmhb9pkjxs66bc6nl2sn-file-x86_64-unknown-linux-gnufilc0-5.45-man/share/man/man3'
 /nix/store/rry6qingvsrqmc7ll7jgaqpybcbdgf5v-coreutils-9.7/bin/mkdir -p '/nix/store/n6zhinws344ncmhb9pkjxs66bc6nl2sn-file-x86_64-unknown-linux-gnufilc0-5.45-man/share/man/man4'
 /nix/store/rry6qingvsrqmc7ll7jgaqpybcbdgf5v-coreutils-9.7/bin/mkdir -p '/nix/store/n6zhinws344ncmhb9pkjxs66bc6nl2sn-file-x86_64-unknown-linux-gnufilc0-5.45-man/share/man/man5'
 /nix/store/rry6qingvsrqmc7ll7jgaqpybcbdgf5v-coreutils-9.7/bin/install -c -m 644 magic.4 '/nix/store/n6zhinws344ncmhb9pkjxs66bc6nl2sn-file-x86_64-unknown-linux-gnufilc0-5.45-man/share/man/man4'
 /nix/store/rry6qingvsrqmc7ll7jgaqpybcbdgf5v-coreutils-9.7/bin/install -c -m 644 libmagic.3 '/nix/store/n6zhinws344ncmhb9pkjxs66bc6nl2sn-file-x86_64-unknown-linux-gnufilc0-5.45-man/share/man/man3'
 /nix/store/rry6qingvsrqmc7ll7jgaqpybcbdgf5v-coreutils-9.7/bin/install -c -m 644 file.1 '/nix/store/n6zhinws344ncmhb9pkjxs66bc6nl2sn-file-x86_64-unknown-linux-gnufilc0-5.45-man/share/man/man1'
make[2]: Leaving directory '/build/file-5.45/doc'
make[1]: Leaving directory '/build/file-5.45/doc'
Making install in python
make[1]: Entering directory '/build/file-5.45/python'
make[2]: Entering directory '/build/file-5.45/python'
make[2]: Nothing to be done for 'install-exec-am'.
make[2]: Nothing to be done for 'install-data-am'.
make[2]: Leaving directory '/build/file-5.45/python'
make[1]: Leaving directory '/build/file-5.45/python'
make[1]: Entering directory '/build/file-5.45'
make[2]: Entering directory '/build/file-5.45'
make[2]: Nothing to be done for 'install-data-am'.
 /nix/store/rry6qingvsrqmc7ll7jgaqpybcbdgf5v-coreutils-9.7/bin/mkdir -p '/nix/store/ra9bvc1bzl66mrhbrln5awv0xj1c289r-file-x86_64-unknown-linux-gnufilc0-5.45/lib/pkgconfig'
 /nix/store/rry6qingvsrqmc7ll7jgaqpybcbdgf5v-coreutils-9.7/bin/install -c -m 644 libmagic.pc '/nix/store/ra9bvc1bzl66mrhbrln5awv0xj1c289r-file-x86_64-unknown-linux-gnufilc0-5.45/lib/pkgconfig'
make[2]: Leaving directory '/build/file-5.45'
make[1]: Leaving directory '/build/file-5.45'
Running phase: fixupPhase
Moving /nix/store/ra9bvc1bzl66mrhbrln5awv0xj1c289r-file-x86_64-unknown-linux-gnufilc0-5.45/lib/pkgconfig to /nix/store/5riil859z3z7as2qx0l26iv4v4galhx5-file-x86_64-unknown-linux-gnufilc0-5.45-dev/lib/pkgconfig
Patching '/nix/store/5riil859z3z7as2qx0l26iv4v4galhx5-file-x86_64-unknown-linux-gnufilc0-5.45-dev/lib/pkgconfig/libmagic.pc' includedir to output /nix/store/5riil859z3z7as2qx0l26iv4v4galhx5-file-x86_64-unknown-linux-gnufilc0-5.45-dev
shrinking RPATHs of ELF executables and libraries in /nix/store/ra9bvc1bzl66mrhbrln5awv0xj1c289r-file-x86_64-unknown-linux-gnufilc0-5.45
shrinking /nix/store/ra9bvc1bzl66mrhbrln5awv0xj1c289r-file-x86_64-unknown-linux-gnufilc0-5.45/lib/libmagic.so.1.0.0
shrinking /nix/store/ra9bvc1bzl66mrhbrln5awv0xj1c289r-file-x86_64-unknown-linux-gnufilc0-5.45/bin/file
checking for references to /build/ in /nix/store/ra9bvc1bzl66mrhbrln5awv0xj1c289r-file-x86_64-unknown-linux-gnufilc0-5.45...
patching script interpreter paths in /nix/store/ra9bvc1bzl66mrhbrln5awv0xj1c289r-file-x86_64-unknown-linux-gnufilc0-5.45
stripping (with command strip and flags -S -p) in  /nix/store/ra9bvc1bzl66mrhbrln5awv0xj1c289r-file-x86_64-unknown-linux-gnufilc0-5.45/lib /nix/store/ra9bvc1bzl66mrhbrln5awv0xj1c289r-file-x86_64-unknown-linux-gnufilc0-5.45/bin
shrinking RPATHs of ELF executables and libraries in /nix/store/5riil859z3z7as2qx0l26iv4v4galhx5-file-x86_64-unknown-linux-gnufilc0-5.45-dev
checking for references to /build/ in /nix/store/5riil859z3z7as2qx0l26iv4v4galhx5-file-x86_64-unknown-linux-gnufilc0-5.45-dev...
patching script interpreter paths in /nix/store/5riil859z3z7as2qx0l26iv4v4galhx5-file-x86_64-unknown-linux-gnufilc0-5.45-dev
stripping (with command strip and flags -S -p) in  /nix/store/5riil859z3z7as2qx0l26iv4v4galhx5-file-x86_64-unknown-linux-gnufilc0-5.45-dev/lib
shrinking RPATHs of ELF executables and libraries in /nix/store/n6zhinws344ncmhb9pkjxs66bc6nl2sn-file-x86_64-unknown-linux-gnufilc0-5.45-man
checking for references to /build/ in /nix/store/n6zhinws344ncmhb9pkjxs66bc6nl2sn-file-x86_64-unknown-linux-gnufilc0-5.45-man...
gzipping man pages under /nix/store/n6zhinws344ncmhb9pkjxs66bc6nl2sn-file-x86_64-unknown-linux-gnufilc0-5.45-man/share/man/
patching script interpreter paths in /nix/store/n6zhinws344ncmhb9pkjxs66bc6nl2sn-file-x86_64-unknown-linux-gnufilc0-5.45-man
```

```
copying path '/nix/store/gqk60hdxyab2rmvm771gwnqdv07pff3n-magic-0.2.9.gem' from 'https://cache.nixos.org'...
Running phase: unpackPhase
Running phase: patchPhase
Running phase: updateAutotoolsGnuConfigScriptsPhase
Running phase: updateAutotoolsGnuConfigScriptsPhase
Running phase: configurePhase
no configure script, doing nothing
Running phase: installPhase
buildFlags: 
WARNING:  You build with buildroot.
  Build root: /
  Bin dir: /nix/store/02hvxi3iar2dlp0n2nyczn7v5mj5x2mg-ruby3.3-magic-0.2.9-x86_64-unknown-linux-gnufilc0/lib/ruby/gems/3.3.0/bin
  Gem home: /nix/store/02hvxi3iar2dlp0n2nyczn7v5mj5x2mg-ruby3.3-magic-0.2.9-x86_64-unknown-linux-gnufilc0/lib/ruby/gems/3.3.0
  Plugins dir: /nix/store/02hvxi3iar2dlp0n2nyczn7v5mj5x2mg-ruby3.3-magic-0.2.9-x86_64-unknown-linux-gnufilc0/lib/ruby/gems/3.3.0/plugins
+-NOTE FOR LINUX USERS----------------------------------------------+
|                                                                   |
| Install libmagic using your package manager, e.g.                 |
|                                                                   |
|   sudo apt-get install file                                       |
|                                                                   |
+-NOTE FOR WINDOWS USERS -------------------------------------------+
|                                                                   |
| Install File for Windows from                                     |
|                                                                   |
|   http://gnuwin32.sourceforge.net/packages/file.htm               |
|                                                                   |
| You'll also need to set your PATH environment variable to the     |
| directory of the magic1.dll file                                  |
|                                                                   |
|   set PATH=C:\Program Files\GnuWin32\bin;%PATH%                   |
|                                                                   |
+-NOTE FOR MAC OS USERS --------------------------------------------+
|                                                                   |
| If you don't have libmagic.1.dylib file in your system, you need  |
| to install it using port command                                  |
|                                                                   |
|   sudo port install file                                          |
|                                                                   |
+-------------------------------------------------------------------+
Successfully installed magic-0.2.9
1 gem installed
/nix/store/02hvxi3iar2dlp0n2nyczn7v5mj5x2mg-ruby3.3-magic-0.2.9-x86_64-unknown-linux-gnufilc0/lib/ruby/gems/3.3.0 /build
removed 'cache/magic-0.2.9.gem'
removed directory 'cache'
/build
Running phase: fixupPhase
shrinking RPATHs of ELF executables and libraries in /nix/store/02hvxi3iar2dlp0n2nyczn7v5mj5x2mg-ruby3.3-magic-0.2.9-x86_64-unknown-linux-gnufilc0
checking for references to /build/ in /nix/store/02hvxi3iar2dlp0n2nyczn7v5mj5x2mg-ruby3.3-magic-0.2.9-x86_64-unknown-linux-gnufilc0...
patching script interpreter paths in /nix/store/02hvxi3iar2dlp0n2nyczn7v5mj5x2mg-ruby3.3-magic-0.2.9-x86_64-unknown-linux-gnufilc0
stripping (with command strip and flags -S -p) in  /nix/store/02hvxi3iar2dlp0n2nyczn7v5mj5x2mg-ruby3.3-magic-0.2.9-x86_64-unknown-linux-gnufilc0/lib /nix/store/02hvxi3iar2dlp0n2nyczn7v5mj5x2mg-ruby3.3-magic-0.2.9-x86_64-unknown-linux-gnufilc0/bin
rewriting symlink /nix/store/02hvxi3iar2dlp0n2nyczn7v5mj5x2mg-ruby3.3-magic-0.2.9-x86_64-unknown-linux-gnufilc0/nix-support/gem-meta/spec to be relative to /nix/store/02hvxi3iar2dlp0n2nyczn7v5mj5x2mg-ruby3.3-magic-0.2.9-x86_64-unknown-linux-gnufilc0
```

```
created 5 symlinks in user environment
```

```
Running phase: patchPhase
Running phase: updateAutotoolsGnuConfigScriptsPhase
Running phase: updateAutotoolsGnuConfigScriptsPhase
Running phase: configurePhase
no configure script, doing nothing
Running phase: buildPhase
no Makefile or custom buildPhase, doing nothing
Running phase: installPhase
Running phase: fixupPhase
shrinking RPATHs of ELF executables and libraries in /nix/store/4hfbrwiagycq94gh224406a42qp13sxa-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0
shrinking /nix/store/4hfbrwiagycq94gh224406a42qp13sxa-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0/bin/bundle
shrinking /nix/store/4hfbrwiagycq94gh224406a42qp13sxa-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0/bin/bundler
shrinking /nix/store/4hfbrwiagycq94gh224406a42qp13sxa-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0/bin/erb
shrinking /nix/store/4hfbrwiagycq94gh224406a42qp13sxa-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0/bin/gem
shrinking /nix/store/4hfbrwiagycq94gh224406a42qp13sxa-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0/bin/irb
shrinking /nix/store/4hfbrwiagycq94gh224406a42qp13sxa-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0/bin/racc
shrinking /nix/store/4hfbrwiagycq94gh224406a42qp13sxa-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0/bin/rake
shrinking /nix/store/4hfbrwiagycq94gh224406a42qp13sxa-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0/bin/rbs
shrinking /nix/store/4hfbrwiagycq94gh224406a42qp13sxa-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0/bin/rdbg
shrinking /nix/store/4hfbrwiagycq94gh224406a42qp13sxa-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0/bin/rdoc
shrinking /nix/store/4hfbrwiagycq94gh224406a42qp13sxa-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0/bin/ri
shrinking /nix/store/4hfbrwiagycq94gh224406a42qp13sxa-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0/bin/ruby
shrinking /nix/store/4hfbrwiagycq94gh224406a42qp13sxa-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0/bin/syntax_suggest
shrinking /nix/store/4hfbrwiagycq94gh224406a42qp13sxa-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0/bin/typeprof
checking for references to /build/ in /nix/store/4hfbrwiagycq94gh224406a42qp13sxa-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0...
patching script interpreter paths in /nix/store/4hfbrwiagycq94gh224406a42qp13sxa-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0
stripping (with command strip and flags -S -p) in  /nix/store/4hfbrwiagycq94gh224406a42qp13sxa-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0/bin
```

</details>

<details>
<summary>✅ <strong>msgpack</strong>: build failed</summary>

```
Running phase: unpackPhase
Unpacked gem: '/build/container/pgav307qjvj98mnhbsx3nad4vsip00bq-msgpack-1.8.0'
Running phase: patchPhase
Running phase: updateAutotoolsGnuConfigScriptsPhase
Running phase: updateAutotoolsGnuConfigScriptsPhase
Running phase: configurePhase
no configure script, doing nothing
Running phase: buildPhase
WARNING:  expected RubyGems version 3.6.6, was 3.6.2
WARNING:  License identifier 'Apache 2.0' is invalid. Use an identifier from
https://spdx.org/licenses or 'Nonstandard' for a nonstandard license,
or set it to nil if you don't want to specify a license.
Did you mean 'Apache-2.0'?
WARNING:  open-ended dependency on bundler (>= 0, development) is not recommended
  use a bounded requirement, such as "~> x.y"
WARNING:  open-ended dependency on rake (>= 0, development) is not recommended
  use a bounded requirement, such as "~> x.y"
WARNING:  open-ended dependency on rake-compiler (>= 1.1.9, development) is not recommended
  if rake-compiler is semantically versioned, use:
    add_development_dependency "rake-compiler", "~> 1.1", ">= 1.1.9"
WARNING:  open-ended dependency on ruby_memcheck (>= 0, development) is not recommended
  use a bounded requirement, such as "~> x.y"
WARNING:  open-ended dependency on yard (>= 0, development) is not recommended
  use a bounded requirement, such as "~> x.y"
WARNING:  open-ended dependency on json (>= 0, development) is not recommended
  use a bounded requirement, such as "~> x.y"
WARNING:  See https://guides.rubygems.org/specification-reference/ for help
  Successfully built RubyGem
  Name: msgpack
  Version: 1.8.0
  File: msgpack-1.8.0.gem
gem package built: msgpack-1.8.0.gem
Running phase: installPhase
buildFlags: 
WARNING:  You build with buildroot.
  Build root: /
  Bin dir: /nix/store/pbm46j0ifa6zsv2dw4kcx3jrkjliwryy-ruby3.3-msgpack-1.8.0-x86_64-unknown-linux-gnufilc0/lib/ruby/gems/3.3.0/bin
  Gem home: /nix/store/pbm46j0ifa6zsv2dw4kcx3jrkjliwryy-ruby3.3-msgpack-1.8.0-x86_64-unknown-linux-gnufilc0/lib/ruby/gems/3.3.0
  Plugins dir: /nix/store/pbm46j0ifa6zsv2dw4kcx3jrkjliwryy-ruby3.3-msgpack-1.8.0-x86_64-unknown-linux-gnufilc0/lib/ruby/gems/3.3.0/plugins
Building native extensions. This could take a while...
Successfully installed msgpack-1.8.0
1 gem installed
/nix/store/pbm46j0ifa6zsv2dw4kcx3jrkjliwryy-ruby3.3-msgpack-1.8.0-x86_64-unknown-linux-gnufilc0/lib/ruby/gems/3.3.0 /build/source
gems/msgpack-1.8.0/ext/msgpack/Makefile
extensions/x86_64-linux/3.3.0/msgpack-1.8.0/mkmf.log
extensions/x86_64-linux/3.3.0/msgpack-1.8.0/gem_make.out
removed 'cache/msgpack-1.8.0.gem'
removed directory 'cache'
/build/source
Running phase: fixupPhase
shrinking RPATHs of ELF executables and libraries in /nix/store/pbm46j0ifa6zsv2dw4kcx3jrkjliwryy-ruby3.3-msgpack-1.8.0-x86_64-unknown-linux-gnufilc0
shrinking /nix/store/pbm46j0ifa6zsv2dw4kcx3jrkjliwryy-ruby3.3-msgpack-1.8.0-x86_64-unknown-linux-gnufilc0/lib/ruby/gems/3.3.0/extensions/x86_64-linux/3.3.0/msgpack-1.8.0/msgpack/msgpack.so
shrinking /nix/store/pbm46j0ifa6zsv2dw4kcx3jrkjliwryy-ruby3.3-msgpack-1.8.0-x86_64-unknown-linux-gnufilc0/lib/ruby/gems/3.3.0/gems/msgpack-1.8.0/lib/msgpack/msgpack.so
checking for references to /build/ in /nix/store/pbm46j0ifa6zsv2dw4kcx3jrkjliwryy-ruby3.3-msgpack-1.8.0-x86_64-unknown-linux-gnufilc0...
patching script interpreter paths in /nix/store/pbm46j0ifa6zsv2dw4kcx3jrkjliwryy-ruby3.3-msgpack-1.8.0-x86_64-unknown-linux-gnufilc0
stripping (with command strip and flags -S -p) in  /nix/store/pbm46j0ifa6zsv2dw4kcx3jrkjliwryy-ruby3.3-msgpack-1.8.0-x86_64-unknown-linux-gnufilc0/lib /nix/store/pbm46j0ifa6zsv2dw4kcx3jrkjliwryy-ruby3.3-msgpack-1.8.0-x86_64-unknown-linux-gnufilc0/bin
rewriting symlink /nix/store/pbm46j0ifa6zsv2dw4kcx3jrkjliwryy-ruby3.3-msgpack-1.8.0-x86_64-unknown-linux-gnufilc0/nix-support/gem-meta/spec to be relative to /nix/store/pbm46j0ifa6zsv2dw4kcx3jrkjliwryy-ruby3.3-msgpack-1.8.0-x86_64-unknown-linux-gnufilc0
```

```
created 1 symlinks in user environment
```

```
Running phase: patchPhase
Running phase: updateAutotoolsGnuConfigScriptsPhase
Running phase: updateAutotoolsGnuConfigScriptsPhase
Running phase: configurePhase
no configure script, doing nothing
Running phase: buildPhase
no Makefile or custom buildPhase, doing nothing
Running phase: installPhase
Running phase: fixupPhase
shrinking RPATHs of ELF executables and libraries in /nix/store/fchyjh7nl9ymrjp1fb1hnih78khisg97-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0
shrinking /nix/store/fchyjh7nl9ymrjp1fb1hnih78khisg97-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0/bin/bundle
shrinking /nix/store/fchyjh7nl9ymrjp1fb1hnih78khisg97-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0/bin/bundler
shrinking /nix/store/fchyjh7nl9ymrjp1fb1hnih78khisg97-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0/bin/erb
shrinking /nix/store/fchyjh7nl9ymrjp1fb1hnih78khisg97-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0/bin/gem
shrinking /nix/store/fchyjh7nl9ymrjp1fb1hnih78khisg97-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0/bin/irb
shrinking /nix/store/fchyjh7nl9ymrjp1fb1hnih78khisg97-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0/bin/racc
shrinking /nix/store/fchyjh7nl9ymrjp1fb1hnih78khisg97-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0/bin/rake
shrinking /nix/store/fchyjh7nl9ymrjp1fb1hnih78khisg97-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0/bin/rbs
shrinking /nix/store/fchyjh7nl9ymrjp1fb1hnih78khisg97-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0/bin/rdbg
shrinking /nix/store/fchyjh7nl9ymrjp1fb1hnih78khisg97-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0/bin/rdoc
shrinking /nix/store/fchyjh7nl9ymrjp1fb1hnih78khisg97-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0/bin/ri
shrinking /nix/store/fchyjh7nl9ymrjp1fb1hnih78khisg97-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0/bin/ruby
shrinking /nix/store/fchyjh7nl9ymrjp1fb1hnih78khisg97-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0/bin/syntax_suggest
shrinking /nix/store/fchyjh7nl9ymrjp1fb1hnih78khisg97-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0/bin/typeprof
checking for references to /build/ in /nix/store/fchyjh7nl9ymrjp1fb1hnih78khisg97-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0...
patching script interpreter paths in /nix/store/fchyjh7nl9ymrjp1fb1hnih78khisg97-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0
stripping (with command strip and flags -S -p) in  /nix/store/fchyjh7nl9ymrjp1fb1hnih78khisg97-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0/bin
```

</details>

<details>
<summary>❌ <strong>mysql2</strong>: /nix/store/fmj1ilm5jk1hba6s3cv6gkpgsjvkxaqv-binutils-2.43.1/bin/ld: error: /build/source/build/libma...</summary>

```
[ 68%] Generating libmysqlclient.a
[ 68%] Generating libmariadb.a
[ 69%] Building C object unittest/libmariadb/CMakeFiles/conc336.dir/conc336.c.o
[ 70%] Generating libmysqlclient_r.a
clang-20: error: linker command failed with exit code 1 (use -v to see invocation)
[ 71%] Building C object unittest/libmariadb/CMakeFiles/basic-t.dir/basic-t.c.o
[ 72%] Building C object unittest/libmariadb/CMakeFiles/bulk1.dir/bulk1.c.o
[ 73%] Building C object unittest/libmariadb/CMakeFiles/charset.dir/charset.c.o
[ 74%] Building C object unittest/libmariadb/CMakeFiles/performance.dir/performance.c.o
[ 74%] Building C object unittest/libmariadb/CMakeFiles/logs.dir/logs.c.o
[ 74%] Building C object unittest/libmariadb/CMakeFiles/fetch.dir/fetch.c.o
[ 74%] Building C object unittest/libmariadb/CMakeFiles/cursor.dir/cursor.c.o
[ 74%] Building C object unittest/libmariadb/CMakeFiles/thread.dir/thread.c.o
[ 75%] Building C object unittest/libmariadb/CMakeFiles/view.dir/view.c.o
[ 77%] Building C object unittest/libmariadb/CMakeFiles/errors.dir/errors.c.o
[ 77%] Building C object unittest/libmariadb/CMakeFiles/ps_bugs.dir/ps_bugs.c.o
make[2]: *** [libmariadb/CMakeFiles/libmariadb.dir/build.make:160: libmariadb/libmariadb.so.3] Error 1
[ 78%] Building C object unittest/libmariadb/CMakeFiles/sp.dir/sp.c.o
make[1]: *** [CMakeFiles/Makefile2:620: libmariadb/CMakeFiles/libmariadb.dir/all] Error 2
[ 78%] Building C object unittest/libmariadb/CMakeFiles/ps.dir/ps.c.o
make[1]: *** Waiting for unfinished jobs....
[ 80%] Building C object unittest/libmariadb/CMakeFiles/result.dir/result.c.o
[ 80%] Building C object unittest/libmariadb/CMakeFiles/ps_new.dir/ps_new.c.o
[ 81%] Building C object unittest/libmariadb/CMakeFiles/connection.dir/connection.c.o
[ 81%] Building C object unittest/libmariadb/CMakeFiles/features-10_2.dir/features-10_2.c.o
[ 81%] Building C object unittest/libmariadb/CMakeFiles/misc.dir/misc.c.o
[ 82%] Building C object unittest/libmariadb/CMakeFiles/dyncol.dir/dyncol.c.o
[ 82%] Building C object unittest/libmariadb/CMakeFiles/async.dir/async.c.o
[ 84%] Building C object unittest/libmariadb/CMakeFiles/rpl_api.dir/rpl_api.c.o
[ 84%] Building C object unittest/libmariadb/CMakeFiles/t_conc173.dir/t_conc173.c.o
[ 84%] Built target SYM_libmysqlclient_r.a
[ 84%] Linking C executable conc336
[ 84%] Built target SYM_libmysqlclient.a
[ 84%] Built target SYM_libmariadb.a
[ 84%] Linking C executable charset
[ 84%] Linking C executable basic-t
[ 85%] Linking C executable bulk1
[ 85%] Linking C executable view
[ 86%] Linking C executable performance
[ 87%] Linking C executable cursor
[ 88%] Linking C executable thread
[ 89%] Linking C executable result
[ 89%] Linking C executable logs
[ 89%] Linking C executable sp
[ 90%] Linking C executable features-10_2
[ 91%] Linking C executable dyncol
[ 91%] Linking C executable async
[ 94%] Linking C executable fetch
[ 94%] Linking C executable errors
[ 94%] Linking C executable ps_new
[ 95%] Linking C executable t_conc173
[ 97%] Linking C executable rpl_api
[ 97%] Linking C executable misc
[ 98%] Linking C executable connection
[ 99%] Linking C executable ps
[ 99%] Linking C executable ps_bugs
[ 99%] Built target charset
[ 99%] Built target conc336
[ 99%] Built target cursor
[ 99%] Built target bulk1
[ 99%] Built target basic-t
[ 99%] Built target async
[ 99%] Built target ps_new
[ 99%] Built target sp
[ 99%] Built target t_conc173
[ 99%] Built target ps_bugs
[ 99%] Built target connection
[ 99%] Built target dyncol
[ 99%] Built target thread
[ 99%] Built target logs
[ 99%] Built target features-10_2
[ 99%] Built target rpl_api
[ 99%] Built target fetch
[ 99%] Built target view
[ 99%] Built target performance
[ 99%] Built target result
[ 99%] Built target ps
[ 99%] Built target misc
[ 99%] Built target errors
make: *** [Makefile:156: all] Error 2
```

</details>

<details>
<summary>✅ <strong>ncursesw</strong>: build failed</summary>

```
Running phase: unpackPhase
Running phase: patchPhase
Running phase: updateAutotoolsGnuConfigScriptsPhase
Running phase: updateAutotoolsGnuConfigScriptsPhase
Running phase: configurePhase
no configure script, doing nothing
Running phase: installPhase
buildFlags: --with-cflags=-I/nix/store/gsqm8q3ibkc95dh282hxq6vflry2x0jv-ncurses-x86_64-unknown-linux-gnufilc0-6.5-dev/include --with-ldflags=-L/nix/store/6gbniiz3fkg0z8fj5bdbpx9gkncdn0iv-ncurses-x86_64-unknown-linux-gnufilc0-6.5/lib
WARNING:  You build with buildroot.
  Build root: /
  Bin dir: /nix/store/4gyl1ls5iijiba39zqm94qjwy9mqbgwa-ruby3.3-ncursesw-1.4.11-x86_64-unknown-linux-gnufilc0/lib/ruby/gems/3.3.0/bin
  Gem home: /nix/store/4gyl1ls5iijiba39zqm94qjwy9mqbgwa-ruby3.3-ncursesw-1.4.11-x86_64-unknown-linux-gnufilc0/lib/ruby/gems/3.3.0
  Plugins dir: /nix/store/4gyl1ls5iijiba39zqm94qjwy9mqbgwa-ruby3.3-ncursesw-1.4.11-x86_64-unknown-linux-gnufilc0/lib/ruby/gems/3.3.0/plugins
Building native extensions with: '--with-cflags=-I/nix/store/gsqm8q3ibkc95dh282hxq6vflry2x0jv-ncurses-x86_64-unknown-linux-gnufilc0-6.5-dev/include --with-ldflags=-L/nix/store/6gbniiz3fkg0z8fj5bdbpx9gkncdn0iv-ncurses-x86_64-unknown-linux-gnufilc0-6.5/lib'
This could take a while...
Successfully installed ncursesw-1.4.11
1 gem installed
/nix/store/4gyl1ls5iijiba39zqm94qjwy9mqbgwa-ruby3.3-ncursesw-1.4.11-x86_64-unknown-linux-gnufilc0/lib/ruby/gems/3.3.0 /build
extensions/x86_64-linux/3.3.0/ncursesw-1.4.11/mkmf.log
extensions/x86_64-linux/3.3.0/ncursesw-1.4.11/gem_make.out
removed 'cache/ncursesw-1.4.11.gem'
removed directory 'cache'
/build
Running phase: fixupPhase
shrinking RPATHs of ELF executables and libraries in /nix/store/4gyl1ls5iijiba39zqm94qjwy9mqbgwa-ruby3.3-ncursesw-1.4.11-x86_64-unknown-linux-gnufilc0
shrinking /nix/store/4gyl1ls5iijiba39zqm94qjwy9mqbgwa-ruby3.3-ncursesw-1.4.11-x86_64-unknown-linux-gnufilc0/lib/ruby/gems/3.3.0/extensions/x86_64-linux/3.3.0/ncursesw-1.4.11/ncursesw_bin.so
shrinking /nix/store/4gyl1ls5iijiba39zqm94qjwy9mqbgwa-ruby3.3-ncursesw-1.4.11-x86_64-unknown-linux-gnufilc0/lib/ruby/gems/3.3.0/gems/ncursesw-1.4.11/lib/ncursesw_bin.so
checking for references to /build/ in /nix/store/4gyl1ls5iijiba39zqm94qjwy9mqbgwa-ruby3.3-ncursesw-1.4.11-x86_64-unknown-linux-gnufilc0...
patching script interpreter paths in /nix/store/4gyl1ls5iijiba39zqm94qjwy9mqbgwa-ruby3.3-ncursesw-1.4.11-x86_64-unknown-linux-gnufilc0
stripping (with command strip and flags -S -p) in  /nix/store/4gyl1ls5iijiba39zqm94qjwy9mqbgwa-ruby3.3-ncursesw-1.4.11-x86_64-unknown-linux-gnufilc0/lib /nix/store/4gyl1ls5iijiba39zqm94qjwy9mqbgwa-ruby3.3-ncursesw-1.4.11-x86_64-unknown-linux-gnufilc0/bin
rewriting symlink /nix/store/4gyl1ls5iijiba39zqm94qjwy9mqbgwa-ruby3.3-ncursesw-1.4.11-x86_64-unknown-linux-gnufilc0/nix-support/gem-meta/spec to be relative to /nix/store/4gyl1ls5iijiba39zqm94qjwy9mqbgwa-ruby3.3-ncursesw-1.4.11-x86_64-unknown-linux-gnufilc0
```

```
created 1 symlinks in user environment
```

```
Running phase: patchPhase
Running phase: updateAutotoolsGnuConfigScriptsPhase
Running phase: updateAutotoolsGnuConfigScriptsPhase
Running phase: configurePhase
no configure script, doing nothing
Running phase: buildPhase
no Makefile or custom buildPhase, doing nothing
Running phase: installPhase
Running phase: fixupPhase
shrinking RPATHs of ELF executables and libraries in /nix/store/njxpcp825784nhfqzyxp1rsdnhzrbz2x-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0
shrinking /nix/store/njxpcp825784nhfqzyxp1rsdnhzrbz2x-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0/bin/bundle
shrinking /nix/store/njxpcp825784nhfqzyxp1rsdnhzrbz2x-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0/bin/bundler
shrinking /nix/store/njxpcp825784nhfqzyxp1rsdnhzrbz2x-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0/bin/erb
shrinking /nix/store/njxpcp825784nhfqzyxp1rsdnhzrbz2x-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0/bin/gem
shrinking /nix/store/njxpcp825784nhfqzyxp1rsdnhzrbz2x-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0/bin/irb
shrinking /nix/store/njxpcp825784nhfqzyxp1rsdnhzrbz2x-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0/bin/racc
shrinking /nix/store/njxpcp825784nhfqzyxp1rsdnhzrbz2x-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0/bin/rake
shrinking /nix/store/njxpcp825784nhfqzyxp1rsdnhzrbz2x-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0/bin/rbs
shrinking /nix/store/njxpcp825784nhfqzyxp1rsdnhzrbz2x-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0/bin/rdbg
shrinking /nix/store/njxpcp825784nhfqzyxp1rsdnhzrbz2x-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0/bin/rdoc
shrinking /nix/store/njxpcp825784nhfqzyxp1rsdnhzrbz2x-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0/bin/ri
shrinking /nix/store/njxpcp825784nhfqzyxp1rsdnhzrbz2x-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0/bin/ruby
shrinking /nix/store/njxpcp825784nhfqzyxp1rsdnhzrbz2x-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0/bin/syntax_suggest
shrinking /nix/store/njxpcp825784nhfqzyxp1rsdnhzrbz2x-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0/bin/typeprof
checking for references to /build/ in /nix/store/njxpcp825784nhfqzyxp1rsdnhzrbz2x-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0...
patching script interpreter paths in /nix/store/njxpcp825784nhfqzyxp1rsdnhzrbz2x-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0
stripping (with command strip and flags -S -p) in  /nix/store/njxpcp825784nhfqzyxp1rsdnhzrbz2x-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0/bin
```

</details>

<details>
<summary>❌ <strong>nokogiri</strong>: cparse.c:648:23: error: incompatible integer to pointer conversion passing 'int' to parameter of typ...</summary>

```
Running phase: unpackPhase
Running phase: patchPhase
Running phase: updateAutotoolsGnuConfigScriptsPhase
Running phase: updateAutotoolsGnuConfigScriptsPhase
Running phase: configurePhase
no configure script, doing nothing
Running phase: installPhase
buildFlags: 
WARNING:  You build with buildroot.
  Build root: /
  Bin dir: /nix/store/i90500w6rqzb91wlyw5bc5zk532prw82-ruby3.3-racc-1.8.1-x86_64-unknown-linux-gnufilc0/lib/ruby/gems/3.3.0/bin
  Gem home: /nix/store/i90500w6rqzb91wlyw5bc5zk532prw82-ruby3.3-racc-1.8.1-x86_64-unknown-linux-gnufilc0/lib/ruby/gems/3.3.0
  Plugins dir: /nix/store/i90500w6rqzb91wlyw5bc5zk532prw82-ruby3.3-racc-1.8.1-x86_64-unknown-linux-gnufilc0/lib/ruby/gems/3.3.0/plugins
Building native extensions. This could take a while...
ERROR:  Error installing /nix/store/il5dwg6pwr3a3099ydsrcq4yxxxk3jgf-racc-1.8.1.gem:
        ERROR: Failed to build gem native extension.

    current directory: /nix/store/i90500w6rqzb91wlyw5bc5zk532prw82-ruby3.3-racc-1.8.1-x86_64-unknown-linux-gnufilc0/lib/ruby/gems/3.3.0/gems/racc-1.8.1/ext/racc/cparse
/nix/store/65in3amyafclxn1lg3yjb1v9a3ngk1rm-ruby-3.3.10-x86_64-unknown-linux-gnufilc0/bin/ruby extconf.rb
creating Makefile

current directory: /nix/store/i90500w6rqzb91wlyw5bc5zk532prw82-ruby3.3-racc-1.8.1-x86_64-unknown-linux-gnufilc0/lib/ruby/gems/3.3.0/gems/racc-1.8.1/ext/racc/cparse
make DESTDIR\= sitearchdir\=./.gem.20251203-36-u192wp sitelibdir\=./.gem.20251203-36-u192wp clean

current directory: /nix/store/i90500w6rqzb91wlyw5bc5zk532prw82-ruby3.3-racc-1.8.1-x86_64-unknown-linux-gnufilc0/lib/ruby/gems/3.3.0/gems/racc-1.8.1/ext/racc/cparse
make DESTDIR\= sitearchdir\=./.gem.20251203-36-u192wp sitelibdir\=./.gem.20251203-36-u192wp
compiling cparse.c
cparse.c:427:18: warning: format specifies type 'long' but the argument has type 'VALUE' (aka 'struct rb_value_unit_struct *') [-Wformat]
  424 |                  "%s() %s %"PRIsVALUE" (must be Array[2])",
      |                           ~~~~~~~~~~~
  425 |                  v->lex_is_iterator ? rb_id2name(v->lexmid) : "next_token",
  426 |                  v->lex_is_iterator ? "yielded" : "returned",
  427 |                  rb_obj_class(block_args));
      |                  ^~~~~~~~~~~~~~~~~~~~~~~~
cparse.c:648:23: error: incompatible integer to pointer conversion passing 'int' to parameter of type 'VALUE' (aka 'struct rb_value_unit_struct *') [-Wint-conversion]
  648 |         SHIFT(v, act, ERROR_TOKEN, val);
      |                       ^~~~~~~~~~~
cparse.c:28:24: note: expanded from macro 'ERROR_TOKEN'
   28 | #define ERROR_TOKEN    1
      |                        ^
cparse.c:440:42: note: expanded from macro 'SHIFT'
  440 | #define SHIFT(v,act,tok,val) shift(v,act,tok,val)
      |                                          ^~~
cparse.c:207:60: note: passing argument to parameter 'tok' here
  207 | static void shift(struct cparse_params* v, long act, VALUE tok, VALUE val);
      |                                                            ^
1 warning and 1 error generated.
make: *** [Makefile:248: cparse.o] Error 1

make failed, exit code 2

Gem files will remain installed in /nix/store/i90500w6rqzb91wlyw5bc5zk532prw82-ruby3.3-racc-1.8.1-x86_64-unknown-linux-gnufilc0/lib/ruby/gems/3.3.0/gems/racc-1.8.1 for inspection.
Results logged to /nix/store/i90500w6rqzb91wlyw5bc5zk532prw82-ruby3.3-racc-1.8.1-x86_64-unknown-linux-gnufilc0/lib/ruby/gems/3.3.0/extensions/x86_64-linux/3.3.0/racc-1.8.1/gem_make.out
```

</details>

<details>
<summary>❌ <strong>openssl</strong>: ossl.c:112:38: error: incompatible integer to pointer conversion passing 'long' to parameter of type...</summary>

```
checking for ENGINE_load_nuron() in openssl/engine.h... no
checking for ENGINE_load_sureware() in openssl/engine.h... no
checking for ENGINE_load_ubsec() in openssl/engine.h... no
checking for ENGINE_load_padlock() in openssl/engine.h... no
checking for ENGINE_load_capi() in openssl/engine.h... no
checking for ENGINE_load_gmp() in openssl/engine.h... no
checking for ENGINE_load_gost() in openssl/engine.h... no
checking for ENGINE_load_cryptodev() in openssl/engine.h... yes
checking for i2d_re_X509_tbs(NULL, NULL) in openssl/x509.h... yes
checking for SSL.ctx in openssl/ssl.h... no
checking for EVP_MD_CTX_new() in openssl/evp.h... yes
checking for EVP_MD_CTX_free(NULL) in openssl/evp.h... yes
checking for EVP_MD_CTX_pkey_ctx(NULL) in openssl/evp.h... yes
checking for X509_STORE_get_ex_data(NULL, 0) in openssl/x509.h... yes
checking for X509_STORE_set_ex_data(NULL, 0, NULL) in openssl/x509.h... yes
checking for X509_STORE_get_ex_new_index(0, NULL, NULL, NULL, NULL) in openssl/x509.h... yes
checking for X509_CRL_get0_signature(NULL, NULL, NULL) in openssl/x509.h... yes
checking for X509_REQ_get0_signature(NULL, NULL, NULL) in openssl/x509.h... yes
checking for X509_REVOKED_get0_serialNumber(NULL) in openssl/x509.h... yes
checking for X509_REVOKED_get0_revocationDate(NULL) in openssl/x509.h... yes
checking for X509_get0_tbs_sigalg(NULL) in openssl/x509.h... yes
checking for X509_STORE_CTX_get0_untrusted(NULL) in openssl/x509.h... yes
checking for X509_STORE_CTX_get0_cert(NULL) in openssl/x509.h... yes
checking for X509_STORE_CTX_get0_chain(NULL) in openssl/x509.h... yes
checking for OCSP_SINGLERESP_get0_id(NULL) in openssl/ocsp.h... yes
checking for SSL_CTX_get_ciphers(NULL) in openssl/ssl.h... yes
checking for X509_up_ref(NULL) in openssl/x509.h... yes
checking for X509_CRL_up_ref(NULL) in openssl/x509.h... yes
checking for X509_STORE_up_ref(NULL) in openssl/x509.h... yes
checking for SSL_SESSION_up_ref(NULL) in openssl/ssl.h... yes
checking for EVP_PKEY_up_ref(NULL) in openssl/evp.h... yes
checking for SSL_CTX_set_min_proto_version(NULL, 0) in openssl/ssl.h... yes
checking for SSL_CTX_get_security_level(NULL) in openssl/ssl.h... yes
checking for X509_get0_notBefore(NULL) in openssl/x509.h... yes
checking for SSL_SESSION_get_protocol_version(NULL) in openssl/ssl.h... yes
checking for TS_STATUS_INFO_get0_status(NULL) in openssl/ts.h... yes
checking for TS_STATUS_INFO_get0_text(NULL) in openssl/ts.h... yes
checking for TS_STATUS_INFO_get0_failure_info(NULL) in openssl/ts.h... yes
checking for TS_VERIFY_CTS_set_certs(NULL, NULL) in openssl/ts.h... yes
checking for TS_VERIFY_CTX_set_store(NULL, NULL) in openssl/ts.h... yes
checking for TS_VERIFY_CTX_add_flags(NULL, 0) in openssl/ts.h... yes
checking for TS_RESP_CTX_set_time_cb(NULL, NULL, NULL) in openssl/ts.h... yes
checking for EVP_PBE_scrypt("", 0, (unsigned char *)"", 0, 0, 0, 0, 0, NULL, 0) in openssl/evp.h... yes
checking for SSL_CTX_set_post_handshake_auth(NULL, 0) in openssl/ssl.h... yes
checking for X509_STORE_get0_param(NULL) in openssl/x509.h... yes
checking for EVP_PKEY_check(NULL) in openssl/evp.h... yes
checking for EVP_PKEY_new_raw_private_key(0, NULL, (unsigned char *)"", 0) in openssl/evp.h... yes
checking for SSL_CTX_set_ciphersuites(NULL, "") in openssl/ssl.h... yes
checking for SSL_set0_tmp_dh_pkey(NULL, NULL) in openssl/ssl.h... yes
checking for ERR_get_error_all(NULL, NULL, NULL, NULL, NULL) in openssl/err.h... yes
checking for TS_VERIFY_CTX_set_certs(NULL, NULL) in openssl/ts.h... yes
checking for SSL_CTX_load_verify_file(NULL, "") in openssl/ssl.h... yes
checking for BN_check_prime(NULL, NULL, NULL) in openssl/bn.h... yes
checking for EVP_MD_CTX_get0_md(NULL) in openssl/evp.h... yes
checking for EVP_MD_CTX_get_pkey_ctx(NULL) in openssl/evp.h... yes
checking for EVP_PKEY_eq(NULL, NULL) in openssl/evp.h... yes
checking for EVP_PKEY_dup(NULL) in openssl/evp.h... yes
creating extconf.h
creating Makefile

current directory: /nix/store/m750v0wak24r0wcc5kmh8c6qkx34dqnp-ruby3.3-openssl-3.3.0-x86_64-unknown-linux-gnufilc0/lib/ruby/gems/3.3.0/gems/openssl-3.3.0/ext/openssl
make DESTDIR\= sitearchdir\=./.gem.20251203-36-5wsb8t sitelibdir\=./.gem.20251203-36-5wsb8t clean

current directory: /nix/store/m750v0wak24r0wcc5kmh8c6qkx34dqnp-ruby3.3-openssl-3.3.0-x86_64-unknown-linux-gnufilc0/lib/ruby/gems/3.3.0/gems/openssl-3.3.0/ext/openssl
make DESTDIR\= sitearchdir\=./.gem.20251203-36-5wsb8t sitelibdir\=./.gem.20251203-36-5wsb8t
compiling openssl_missing.c
compiling ossl.c
ossl.c:112:38: error: incompatible integer to pointer conversion passing 'long' to parameter of type 'VALUE' (aka 'struct rb_value_unit_struct *') [-Wint-conversion]
  112 |     str = rb_protect(ossl_str_new_i, len, &state);
      |                                      ^~~
/nix/store/65in3amyafclxn1lg3yjb1v9a3ngk1rm-ruby-3.3.10-x86_64-unknown-linux-gnufilc0/include/ruby-3.3.0/ruby/internal/intern/proc.h:349:51: note: passing argument to parameter 'args' here
  349 | VALUE rb_protect(VALUE (*func)(VALUE args), VALUE args, int *state);
      |                                                   ^
1 error generated.
make: *** [Makefile:248: ossl.o] Error 1

make failed, exit code 2

Gem files will remain installed in /nix/store/m750v0wak24r0wcc5kmh8c6qkx34dqnp-ruby3.3-openssl-3.3.0-x86_64-unknown-linux-gnufilc0/lib/ruby/gems/3.3.0/gems/openssl-3.3.0 for inspection.
Results logged to /nix/store/m750v0wak24r0wcc5kmh8c6qkx34dqnp-ruby3.3-openssl-3.3.0-x86_64-unknown-linux-gnufilc0/lib/ruby/gems/3.3.0/extensions/x86_64-linux/3.3.0/openssl-3.3.0/gem_make.out
```

</details>

<details>
<summary>❌ <strong>ovirt-engine-sdk</strong>: build failed</summary>

```
Running phase: unpackPhase
Running phase: patchPhase
Running phase: updateAutotoolsGnuConfigScriptsPhase
Running phase: updateAutotoolsGnuConfigScriptsPhase
Running phase: configurePhase
no configure script, doing nothing
Running phase: installPhase
buildFlags: 
WARNING:  You build with buildroot.
  Build root: /
  Bin dir: /nix/store/s5lwip7k1dws7s9jvr99cj943z8161nm-ruby3.3-json-2.10.2-x86_64-unknown-linux-gnufilc0/lib/ruby/gems/3.3.0/bin
  Gem home: /nix/store/s5lwip7k1dws7s9jvr99cj943z8161nm-ruby3.3-json-2.10.2-x86_64-unknown-linux-gnufilc0/lib/ruby/gems/3.3.0
  Plugins dir: /nix/store/s5lwip7k1dws7s9jvr99cj943z8161nm-ruby3.3-json-2.10.2-x86_64-unknown-linux-gnufilc0/lib/ruby/gems/3.3.0/plugins
Building native extensions. This could take a while...
Successfully installed json-2.10.2
1 gem installed
/nix/store/s5lwip7k1dws7s9jvr99cj943z8161nm-ruby3.3-json-2.10.2-x86_64-unknown-linux-gnufilc0/lib/ruby/gems/3.3.0 /build
gems/json-2.10.2/ext/json/ext/generator/Makefile
gems/json-2.10.2/ext/json/ext/parser/Makefile
extensions/x86_64-linux/3.3.0/json-2.10.2/gem_make.out
extensions/x86_64-linux/3.3.0/json-2.10.2/mkmf.log
removed 'cache/json-2.10.2.gem'
removed directory 'cache'
/build
Running phase: fixupPhase
shrinking RPATHs of ELF executables and libraries in /nix/store/s5lwip7k1dws7s9jvr99cj943z8161nm-ruby3.3-json-2.10.2-x86_64-unknown-linux-gnufilc0
shrinking /nix/store/s5lwip7k1dws7s9jvr99cj943z8161nm-ruby3.3-json-2.10.2-x86_64-unknown-linux-gnufilc0/lib/ruby/gems/3.3.0/extensions/x86_64-linux/3.3.0/json-2.10.2/json/ext/generator.so
shrinking /nix/store/s5lwip7k1dws7s9jvr99cj943z8161nm-ruby3.3-json-2.10.2-x86_64-unknown-linux-gnufilc0/lib/ruby/gems/3.3.0/extensions/x86_64-linux/3.3.0/json-2.10.2/json/ext/parser.so
shrinking /nix/store/s5lwip7k1dws7s9jvr99cj943z8161nm-ruby3.3-json-2.10.2-x86_64-unknown-linux-gnufilc0/lib/ruby/gems/3.3.0/gems/json-2.10.2/lib/json/ext/generator.so
shrinking /nix/store/s5lwip7k1dws7s9jvr99cj943z8161nm-ruby3.3-json-2.10.2-x86_64-unknown-linux-gnufilc0/lib/ruby/gems/3.3.0/gems/json-2.10.2/lib/json/ext/parser.so
checking for references to /build/ in /nix/store/s5lwip7k1dws7s9jvr99cj943z8161nm-ruby3.3-json-2.10.2-x86_64-unknown-linux-gnufilc0...
patching script interpreter paths in /nix/store/s5lwip7k1dws7s9jvr99cj943z8161nm-ruby3.3-json-2.10.2-x86_64-unknown-linux-gnufilc0
stripping (with command strip and flags -S -p) in  /nix/store/s5lwip7k1dws7s9jvr99cj943z8161nm-ruby3.3-json-2.10.2-x86_64-unknown-linux-gnufilc0/lib /nix/store/s5lwip7k1dws7s9jvr99cj943z8161nm-ruby3.3-json-2.10.2-x86_64-unknown-linux-gnufilc0/bin
rewriting symlink /nix/store/s5lwip7k1dws7s9jvr99cj943z8161nm-ruby3.3-json-2.10.2-x86_64-unknown-linux-gnufilc0/nix-support/gem-meta/spec to be relative to /nix/store/s5lwip7k1dws7s9jvr99cj943z8161nm-ruby3.3-json-2.10.2-x86_64-unknown-linux-gnufilc0
```

```
copying path '/nix/store/kw1iwf7i813vi9b9n5y3vnjdl3jankzj-ovirt-engine-sdk-4.6.0.gem' from 'https://cache.nixos.org'...
Running phase: unpackPhase
Unpacked gem: '/build/container/kw1iwf7i813vi9b9n5y3vnjdl3jankzj-ovirt-engine-sdk-4.6.0'
Running phase: patchPhase
Running phase: updateAutotoolsGnuConfigScriptsPhase
Running phase: updateAutotoolsGnuConfigScriptsPhase
Running phase: configurePhase
no configure script, doing nothing
Running phase: buildPhase
WARNING:  expected RubyGems version 3.6.6, was 3.3.7
WARNING:  See https://guides.rubygems.org/specification-reference/ for help
  Successfully built RubyGem
  Name: ovirt-engine-sdk
  Version: 4.6.0
  File: ovirt-engine-sdk-4.6.0.gem
gem package built: ovirt-engine-sdk-4.6.0.gem
Running phase: installPhase
buildFlags: 
WARNING:  You build with buildroot.
  Build root: /
  Bin dir: /nix/store/85gdm42h652738gglchk4w63x3a0wzw8-ruby3.3-ovirt-engine-sdk-4.6.0-x86_64-unknown-linux-gnufilc0/lib/ruby/gems/3.3.0/bin
  Gem home: /nix/store/85gdm42h652738gglchk4w63x3a0wzw8-ruby3.3-ovirt-engine-sdk-4.6.0-x86_64-unknown-linux-gnufilc0/lib/ruby/gems/3.3.0
  Plugins dir: /nix/store/85gdm42h652738gglchk4w63x3a0wzw8-ruby3.3-ovirt-engine-sdk-4.6.0-x86_64-unknown-linux-gnufilc0/lib/ruby/gems/3.3.0/plugins
Building native extensions. This could take a while...
ERROR:  Error installing ovirt-engine-sdk-4.6.0.gem:
        ERROR: Failed to build gem native extension.

    current directory: /nix/store/85gdm42h652738gglchk4w63x3a0wzw8-ruby3.3-ovirt-engine-sdk-4.6.0-x86_64-unknown-linux-gnufilc0/lib/ruby/gems/3.3.0/gems/ovirt-engine-sdk-4.6.0/ext/ovirtsdk4c
/nix/store/65in3amyafclxn1lg3yjb1v9a3ngk1rm-ruby-3.3.10-x86_64-unknown-linux-gnufilc0/bin/ruby extconf.rb
checking for xml2-config... no
checking for pkg-config for libxml2... not found
*** extconf.rb failed ***
Could not create Makefile due to some reason, probably lack of necessary
libraries and/or headers.  Check the mkmf.log file for more details.  You may
need configuration options.

Provided configuration options:
        --with-opt-dir
        --without-opt-dir
        --with-opt-include=${opt-dir}/include
        --without-opt-include
        --with-opt-lib=${opt-dir}/lib
        --without-opt-lib
        --with-make-prog
        --without-make-prog
        --srcdir=.
        --curdir
        --ruby=/nix/store/65in3amyafclxn1lg3yjb1v9a3ngk1rm-ruby-3.3.10-x86_64-unknown-linux-gnufilc0/bin/$(RUBY_BASE_NAME)
        --with-libxml2-dir
        --without-libxml2-dir
        --with-libxml2-include=${libxml2-dir}/include
        --without-libxml2-include
        --with-libxml2-lib=${libxml2-dir}/lib
        --without-libxml2-lib
        --with-libxml2-config
        --without-libxml2-config
        --with-pkg-config
        --without-pkg-config
extconf.rb:29:in `<main>': The "libxml2" package isn't available. (RuntimeError)

To see why this extension failed to compile, please check the mkmf.log which can be found here:

  /nix/store/85gdm42h652738gglchk4w63x3a0wzw8-ruby3.3-ovirt-engine-sdk-4.6.0-x86_64-unknown-linux-gnufilc0/lib/ruby/gems/3.3.0/extensions/x86_64-linux/3.3.0/ovirt-engine-sdk-4.6.0/mkmf.log

extconf failed, exit code 1

Gem files will remain installed in /nix/store/85gdm42h652738gglchk4w63x3a0wzw8-ruby3.3-ovirt-engine-sdk-4.6.0-x86_64-unknown-linux-gnufilc0/lib/ruby/gems/3.3.0/gems/ovirt-engine-sdk-4.6.0 for inspection.
Results logged to /nix/store/85gdm42h652738gglchk4w63x3a0wzw8-ruby3.3-ovirt-engine-sdk-4.6.0-x86_64-unknown-linux-gnufilc0/lib/ruby/gems/3.3.0/extensions/x86_64-linux/3.3.0/ovirt-engine-sdk-4.6.0/gem_make.out
```

</details>

<details>
<summary>❌ <strong>patron</strong>: build failed</summary>

```
/nix/store/65in3amyafclxn1lg3yjb1v9a3ngk1rm-ruby-3.3.10-x86_64-unknown-linux-gnufilc0/include/ruby-3.3.0/ruby/internal/anyargs.h:263:123: note: expanded from macro 'RBIMPL_ANYARGS_DECL'
  263 | RBIMPL_ANYARGS_ATTRSET(sym) static void sym ## _05(__VA_ARGS__, VALUE(*)(VALUE, VALUE, VALUE, VALUE, VALUE, VALUE), int); \
      |                                                                                                                           ^
/nix/store/65in3amyafclxn1lg3yjb1v9a3ngk1rm-ruby-3.3.10-x86_64-unknown-linux-gnufilc0/include/ruby-3.3.0/ruby/internal/anyargs.h:252:38: note: expanded from macro '\
RBIMPL_ANYARGS_ATTRSET'
  252 | # define RBIMPL_ANYARGS_ATTRSET(sym) RBIMPL_ATTR_MAYBE_UNUSED() RBIMPL_ATTR_NONNULL(()) RBIMPL_ATTR_WEAKREF(sym)
      |                                      ^
/nix/store/65in3amyafclxn1lg3yjb1v9a3ngk1rm-ruby-3.3.10-x86_64-unknown-linux-gnufilc0/include/ruby-3.3.0/ruby/internal/attr/maybe_unused.h:31:37: note: expanded from macro 'RBIMPL_ATTR_MAYBE_UNUSED'
   31 | # define RBIMPL_ATTR_MAYBE_UNUSED() [[maybe_unused]]
      |                                     ^
In file included from session_ext.c:1:
In file included from /nix/store/65in3amyafclxn1lg3yjb1v9a3ngk1rm-ruby-3.3.10-x86_64-unknown-linux-gnufilc0/include/ruby-3.3.0/ruby.h:38:
In file included from /nix/store/65in3amyafclxn1lg3yjb1v9a3ngk1rm-ruby-3.3.10-x86_64-unknown-linux-gnufilc0/include/ruby-3.3.0/ruby/ruby.h:27:
/nix/store/65in3amyafclxn1lg3yjb1v9a3ngk1rm-ruby-3.3.10-x86_64-unknown-linux-gnufilc0/include/ruby-3.3.0/ruby/internal/anyargs.h:279:1: warning: [[]] attributes are a C23 extension [-Wc23-extensions]
/nix/store/65in3amyafclxn1lg3yjb1v9a3ngk1rm-ruby-3.3.10-x86_64-unknown-linux-gnufilc0/include/ruby-3.3.0/ruby/internal/anyargs.h:264:130: note: expanded from macro 'RBIMPL_ANYARGS_DECL'
  264 | RBIMPL_ANYARGS_ATTRSET(sym) static void sym ## _06(__VA_ARGS__, VALUE(*)(VALUE, VALUE, VALUE, VALUE, VALUE, VALUE, VALUE), int); \
      |                                                                                                                                  ^
/nix/store/65in3amyafclxn1lg3yjb1v9a3ngk1rm-ruby-3.3.10-x86_64-unknown-linux-gnufilc0/include/ruby-3.3.0/ruby/internal/anyargs.h:252:38: note: expanded from macro '\
RBIMPL_ANYARGS_ATTRSET'
  252 | # define RBIMPL_ANYARGS_ATTRSET(sym) RBIMPL_ATTR_MAYBE_UNUSED() RBIMPL_ATTR_NONNULL(()) RBIMPL_ATTR_WEAKREF(sym)
      |                                      ^
/nix/store/65in3amyafclxn1lg3yjb1v9a3ngk1rm-ruby-3.3.10-x86_64-unknown-linux-gnufilc0/include/ruby-3.3.0/ruby/internal/attr/maybe_unused.h:31:37: note: expanded from macro 'RBIMPL_ATTR_MAYBE_UNUSED'
   31 | # define RBIMPL_ATTR_MAYBE_UNUSED() [[maybe_unused]]
      |                                     ^
In file included from session_ext.c:1:
In file included from /nix/store/65in3amyafclxn1lg3yjb1v9a3ngk1rm-ruby-3.3.10-x86_64-unknown-linux-gnufilc0/include/ruby-3.3.0/ruby.h:38:
In file included from /nix/store/65in3amyafclxn1lg3yjb1v9a3ngk1rm-ruby-3.3.10-x86_64-unknown-linux-gnufilc0/include/ruby-3.3.0/ruby/ruby.h:27:
/nix/store/65in3amyafclxn1lg3yjb1v9a3ngk1rm-ruby-3.3.10-x86_64-unknown-linux-gnufilc0/include/ruby-3.3.0/ruby/internal/anyargs.h:279:1: warning: [[]] attributes are a C23 extension [-Wc23-extensions]
/nix/store/65in3amyafclxn1lg3yjb1v9a3ngk1rm-ruby-3.3.10-x86_64-unknown-linux-gnufilc0/include/ruby-3.3.0/ruby/internal/anyargs.h:265:137: note: expanded from macro 'RBIMPL_ANYARGS_DECL'
  265 | RBIMPL_ANYARGS_ATTRSET(sym) static void sym ## _07(__VA_ARGS__, VALUE(*)(VALUE, VALUE, VALUE, VALUE, VALUE, VALUE, VALUE, VALUE), int); \
      |                                                                                                                                         ^
/nix/store/65in3amyafclxn1lg3yjb1v9a3ngk1rm-ruby-3.3.10-x86_64-unknown-linux-gnufilc0/include/ruby-3.3.0/ruby/internal/anyargs.h:252:38: note: expanded from macro '\
RBIMPL_ANYARGS_ATTRSET'
  252 | # define RBIMPL_ANYARGS_ATTRSET(sym) RBIMPL_ATTR_MAYBE_UNUSED() RBIMPL_ATTR_NONNULL(()) RBIMPL_ATTR_WEAKREF(sym)
      |                                      ^
/nix/store/65in3amyafclxn1lg3yjb1v9a3ngk1rm-ruby-3.3.10-x86_64-unknown-linux-gnufilc0/include/ruby-3.3.0/ruby/internal/attr/maybe_unused.h:31:37: note: expanded from macro 'RBIMPL_ATTR_MAYBE_UNUSED'
   31 | # define RBIMPL_ATTR_MAYBE_UNUSED() [[maybe_unused]]
      |                                     ^
In file included from session_ext.c:1:
In file included from /nix/store/65in3amyafclxn1lg3yjb1v9a3ngk1rm-ruby-3.3.10-x86_64-unknown-linux-gnufilc0/include/ruby-3.3.0/ruby.h:38:
In file included from /nix/store/65in3amyafclxn1lg3yjb1v9a3ngk1rm-ruby-3.3.10-x86_64-unknown-linux-gnufilc0/include/ruby-3.3.0/ruby/ruby.h:27:
/nix/store/65in3amyafclxn1lg3yjb1v9a3ngk1rm-ruby-3.3.10-x86_64-unknown-linux-gnufilc0/include/ruby-3.3.0/ruby/internal/anyargs.h:279:1: warning: [[]] attributes are a C23 extension [-Wc23-extensions]
/nix/store/65in3amyafclxn1lg3yjb1v9a3ngk1rm-ruby-3.3.10-x86_64-unknown-linux-gnufilc0/include/ruby-3.3.0/ruby/internal/anyargs.h:266:144: note: expanded from macro 'RBIMPL_ANYARGS_DECL'
  266 | RBIMPL_ANYARGS_ATTRSET(sym) static void sym ## _08(__VA_ARGS__, VALUE(*)(VALUE, VALUE, VALUE, VALUE, VALUE, VALUE, VALUE, VALUE, VALUE), int); \
      |                                                               
                                                                                 ^
/nix/store/65in3amyafclxn1lg3yjb1v9a3ngk1rm-ruby-3.3.10-x86_64-unknown-linux-gnufilc0/include/ruby-3.3.0/ruby/internal/anyargs.h:252:38: note: expanded from macro '\
RBIMPL_ANYARGS_ATTRSET'
  252 | # define RBIMPL_ANYARGS_ATTRSET(sym) RBIMPL_ATTR_MAYBE_UNUSED() RBIMPL_ATTR_NONNULL(()) RBIMPL_ATTR_WEAKREF(sym)
      |                                      ^
/nix/store/65in3amyafclxn1lg3yjb1v9a3ngk1rm-ruby-3.3.10-x86_64-unknown-linux-gnufilc0/include/ruby-3.3.0/ruby/internal/attr/maybe_unused.h:31:37: note: expanded from macro 'RBIMPL_ATTR_MAYBE_UNUSED'
   31 | # define RBIMPL_ATTR_MAYBE_UNUSED() [[maybe_unused]]
      |                                     ^
In file included from session_ext.c:1:
In file included from /nix/store/65in3amyafclxn1lg3yjb1v9a3ngk1rm-ruby-3.3.10-x86_64-unknown-linux-gnufilc0/include/ruby-3.3.0/ruby.h:38:
In file included from /nix/store/65in3amyafclxn1lg3yjb1v9a3ngk1rm-ruby-3.3.10-x86_64-unknown-linux-gnufilc0/include/ruby-3.3.0/ruby/ruby.h:27:
/nix/store/65in3amyafclxn1lg3yjb1v9a3ngk1rm-ruby-3.3.10-x86_64-unknown-linux-gnufilc0/include/ruby-3.3.0/ruby/internal/anyargs.h:279:1: warning: [[]] attributes are a C23 extension [-Wc23-extensions]
/nix/store/65in3amyafclxn1lg3yjb1v9a3ngk1rm-ruby-3.3.10-x86_64-unknown-linux-gnufilc0/include/ruby-3.3.0/ruby/internal/anyargs.h:267:151: note: expanded from macro 'RBIMPL_ANYARGS_DECL'
  267 | RBIMPL_ANYARGS_ATTRSET(sym) static void sym ## _09(__VA_ARGS__, VALUE(*)(VALUE, VALUE, VALUE, VALUE, VALUE, VALUE, VALUE, VALUE, VALUE, VALUE), int); \
      |                                                                                                                                                       ^
/nix/store/65in3amyafclxn1lg3yjb1v9a3ngk1rm-ruby-3.3.10-x86_64-unknown-linux-gnufilc0/include/ruby-3.3.0/ruby/internal/anyargs.h:252:38: note: expanded from macro '\
RBIMPL_ANYARGS_ATTRSET'
  252 | # define RBIMPL_ANYARGS_ATTRSET(sym) RBIMPL_ATTR_MAYBE_UNUSED() RBIMPL_ATTR_NONNULL(()) RBIMPL_ATTR_WEAKREF(sym)
      |                                      ^
/nix/store/65in3amyafclxn1lg3yjb1v9a3ngk1rm-ruby-3.3.10-x86_64-unknown-linux-gnufilc0/include/ruby-3.3.0/ruby/internal/attr/maybe_unused.h:31:37: note: expanded from macro 'RBIMPL_ATTR_MAYBE_UNUSED'
   31 | # define RBIMPL_ATTR_MAYBE_UNUSED() [[maybe_unused]]
      |                                     ^
In file included from session_ext.c:1:
In file included from /nix/store/65in3amyafclxn1lg3yjb1v9a3ngk1rm-ruby-3.3.10-x86_64-unknown-linux-gnufilc0/include/ruby-3.3.0/ruby.h:38:
In file included from /nix/store/65in3amyafclxn1lg3yjb1v9a3ngk1rm-ruby-3.3.10-x86_64-unknown-linux-gnufilc0/include/ruby-3.3.0/ruby/ruby.h:27:
/nix/store/65in3amyafclxn1lg3yjb1v9a3ngk1rm-ruby-3.3.10-x86_64-unknown-linux-gnufilc0/include/ruby-3.3.0/ruby/internal/anyargs.h:279:1: warning: [[]] attributes are a C23 extension [-Wc23-extensions]
/nix/store/65in3amyafclxn1lg3yjb1v9a3ngk1rm-ruby-3.3.10-x86_64-unknown-linux-gnufilc0/include/ruby-3.3.0/ruby/internal/anyargs.h:268:158: note: expanded from macro 'RBIMPL_ANYARGS_DECL'
  268 | RBIMPL_ANYARGS_ATTRSET(sym) static void sym ## _10(__VA_ARGS__, VALUE(*)(VALUE, VALUE, VALUE, VALUE, VALUE, VALUE, VALUE, VALUE, VALUE, VALUE, VALUE), int); \
      |                                                                                                                                                              ^
/nix/store/65in3amyafclxn1lg3yjb1v9a3ngk1rm-ruby-3.3.10-x86_64-unknown-linux-gnufilc0/include/ruby-3.3.0/ruby/internal/anyargs.h:252:38: note: expanded from macro '\
RBIMPL_ANYARGS_ATTRSET'
  252 | # define RBIMPL_ANYARGS_ATTRSET(sym) RBIMPL_ATTR_MAYBE_UNUSED() RBIMPL_ATTR_NONNULL(()) RBIMPL_ATTR_WEAKREF(sym)
      |                                      ^
/nix/store/65in3amyafclxn1lg3yjb1v9a3ngk1rm-ruby-3.3.10-x86_64-unknown-linux-gnufilc0/include/ruby-3.3.0/ruby/internal/attr/maybe_unused.h:31:37: note: expanded from macro 'RBIMPL_ATTR_MAYBE_UNUSED'
   31 | # define RBIMPL_ATTR_MAYBE_UNUSED() [[maybe_unused]]
```

</details>

<details>
<summary>❌ <strong>pcaprub</strong>: build failed</summary>

```
shrinking /nix/store/slf067xfml42wqqaf19drjh0n30wbvr1-libnl-x86_64-unknown-linux-gnufilc0-3.11.0-bin/bin/genl-ctrl-list
shrinking /nix/store/slf067xfml42wqqaf19drjh0n30wbvr1-libnl-x86_64-unknown-linux-gnufilc0-3.11.0-bin/bin/idiag-socket-details
shrinking /nix/store/slf067xfml42wqqaf19drjh0n30wbvr1-libnl-x86_64-unknown-linux-gnufilc0-3.11.0-bin/bin/nf-ct-add
shrinking /nix/store/slf067xfml42wqqaf19drjh0n30wbvr1-libnl-x86_64-unknown-linux-gnufilc0-3.11.0-bin/bin/nf-ct-events
shrinking /nix/store/slf067xfml42wqqaf19drjh0n30wbvr1-libnl-x86_64-unknown-linux-gnufilc0-3.11.0-bin/bin/nf-ct-list
shrinking /nix/store/slf067xfml42wqqaf19drjh0n30wbvr1-libnl-x86_64-unknown-linux-gnufilc0-3.11.0-bin/bin/nf-exp-add
shrinking /nix/store/slf067xfml42wqqaf19drjh0n30wbvr1-libnl-x86_64-unknown-linux-gnufilc0-3.11.0-bin/bin/nf-exp-delete
shrinking /nix/store/slf067xfml42wqqaf19drjh0n30wbvr1-libnl-x86_64-unknown-linux-gnufilc0-3.11.0-bin/bin/nf-exp-list
shrinking /nix/store/slf067xfml42wqqaf19drjh0n30wbvr1-libnl-x86_64-unknown-linux-gnufilc0-3.11.0-bin/bin/nf-log
shrinking /nix/store/slf067xfml42wqqaf19drjh0n30wbvr1-libnl-x86_64-unknown-linux-gnufilc0-3.11.0-bin/bin/nf-monitor
shrinking /nix/store/slf067xfml42wqqaf19drjh0n30wbvr1-libnl-x86_64-unknown-linux-gnufilc0-3.11.0-bin/bin/nf-queue
shrinking /nix/store/slf067xfml42wqqaf19drjh0n30wbvr1-libnl-x86_64-unknown-linux-gnufilc0-3.11.0-bin/bin/nl-addr-add
shrinking /nix/store/slf067xfml42wqqaf19drjh0n30wbvr1-libnl-x86_64-unknown-linux-gnufilc0-3.11.0-bin/bin/nl-addr-delete
shrinking /nix/store/slf067xfml42wqqaf19drjh0n30wbvr1-libnl-x86_64-unknown-linux-gnufilc0-3.11.0-bin/bin/nl-addr-list
shrinking /nix/store/slf067xfml42wqqaf19drjh0n30wbvr1-libnl-x86_64-unknown-linux-gnufilc0-3.11.0-bin/bin/nl-class-add
shrinking /nix/store/slf067xfml42wqqaf19drjh0n30wbvr1-libnl-x86_64-unknown-linux-gnufilc0-3.11.0-bin/bin/nl-class-delete
shrinking /nix/store/slf067xfml42wqqaf19drjh0n30wbvr1-libnl-x86_64-unknown-linux-gnufilc0-3.11.0-bin/bin/nl-class-list
shrinking /nix/store/slf067xfml42wqqaf19drjh0n30wbvr1-libnl-x86_64-unknown-linux-gnufilc0-3.11.0-bin/bin/nl-classid-lookup
shrinking /nix/store/slf067xfml42wqqaf19drjh0n30wbvr1-libnl-x86_64-unknown-linux-gnufilc0-3.11.0-bin/bin/nl-cls-add
shrinking /nix/store/slf067xfml42wqqaf19drjh0n30wbvr1-libnl-x86_64-unknown-linux-gnufilc0-3.11.0-bin/bin/nl-cls-delete
shrinking /nix/store/slf067xfml42wqqaf19drjh0n30wbvr1-libnl-x86_64-unknown-linux-gnufilc0-3.11.0-bin/bin/nl-cls-list
shrinking /nix/store/slf067xfml42wqqaf19drjh0n30wbvr1-libnl-x86_64-unknown-linux-gnufilc0-3.11.0-bin/bin/nl-fib-lookup
shrinking /nix/store/slf067xfml42wqqaf19drjh0n30wbvr1-libnl-x86_64-unknown-linux-gnufilc0-3.11.0-bin/bin/nl-link-enslave
shrinking /nix/store/slf067xfml42wqqaf19drjh0n30wbvr1-libnl-x86_64-unknown-linux-gnufilc0-3.11.0-bin/bin/nl-link-ifindex2name
shrinking /nix/store/slf067xfml42wqqaf19drjh0n30wbvr1-libnl-x86_64-unknown-linux-gnufilc0-3.11.0-bin/bin/nl-link-list
shrinking /nix/store/slf067xfml42wqqaf19drjh0n30wbvr1-libnl-x86_64-unknown-linux-gnufilc0-3.11.0-bin/bin/nl-link-name2ifindex
shrinking /nix/store/slf067xfml42wqqaf19drjh0n30wbvr1-libnl-x86_64-unknown-linux-gnufilc0-3.11.0-bin/bin/nl-link-release
shrinking /nix/store/slf067xfml42wqqaf19drjh0n30wbvr1-libnl-x86_64-unknown-linux-gnufilc0-3.11.0-bin/bin/nl-link-set
shrinking /nix/store/slf067xfml42wqqaf19drjh0n30wbvr1-libnl-x86_64-unknown-linux-gnufilc0-3.11.0-bin/bin/nl-link-stats
shrinking /nix/store/slf067xfml42wqqaf19drjh0n30wbvr1-libnl-x86_64-unknown-linux-gnufilc0-3.11.0-bin/bin/nl-list-caches
shrinking /nix/store/slf067xfml42wqqaf19drjh0n30wbvr1-libnl-x86_64-unknown-linux-gnufilc0-3.11.0-bin/bin/nl-list-sockets
shrinking /nix/store/slf067xfml42wqqaf19drjh0n30wbvr1-libnl-x86_64-unknown-linux-gnufilc0-3.11.0-bin/bin/nl-monitor
shrinking /nix/store/slf067xfml42wqqaf19drjh0n30wbvr1-libnl-x86_64-unknown-linux-gnufilc0-3.11.0-bin/bin/nl-neigh-add
shrinking /nix/store/slf067xfml42wqqaf19drjh0n30wbvr1-libnl-x86_64-unknown-linux-gnufilc0-3.11.0-bin/bin/nl-neigh-delete
shrinking /nix/store/slf067xfml42wqqaf19drjh0n30wbvr1-libnl-x86_64-unknown-linux-gnufilc0-3.11.0-bin/bin/nl-neigh-list
shrinking /nix/store/slf067xfml42wqqaf19drjh0n30wbvr1-libnl-x86_64-unknown-linux-gnufilc0-3.11.0-bin/bin/nl-neightbl-list
shrinking /nix/store/slf067xfml42wqqaf19drjh0n30wbvr1-libnl-x86_64-unknown-linux-gnufilc0-3.11.0-bin/bin/nl-nh-list
shrinking /nix/store/slf067xfml42wqqaf19drjh0n30wbvr1-libnl-x86_64-unknown-linux-gnufilc0-3.11.0-bin/bin/nl-pktloc-lookup
shrinking /nix/store/slf067xfml42wqqaf19drjh0n30wbvr1-libnl-x86_64-unknown-linux-gnufilc0-3.11.0-bin/bin/nl-qdisc-add
shrinking /nix/store/slf067xfml42wqqaf19drjh0n30wbvr1-libnl-x86_64-unknown-linux-gnufilc0-3.11.0-bin/bin/nl-qdisc-delete
shrinking /nix/store/slf067xfml42wqqaf19drjh0n30wbvr1-libnl-x86_64-unknown-linux-gnufilc0-3.11.0-bin/bin/nl-qdisc-list
shrinking /nix/store/slf067xfml42wqqaf19drjh0n30wbvr1-libnl-x86_64-unknown-linux-gnufilc0-3.11.0-bin/bin/nl-route-add
shrinking /nix/store/slf067xfml42wqqaf19drjh0n30wbvr1-libnl-x86_64-unknown-linux-gnufilc0-3.11.0-bin/bin/nl-route-delete
shrinking /nix/store/slf067xfml42wqqaf19drjh0n30wbvr1-libnl-x86_64-unknown-linux-gnufilc0-3.11.0-bin/bin/nl-route-get
shrinking /nix/store/slf067xfml42wqqaf19drjh0n30wbvr1-libnl-x86_64-unknown-linux-gnufilc0-3.11.0-bin/bin/nl-route-list
shrinking /nix/store/slf067xfml42wqqaf19drjh0n30wbvr1-libnl-x86_64-unknown-linux-gnufilc0-3.11.0-bin/bin/nl-rule-list
shrinking /nix/store/slf067xfml42wqqaf19drjh0n30wbvr1-libnl-x86_64-unknown-linux-gnufilc0-3.11.0-bin/bin/nl-tctree-list
shrinking /nix/store/slf067xfml42wqqaf19drjh0n30wbvr1-libnl-x86_64-unknown-linux-gnufilc0-3.11.0-bin/bin/nl-util-addr
checking for references to /build/ in /nix/store/slf067xfml42wqqaf19drjh0n30wbvr1-libnl-x86_64-unknown-linux-gnufilc0-3.11.0-bin...
patching script interpreter paths in /nix/store/slf067xfml42wqqaf19drjh0n30wbvr1-libnl-x86_64-unknown-linux-gnufilc0-3.11.0-bin
stripping (with command strip and flags -S -p) in  /nix/store/slf067xfml42wqqaf19drjh0n30wbvr1-libnl-x86_64-unknown-linux-gnufilc0-3.11.0-bin/bin
shrinking RPATHs of ELF executables and libraries in /nix/store/5h4lbczl3wq0qvm1k4w7sl1nz2a84fzs-libnl-x86_64-unknown-linux-gnufilc0-3.11.0-dev
checking for references to /build/ in /nix/store/5h4lbczl3wq0qvm1k4w7sl1nz2a84fzs-libnl-x86_64-unknown-linux-gnufilc0-3.11.0-dev...
patching script interpreter paths in /nix/store/5h4lbczl3wq0qvm1k4w7sl1nz2a84fzs-libnl-x86_64-unknown-linux-gnufilc0-3.11.0-dev
stripping (with command strip and flags -S -p) in  /nix/store/5h4lbczl3wq0qvm1k4w7sl1nz2a84fzs-libnl-x86_64-unknown-linux-gnufilc0-3.11.0-dev/lib
shrinking RPATHs of ELF executables and libraries in /nix/store/mfqvm83g2blrva7s2gnaghzr07h6j3mn-libnl-x86_64-unknown-linux-gnufilc0-3.11.0
shrinking /nix/store/mfqvm83g2blrva7s2gnaghzr07h6j3mn-libnl-x86_64-unknown-linux-gnufilc0-3.11.0/lib/libnl/cli/cls/basic.so
shrinking /nix/store/mfqvm83g2blrva7s2gnaghzr07h6j3mn-libnl-x86_64-unknown-linux-gnufilc0-3.11.0/lib/libnl/cli/cls/cgroup.so
shrinking /nix/store/mfqvm83g2blrva7s2gnaghzr07h6j3mn-libnl-x86_64-unknown-linux-gnufilc0-3.11.0/lib/libnl/cli/qdisc/bfifo.so
shrinking /nix/store/mfqvm83g2blrva7s2gnaghzr07h6j3mn-libnl-x86_64-unknown-linux-gnufilc0-3.11.0/lib/libnl/cli/qdisc/blackhole.so
shrinking /nix/store/mfqvm83g2blrva7s2gnaghzr07h6j3mn-libnl-x86_64-unknown-linux-gnufilc0-3.11.0/lib/libnl/cli/qdisc/fq_codel.so
shrinking /nix/store/mfqvm83g2blrva7s2gnaghzr07h6j3mn-libnl-x86_64-unknown-linux-gnufilc0-3.11.0/lib/libnl/cli/qdisc/hfsc.so
shrinking /nix/store/mfqvm83g2blrva7s2gnaghzr07h6j3mn-libnl-x86_64-unknown-linux-gnufilc0-3.11.0/lib/libnl/cli/qdisc/htb.so
shrinking /nix/store/mfqvm83g2blrva7s2gnaghzr07h6j3mn-libnl-x86_64-unknown-linux-gnufilc0-3.11.0/lib/libnl/cli/qdisc/ingress.so
shrinking /nix/store/mfqvm83g2blrva7s2gnaghzr07h6j3mn-libnl-x86_64-unknown-linux-gnufilc0-3.11.0/lib/libnl/cli/qdisc/pfifo.so
shrinking /nix/store/mfqvm83g2blrva7s2gnaghzr07h6j3mn-libnl-x86_64-unknown-linux-gnufilc0-3.11.0/lib/libnl/cli/qdisc/plug.so
shrinking /nix/store/mfqvm83g2blrva7s2gnaghzr07h6j3mn-libnl-x86_64-unknown-linux-gnufilc0-3.11.0/lib/libnl-3.so.200.26.0
shrinking /nix/store/mfqvm83g2blrva7s2gnaghzr07h6j3mn-libnl-x86_64-unknown-linux-gnufilc0-3.11.0/lib/libnl-route-3.so.200.26.0
shrinking /nix/store/mfqvm83g2blrva7s2gnaghzr07h6j3mn-libnl-x86_64-unknown-linux-gnufilc0-3.11.0/lib/libnl-idiag-3.so.200.26.0
shrinking /nix/store/mfqvm83g2blrva7s2gnaghzr07h6j3mn-libnl-x86_64-unknown-linux-gnufilc0-3.11.0/lib/libnl-genl-3.so.200.26.0
shrinking /nix/store/mfqvm83g2blrva7s2gnaghzr07h6j3mn-libnl-x86_64-unknown-linux-gnufilc0-3.11.0/lib/libnl-nf-3.so.200.26.0
shrinking /nix/store/mfqvm83g2blrva7s2gnaghzr07h6j3mn-libnl-x86_64-unknown-linux-gnufilc0-3.11.0/lib/libnl-xfrm-3.so.200.26.0
shrinking /nix/store/mfqvm83g2blrva7s2gnaghzr07h6j3mn-libnl-x86_64-unknown-linux-gnufilc0-3.11.0/lib/libnl-cli-3.so.200.26.0
checking for references to /build/ in /nix/store/mfqvm83g2blrva7s2gnaghzr07h6j3mn-libnl-x86_64-unknown-linux-gnufilc0-3.11.0...
patching script interpreter paths in /nix/store/mfqvm83g2blrva7s2gnaghzr07h6j3mn-libnl-x86_64-unknown-linux-gnufilc0-3.11.0
stripping (with command strip and flags -S -p) in  /nix/store/mfqvm83g2blrva7s2gnaghzr07h6j3mn-libnl-x86_64-unknown-linux-gnufilc0-3.11.0/lib
shrinking RPATHs of ELF executables and libraries in /nix/store/hfkfq2frigjvg70bx94dpacx0i2s41an-libnl-x86_64-unknown-linux-gnufilc0-3.11.0-man
checking for references to /build/ in /nix/store/hfkfq2frigjvg70bx94dpacx0i2s41an-libnl-x86_64-unknown-linux-gnufilc0-3.11.0-man...
gzipping man pages under /nix/store/hfkfq2frigjvg70bx94dpacx0i2s41an-libnl-x86_64-unknown-linux-gnufilc0-3.11.0-man/share/man/
patching script interpreter paths in /nix/store/hfkfq2frigjvg70bx94dpacx0i2s41an-libnl-x86_64-unknown-linux-gnufilc0-3.11.0-man
```

```
    (mkdir -p /nix/store/39hl65hjazmlflqfpabk5h6ilvyda387-libpcap-x86_64-unknown-linux-gnufilc0-1.10.5/lib/pkgconfig; chmod 755 /nix/store/39hl65hjazmlflqfpabk5h6ilvyda387-libpcap-x86_64-unknown-linux-gnufilc0-1.10.5/lib/pkgconfig)
/nix/store/rry6qingvsrqmc7ll7jgaqpybcbdgf5v-coreutils-9.7/bin/install -c -m 644 libpcap.pc /nix/store/39hl65hjazmlflqfpabk5h6ilvyda387-libpcap-x86_64-unknown-linux-gnufilc0-1.10.5/lib/pkgconfig/libpcap.pc
for i in pcap-config.1; do \
        /nix/store/rry6qingvsrqmc7ll7jgaqpybcbdgf5v-coreutils-9.7/bin/install -c -m 644 ./$i \
            /nix/store/39hl65hjazmlflqfpabk5h6ilvyda387-libpcap-x86_64-unknown-linux-gnufilc0-1.10.5/share/man/man1/$i; done
for i in pcap_activate.3pcap pcap_breakloop.3pcap pcap_can_set_rfmon.3pcap pcap_close.3pcap pcap_create.3pcap pcap_datalink_name_to_val.3pcap pcap_datalink_val_to_name.3pcap pcap_dump.3pcap pcap_dump_close.3pcap pcap_dump_file.3pcap pcap_dump_flush.3pcap pcap_dump_ftell.3pcap pcap_file.3pcap pcap_fileno.3pcap pcap_findalldevs.3pcap pcap_freecode.3pcap pcap_get_required_select_timeout.3pcap pcap_get_selectable_fd.3pcap pcap_geterr.3pcap pcap_init.3pcap pcap_inject.3pcap pcap_is_swapped.3pcap pcap_lib_version.3pcap pcap_lookupdev.3pcap pcap_lookupnet.3pcap pcap_loop.3pcap pcap_major_version.3pcap pcap_next_ex.3pcap pcap_offline_filter.3pcap pcap_open_live.3pcap pcap_set_buffer_size.3pcap pcap_set_datalink.3pcap pcap_set_promisc.3pcap pcap_set_protocol_linux.3pcap pcap_set_rfmon.3pcap pcap_set_snaplen.3pcap pcap_set_timeout.3pcap pcap_setdirection.3pcap pcap_setfilter.3pcap pcap_setnonblock.3pcap pcap_snapshot.3pcap pcap_stats.3pcap pcap_statustostr.3pcap pcap_strerror.3pcap pcap_tstamp_type_name_to_val.3pcap pcap_tstamp_type_val_to_name.3pcap; do \
        /nix/store/rry6qingvsrqmc7ll7jgaqpybcbdgf5v-coreutils-9.7/bin/install -c -m 644 ./$i \
            /nix/store/39hl65hjazmlflqfpabk5h6ilvyda387-libpcap-x86_64-unknown-linux-gnufilc0-1.10.5/share/man/man3/$i; done
for i in pcap.3pcap pcap_compile.3pcap pcap_datalink.3pcap pcap_dump_open.3pcap pcap_get_tstamp_precision.3pcap pcap_list_datalinks.3pcap pcap_list_tstamp_types.3pcap pcap_open_dead.3pcap pcap_open_offline.3pcap pcap_set_immediate_mode.3pcap pcap_set_tstamp_precision.3pcap pcap_set_tstamp_type.3pcap; do \
        /nix/store/rry6qingvsrqmc7ll7jgaqpybcbdgf5v-coreutils-9.7/bin/install -c -m 644 $i \
            /nix/store/39hl65hjazmlflqfpabk5h6ilvyda387-libpcap-x86_64-unknown-linux-gnufilc0-1.10.5/share/man/man3/$i; done
(cd /nix/store/39hl65hjazmlflqfpabk5h6ilvyda387-libpcap-x86_64-unknown-linux-gnufilc0-1.10.5/share/man/man3 && \
rm -f pcap_datalink_val_to_description.3pcap && \
ln -s pcap_datalink_val_to_name.3pcap \
         pcap_datalink_val_to_description.3pcap && \
rm -f pcap_datalink_val_to_description_or_dlt.3pcap && \
ln -s pcap_datalink_val_to_name.3pcap \
         pcap_datalink_val_to_description_or_dlt.3pcap && \
rm -f pcap_dump_fopen.3pcap && \
ln -s pcap_dump_open.3pcap pcap_dump_fopen.3pcap && \
rm -f pcap_freealldevs.3pcap && \
ln -s pcap_findalldevs.3pcap pcap_freealldevs.3pcap && \
rm -f pcap_perror.3pcap && \
ln -s pcap_geterr.3pcap pcap_perror.3pcap && \
rm -f pcap_sendpacket.3pcap && \
ln -s pcap_inject.3pcap pcap_sendpacket.3pcap && \
rm -f pcap_free_datalinks.3pcap && \
ln -s pcap_list_datalinks.3pcap pcap_free_datalinks.3pcap && \
rm -f pcap_free_tstamp_types.3pcap && \
ln -s pcap_list_tstamp_types.3pcap pcap_free_tstamp_types.3pcap && \
rm -f pcap_dispatch.3pcap && \
ln -s pcap_loop.3pcap pcap_dispatch.3pcap && \
rm -f pcap_minor_version.3pcap && \
ln -s pcap_major_version.3pcap pcap_minor_version.3pcap && \
rm -f pcap_next.3pcap && \
ln -s pcap_next_ex.3pcap pcap_next.3pcap && \
rm -f pcap_open_dead_with_tstamp_precision.3pcap && \
ln -s pcap_open_dead.3pcap \
         pcap_open_dead_with_tstamp_precision.3pcap && \
rm -f pcap_open_offline_with_tstamp_precision.3pcap && \
ln -s pcap_open_offline.3pcap pcap_open_offline_with_tstamp_precision.3pcap && \
rm -f pcap_fopen_offline.3pcap && \
ln -s pcap_open_offline.3pcap pcap_fopen_offline.3pcap && \
rm -f pcap_fopen_offline_with_tstamp_precision.3pcap && \
ln -s pcap_open_offline.3pcap pcap_fopen_offline_with_tstamp_precision.3pcap && \
rm -f pcap_tstamp_type_val_to_description.3pcap && \
ln -s pcap_tstamp_type_val_to_name.3pcap pcap_tstamp_type_val_to_description.3pcap && \
rm -f pcap_getnonblock.3pcap && \
ln -s pcap_setnonblock.3pcap pcap_getnonblock.3pcap)
for i in pcap-savefile.manfile.in; do \
        /nix/store/rry6qingvsrqmc7ll7jgaqpybcbdgf5v-coreutils-9.7/bin/install -c -m 644 `echo $i | sed 's/.manfile.in/.manfile/'` \
            /nix/store/39hl65hjazmlflqfpabk5h6ilvyda387-libpcap-x86_64-unknown-linux-gnufilc0-1.10.5/share/man/man5/`echo $i | sed 's/.manfile.in/.5/'`; done
for i in pcap-filter.manmisc.in pcap-linktype.manmisc.in pcap-tstamp.manmisc.in; do \
        /nix/store/rry6qingvsrqmc7ll7jgaqpybcbdgf5v-coreutils-9.7/bin/install -c -m 644 `echo $i | sed 's/.manmisc.in/.manmisc/'` \
            /nix/store/39hl65hjazmlflqfpabk5h6ilvyda387-libpcap-x86_64-unknown-linux-gnufilc0-1.10.5/share/man/man7/`echo $i | sed 's/.manmisc.in/.7/'`; done
/nix/store/v1s0dg76qm22jhwfg8byj466k15zgz27-stdenv-linux/setup: line 269: [: : integer expression expected
Running phase: fixupPhase
shrinking RPATHs of ELF executables and libraries in /nix/store/39hl65hjazmlflqfpabk5h6ilvyda387-libpcap-x86_64-unknown-linux-gnufilc0-1.10.5
shrinking /nix/store/39hl65hjazmlflqfpabk5h6ilvyda387-libpcap-x86_64-unknown-linux-gnufilc0-1.10.5/lib/libpcap.so.1.10.5
checking for references to /build/ in /nix/store/39hl65hjazmlflqfpabk5h6ilvyda387-libpcap-x86_64-unknown-linux-gnufilc0-1.10.5...
gzipping man pages under /nix/store/39hl65hjazmlflqfpabk5h6ilvyda387-libpcap-x86_64-unknown-linux-gnufilc0-1.10.5/share/man/
patching script interpreter paths in /nix/store/39hl65hjazmlflqfpabk5h6ilvyda387-libpcap-x86_64-unknown-linux-gnufilc0-1.10.5
stripping (with command strip and flags -S -p) in  /nix/store/39hl65hjazmlflqfpabk5h6ilvyda387-libpcap-x86_64-unknown-linux-gnufilc0-1.10.5/lib /nix/store/39hl65hjazmlflqfpabk5h6ilvyda387-libpcap-x86_64-unknown-linux-gnufilc0-1.10.5/bin
rewriting symlink /nix/store/39hl65hjazmlflqfpabk5h6ilvyda387-libpcap-x86_64-unknown-linux-gnufilc0-1.10.5/share/man/man3/pcap_datalink_val_to_description.3pcap.gz to be relative to /nix/store/39hl65hjazmlflqfpabk5h6ilvyda387-libpcap-x86_64-unknown-linux-gnufilc0-1.10.5
rewriting symlink /nix/store/39hl65hjazmlflqfpabk5h6ilvyda387-libpcap-x86_64-unknown-linux-gnufilc0-1.10.5/share/man/man3/pcap_datalink_val_to_description_or_dlt.3pcap.gz to be relative to /nix/store/39hl65hjazmlflqfpabk5h6ilvyda387-libpcap-x86_64-unknown-linux-gnufilc0-1.10.5
rewriting symlink /nix/store/39hl65hjazmlflqfpabk5h6ilvyda387-libpcap-x86_64-unknown-linux-gnufilc0-1.10.5/share/man/man3/pcap_dispatch.3pcap.gz to be relative to /nix/store/39hl65hjazmlflqfpabk5h6ilvyda387-libpcap-x86_64-unknown-linux-gnufilc0-1.10.5
rewriting symlink /nix/store/39hl65hjazmlflqfpabk5h6ilvyda387-libpcap-x86_64-unknown-linux-gnufilc0-1.10.5/share/man/man3/pcap_dump_fopen.3pcap.gz to be relative to /nix/store/39hl65hjazmlflqfpabk5h6ilvyda387-libpcap-x86_64-unknown-linux-gnufilc0-1.10.5
rewriting symlink /nix/store/39hl65hjazmlflqfpabk5h6ilvyda387-libpcap-x86_64-unknown-linux-gnufilc0-1.10.5/share/man/man3/pcap_fopen_offline.3pcap.gz to be relative to /nix/store/39hl65hjazmlflqfpabk5h6ilvyda387-libpcap-x86_64-unknown-linux-gnufilc0-1.10.5
rewriting symlink /nix/store/39hl65hjazmlflqfpabk5h6ilvyda387-libpcap-x86_64-unknown-linux-gnufilc0-1.10.5/share/man/man3/pcap_fopen_offline_with_tstamp_precision.3pcap.gz to be relative to /nix/store/39hl65hjazmlflqfpabk5h6ilvyda387-libpcap-x86_64-unknown-linux-gnufilc0-1.10.5
rewriting symlink /nix/store/39hl65hjazmlflqfpabk5h6ilvyda387-libpcap-x86_64-unknown-linux-gnufilc0-1.10.5/share/man/man3/pcap_free_datalinks.3pcap.gz to be relative to /nix/store/39hl65hjazmlflqfpabk5h6ilvyda387-libpcap-x86_64-unknown-linux-gnufilc0-1.10.5
rewriting symlink /nix/store/39hl65hjazmlflqfpabk5h6ilvyda387-libpcap-x86_64-unknown-linux-gnufilc0-1.10.5/share/man/man3/pcap_free_tstamp_types.3pcap.gz to be relative to /nix/store/39hl65hjazmlflqfpabk5h6ilvyda387-libpcap-x86_64-unknown-linux-gnufilc0-1.10.5
rewriting symlink /nix/store/39hl65hjazmlflqfpabk5h6ilvyda387-libpcap-x86_64-unknown-linux-gnufilc0-1.10.5/share/man/man3/pcap_freealldevs.3pcap.gz to be relative to /nix/store/39hl65hjazmlflqfpabk5h6ilvyda387-libpcap-x86_64-unknown-linux-gnufilc0-1.10.5
rewriting symlink /nix/store/39hl65hjazmlflqfpabk5h6ilvyda387-libpcap-x86_64-unknown-linux-gnufilc0-1.10.5/share/man/man3/pcap_getnonblock.3pcap.gz to be relative to /nix/store/39hl65hjazmlflqfpabk5h6ilvyda387-libpcap-x86_64-unknown-linux-gnufilc0-1.10.5
rewriting symlink /nix/store/39hl65hjazmlflqfpabk5h6ilvyda387-libpcap-x86_64-unknown-linux-gnufilc0-1.10.5/share/man/man3/pcap_minor_version.3pcap.gz to be relative to /nix/store/39hl65hjazmlflqfpabk5h6ilvyda387-libpcap-x86_64-unknown-linux-gnufilc0-1.10.5
rewriting symlink /nix/store/39hl65hjazmlflqfpabk5h6ilvyda387-libpcap-x86_64-unknown-linux-gnufilc0-1.10.5/share/man/man3/pcap_next.3pcap.gz to be relative to /nix/store/39hl65hjazmlflqfpabk5h6ilvyda387-libpcap-x86_64-unknown-linux-gnufilc0-1.10.5
rewriting symlink /nix/store/39hl65hjazmlflqfpabk5h6ilvyda387-libpcap-x86_64-unknown-linux-gnufilc0-1.10.5/share/man/man3/pcap_open_dead_with_tstamp_precision.3pcap.gz to be relative to /nix/store/39hl65hjazmlflqfpabk5h6ilvyda387-libpcap-x86_64-unknown-linux-gnufilc0-1.10.5
rewriting symlink /nix/store/39hl65hjazmlflqfpabk5h6ilvyda387-libpcap-x86_64-unknown-linux-gnufilc0-1.10.5/share/man/man3/pcap_open_offline_with_tstamp_precision.3pcap.gz to be relative to /nix/store/39hl65hjazmlflqfpabk5h6ilvyda387-libpcap-x86_64-unknown-linux-gnufilc0-1.10.5
rewriting symlink /nix/store/39hl65hjazmlflqfpabk5h6ilvyda387-libpcap-x86_64-unknown-linux-gnufilc0-1.10.5/share/man/man3/pcap_perror.3pcap.gz to be relative to /nix/store/39hl65hjazmlflqfpabk5h6ilvyda387-libpcap-x86_64-unknown-linux-gnufilc0-1.10.5
rewriting symlink /nix/store/39hl65hjazmlflqfpabk5h6ilvyda387-libpcap-x86_64-unknown-linux-gnufilc0-1.10.5/share/man/man3/pcap_sendpacket.3pcap.gz to be relative to /nix/store/39hl65hjazmlflqfpabk5h6ilvyda387-libpcap-x86_64-unknown-linux-gnufilc0-1.10.5
rewriting symlink /nix/store/39hl65hjazmlflqfpabk5h6ilvyda387-libpcap-x86_64-unknown-linux-gnufilc0-1.10.5/share/man/man3/pcap_tstamp_type_val_to_description.3pcap.gz to be relative to /nix/store/39hl65hjazmlflqfpabk5h6ilvyda387-libpcap-x86_64-unknown-linux-gnufilc0-1.10.5
```

```
Running phase: patchPhase
Running phase: updateAutotoolsGnuConfigScriptsPhase
Running phase: updateAutotoolsGnuConfigScriptsPhase
Running phase: configurePhase
no configure script, doing nothing
Running phase: installPhase
buildFlags: 
WARNING:  You build with buildroot.
  Build root: /
  Bin dir: /nix/store/abcscwhgd2x0fvwn3hpl6d1lmrqfsb24-ruby3.3-pcaprub-0.13.3-x86_64-unknown-linux-gnufilc0/lib/ruby/gems/3.3.0/bin
  Gem home: /nix/store/abcscwhgd2x0fvwn3hpl6d1lmrqfsb24-ruby3.3-pcaprub-0.13.3-x86_64-unknown-linux-gnufilc0/lib/ruby/gems/3.3.0
  Plugins dir: /nix/store/abcscwhgd2x0fvwn3hpl6d1lmrqfsb24-ruby3.3-pcaprub-0.13.3-x86_64-unknown-linux-gnufilc0/lib/ruby/gems/3.3.0/plugins
Building native extensions. This could take a while...
ERROR:  Error installing /nix/store/lcnh70zmxwsfiqmdr528d1n744lyp9i6-pcaprub-0.13.3.gem:
        ERROR: Failed to build gem native extension.

    current directory: /nix/store/abcscwhgd2x0fvwn3hpl6d1lmrqfsb24-ruby3.3-pcaprub-0.13.3-x86_64-unknown-linux-gnufilc0/lib/ruby/gems/3.3.0/gems/pcaprub-0.13.3/ext/pcaprub_c
/nix/store/65in3amyafclxn1lg3yjb1v9a3ngk1rm-ruby-3.3.10-x86_64-unknown-linux-gnufilc0/bin/ruby extconf.rb

[*] Running checks for pcaprub_c code...
platform is x86_64-linux-filc0
checking for ruby/thread.h... yes
checking for rb_thread_blocking_region()... no
checking for rb_thread_call_without_gvl()... yes
checking for pcap_open_live() in -lpcap... yes
checking for pcap_setnonblock() in -lpcap... yes
creating Makefile

current directory: /nix/store/abcscwhgd2x0fvwn3hpl6d1lmrqfsb24-ruby3.3-pcaprub-0.13.3-x86_64-unknown-linux-gnufilc0/lib/ruby/gems/3.3.0/gems/pcaprub-0.13.3/ext/pcaprub_c
make DESTDIR\= sitearchdir\=./.gem.20251203-36-bd4pdr sitelibdir\=./.gem.20251203-36-bd4pdr clean

current directory: /nix/store/abcscwhgd2x0fvwn3hpl6d1lmrqfsb24-ruby3.3-pcaprub-0.13.3-x86_64-unknown-linux-gnufilc0/lib/ruby/gems/3.3.0/gems/pcaprub-0.13.3/ext/pcaprub_c
make DESTDIR\= sitearchdir\=./.gem.20251203-36-bd4pdr sitelibdir\=./.gem.20251203-36-bd4pdr
compiling pcaprub.c
pcaprub.c:572:3: error: statement requires expression of integer type ('VALUE' (aka 'struct rb_value_unit_struct *') invalid)
  572 |   switch(promisc) {
      |   ^      ~~~~~~~
pcaprub.c:573:9: error: integer constant expression must have integer type, not 'VALUE' (aka 'struct rb_value_unit_struct *')
  573 |         case Qtrue:
      |              ^~~~~
/nix/store/65in3amyafclxn1lg3yjb1v9a3ngk1rm-ruby-3.3.10-x86_64-unknown-linux-gnufilc0/include/ruby-3.3.0/ruby/internal/special_consts.h:61:25: note: expanded from macro 'Qtrue'
   61 | #define Qtrue           RUBY_Qtrue             /**< @old{RUBY_Qtrue} */
      |                         ^~~~~~~~~~
/nix/store/65in3amyafclxn1lg3yjb1v9a3ngk1rm-ruby-3.3.10-x86_64-unknown-linux-gnufilc0/include/ruby-3.3.0/ruby/internal/special_consts.h:346:21: note: expanded from macro 'RUBY_Qtrue'
  346 | #define RUBY_Qtrue  RBIMPL_CAST((VALUE)RUBY_Qtrue)
      |                     ^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
/nix/store/65in3amyafclxn1lg3yjb1v9a3ngk1rm-ruby-3.3.10-x86_64-unknown-linux-gnufilc0/include/ruby-3.3.0/ruby/internal/cast.h:31:28: note: expanded from macro 'RBIMPL_CAST'
   31 | # define RBIMPL_CAST(expr) (expr)
      |                            ^~~~~~
pcaprub.c:576:9: error: integer constant expression must have integer type, not 'VALUE' (aka 'struct rb_value_unit_struct *')
  576 |         case Qfalse:
      |              ^~~~~~
/nix/store/65in3amyafclxn1lg3yjb1v9a3ngk1rm-ruby-3.3.10-x86_64-unknown-linux-gnufilc0/include/ruby-3.3.0/ruby/internal/special_consts.h:59:25: note: expanded from macro 'Qfalse'
   59 | #define Qfalse          RUBY_Qfalse            /**< @old{RUBY_Qfalse} */
      |                         ^~~~~~~~~~~
/nix/store/65in3amyafclxn1lg3yjb1v9a3ngk1rm-ruby-3.3.10-x86_64-unknown-linux-gnufilc0/include/ruby-3.3.0/ruby/internal/special_consts.h:345:21: note: expanded from macro 'RUBY_Qfalse'
  345 | #define RUBY_Qfalse RBIMPL_CAST((VALUE)RUBY_Qfalse)
      |                     ^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
/nix/store/65in3amyafclxn1lg3yjb1v9a3ngk1rm-ruby-3.3.10-x86_64-unknown-linux-gnufilc0/include/ruby-3.3.0/ruby/internal/cast.h:31:28: note: expanded from macro 'RBIMPL_CAST'
   31 | # define RBIMPL_CAST(expr) (expr)
      |                            ^~~~~~
pcaprub.c:999:19: warning: pointer/integer type mismatch in conditional expression ('int' and 'VALUE' (aka 'struct rb_value_unit_struct *')) [-Wconditional-type-mismatch]
  999 |           packet == Qnil ? rb_thread_wait_fd(fno) : rb_yield(packet);
      |                          ^ ~~~~~~~~~~~~~~~~~~~~~~   ~~~~~~~~~~~~~~~~
pcaprub.c:1041:19: warning: pointer/integer type mismatch in conditional expression ('int' and 'VALUE' (aka 'struct rb_value_unit_struct *')) [-Wconditional-type-mismatch]
 1041 |           packet == Qnil ? rb_thread_wait_fd(fno) : rb_yield(packet);
      |                          ^ ~~~~~~~~~~~~~~~~~~~~~~   ~~~~~~~~~~~~~~~~
pcaprub.c:1174:35: warning: implicit conversion loses integer precision: '__time_t' (aka 'long') to 'int' [-Wshorten-64-to-32]
 1174 |   return INT2NUM(rbpacket->hdr.ts.tv_sec);
      |          ~~~~~~~ ~~~~~~~~~~~~~~~~~^~~~~~
pcaprub.c:1194:35: warning: implicit conversion loses integer precision: '__suseconds_t' (aka 'long') to 'int' [-Wshorten-64-to-32]
 1194 |   return INT2NUM(rbpacket->hdr.ts.tv_usec);
      |          ~~~~~~~ ~~~~~~~~~~~~~~~~~^~~~~~~
4 warnings and 3 errors generated.
make: *** [Makefile:248: pcaprub.o] Error 1

make failed, exit code 2

Gem files will remain installed in /nix/store/abcscwhgd2x0fvwn3hpl6d1lmrqfsb24-ruby3.3-pcaprub-0.13.3-x86_64-unknown-linux-gnufilc0/lib/ruby/gems/3.3.0/gems/pcaprub-0.13.3 for inspection.
Results logged to /nix/store/abcscwhgd2x0fvwn3hpl6d1lmrqfsb24-ruby3.3-pcaprub-0.13.3-x86_64-unknown-linux-gnufilc0/lib/ruby/gems/3.3.0/extensions/x86_64-linux/3.3.0/pcaprub-0.13.3/gem_make.out
```

</details>

<details>
<summary>❌ <strong>pg</strong>: build failed</summary>

```
make -C ../../../src/port all
make[1]: Entering directory '/build/source/src/port'
make[1]: Nothing to be done for 'all'.
make[1]: Leaving directory '/build/source/src/port'
make -C ../../../src/common all
make[1]: Entering directory '/build/source/src/common'
make[1]: Nothing to be done for 'all'.
make[1]: Leaving directory '/build/source/src/common'
/nix/store/rry6qingvsrqmc7ll7jgaqpybcbdgf5v-coreutils-9.7/bin/mkdir -p '/nix/store/6c2w761acwna1v6q4k7ywwqy1my2rbp8-libpq-x86_64-unknown-linux-gnufilc0-17.6/lib' '/nix/store/6c2w761acwna1v6q4k7ywwqy1my2rbp8-libpq-x86_64-unknown-linux-gnufilc0-17.6/lib/pkgconfig' 
/nix/store/rry6qingvsrqmc7ll7jgaqpybcbdgf5v-coreutils-9.7/bin/mkdir -p '/nix/store/5iicrvxcn5681ya4bj44nwchs6v04gy2-libpq-x86_64-unknown-linux-gnufilc0-17.6-dev/include' '/nix/store/5iicrvxcn5681ya4bj44nwchs6v04gy2-libpq-x86_64-unknown-linux-gnufilc0-17.6-dev/include/postgresql/internal' '/nix/store/6c2w761acwna1v6q4k7ywwqy1my2rbp8-libpq-x86_64-unknown-linux-gnufilc0-17.6/share/postgresql'
/nix/store/rry6qingvsrqmc7ll7jgaqpybcbdgf5v-coreutils-9.7/bin/install -c -m 755  libpq.so.5.17 '/nix/store/6c2w761acwna1v6q4k7ywwqy1my2rbp8-libpq-x86_64-unknown-linux-gnufilc0-17.6/lib/libpq.so.5.17'
cd '/nix/store/6c2w761acwna1v6q4k7ywwqy1my2rbp8-libpq-x86_64-unknown-linux-gnufilc0-17.6/lib' && \
rm -f libpq.so.5 && \
ln -s libpq.so.5.17 libpq.so.5
cd '/nix/store/6c2w761acwna1v6q4k7ywwqy1my2rbp8-libpq-x86_64-unknown-linux-gnufilc0-17.6/lib' && \
rm -f libpq.so && \
ln -s libpq.so.5.17 libpq.so
/nix/store/rry6qingvsrqmc7ll7jgaqpybcbdgf5v-coreutils-9.7/bin/install -c -m 644  libpq.a '/nix/store/6c2w761acwna1v6q4k7ywwqy1my2rbp8-libpq-x86_64-unknown-linux-gnufilc0-17.6/lib/libpq.a'
/nix/store/rry6qingvsrqmc7ll7jgaqpybcbdgf5v-coreutils-9.7/bin/install -c -m 644 libpq.pc '/nix/store/6c2w761acwna1v6q4k7ywwqy1my2rbp8-libpq-x86_64-unknown-linux-gnufilc0-17.6/lib/pkgconfig/libpq.pc'
/nix/store/rry6qingvsrqmc7ll7jgaqpybcbdgf5v-coreutils-9.7/bin/install -c -m 644 ./libpq-fe.h '/nix/store/5iicrvxcn5681ya4bj44nwchs6v04gy2-libpq-x86_64-unknown-linux-gnufilc0-17.6-dev/include'
/nix/store/rry6qingvsrqmc7ll7jgaqpybcbdgf5v-coreutils-9.7/bin/install -c -m 644 ./libpq-events.h '/nix/store/5iicrvxcn5681ya4bj44nwchs6v04gy2-libpq-x86_64-unknown-linux-gnufilc0-17.6-dev/include'
/nix/store/rry6qingvsrqmc7ll7jgaqpybcbdgf5v-coreutils-9.7/bin/install -c -m 644 ./libpq-int.h '/nix/store/5iicrvxcn5681ya4bj44nwchs6v04gy2-libpq-x86_64-unknown-linux-gnufilc0-17.6-dev/include/postgresql/internal'
/nix/store/rry6qingvsrqmc7ll7jgaqpybcbdgf5v-coreutils-9.7/bin/install -c -m 644 ./fe-auth-sasl.h '/nix/store/5iicrvxcn5681ya4bj44nwchs6v04gy2-libpq-x86_64-unknown-linux-gnufilc0-17.6-dev/include/postgresql/internal'
/nix/store/rry6qingvsrqmc7ll7jgaqpybcbdgf5v-coreutils-9.7/bin/install -c -m 644 ./pqexpbuffer.h '/nix/store/5iicrvxcn5681ya4bj44nwchs6v04gy2-libpq-x86_64-unknown-linux-gnufilc0-17.6-dev/include/postgresql/internal'
/nix/store/rry6qingvsrqmc7ll7jgaqpybcbdgf5v-coreutils-9.7/bin/install -c -m 644 ./pg_service.conf.sample '/nix/store/6c2w761acwna1v6q4k7ywwqy1my2rbp8-libpq-x86_64-unknown-linux-gnufilc0-17.6/share/postgresql/pg_service.conf.sample'
make: Leaving directory '/build/source/src/interfaces/libpq'
make: Entering directory '/build/source/src/port'
make -C ../../src/backend generated-headers
make[1]: Entering directory '/build/source/src/backend'
make -C ../include/catalog generated-headers
make[2]: Entering directory '/build/source/src/include/catalog'
make[2]: Nothing to be done for 'generated-headers'.
make[2]: Leaving directory '/build/source/src/include/catalog'
make -C nodes generated-header-symlinks
make[2]: Entering directory '/build/source/src/backend/nodes'
make[2]: Nothing to be done for 'generated-header-symlinks'.
make[2]: Leaving directory '/build/source/src/backend/nodes'
make -C utils generated-header-symlinks
make[2]: Entering directory '/build/source/src/backend/utils'
make -C adt jsonpath_gram.h
make[3]: Entering directory '/build/source/src/backend/utils/adt'
make[3]: 'jsonpath_gram.h' is up to date.
make[3]: Leaving directory '/build/source/src/backend/utils/adt'
make[2]: Leaving directory '/build/source/src/backend/utils'
make[1]: Leaving directory '/build/source/src/backend'
/nix/store/rry6qingvsrqmc7ll7jgaqpybcbdgf5v-coreutils-9.7/bin/mkdir -p '/nix/store/6c2w761acwna1v6q4k7ywwqy1my2rbp8-libpq-x86_64-unknown-linux-gnufilc0-17.6/lib'
/nix/store/rry6qingvsrqmc7ll7jgaqpybcbdgf5v-coreutils-9.7/bin/install -c -m 644  libpgport.a '/nix/store/6c2w761acwna1v6q4k7ywwqy1my2rbp8-libpq-x86_64-unknown-linux-gnufilc0-17.6/lib/libpgport.a'
/nix/store/rry6qingvsrqmc7ll7jgaqpybcbdgf5v-coreutils-9.7/bin/install -c -m 644  libpgport_shlib.a '/nix/store/6c2w761acwna1v6q4k7ywwqy1my2rbp8-libpq-x86_64-unknown-linux-gnufilc0-17.6/lib/libpgport_shlib.a'
make: Leaving directory '/build/source/src/port'
Moving /nix/store/6c2w761acwna1v6q4k7ywwqy1my2rbp8-libpq-x86_64-unknown-linux-gnufilc0-17.6/lib/libpgcommon.a to /nix/store/5iicrvxcn5681ya4bj44nwchs6v04gy2-libpq-x86_64-unknown-linux-gnufilc0-17.6-dev/lib/libpgcommon.a
Moving /nix/store/6c2w761acwna1v6q4k7ywwqy1my2rbp8-libpq-x86_64-unknown-linux-gnufilc0-17.6/lib/libpgcommon_shlib.a to /nix/store/5iicrvxcn5681ya4bj44nwchs6v04gy2-libpq-x86_64-unknown-linux-gnufilc0-17.6-dev/lib/libpgcommon_shlib.a
Moving /nix/store/6c2w761acwna1v6q4k7ywwqy1my2rbp8-libpq-x86_64-unknown-linux-gnufilc0-17.6/lib/libpgport.a to /nix/store/5iicrvxcn5681ya4bj44nwchs6v04gy2-libpq-x86_64-unknown-linux-gnufilc0-17.6-dev/lib/libpgport.a
Moving /nix/store/6c2w761acwna1v6q4k7ywwqy1my2rbp8-libpq-x86_64-unknown-linux-gnufilc0-17.6/lib/libpgport_shlib.a to /nix/store/5iicrvxcn5681ya4bj44nwchs6v04gy2-libpq-x86_64-unknown-linux-gnufilc0-17.6-dev/lib/libpgport_shlib.a
Moving /nix/store/6c2w761acwna1v6q4k7ywwqy1my2rbp8-libpq-x86_64-unknown-linux-gnufilc0-17.6/lib/libpq.a to /nix/store/5iicrvxcn5681ya4bj44nwchs6v04gy2-libpq-x86_64-unknown-linux-gnufilc0-17.6-dev/lib/libpq.a
removed '/nix/store/6c2w761acwna1v6q4k7ywwqy1my2rbp8-libpq-x86_64-unknown-linux-gnufilc0-17.6/share/postgresql/postgres.bki'
removed '/nix/store/6c2w761acwna1v6q4k7ywwqy1my2rbp8-libpq-x86_64-unknown-linux-gnufilc0-17.6/share/postgresql/system_constraints.sql'
removed '/nix/store/6c2w761acwna1v6q4k7ywwqy1my2rbp8-libpq-x86_64-unknown-linux-gnufilc0-17.6/share/postgresql/pg_service.conf.sample'
removed directory '/nix/store/6c2w761acwna1v6q4k7ywwqy1my2rbp8-libpq-x86_64-unknown-linux-gnufilc0-17.6/share/postgresql'
removed directory '/nix/store/6c2w761acwna1v6q4k7ywwqy1my2rbp8-libpq-x86_64-unknown-linux-gnufilc0-17.6/share'
removed '/nix/store/5iicrvxcn5681ya4bj44nwchs6v04gy2-libpq-x86_64-unknown-linux-gnufilc0-17.6-dev/lib/libpgcommon_shlib.a'
removed '/nix/store/5iicrvxcn5681ya4bj44nwchs6v04gy2-libpq-x86_64-unknown-linux-gnufilc0-17.6-dev/lib/libpgport_shlib.a'
removed '/nix/store/5iicrvxcn5681ya4bj44nwchs6v04gy2-libpq-x86_64-unknown-linux-gnufilc0-17.6-dev/lib/libpgcommon.a'
removed '/nix/store/5iicrvxcn5681ya4bj44nwchs6v04gy2-libpq-x86_64-unknown-linux-gnufilc0-17.6-dev/lib/libpgport.a'
removed '/nix/store/5iicrvxcn5681ya4bj44nwchs6v04gy2-libpq-x86_64-unknown-linux-gnufilc0-17.6-dev/lib/libpq.a'
Running phase: fixupPhase
Moving /nix/store/6c2w761acwna1v6q4k7ywwqy1my2rbp8-libpq-x86_64-unknown-linux-gnufilc0-17.6/lib/pkgconfig to /nix/store/5iicrvxcn5681ya4bj44nwchs6v04gy2-libpq-x86_64-unknown-linux-gnufilc0-17.6-dev/lib/pkgconfig
Patching '/nix/store/5iicrvxcn5681ya4bj44nwchs6v04gy2-libpq-x86_64-unknown-linux-gnufilc0-17.6-dev/lib/pkgconfig/libpq.pc' includedir to output /nix/store/5iicrvxcn5681ya4bj44nwchs6v04gy2-libpq-x86_64-unknown-linux-gnufilc0-17.6-dev
shrinking RPATHs of ELF executables and libraries in /nix/store/5iicrvxcn5681ya4bj44nwchs6v04gy2-libpq-x86_64-unknown-linux-gnufilc0-17.6-dev
checking for references to /build/ in /nix/store/5iicrvxcn5681ya4bj44nwchs6v04gy2-libpq-x86_64-unknown-linux-gnufilc0-17.6-dev...
patching script interpreter paths in /nix/store/5iicrvxcn5681ya4bj44nwchs6v04gy2-libpq-x86_64-unknown-linux-gnufilc0-17.6-dev
stripping (with command strip and flags -S -p) in  /nix/store/5iicrvxcn5681ya4bj44nwchs6v04gy2-libpq-x86_64-unknown-linux-gnufilc0-17.6-dev/lib
shrinking RPATHs of ELF executables and libraries in /nix/store/vkhrh2jqnhm0z1a69shgq7r3kci098ad-libpq-x86_64-unknown-linux-gnufilc0-17.6-debug
checking for references to /build/ in /nix/store/vkhrh2jqnhm0z1a69shgq7r3kci098ad-libpq-x86_64-unknown-linux-gnufilc0-17.6-debug...
patching script interpreter paths in /nix/store/vkhrh2jqnhm0z1a69shgq7r3kci098ad-libpq-x86_64-unknown-linux-gnufilc0-17.6-debug
separating debug info from /nix/store/6c2w761acwna1v6q4k7ywwqy1my2rbp8-libpq-x86_64-unknown-linux-gnufilc0-17.6/lib/libpq.so.5.17 (build ID 1e0a3aaf872656ad5c8a580117ede4c0620fe9ae)
shrinking RPATHs of ELF executables and libraries in /nix/store/6c2w761acwna1v6q4k7ywwqy1my2rbp8-libpq-x86_64-unknown-linux-gnufilc0-17.6
shrinking /nix/store/6c2w761acwna1v6q4k7ywwqy1my2rbp8-libpq-x86_64-unknown-linux-gnufilc0-17.6/lib/libpq.so.5.17
checking for references to /build/ in /nix/store/6c2w761acwna1v6q4k7ywwqy1my2rbp8-libpq-x86_64-unknown-linux-gnufilc0-17.6...
patching script interpreter paths in /nix/store/6c2w761acwna1v6q4k7ywwqy1my2rbp8-libpq-x86_64-unknown-linux-gnufilc0-17.6
stripping (with command strip and flags -S -p) in  /nix/store/6c2w761acwna1v6q4k7ywwqy1my2rbp8-libpq-x86_64-unknown-linux-gnufilc0-17.6/lib
```

</details>

<details>
<summary>❌ <strong>psych</strong>: date_core.c:6942:10: error: incompatible pointer to integer conversion assigning to 'st_index_t' (ak...</summary>

```
Running phase: unpackPhase
Running phase: patchPhase
Running phase: updateAutotoolsGnuConfigScriptsPhase
Running phase: updateAutotoolsGnuConfigScriptsPhase
Running phase: configurePhase
no configure script, doing nothing
Running phase: installPhase
buildFlags: 
WARNING:  You build with buildroot.
  Build root: /
  Bin dir: /nix/store/drq29c65krm5kca1klb16l3ly4i1qfhl-ruby3.3-date-3.4.1-x86_64-unknown-linux-gnufilc0/lib/ruby/gems/3.3.0/bin
  Gem home: /nix/store/drq29c65krm5kca1klb16l3ly4i1qfhl-ruby3.3-date-3.4.1-x86_64-unknown-linux-gnufilc0/lib/ruby/gems/3.3.0
  Plugins dir: /nix/store/drq29c65krm5kca1klb16l3ly4i1qfhl-ruby3.3-date-3.4.1-x86_64-unknown-linux-gnufilc0/lib/ruby/gems/3.3.0/plugins
Building native extensions. This could take a while...
ERROR:  Error installing /nix/store/2k05pr4b7l5vwphhxbjjfy8bpfym38sx-date-3.4.1.gem:
        ERROR: Failed to build gem native extension.

    current directory: /nix/store/drq29c65krm5kca1klb16l3ly4i1qfhl-ruby3.3-date-3.4.1-x86_64-unknown-linux-gnufilc0/lib/ruby/gems/3.3.0/gems/date-3.4.1/ext/date
/nix/store/65in3amyafclxn1lg3yjb1v9a3ngk1rm-ruby-3.3.10-x86_64-unknown-linux-gnufilc0/bin/ruby extconf.rb
checking for rb_category_warn()... yes
checking for timezone in time.h with  -Werror... yes
checking for altzone in time.h with  -Werror... no
creating Makefile

current directory: /nix/store/drq29c65krm5kca1klb16l3ly4i1qfhl-ruby3.3-date-3.4.1-x86_64-unknown-linux-gnufilc0/lib/ruby/gems/3.3.0/gems/date-3.4.1/ext/date
make DESTDIR\= sitearchdir\=./.gem.20251203-36-75r2od sitelibdir\=./.gem.20251203-36-75r2od clean

current directory: /nix/store/drq29c65krm5kca1klb16l3ly4i1qfhl-ruby3.3-date-3.4.1-x86_64-unknown-linux-gnufilc0/lib/ruby/gems/3.3.0/gems/date-3.4.1/ext/date
make DESTDIR\= sitearchdir\=./.gem.20251203-36-75r2od sitelibdir\=./.gem.20251203-36-75r2od
compiling date_core.c
date_core.c:6942:10: error: incompatible pointer to integer conversion assigning to 'st_index_t' (aka 'unsigned long') from 'VALUE' (aka 'struct rb_value_unit_struct *') [-Wint-conversion]
 6942 |     h[0] = m_nth(dat);
      |          ^ ~~~~~~~~~~
date_core.c:6945:10: error: incompatible pointer to integer conversion assigning to 'st_index_t' (aka 'unsigned long') from 'VALUE' (aka 'struct rb_value_unit_struct *') [-Wint-conversion]
 6945 |     h[3] = m_sf(dat);
      |          ^ ~~~~~~~~~
date_core.c:7038:6: warning: format specifies type 'long' but the argument has type 'VALUE' (aka 'struct rb_value_unit_struct *') [-Wformat]
 7036 |                           "#<%"PRIsVALUE": %"PRIsVALUE" "
      |                              ~~~~~~~~~~~
 7037 |                           "((%+"PRIsVALUE"j,%ds,%+"PRIsVALUE"n),%+ds,%.0fj)>",
 7038 |                           klass, to_s,
      |                           ^~~~~
date_core.c:7038:13: warning: format specifies type 'long' but the argument has type 'VALUE' (aka 'struct rb_value_unit_struct *') [-Wformat]
 7036 |                           "#<%"PRIsVALUE": %"PRIsVALUE" "
      |                                            ~~~~~~~~~~~
 7037 |                           "((%+"PRIsVALUE"j,%ds,%+"PRIsVALUE"n),%+ds,%.0fj)>",
 7038 |                           klass, to_s,
      |                                  ^~~~
date_core.c:7039:6: warning: format specifies type 'long' but the argument has type 'VALUE' (aka 'struct rb_value_unit_struct *') [-Wformat]
 7037 |                           "((%+"PRIsVALUE"j,%ds,%+"PRIsVALUE"n),%+ds,%.0fj)>",
      |                              ~~~~~~~~~~~~
 7038 |                           klass, to_s,
 7039 |                           m_real_jd(x), m_df(x), m_sf(x),
      |                           ^~~~~~~~~~~~
date_core.c:7039:29: warning: format specifies type 'long' but the argument has type 'VALUE' (aka 'struct rb_value_unit_struct *') [-Wformat]
 7037 |                           "((%+"PRIsVALUE"j,%ds,%+"PRIsVALUE"n),%+ds,%.0fj)>",
      |                                                 ~~~~~~~~~~~~
 7038 |                           klass, to_s,
 7039 |                           m_real_jd(x), m_df(x), m_sf(x),
      |                                                  ^~~~~~~
date_core.c:7443:18: warning: format specifies type 'long' but the argument has type 'VALUE' (aka 'struct rb_value_unit_struct *') [-Wformat]
 7442 |                  "wrong argument type %"PRIsVALUE" (expected Array or nil)",
      |                                       ~~~~~~~~~~~
 7443 |                  rb_obj_class(keys));
      |                  ^~~~~~~~~~~~~~~~~~
5 warnings and 2 errors generated.
make: *** [Makefile:248: date_core.o] Error 1

make failed, exit code 2

Gem files will remain installed in /nix/store/drq29c65krm5kca1klb16l3ly4i1qfhl-ruby3.3-date-3.4.1-x86_64-unknown-linux-gnufilc0/lib/ruby/gems/3.3.0/gems/date-3.4.1 for inspection.
Results logged to /nix/store/drq29c65krm5kca1klb16l3ly4i1qfhl-ruby3.3-date-3.4.1-x86_64-unknown-linux-gnufilc0/lib/ruby/gems/3.3.0/extensions/x86_64-linux/3.3.0/date-3.4.1/gem_make.out
```

```
copying path '/nix/store/zf48ji1qq8lg6mamcvw0xsa23jlhrwid-stringio-3.1.6.gem' from 'https://cache.nixos.org'...
Running phase: unpackPhase
Running phase: patchPhase
Running phase: updateAutotoolsGnuConfigScriptsPhase
Running phase: updateAutotoolsGnuConfigScriptsPhase
Running phase: configurePhase
no configure script, doing nothing
Running phase: installPhase
buildFlags: 
WARNING:  You build with buildroot.
  Build root: /
  Bin dir: /nix/store/84i003r360z5ym6cbizyxfmmv1w7hbsi-ruby3.3-stringio-3.1.6-x86_64-unknown-linux-gnufilc0/lib/ruby/gems/3.3.0/bin
  Gem home: /nix/store/84i003r360z5ym6cbizyxfmmv1w7hbsi-ruby3.3-stringio-3.1.6-x86_64-unknown-linux-gnufilc0/lib/ruby/gems/3.3.0
  Plugins dir: /nix/store/84i003r360z5ym6cbizyxfmmv1w7hbsi-ruby3.3-stringio-3.1.6-x86_64-unknown-linux-gnufilc0/lib/ruby/gems/3.3.0/plugins
Building native extensions. This could take a while...
```

</details>

<details>
<summary>❌ <strong>puma</strong>: monitor.c:209:14: error: incompatible integer to pointer conversion assigning to 'VALUE' (aka 'struc...</summary>

```
Running phase: unpackPhase
Running phase: patchPhase
Running phase: updateAutotoolsGnuConfigScriptsPhase
Running phase: updateAutotoolsGnuConfigScriptsPhase
Running phase: configurePhase
no configure script, doing nothing
Running phase: installPhase
buildFlags: 
WARNING:  You build with buildroot.
  Build root: /
  Bin dir: /nix/store/7az57g288ihyp3h3wd6bncn9042rm821-ruby3.3-nio4r-2.7.4-x86_64-unknown-linux-gnufilc0/lib/ruby/gems/3.3.0/bin
  Gem home: /nix/store/7az57g288ihyp3h3wd6bncn9042rm821-ruby3.3-nio4r-2.7.4-x86_64-unknown-linux-gnufilc0/lib/ruby/gems/3.3.0
  Plugins dir: /nix/store/7az57g288ihyp3h3wd6bncn9042rm821-ruby3.3-nio4r-2.7.4-x86_64-unknown-linux-gnufilc0/lib/ruby/gems/3.3.0/plugins
Building native extensions. This could take a while...
ERROR:  Error installing /nix/store/nrspcwwjbhzrj13pnkakl2f114ch1h17-nio4r-2.7.4.gem:
        ERROR: Failed to build gem native extension.

    current directory: /nix/store/7az57g288ihyp3h3wd6bncn9042rm821-ruby3.3-nio4r-2.7.4-x86_64-unknown-linux-gnufilc0/lib/ruby/gems/3.3.0/gems/nio4r-2.7.4/ext/nio4r
/nix/store/65in3amyafclxn1lg3yjb1v9a3ngk1rm-ruby-3.3.10-x86_64-unknown-linux-gnufilc0/bin/ruby extconf.rb
checking for unistd.h... yes
checking for rb_io_descriptor()... yes
checking for linux/aio_abi.h... yes
checking for linux/io_uring.h... yes
checking for sys/select.h... yes
checking for port_event_t in poll.h... no
checking for sys/epoll.h... yes
checking for sys/event.h... no
checking for port_event_t in port.h... no
checking for sys/resource.h... yes
creating Makefile

current directory: /nix/store/7az57g288ihyp3h3wd6bncn9042rm821-ruby3.3-nio4r-2.7.4-x86_64-unknown-linux-gnufilc0/lib/ruby/gems/3.3.0/gems/nio4r-2.7.4/ext/nio4r
make DESTDIR\= sitearchdir\=./.gem.20251203-36-t02yr5 sitelibdir\=./.gem.20251203-36-t02yr5 clean

current directory: /nix/store/7az57g288ihyp3h3wd6bncn9042rm821-ruby3.3-nio4r-2.7.4-x86_64-unknown-linux-gnufilc0/lib/ruby/gems/3.3.0/gems/nio4r-2.7.4/ext/nio4r
make DESTDIR\= sitearchdir\=./.gem.20251203-36-t02yr5 sitelibdir\=./.gem.20251203-36-t02yr5
compiling bytebuffer.c
compiling monitor.c
monitor.c:209:14: error: incompatible integer to pointer conversion assigning to 'VALUE' (aka 'struct rb_value_unit_struct *') from 'int' [-Wint-conversion]
  209 |     interest = monitor->interests | NIO_Monitor_symbol2interest(interest);
      |              ^ ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
monitor.c:210:40: warning: cast to smaller integer type 'int' from 'VALUE' (aka 'struct rb_value_unit_struct *') [-Wpointer-to-int-cast]
  210 |     NIO_Monitor_update_interests(self, (int)interest);
      |                                        ^~~~~~~~~~~~~
monitor.c:220:14: error: incompatible integer to pointer conversion assigning to 'VALUE' (aka 'struct rb_value_unit_struct *') from 'int' [-Wint-conversion]
  220 |     interest = monitor->interests & ~NIO_Monitor_symbol2interest(interest);
      |              ^ ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
monitor.c:221:40: warning: cast to smaller integer type 'int' from 'VALUE' (aka 'struct rb_value_unit_struct *') [-Wpointer-to-int-cast]
  221 |     NIO_Monitor_update_interests(self, (int)interest);
      |                                        ^~~~~~~~~~~~~
2 warnings and 2 errors generated.
make: *** [Makefile:248: monitor.o] Error 1

make failed, exit code 2

Gem files will remain installed in /nix/store/7az57g288ihyp3h3wd6bncn9042rm821-ruby3.3-nio4r-2.7.4-x86_64-unknown-linux-gnufilc0/lib/ruby/gems/3.3.0/gems/nio4r-2.7.4 for inspection.
Results logged to /nix/store/7az57g288ihyp3h3wd6bncn9042rm821-ruby3.3-nio4r-2.7.4-x86_64-unknown-linux-gnufilc0/lib/ruby/gems/3.3.0/extensions/x86_64-linux/3.3.0/nio4r-2.7.4/gem_make.out
```

</details>

<details>
<summary>✅ <strong>rbnacl</strong>: build succeeded</summary>

</details>

<details>
<summary>❌ <strong>re2</strong>: ../../lib/libicuuc.so: error: undefined reference to 'pizlonated_icudt76_dat'</summary>

```
config.status: creating tools/gendict/gendict.1
make[2]: Leaving directory '/build/icu/source/tools/gendict'
make[1]: Making `all' in `icuexportdata'
make[2]: Entering directory '/build/icu/source/tools/icuexportdata'
   (deps)        icuexportdata.cpp
cd ../.. \
 && CONFIG_FILES=tools/icuexportdata/icuexportdata.1 CONFIG_HEADERS= /nix/store/cfqbabpc7xwg8akbcchqbq3cai6qq2vs-bash-5.2p37/bin/bash ./config.status
   clang++       ...  icuexportdata.cpp
clang++ -O2 -W -Wall -pedantic -Wpointer-arith -Wwrite-strings -Wno-long-long -std=c++17  -Qunused-arguments -Wno-parentheses-equality   -o ../../bin/icuexportdata icuexportdata.o -L../../lib -licutu -L../../lib -licui18n -L../../lib -licuuc -L../../stubdata -licudata -lpthread -lm  
config.status: creating tools/icuexportdata/icuexportdata.1
make[2]: Leaving directory '/build/icu/source/tools/icuexportdata'
make[1]: Making `all' in `escapesrc'
make[2]: Entering directory '/build/icu/source/tools/escapesrc'
   (deps)        escapesrc.cpp
   clang++       ...  escapesrc.cpp
clang++ -O2 -W -Wall -pedantic -Wpointer-arith -Wwrite-strings -Wno-long-long -std=c++17  -Qunused-arguments -Wno-parentheses-equality   -o ../../bin/escapesrc escapesrc.o -lpthread -lm  
make[2]: Leaving directory '/build/icu/source/tools/escapesrc'
make[2]: Entering directory '/build/icu/source/tools'
make[2]: Nothing to be done for 'all-local'.
make[2]: Leaving directory '/build/icu/source/tools'
make[1]: Leaving directory '/build/icu/source/tools'
make[0]: Making `all' in `data'
make[1]: Entering directory '/build/icu/source/data'
make -f pkgdataMakefile
/nix/store/cfqbabpc7xwg8akbcchqbq3cai6qq2vs-bash-5.2p37/bin/bash ../mkinstalldirs ./out/tmp ./out/build/icudt76l
make[2]: Entering directory '/build/icu/source/data'
rm -rf icupkg.inc
mkdir ./out
mkdir ./out/tmp
mkdir ./out/build
mkdir ./out/build/icudt76l
Unpacking ./in/icudt76l.dat and generating out/tmp/icudata.lst (list of data files)
LD_LIBRARY_PATH=/nix/store/picm2hyv7mxa0s0q6v2vm8fxy1dcgfwv-icu4c-build-root-76.1/lib:/nix/store/picm2hyv7mxa0s0q6v2vm8fxy1dcgfwv-icu4c-build-root-76.1/stubdata:/nix/store/picm2hyv7mxa0s0q6v2vm8fxy1dcgfwv-icu4c-build-root-76.1/tools/ctestfw:$LD_LIBRARY_PATH /nix/store/picm2hyv7mxa0s0q6v2vm8fxy1dcgfwv-icu4c-build-root-76.1/bin/icupkg -d ./out/build/icudt76l --list -x \* ./in/icudt76l.dat -o out/tmp/icudata.lst
make[2]: Leaving directory '/build/icu/source/data'
echo timestamp > build-local
LD_LIBRARY_PATH=/nix/store/picm2hyv7mxa0s0q6v2vm8fxy1dcgfwv-icu4c-build-root-76.1/stubdata:/nix/store/picm2hyv7mxa0s0q6v2vm8fxy1dcgfwv-icu4c-build-root-76.1/tools/ctestfw:/nix/store/picm2hyv7mxa0s0q6v2vm8fxy1dcgfwv-icu4c-build-root-76.1/lib:$LD_LIBRARY_PATH  /nix/store/picm2hyv7mxa0s0q6v2vm8fxy1dcgfwv-icu4c-build-root-76.1/bin/pkgdata -O ../data/icupkg.inc -q -c -s /build/icu/source/data/out/build/icudt76l -d ../lib -e icudt76  -T ./out/tmp -p icudt76l -m dll -r 76.1 -L icudata ./out/tmp/icudata.lst
pkgdata: clang -D_REENTRANT  -DU_HAVE_ELF_H=1 -DU_HAVE_STRTOD_L=1 -DU_HAVE_XLOCALE_H=0  -DU_ALL_IMPLEMENTATION -DU_ATTRIBUTE_DEPRECATED= -O2 -std=c11 -Wall -pedantic -Wshadow -Wpointer-arith -Wmissing-prototypes -Wwrite-strings  -Qunused-arguments -Wno-parentheses-equality -c -I../common -I../common -DPIC -fPIC -o ./out/tmp/icudt76l_dat.o ./out/tmp/icudt76l_dat.S
pkgdata: clang -O2 -std=c11 -Wall -pedantic -Wshadow -Wpointer-arith -Wmissing-prototypes -Wwrite-strings  -Qunused-arguments -Wno-parentheses-equality  -shared -Wl,-Bsymbolic -nodefaultlibs -nostdlib -o ../lib/libicudata.so.76.1 ./out/tmp/icudt76l_dat.o -Wl,-soname -Wl,libicudata.so.76  -Wl,-Bsymbolic
pkgdata: cd ../lib/ && rm -f libicudata.so.76 && ln -s libicudata.so.76.1 libicudata.so.76
pkgdata: cd ../lib/ && rm -f libicudata.so && ln -s libicudata.so.76.1 libicudata.so
echo timestamp > packagedata
make[1]: Leaving directory '/build/icu/source/data'
make[0]: Making `all' in `extra'
make[1]: Entering directory '/build/icu/source/extra'
make[1]: Making `all' in `scrptrun'
make[2]: Entering directory '/build/icu/source/extra/scrptrun'
   (deps)        scrptrun.cpp
   (deps)        srtest.cpp
   clang++       ...  scrptrun.cpp
   clang++       ...  srtest.cpp
clang++ -O2 -W -Wall -pedantic -Wpointer-arith -Wwrite-strings -Wno-long-long -std=c++17  -Qunused-arguments -Wno-parentheses-equality   -o srtest scrptrun.o srtest.o -L../../lib -licuuc -L../../stubdata -licudata 
make[2]: Leaving directory '/build/icu/source/extra/scrptrun'
make[1]: Making `all' in `uconv'
make[2]: Entering directory '/build/icu/source/extra/uconv'
make -f pkgdataMakefile
   clang++       ...  uconv.cpp
   clang         ...  uwmsg.c
mkdir uconvmsg
make[3]: Entering directory '/build/icu/source/extra/uconv'
rm -rf pkgdata.inc
LD_LIBRARY_PATH=/nix/store/picm2hyv7mxa0s0q6v2vm8fxy1dcgfwv-icu4c-build-root-76.1/lib:/nix/store/picm2hyv7mxa0s0q6v2vm8fxy1dcgfwv-icu4c-build-root-76.1/stubdata:/nix/store/picm2hyv7mxa0s0q6v2vm8fxy1dcgfwv-icu4c-build-root-76.1/tools/ctestfw:$LD_LIBRARY_PATH /nix/store/picm2hyv7mxa0s0q6v2vm8fxy1dcgfwv-icu4c-build-root-76.1/bin/genrb -e UTF-8 -s resources -d uconvmsg root.txt
LD_LIBRARY_PATH=/nix/store/picm2hyv7mxa0s0q6v2vm8fxy1dcgfwv-icu4c-build-root-76.1/lib:/nix/store/picm2hyv7mxa0s0q6v2vm8fxy1dcgfwv-icu4c-build-root-76.1/stubdata:/nix/store/picm2hyv7mxa0s0q6v2vm8fxy1dcgfwv-icu4c-build-root-76.1/tools/ctestfw:$LD_LIBRARY_PATH /nix/store/picm2hyv7mxa0s0q6v2vm8fxy1dcgfwv-icu4c-build-root-76.1/bin/genrb -e UTF-8 -s resources -d uconvmsg fr.txt
make[3]: Leaving directory '/build/icu/source/extra/uconv'
LD_LIBRARY_PATH=/nix/store/picm2hyv7mxa0s0q6v2vm8fxy1dcgfwv-icu4c-build-root-76.1/lib:/nix/store/picm2hyv7mxa0s0q6v2vm8fxy1dcgfwv-icu4c-build-root-76.1/stubdata:/nix/store/picm2hyv7mxa0s0q6v2vm8fxy1dcgfwv-icu4c-build-root-76.1/tools/ctestfw:$LD_LIBRARY_PATH  /nix/store/picm2hyv7mxa0s0q6v2vm8fxy1dcgfwv-icu4c-build-root-76.1/bin/pkgdata -p uconvmsg -O pkgdata.inc -m static -s uconvmsg -d uconvmsg -T uconvmsg uconvmsg/uconvmsg.lst
cd ../.. \
 && CONFIG_FILES=extra/uconv/uconv.1 CONFIG_HEADERS= /nix/store/cfqbabpc7xwg8akbcchqbq3cai6qq2vs-bash-5.2p37/bin/bash ./config.status
pkgdata: clang -D_REENTRANT  -DU_HAVE_ELF_H=1 -DU_HAVE_STRTOD_L=1 -DU_HAVE_XLOCALE_H=0  -DU_ALL_IMPLEMENTATION -DU_ATTRIBUTE_DEPRECATED= -O2 -std=c11 -Wall -pedantic -Wshadow -Wpointer-arith -Wmissing-prototypes -Wwrite-strings  -Qunused-arguments -Wno-parentheses-equality -c -I../../common -I../../common -DPIC -fPIC -o uconvmsg/uconvmsg_dat.o uconvmsg/uconvmsg_dat.S
pkgdata: ar r uconvmsg/libuconvmsg.a uconvmsg/uconvmsg_dat.o
ar: creating uconvmsg/libuconvmsg.a
pkgdata: ranlib uconvmsg/libuconvmsg.a
clang++ -O2 -W -Wall -pedantic -Wpointer-arith -Wwrite-strings -Wno-long-long -std=c++17  -Qunused-arguments -Wno-parentheses-equality   -o ../../bin/uconv uconv.o uwmsg.o -L../../lib -licui18n -L../../lib -licuuc -L../../stubdata -licudata -lpthread -lm   uconvmsg/libuconvmsg.a
config.status: creating extra/uconv/uconv.1
../../lib/libicuuc.so: error: undefined reference to 'pizlonated_icudt76_dat'
uconv.o:uconv.cpp:function pizlonatedFI__ZL7initMsgPKc:(.text+0xc0c4): error: undefined reference to 'pizlonated_uconvmsg_dat'
clang-20: error: linker command failed with exit code 1 (use -v to see invocation)
make[2]: *** [Makefile:148: ../../bin/uconv] Error 1
make[2]: Leaving directory '/build/icu/source/extra/uconv'
make[1]: *** [Makefile:49: all-recursive] Error 2
make[1]: Leaving directory '/build/icu/source/extra'
make: *** [Makefile:153: all-recursive] Error 2
```

```
unpacking source archive /nix/store/03n938kk5f5nhnvryka2ikl7ddfc6bhj-source
source root is source
Running phase: patchPhase
Running phase: updateAutotoolsGnuConfigScriptsPhase
Running phase: updateAutotoolsGnuConfigScriptsPhase
Running phase: configurePhase
fixing cmake files...
cmake flags: -GNinja -DCMAKE_FIND_USE_SYSTEM_PACKAGE_REGISTRY=OFF -DCMAKE_FIND_USE_PACKAGE_REGISTRY=OFF -DCMAKE_EXPORT_NO_PACKAGE_REGISTRY=ON -DCMAKE_BUILD_TYPE=Release -DCMAKE_INSTALL_LOCALEDIR=/nix/store/mwfxfjp65vgbvx1hnhay9h5g5i2gp4wf-gbenchmark-x86_64-unknown-linux-gnufilc0-1.9.1/share/locale -DCMAKE_INSTALL_LIBEXECDIR=/nix/store/mwfxfjp65vgbvx1hnhay9h5g5i2gp4wf-gbenchmark-x86_64-unknown-linux-gnufilc0-1.9.1/libexec -DCMAKE_INSTALL_LIBDIR=/nix/store/mwfxfjp65vgbvx1hnhay9h5g5i2gp4wf-gbenchmark-x86_64-unknown-linux-gnufilc0-1.9.1/lib -DCMAKE_INSTALL_DOCDIR=/nix/store/mwfxfjp65vgbvx1hnhay9h5g5i2gp4wf-gbenchmark-x86_64-unknown-linux-gnufilc0-1.9.1/share/doc/benchmark -DCMAKE_INSTALL_INFODIR=/nix/store/mwfxfjp65vgbvx1hnhay9h5g5i2gp4wf-gbenchmark-x86_64-unknown-linux-gnufilc0-1.9.1/share/info -DCMAKE_INSTALL_MANDIR=/nix/store/mwfxfjp65vgbvx1hnhay9h5g5i2gp4wf-gbenchmark-x86_64-unknown-linux-gnufilc0-1.9.1/share/man -DCMAKE_INSTALL_INCLUDEDIR=/nix/store/mwfxfjp65vgbvx1hnhay9h5g5i2gp4wf-gbenchmark-x86_64-unknown-linux-gnufilc0-1.9.1/include -DCMAKE_INSTALL_SBINDIR=/nix/store/mwfxfjp65vgbvx1hnhay9h5g5i2gp4wf-gbenchmark-x86_64-unknown-linux-gnufilc0-1.9.1/sbin -DCMAKE_INSTALL_BINDIR=/nix/store/mwfxfjp65vgbvx1hnhay9h5g5i2gp4wf-gbenchmark-x86_64-unknown-linux-gnufilc0-1.9.1/bin -DCMAKE_INSTALL_NAME_DIR=/nix/store/mwfxfjp65vgbvx1hnhay9h5g5i2gp4wf-gbenchmark-x86_64-unknown-linux-gnufilc0-1.9.1/lib -DCMAKE_POLICY_DEFAULT_CMP0025=NEW -DCMAKE_FIND_FRAMEWORK=LAST -DCMAKE_STRIP=/nix/store/a0nc03czg70yaj0p9qphx5b3ppnb939i-filc-cc-wrapper-/bin/strip -DCMAKE_RANLIB=/nix/store/a0nc03czg70yaj0p9qphx5b3ppnb939i-filc-cc-wrapper-/bin/ranlib -DCMAKE_AR=/nix/store/a0nc03czg70yaj0p9qphx5b3ppnb939i-filc-cc-wrapper-/bin/ar -DCMAKE_C_COMPILER=clang -DCMAKE_CXX_COMPILER=clang++ -DCMAKE_INSTALL_PREFIX=/nix/store/mwfxfjp65vgbvx1hnhay9h5g5i2gp4wf-gbenchmark-x86_64-unknown-linux-gnufilc0-1.9.1 -DBENCHMARK_USE_BUNDLED_GTEST:BOOL=FALSE -DBENCHMARK_ENABLE_WERROR:BOOL=FALSE -DCMAKE_SYSTEM_NAME=Linux -DCMAKE_SYSTEM_PROCESSOR=x86_64 -DCMAKE_HOST_SYSTEM_NAME=Linux -DCMAKE_HOST_SYSTEM_PROCESSOR=x86_64 -DCMAKE_CROSSCOMPILING_EMULATOR=env
-- The CXX compiler identification is Clang 20.1.8
-- Detecting CXX compiler ABI info
-- Detecting CXX compiler ABI info - done
-- Check for working CXX compiler: /nix/store/a0nc03czg70yaj0p9qphx5b3ppnb939i-filc-cc-wrapper-/bin/clang++ - skipped
-- Detecting CXX compile features
-- Detecting CXX compile features - done
-- Failed to find LLVM FileCheck
-- Could NOT find Git (missing: GIT_EXECUTABLE) 
-- Google Benchmark version: v1.9.1, normalized to 1.9.1
-- Looking for shm_open in rt
-- Looking for shm_open in rt - found
-- Performing Test HAVE_CXX_FLAG_WALL
-- Performing Test HAVE_CXX_FLAG_WALL - Success
-- Performing Test HAVE_CXX_FLAG_WEXTRA
-- Performing Test HAVE_CXX_FLAG_WEXTRA - Success
-- Performing Test HAVE_CXX_FLAG_WSHADOW
-- Performing Test HAVE_CXX_FLAG_WSHADOW - Success
-- Performing Test HAVE_CXX_FLAG_WFLOAT_EQUAL
-- Performing Test HAVE_CXX_FLAG_WFLOAT_EQUAL - Success
-- Performing Test HAVE_CXX_FLAG_WOLD_STYLE_CAST
-- Performing Test HAVE_CXX_FLAG_WOLD_STYLE_CAST - Success
-- Performing Test HAVE_CXX_FLAG_WCONVERSION
-- Performing Test HAVE_CXX_FLAG_WCONVERSION - Success
-- Performing Test HAVE_CXX_FLAG_PEDANTIC
-- Performing Test HAVE_CXX_FLAG_PEDANTIC - Success
-- Performing Test HAVE_CXX_FLAG_PEDANTIC_ERRORS
-- Performing Test HAVE_CXX_FLAG_PEDANTIC_ERRORS - Success
-- Performing Test HAVE_CXX_FLAG_WSHORTEN_64_TO_32
-- Performing Test HAVE_CXX_FLAG_WSHORTEN_64_TO_32 - Success
-- Performing Test HAVE_CXX_FLAG_FSTRICT_ALIASING
-- Performing Test HAVE_CXX_FLAG_FSTRICT_ALIASING - Success
-- Performing Test HAVE_CXX_FLAG_WNO_DEPRECATED_DECLARATIONS
-- Performing Test HAVE_CXX_FLAG_WNO_DEPRECATED_DECLARATIONS - Success
-- Performing Test HAVE_CXX_FLAG_WSTRICT_ALIASING
-- Performing Test HAVE_CXX_FLAG_WSTRICT_ALIASING - Success
-- Performing Test HAVE_CXX_FLAG_WD654
-- Performing Test HAVE_CXX_FLAG_WD654 - Failed
-- Performing Test HAVE_CXX_FLAG_WTHREAD_SAFETY
-- Performing Test HAVE_CXX_FLAG_WTHREAD_SAFETY - Success
-- Enabling additional flags: -DINCLUDE_DIRECTORIES=/build/source/include
-- Cross-compiling to test HAVE_THREAD_SAFETY_ATTRIBUTES
CMake Warning at cmake/CXXFeatureCheck.cmake:49 (message):
  If you see build failures due to cross compilation, try setting
  HAVE_THREAD_SAFETY_ATTRIBUTES to 0
Call Stack (most recent call first):
  CMakeLists.txt:233 (cxx_feature_check)


-- Performing Test HAVE_THREAD_SAFETY_ATTRIBUTES -- success
-- Performing Test HAVE_CXX_FLAG_COVERAGE
-- Performing Test HAVE_CXX_FLAG_COVERAGE - Failed
-- Cross-compiling to test HAVE_STD_REGEX
CMake Warning at cmake/CXXFeatureCheck.cmake:49 (message):
  If you see build failures due to cross compilation, try setting
  HAVE_STD_REGEX to 0
Call Stack (most recent call first):
  CMakeLists.txt:312 (cxx_feature_check)


-- Performing Test HAVE_STD_REGEX -- success
-- Cross-compiling to test HAVE_GNU_POSIX_REGEX
-- Performing Test HAVE_GNU_POSIX_REGEX -- failed to compile
-- Cross-compiling to test HAVE_POSIX_REGEX
CMake Warning at cmake/CXXFeatureCheck.cmake:49 (message):
  If you see build failures due to cross compilation, try setting
  HAVE_POSIX_REGEX to 0
Call Stack (most recent call first):
  CMakeLists.txt:314 (cxx_feature_check)


-- Performing Test HAVE_POSIX_REGEX -- success
-- Cross-compiling to test HAVE_STEADY_CLOCK
```

</details>

<details>
<summary>❌ <strong>rmagick</strong>: build failed</summary>

```
checking whether M_PI is declared... yes
checking for deflate in -lz... yes
checking for floor in -lm... yes
checking for uint64_t... yes
checking for getopt_long... yes
checking whether getopt_long reorders its arguments... maybe (cross-compiling)
checking whether to use included getopt... yes
checking for strcasecmp... yes
checking for strncasecmp... yes
checking for Intel 386... yes
checking for inline... inline
checking that generated files are newer than configure... done
configure: creating ./config.status
config.status: creating Makefile
config.status: creating src/Makefile
config.status: creating doc/Makefile
config.status: creating check/Makefile
config.status: creating doc/potrace.1
config.status: creating doc/mkbitmap.1
config.status: creating config.h
config.status: executing depfiles commands
config.status: executing libtool commands
Running phase: buildPhase
build flags: -j32 SHELL=/nix/store/cfqbabpc7xwg8akbcchqbq3cai6qq2vs-bash-5.2p37/bin/bash
make  all-recursive
make[1]: Entering directory '/build/potrace-1.16'
Making all in src
make[2]: Entering directory '/build/potrace-1.16/src'
clang -DHAVE_CONFIG_H -I. -I..  -I./include/getopt   -g -O2 -c -o main.o main.c
clang -DHAVE_CONFIG_H -I. -I..  -I./include/getopt   -g -O2 -c -o bitmap_io.o bitmap_io.c
clang -DHAVE_CONFIG_H -I. -I..  -I./include/getopt   -g -O2 -c -o backend_eps.o backend_eps.c
clang -DHAVE_CONFIG_H -I. -I..  -I./include/getopt   -g -O2 -c -o flate.o flate.c
clang -DHAVE_CONFIG_H -I. -I..  -I./include/getopt   -g -O2 -c -o greymap.o greymap.c
clang -DHAVE_CONFIG_H -I. -I..  -I./include/getopt   -g -O2 -c -o render.o render.c
clang -DHAVE_CONFIG_H -I. -I..  -I./include/getopt   -g -O2 -c -o backend_pgm.o backend_pgm.c
clang -DHAVE_CONFIG_H -I. -I..  -I./include/getopt   -g -O2 -c -o backend_svg.o backend_svg.c
clang -DHAVE_CONFIG_H -I. -I..  -I./include/getopt   -g -O2 -c -o backend_xfig.o backend_xfig.c
clang -DHAVE_CONFIG_H -I. -I..  -I./include/getopt   -g -O2 -c -o backend_dxf.o backend_dxf.c
clang -DHAVE_CONFIG_H -I. -I..  -I./include/get
opt   -g -O2 -c -o backend_pdf.o backend_pdf.c
clang -DHAVE_CONFIG_H -I. -I..  -I./include/getopt   -g -O2 -c -o backend_geojson.o backend_geojson.c
clang -DHAVE_CONFIG_H -I. -I..  -I./include/getopt   -g -O2 -c -o lzw.o lzw.c
clang -DHAVE_CONFIG_H -I. -I..  -I./include/getopt   -g -O2 -c -o progress_bar.o progress_bar.c
clang -DHAVE_CONFIG_H -I. -I..  -I./include/getopt   -g -O2 -c -o bbox.o bbox.c
clang -DHAVE_CONFIG_H -I. -I..  -I./include/getopt   -g -O2 -c -o trans.o trans.c
/nix/store/cfqbabpc7xwg8akbcchqbq3cai6qq2vs-bash-5.2p37/bin/bash ../libtool  --tag=CC   --mode=compile clang -DHAVE_CONFIG_H -I. -I..  -I./include/getopt   -g -O2 -c -o curve.lo curve.c
/nix/store/cfqbabpc7xwg8akbcchqbq3cai6qq2vs-bash-5.2p37/bin/bash ../libtool  --tag=CC   --mode=compile clang -DHAVE_CONFIG_H -I. -I..  -I./include/getopt   -g -O2 -c -o trace.lo trace.c
/nix/store/cfqbabpc7xwg8akbcchqbq3cai6qq2vs-bash-5.2p37/bin/bash ../libtool  --tag=CC   --mode=compile clang -DHAVE_CONFIG_H -I. -I..  -I./include/getopt   -g -O2 -c -o decompose.lo decompose.c
/nix/store/cfqbabpc7xwg8akbcchqbq3cai6qq2vs-bash-5.2p37/bin/bash ../libtool  --tag=CC   --mode=compile clang -DHAVE_CONFIG_H -I. -I..  -I./include/getopt   -g -O2 -c -o potracelib.lo potracelib.c
clang -DHAVE_CONFIG_H -I. -I..  -I./include/getopt   -g -O2 -c -o getopt.o getopt.c
clang -DHAVE_CONFIG_H -I. -I..  -I./include/getopt   -g -O2 -c -o getopt1.o getopt1.c
clang -DHAVE_CONFIG_H -I. -I..  -I./include/getopt   -g -O2 -c -o mkbitmap.o mkbitmap.c
getopt1.c:48:1: warning: a function definition without a prototype is deprecated in all versions of C and is not supported in C23 [-Wdeprecated-non-prototype]
   48 | getopt_long (argc, argv, options, long_options, opt_index)
      | ^
getopt1.c:64:1: warning: a function definition without a prototype is deprecated in all versions of C and is not supported in C23 [-Wdeprecated-non-prototype]
   64 | getopt_long_only (argc, argv, options, long_options, opt_index)
      | ^
2 warnings generated.
getopt.c:287:1: warning: a function definition without a prototype is deprecated in all versions of C and is not supported in C23 [-Wdeprecated-non-prototype]
  287 | exchange (argv)
      | ^
getopt.c:372:1: warning: a function definition without a prototype is deprecated in all versions of C and is not supported in C23 [-Wdeprecated-non-prototype]
  372 | _getopt_initialize (argc, argv, optstring)
      | ^
getopt.c:494:1: warning: a function definition without a prototype is deprecated in all versions of C and is not supported in C23 [-Wdeprecated-non-prototype]
  494 | _getopt_internal (argc, argv, optstring, longopts, longind, long_only)
      | ^
getopt.c:959:1: warning: a function definition without a prototype is deprecated in all versions of C and is not supported in C23 [-Wdeprecated-non-prototype]
  959 | getopt (argc, argv, optstring)
      | ^
4 warnings generated.
/nix/store/cfqbabpc7xwg8akbcchqbq3cai6qq2vs-bash-5.2p37/bin/bash ../libtool  --tag=CC   --mode=link clang  -g -O2   -o mkbitmap mkbitmap.o bitmap_io.o greymap.o getopt.o getopt1.o -lm 
libtool: compile:  clang -DHAVE_CONFIG_H -I. -I.. -I./include/getopt -g -O2 -c curve.c  -fPIC -DPIC -o .libs/curve.o
libtool: compile:  clang -DHAVE_CONFIG_H -I. -I.. -I./include/getopt -g -O2 -c decompose.c  -fPIC -DPIC -o .libs/decompose.o
libtool: compile:  clang -DHAVE_CONFIG_H -I. -I.. -I./include/getopt -g -O2 -c trace.c  -fPIC -DPIC -o .libs/trace.o
libtool: compile:  clang -DHAVE_CONFIG_H -I. -I.. -I./include/getopt -g -O2 -c potracelib.c  -fPIC -DPIC -o .libs/potracelib.o
/nix/store/cfqbabpc7xwg8akbcchqbq3cai6qq2vs-bash-5.2p37/bin/bash ../libtool  --tag=CC   --mode=link clang  -g -O2 -version-info 0:6:0 -rpath '/nix/store/71kq7z0j6zjmgx99rls3lignh498w8x0-potrace-x86_64-unknown-linux-gnufilc0-1.16/lib' -export-symbols ./libpotrace-export.sym -no-undefined  -o libpotrace.la  curve.lo trace.lo decompose.lo potracelib.lo -lm 
libtool: link: clang -g -O2 -o mkbitmap mkbitmap.o bitmap_io.o greymap.o getopt.o getopt1.o  -lm
libtool: link: echo "{ global:" > .libs/libpotrace.ver
```

```
[19/119] Compiling C object src/libdav1d_bitdepth_8.a.p/lf_apply_tmpl.c.o
[20/119] Compiling C object src/libdav1d_bitdepth_16.a.p/lf_apply_tmpl.c.o
[21/119] Compiling C object src/libdav1d_bitdepth_8.a.p/filmgrain_tmpl.c.o
[22/119] Compiling C object src/libdav1d_bitdepth_8.a.p/ipred_tmpl.c.o
[23/119] Compiling C object src/libdav1d_bitdepth_16.a.p/filmgrain_tmpl.c.o
[24/119] Compiling C object src/libdav1d_bitdepth_16.a.p/ipred_tmpl.c.o
[25/119] Generating 'src/libdav1d.so.7.0.0.p/cdef16_avx512.obj'
[26/119] Generating 'src/libdav1d.so.7.0.0.p/looprestoration_avx512.obj'
[27/119] Generating 'src/libdav1d.so.7.0.0.p/filmgrain_avx512.obj'
[28/119] Compiling C object src/libdav1d_bitdepth_16.a.p/looprestoration_tmpl.c.o
[29/119] Compiling C object src/libdav1d_bitdepth_8.a.p/looprestoration_tmpl.c.o
[30/119] Generating 'src/libdav1d.so.7.0.0.p/ipred_avx512.obj'
[31/119] Compiling C object src/libdav1d_bitdepth_8.a.p/mc_tmpl.c.o
[32/119] Compiling C object src/libdav1d_bitdepth_16.a.p/mc_tmpl.c.o
[33/119] Generating 'src/libdav1d.so.7.0.0.p/loopfilter_avx512.obj'
[34/119] Generating 'src/libdav1d.so.7.0.0.p/filmgrain16_avx512.obj'
[35/119] Generating 'src/libdav1d.so.7.0.0.p/looprestoration_avx2.obj'
[36/119] Generating 'src/libdav1d.so.7.0.0.p/cdef16_avx2.obj'
[37/119] Generating 'src/libdav1d.so.7.0.0.p/ipred16_avx512.obj'
[38/119] Generating 'src/libdav1d.so.7.0.0.p/loopfilter16_avx512.obj'
[39/119] Generating 'src/libdav1d.so.7.0.0.p/loopfilter_avx2.obj'
[40/119] Compiling C object src/libdav1d_bitdepth_8.a.p/itx_tmpl.c.o
[41/119] Compiling C object src/libdav1d_bitdepth_16.a.p/itx_tmpl.c.o
[42/119] Generating 'src/libdav1d.so.7.0.0.p/looprestoration16_avx512.obj'
[43/119] Generating 'src/libdav1d.so.7.0.0.p/cdef16_sse.obj'
[44/119] Generating 'src/libdav1d.so.7.0.0.p/loopfilter_sse.obj'
[45/119] Generating 'src/libdav1d.so.7.0.0.p/cdef_avx2.obj'
[46/119] Compiling C object src/libdav1d.so.7.0.0.p/ctx.c.o
[47/119] Generating 'src/libdav1d.so.7.0.0.p/filmgrain_avx2.obj'
[48/119] Compiling C object src/libdav1d.so.7.0.0.p/cpu.c.o
[49/119] Generating 'src/libdav1d.so.7.0.0.p/loopfilter16_avx2.obj'
[50/119] Compiling C object src/libdav1d.so.7.0.0.p/dequant_tables.c.o
[51/119] Compiling C object src/libdav1d.so.7.0.0.p/getbits.c.o
[52/119] Generating 'src/libdav1d.so.7.0.0.p/looprestoration_sse.obj'
[53/119] Compiling C object src/libdav1d.so.7.0.0.p/intra_edge.c.o
[54/119] Compiling C object src/libdav1d.so.7.0.0.p/data.c.o
[55/119] Compiling C object src/libdav1d.so.7.0.0.p/cdf.c.o
[56/119] Compiling C object src/libdav1d.so.7.0.0.p/log.c.o
[57/119] Compiling C object src/libdav1d_bitdepth_16.a.p/recon_tmpl.c.o
[58/119] Compiling C object src/libdav1d.so.7.0.0.p/mem.c.o
[59/119] Generating 'src/libdav1d.so.7.0.0.p/looprestoration16_avx2.obj'
[60/119] Compiling C object src/libdav1d.so.7.0.0.p/pal.c.o
[61/119] Compiling C object src/libdav1d.so.7.0.0.p/msac.c.o
[62/119] Compiling C object src/libdav1d.so.7.0.0.p/lf_mask.c.o
[63/119] Compiling C object src/libdav1d_bitdepth_8.a.p/recon_tmpl.c.o
[64/119] Compiling C object src/libdav1d.so.7.0.0.p/ref.c.o
[65/119] Generating 'src/libdav1d.so.7.0.0.p/loopfilter16_sse.obj'
[66/119] Compiling C object src/libdav1d.so.7.0.0.p/qm.c.o
[67/119] Compiling C object src/libdav1d.so.7.0.0.p/scan.c.o
[68/119] Compiling C object src/libdav1d.so.7.0.0.p/tables.c.o
[69/119] Compiling C object src/libdav1d.so.7.0.0.p/lib.c.o
[70/119] Generating 'src/libdav1d.so.7.0.0.p/mc_avx512.obj'
[71/119] Compiling C object src/libdav1d.so.7.0.0.p/picture.c.o
[72/119] Compiling C object tests/common.h_test.p/header_test.c.o
[73/119] Compiling C object src/libdav1d.so.7.0.0.p/x86_cpu.c.o
[74/119] Compiling C object tests/data.h_test.p/header_test.c.o
[75/119] Compiling C object src/libdav1d.so.7.0.0.p/warpmv.c.o
[76/119] Compiling C object tests/dav1d.h_test.p/header_test.c.o
[77/119] Generating 'src/libdav1d.so.7.0.0.p/looprestoration16_sse.obj'
[78/119] Compiling C object tests/picture.h_test.p/header_test.c.o
[79/119] Compiling C object tests/headers.h_test.p/header_test.c.o
[80/119] Compiling C object tests/version.h_test.p/header_test.c.o
[81/119] Generating 'src/libdav1d.so.7.0.0.p/ipred_avx2.obj'
[82/119] Linking target tests/data.h_test
[83/119] Linking target tests/dav1d.h_test
[84/119] Linking target tests/common.h_test
[85/119] Compiling C object tests/libfuzzer/dav1d_fuzzer.p/dav1d_fuzzer.c.o
[86/119] Compiling C object src/libdav1d.so.7.0.0.p/wedge.c.o
[87/119] Linking target tests/headers.h_test
[88/119] Compiling C object tests/libfuzzer/dav1d_fuzzer.p/main.c.o
[89/119] Linking target tests/picture.h_test
[90/119] Linking target tests/version.h_test
[91/119] Generating 'src/libdav1d.so.7.0.0.p/filmgrain_sse.obj'
[92/119] Compiling C object tests/libfuzzer/dav1d_fuzzer_mt.p/main.c.o
[93/119] Compiling C object tests/libfuzzer/dav1d_fuzzer_mt.p/dav1d_fuzzer.c.o
[94/119] Compiling C object src/libdav1d.so.7.0.0.p/itx_1d.c.o
[95/119] Generating 'src/libdav1d.so.7.0.0.p/filmgrain16_avx2.obj'
[96/119] Generating 'src/libdav1d.so.7.0.0.p/mc16_avx512.obj'
[97/119] Compiling C object src/libdav1d.so.7.0.0.p/refmvs.c.o
[98/119] Generating 'src/libdav1d.so.7.0.0.p/cdef_sse.obj'
```

```
checking for stdio.h... yes
checking for stdlib.h... yes
checking for string.h... yes
checking for inttypes.h... yes
checking for stdint.h... yes
checking for strings.h... yes
checking for sys/stat.h... yes
checking for sys/types.h... yes
checking for unistd.h... yes
checking for wchar.h... yes
checking for minix/config.h... no
checking for uchar.h... yes
checking for sys/param.h... yes
checking for sys/socket.h... yes
checking for error.h... yes
checking for getopt.h... yes
checking for sys/cdefs.h... yes
checking for threads.h... yes
checking for iconv.h... yes
checking for limits.h... yes
checking for crtdefs.h... no
checking for wctype.h... yes
checking for langinfo.h... yes
checking for xlocale.h... no
checking for sys/mman.h... yes
checking for sys/time.h... yes
checking for stdbool.h... yes
checking for stdckdint.h... yes
checking for features.h... yes
checking whether it is safe to define __EXTENSIONS__... yes
checking whether _XOPEN_SOURCE should be defined... no
checking whether to use C++... yes
checking whether the C++ compiler (clang++  ) works... yes
checking whether the C++ compiler supports namespaces... yes
checking dependency style of clang++... none
checking whether the compiler supports GNU C++... yes
checking whether clang++ accepts -g... yes
checking for clang option to enable large file support... none needed
checking whether C compiler handles -Werror -Wunknown-warning-option... yes
checking how to print strings... printf
checking for a sed that does not truncate output... /nix/store/4rpiqv9yr2pw5094v4wc33ijkqjpm9sa-gnused-4.9/bin/sed
checking for grep that handles long lines and -e... /nix/store/l2wvwyg680h0v2la18hz3yiznxy2naqw-gnugrep-3.11/bin/grep
checking for egrep... /nix/store/l2wvwyg680h0v2la18hz3yiznxy2naqw-gnugrep-3.11/bin/grep -E
checking for fgrep... /nix/store/l2wvwyg680h0v2la18hz3yiznxy2naqw-gnugrep-3.11/bin/grep -F
checking for ld used by clang... ld
checking if the linker (ld) is GNU ld... yes
checking for BSD- or MS-compatible name lister (nm)... nm
checking the name lister (nm) interface... BSD nm
checking whether ln -s works... yes
checking the maximum length of command line arguments... 4718592
checking how to convert x86_64-unknown-linux-gnu file names to x86_64-unknown-linux-gnufilc0 format... func_convert_file_noop
checking how to convert x86_64-unknown-linux-gnu file names to toolchain format... func_convert_file_noop
checking for ld option to reload object files... -r
checking for x86_64-unknown-linux-gnufilc0-file... no
checking for file... file
configure: WARNING: using cross tools not prefixed with host triplet
checking for x86_64-unknown-linux-gnufilc0-objdump... objdump
checking how to recognize dependent libraries... (cached) pass_all
checking for x86_64-unknown-linux-gnufilc0-dlltool... no
checking for dlltool... no
checking how to associate runtime and link libraries... printf %s\n
checking for x86_64-unknown-linux-gnufilc0-ar... (cached) ar
checking for archiver @FILE support... @
checking for x86_64-unknown-linux-gnufilc0-strip... (cached) strip
checking for x86_64-unknown-linux-gnufilc0-ranlib... ranlib
checking command to parse nm output from clang object... ok
checking for sysroot... no
checking for a working dd... /nix/store/rry6qingvsrqmc7ll7jgaqpybcbdgf5v-coreutils-9.7/bin/dd
checking how to truncate binary pipes... /nix/store/rry6qingvsrqmc7ll7jgaqpybcbdgf5v-coreutils-9.7/bin/dd bs=4096 count=1
checking for x86_64-unknown-linux-gnufilc0-mt... no
checking for mt... no
checking if : is a manifest tool... no
checking for dlfcn.h... yes
checking for objdir... .libs
checking if clang supports -fno-rtti -fno-exceptions... yes
checking for clang option to produce PIC... -fPIC -DPIC
checking if clang PIC flag -fPIC -DPIC works... yes
checking if clang static flag -static works... yes
checking if clang supports -c -o file.o... yes
checking if clang supports -c -o file.o... (cached) yes
```

```
checking fcntl.h presence... yes
checking for fcntl.h... yes
checking float.h usability... yes
checking float.h presence... yes
checking for float.h... yes
checking invent.h usability... no
checking invent.h presence... no
checking for invent.h... no
checking langinfo.h usability... yes
checking langinfo.h presence... yes
checking for langinfo.h... yes
checking locale.h usability... yes
checking locale.h presence... yes
checking for locale.h... yes
checking nl_types.h usability... yes
checking nl_types.h presence... yes
checking for nl_types.h... yes
checking sys/attributes.h usability... no
checking sys/attributes.h presence... no
checking for sys/attributes.h... no
checking sys/iograph.h usability... no
checking sys/iograph.h presence... no
checking for sys/iograph.h... no
checking sys/mman.h usability... yes
checking sys/mman.h presence... yes
checking for sys/mman.h... yes
checking sys/param.h usability... yes
checking sys/param.h presence... yes
checking for sys/param.h... yes
checking sys/processor.h usability... no
checking sys/processor.h presence... no
checking for sys/processor.h... no
checking sys/pstat.h usability... no
checking sys/pstat.h presence... no
checking for sys/pstat.h... no
checking sys/sysinfo.h usability... yes
checking sys/sysinfo.h presence... yes
checking for sys/sysinfo.h... yes
checking sys/syssgi.h usability... no
checking sys/syssgi.h presence... no
checking for sys/syssgi.h... no
checking sys/systemcfg.h usability... no
checking sys/systemcfg.h presence... no
checking for sys/systemcfg.h... no
checking sys/time.h usability... yes
checking sys/time.h presence... yes
checking for sys/time.h... yes
checking sys/times.h usability... yes
checking sys/times.h presence... yes
checking for sys/times.h... yes
checking for sys/resource.h... yes
checking for sys/sysctl.h... no
checking for machine/hal_sysinfo.h... no
checking whether fgetc is declared... yes
checking whether fscanf is declared... yes
checking whether optarg is declared... yes
checking whether ungetc is declared... yes
checking whether vfprintf is declared... yes
checking whether sys_errlist is declared... no
checking whether sys_nerr is declared... no
checking return type of signal handlers... void
checking for intmax_t... yes
checking for long double... yes
checking for long long... yes
checking for ptrdiff_t... yes
checking for quad_t... yes
checking for uint_least32_t... yes
checking for intptr_t... yes
checking for working volatile... yes
checking for C/C++ restrict keyword... __restrict
checking whether gcc __attribute__ ((const)) works... yes
checking whether gcc __attribute__ ((malloc)) works... yes
checking whether gcc __attribute__ ((mode (XX))) works... yes
checking whether gcc __attribute__ ((noreturn)) works... yes
checking whether gcc hidden aliases work... yes
checking for inline... inline
checking for cos in -lm... yes
checking for working alloca.h... yes
checking for alloca (via gmp-impl.h)... yes
checking how to allocate temporary memory... alloca
```

```
-- Build files have been written to: /build/source/build
Running phase: buildPhase
build flags: -j32 SHELL=/nix/store/cfqbabpc7xwg8akbcchqbq3cai6qq2vs-bash-5.2p37/bin/bash
[  1%] Building CXX object libde265/x86/CMakeFiles/x86_sse.dir/sse-motion.cc.o
[  3%] Building CXX object libde265/x86/CMakeFiles/x86_sse.dir/sse-dct.cc.o
[  6%] Building CXX object libde265/encoder/algo/CMakeFiles/algo.dir/ctb-qscale.cc.o
[  7%] Building CXX object libde265/encoder/algo/CMakeFiles/algo.dir/coding-options.cc.o
[  9%] Building CXX object libde265/encoder/CMakeFiles/encoder.dir/encoder-params.cc.o
[ 12%] Building CXX object libde265/encoder/algo/CMakeFiles/algo.dir/cb-split.cc.o
[ 12%] Building CXX object libde265/encoder/CMakeFiles/encoder.dir/encoder-context.cc.o
[ 14%] Building CXX object libde265/encoder/CMakeFiles/encoder.dir/encoder-syntax.cc.o
[ 15%] Building CXX object libde265/encoder/CMakeFiles/encoder.dir/encoder-intrapred.cc.o
[ 17%] Building CXX object libde265/encoder/CMakeFiles/encoder.dir/encoder-motion.cc.o
[ 17%] Building CXX object libde265/encoder/algo/CMakeFiles/algo.dir/algo.cc.o
[ 22%] Building CXX object libde265/encoder/CMakeFiles/encoder.dir/encoder-types.cc.o
[ 30%] Building CXX object libde265/encoder/algo/CMakeFiles/algo.dir/cb-intrapartmode.cc.o
[ 25%] Building CXX object libde265/encoder/CMakeFiles/encoder.dir/encoder-core.cc.o
[ 31%] Building CXX object libde265/encoder/CMakeFiles/encoder.dir/sop.cc.o
[ 25%] Building CXX object libde265/x86/CMakeFiles/x86.dir/sse.cc.o
[ 20%] Building CXX object libde265/encoder/algo/CMakeFiles/algo.dir/cb-intra-inter.cc.o
[ 34%] Building CXX object libde265/encoder/algo/CMakeFiles/algo.dir/tb-transform.cc.o
[ 34%] Building CXX object libde265/encoder/algo/CMakeFiles/algo.dir/cb-mergeindex.cc.o
[ 36%] Building CXX object libde265/encoder/algo/CMakeFiles/algo.dir/tb-split.cc.o
[ 26%] Building CXX object libde265/encoder/algo/CMakeFiles/algo.dir/cb-interpartmode.cc.o
[ 31%] Building CXX object libde265/encoder/algo/CMakeFiles/algo.dir/cb-skip.cc.o
[ 30%] Building CXX object libde265/encoder/CMakeFiles/encoder.dir/encpicbuf.cc.o
[ 38%] Building CXX object libde265/encoder/algo/CMakeFiles/algo.dir/tb-intrapredmode.cc.o
[ 39%] Building CXX object libde265/encoder/algo/CMakeFiles/algo.dir/tb-rateestim.cc.o
[ 41%] Building CXX object libde265/encoder/algo/CMakeFiles/algo.dir/pb-mv.cc.o
[ 41%] Built target x86
/build/source/libde265/x86/sse-motion.cc:3530:68: warning: implicit conversion from 'int' to 'short' changes value from 65535 to -1 [-Wconstant-conversion]
 3530 |                     _mm_set_epi16(0, 65535, 0, 65535, 0, 65535, 0, 65535));
      |                     ~~~~~~~~~~~~~                                  ^~~~~
/build/source/libde265/x86/sse-motion.cc:3530:58: warning: implicit conversion from 'int' to 'short' changes value from 65535 to -1 [-Wconstant-conversion]
 3530 |                     _mm_set_epi16(0, 65535, 0, 65535, 0, 65535, 0, 65535));
      |                     ~~~~~~~~~~~~~                        ^~~~~
/build/source/libde265/x86/sse-motion.cc:3530:48: warning: implicit conversion from 'int' to 'short' changes value from 65535 to -1 [-Wconstant-conversion]
 3530 |                     _mm_set_epi16(0, 65535, 0, 65535, 0, 65535, 0, 65535));
      |                     ~~~~~~~~~~~~~              ^~~~~
/build/source/libde265/x86/sse-motion.cc:3530:38: warning: implicit convers
ion from 'int' to 'short' changes value from 65535 to -1 [-Wconstant-conversion]
 3530 |                     _mm_set_epi16(0, 65535, 0, 65535, 0, 65535, 0, 65535));
      |                     ~~~~~~~~~~~~~    ^~~~~
/build/source/libde265/x86/sse-motion.cc:3532:68: warning: implicit conversion from 'int' to 'short' changes value from 65535 to -1 [-Wconstant-conversion]
 3532 |                     _mm_set_epi16(0, 65535, 0, 65535, 0, 65535, 0, 65535));
      |                     ~~~~~~~~~~~~~                                  ^~~~~
/build/source/libde265/x86/sse-motion.cc:3532:58: warning: implicit conversion from 'int' to 'short' changes value from 65535 to -1 [-Wconstant-conversion]
 3532 |                     _mm_set_epi16(0, 65535, 0, 65535, 0, 65535, 0, 65535));
      |                     ~~~~~~~~~~~~~                        ^~~~~
/build/source/libde265/x86/sse-motion.cc:3532:48: warning: implicit conversion from 'int' to 'short' changes value from 65535 to -1 [-Wconstant-conversion]
 3532 |                     _mm_set_epi16(0, 65535, 0, 65535, 0, 65535, 0, 65535));
      |                     ~~~~~~~~~~~~~              ^~~~~
/build/source/libde265/x86/sse-motion.cc:3532:38: warning: implicit conversion from 'int' to 'short' changes value from 65535 to -1 [-Wconstant-conversion]
 3532 |                     _mm_set_epi16(0, 65535, 0, 65535, 0, 65535, 0, 65535));
      |                     ~~~~~~~~~~~~~    ^~~~~
/build/source/libde265/x86/sse-motion.cc:3713:68: warning: implicit conversion from 'int' to 'short' changes value from 65535 to -1 [-Wconstant-conversion]
 3713 |                     _mm_set_epi16(0, 65535, 0, 65535, 0, 65535, 0, 65535));
      |                     ~~~~~~~~~~~~~                                  ^~~~~
/build/source/libde265/x86/sse-motion.cc:3713:58: warning: implicit conversion from 'int' to 'short' changes value from 65535 to -1 [-Wconstant-conversion]
 3713 |                     _mm_set_epi16(0, 65535, 0, 65535, 0, 65535, 0, 65535));
      |                     ~~~~~~~~~~~~~                        ^~~~~
/build/source/libde265/x86/sse-motion.cc:3713:48: warning: implicit conversion from 'int' to 'short' changes value from 65535 to -1 [-Wconstant-conversion]
 3713 |                     _mm_set_epi16(0, 65535, 0, 65535, 0, 65535, 0, 65535));
      |                     ~~~~~~~~~~~~~              ^~~~~
/build/source/libde265/x86/sse-motion.cc:3713:38: warning: implicit conversion from 'int' to 'short' changes value from 65535 to -1 [-Wconstant-conversion]
 3713 |                     _mm_set_epi16(0, 65535, 0, 65535, 0, 65535, 0, 65535));
      |                     ~~~~~~~~~~~~~    ^~~~~
/build/source/libde265/x86/sse-motion.cc:3715:68: warning: implicit conversion from 'int' to 'short' changes value from 65535 to -1 [-Wconstant-conversion]
 3715 |                     _mm_set_epi16(0, 65535, 0, 65535, 0, 65535, 0, 65535));
      |                     ~~~~~~~~~~~~~                                  ^~~~~
/build/source/libde265/x86/sse-motion.cc:3715:58: warning: implicit conversion from 'int' to 'short' changes value from 65535 to -1 [-Wconstant-conversion]
 3715 |                     _mm_set_epi16(0, 65535, 0, 65535, 0, 65535, 0, 65535));
      |                     ~~~~~~~~~~~~~                        ^~~~~
/build/source/libde265/x86/sse-motion.cc:3715:48: warning: implicit conversion from 'int' to 'short' changes value from 65535 to -1 [-Wconstant-conversion]
 3715 |                     _mm_set_epi16(0, 65535, 0, 65535, 0, 65535, 0, 65535));
      |                     ~~~~~~~~~~~~~              ^~~~~
/build/source/libde265/x86/sse-motion.cc:3715:38: warning: implicit conversion from 'int' to 'short' changes value from 65535 to -1 [-Wconstant-conversion]
 3715 |                     _mm_set_epi16(0, 65535, 0, 65535, 0, 65535, 0, 65535));
      |                     ~~~~~~~~~~~~~    ^~~~~
/build/source/libde265/x86/sse-motion.cc:3890:68: warning: implicit conversion from 'int' to 'short' changes value from 65535 to -1 [-Wconstant-conversion]
```

```
[ 88%] Linking C executable test_trailing_bytes
[ 90%] Linking C executable test_overread
[ 96%] Linking C executable test_custom_malloc
[ 96%] Linking C executable test_invalid_str
eams
[ 96%] Linking C executable test_slow_decompression
[ 98%] Linking C executable checksum
[100%] Linking C executable benchmark
[100%] Built target test_overread
[100%] Built target test_incomplete_codes
[100%] Built target test_slow_decompression
[100%] Built target test_litrunlen_overflow
[100%] Built target test_invalid_streams
[100%] Built target test_custom_malloc
[100%] Built target checksum
[100%] Built target test_checksums
[100%] Built target test_trailing_bytes
[100%] Built target benchmark
Running phase: checkPhase
check flags: SHELL=/nix/store/cfqbabpc7xwg8akbcchqbq3cai6qq2vs-bash-5.2p37/bin/bash VERBOSE=y test
Running tests...
/nix/store/sywrvcqgm7bf6njpfbkhd8iy4iaymhj2-cmake-3.31.6/bin/ctest --force-new-ctest-process 
Test project /build/source/build
    Start 1: test_checksums
    Start 2: test_custom_malloc
    Start 3: test_incomplete_codes
    Start 4: test_invalid_streams
    Start 5: test_litrunlen_overflow
    Start 6: test_overread
    Start 7: test_slow_decompression
    Start 8: test_trailing_bytes
1/8 Test #7: test_slow_decompression ..........   Passed    0.01 sec
2/8 Test #2: test_custom_malloc ...............   Passed    0.05 sec
3/8 Test #1: test_checksums ...................SIGTRAP***Exception:   0.11 sec
filc safety error: cannot handle inline asm (nontrivial assembly, cannot analyze):   %3 = call { i32, i32, i32, i32 } asm sideeffect "cpuid", "={ax},={bx},={cx},={dx},{ax},{cx},~{dirflag},~{fpsr},~{flags}"(i32 0, i32 0) #12
    <somewhere>: libdeflate_init_x86_cpu_features
    <somewhere>: dispatch_adler32
    <somewhere>: libdeflate_adler32
    <somewhere>: test_adler32
    <somewhere>: test_random_buffers
    <somewhere>: main
    ../sysdeps/nptl/libc_start_call_main.h:58:16: __libc_start_call_main
    ../csu/libc-start.c:161:3: __libc_start_main
    <runtime>: start_program
[838] filc panic: thwarted a futile attempt to violate memory safety.

4/8 Test #6: test_overread ....................SIGTRAP***Exception:   0.12 sec
filc safety error: cannot handle inline asm (nontrivial assembly, cannot analyze):   %3 = call { i32, i32, i32, i32 } asm sideeffect "cpuid", "={ax},={bx},={cx},={dx},{ax},{cx},~{dirflag},~{fpsr},~{flags}"(i32 0, i32 0) #12
    <somewhere>: libdeflate_init_x86_cpu_features
    <somewhere>: dispatch_decomp
    <somewhere>: libdeflate_deflate_decompress
    <somewhere>: main
    ../sysdeps/nptl/libc_start_call_main.h:58:16: __libc_start_call_main
    ../csu/libc-start.c:161:3: __libc_start_main
    <runtime>: start_program
[843] filc panic: thwarted a futile attempt to violate memory safety.

5/8 Test #4: test_invalid_streams .............SIGTRAP***Exception:   0.13 sec
filc safety error: cannot handle inline asm (nontrivial assembly, cannot analyze):   %3 = call { i32, i32, i32, i32 } asm sideeffect "cpuid", "={ax},={bx},={cx},={dx},{ax},{cx},~{dirflag},~{fpsr},~{flags}"(i32 0, i32 0) #12
    <somewhere>: libdeflate_init_x86_cpu_features
    <somewhere>: dispatch_decomp
    <somewhere>: libdeflate_deflate_decompress
    <somewhere>: main
    ../sysdeps/nptl/libc_start_call_main.h:58:16: __libc_start_call_main
    ../csu/libc-start.c:161:3: __libc_start_main
    <runtime>: start_program
[841] filc panic: thwarted a futile attempt to violate memory safety.

6/8 Test #8: test_trailing_bytes ..............SIGTRAP***Exception:   0.14 sec
filc safety error: cannot handle inline asm (nontrivial assembly, cannot analyze):   %3 = call { i32, i32, i32, i32 } asm sideeffect "cpuid", "={ax},={bx},={cx},={dx},{ax},{cx},~{dirflag},~{fpsr},~{flags}"(i32 0, i32 0) #12
    <somewhere>: libdeflate_init_x86_cpu_features
    <somewhere>: dispatch_decomp
    <somewhere>: libdeflate_deflate_decompress
    <somewhere>: main
    ../sysdeps/nptl/libc_start_call_main.h:58:16: __libc_start_call_main
    ../csu/libc-start.c:161:3: __libc_start_main
    <runtime>: start_program
[845] filc panic: thwarted a futile attempt to violate memory safety.

7/8 Test #3: test_incomplete_codes ............SIGTRAP***Exception:   0.16 sec
```

```
checking for unistd.h... yes
checking for dlfcn.h... yes
checking for objdir... .libs
checking if clang supports -fno-rtti -fno-exceptions... yes
checking for clang option to produce PIC... -fPIC -DPIC
checking if clang PIC flag -fPIC -DPIC works... yes
checking if clang static flag -static works... yes
checking if clang supports -c -o file.o... yes
checking if clang supports -c -o file.o... (cached) yes
checking whether the clang linker (ld -m elf_x86_64) supports shared libraries... yes
checking whether -lc should be explicitly linked in... no
checking dynamic linker characteristics... GNU/Linux ld.so
checking how to hardcode library paths into programs... immediate
checking whether stripping libraries is possible... yes
checking if libtool supports shared libraries... yes
checking whether to build shared libraries... yes
checking whether to build static libraries... no
checking whether linker supports -version-script... yes
checking for doxygen... no
checking for trietool-0.2... trietool-0.2
checking pkg-config is at least version 0.9.0... yes
checking for datrie-0.2... yes
checking for stddef.h... yes
checking for stdlib.h... (cached) yes
checking for string.h... (cached) yes
checking for wchar.h... yes
checking for an ANSI C-conforming const... yes
checking for size_t... yes
checking that generated files are newer than configure... done
configure: creating ./config.status
config.status: creating libthai.pc
config.status: creating Makefile
config.status: creating include/Makefile
config.status: creating include/thai/Makefile
config.status: creating src/Makefile
config.status: creating src/thctype/Makefile
config.status: creating src/thstr/Makefile
config.status: creating src/thcell/Makefile
config.status: creating src/thinp/Makefile
config.status: creating src/thrend/Makefile
config.status: creating src/thcoll/Makefile
config.status: creating src/thbrk/Makefile
config.status: creating src/thwchar/Makefile
config.status: creating src/thwctype/Makefile
config.status: creating src/thwstr/Makefile
config.status: creating src/thwbrk/Makefile
config.status: creating data/Makefile
config.status: creating tests/Makefile
config.status: creating doc/Makefile
config.status: creating doc/Doxyfile
config.status: executing depfiles commands
config.status: executing libtool commands
Type make to build libthai.
Running phase: buildPhase
build flags: SHELL=/nix/store/cfqbabpc7xwg8akbcchqbq3cai6qq2vs-bash-5.2p37/bin/bash
Making all in include
make[1]: Entering directory '/build/libthai-0.1.29/include'
Making all in thai
make[2]: Entering directory '/build/libthai-0.1.29/include/thai'
make[2]: Nothing to be done for 'all'.
make[2]: Leaving directory '/build/libthai-0.1.29/include/thai'
make[2]: Entering directory '/build/libthai-0.1.29/include'
make[2]: Nothing to be done for 'all-am'.
make[2]: Leaving directory '/build/libthai-0.1.29/include'
make[1]: Leaving directory '/build/libthai-0.1.29/include'
Making all in src
make[1]: Entering directory '/build/libthai-0.1.29/src'
Making all in thctype
make[2]: Entering directory '/build/libthai-0.1.29/src/thctype'
/nix/store/cfqbabpc7xwg8akbcchqbq3cai6qq2vs-bash-5.2p37/bin/bash ../../libtool  --tag=CC   --mode=compile clang -DPACKAGE_NAME=\"libthai\" -DPACKAGE_TARNAME=\"libthai\" -DPACKAGE_VERSION=\"0.1.29\" -DPACKAGE_STRING=\"libthai\ 0.1.29\" -DPACKAGE_BUGREPORT=\"https://github.com/tlwg/libthai/issues\" -DPACKAGE_URL=\"\" -DPACKAGE=\"libthai\" -DVERSION=\"0.1.29\" -DHAVE_STDIO_H=1 -DHAVE_STDLIB_H=1 -DHAVE_STRING_H=1 -DHAVE_INTTYPES_H=1 -DHAVE_STDINT_H=1 -DHAVE_STRINGS_H=1 -DHAVE_SYS_STAT_H=1 -DHAVE_SYS_TYPES_H=1 -DHAVE_UNISTD_H=1 -DSTDC_HEADERS=1 -DHAVE_DLFCN_H=1 -DLT_OBJDIR=\".libs/\" -DHAVE_STDDEF_H=1 -DHAVE_STDLIB_H=1 -DHAVE_STRING_H=1 -DHAVE_WCHAR_H=1 -I.  -I. -I../../include   -g -O2 -Wall -DNDEBUG -c -o thctype.lo thctype.c
libtool: compile:  clang -DPACKAGE_NAME=\"libthai\" -DPACKAGE_TARNAME=\"libthai\" -DPACKAGE_VERSION=\"0.1.29\" "-DPACKAGE_STRING=\"libthai 0.1.29\"" -DPACKAGE_BUGREPORT=\"https://github.com/tlwg/libthai/issues\" -DPACKAGE_URL=\"\" -DPACKAGE=\"libthai\" -DVERSION=\"0.1.29\" -DHAVE_STDIO_H=1 -DHAVE_STDLIB_H=1 -DHAVE_STRING_H=1 -DHAVE_INTTYPES_H=1 -DHAVE_STDINT_H=1 -DHAVE_STRINGS_H=1 -DHAVE_SYS_STAT_H=1 -DHAVE_SYS_TYPES_H=1 -DHAVE_UNISTD_H=1 -DSTDC_HEADERS=1 -DHAVE_DLFCN_H=1 -DLT_OBJDIR=\".libs/\" -DHAVE_STDDEF_H=1 -DHAVE_STDLIB_H=1 -DHAVE_STRING_H=1 -DHAVE_WCHAR_H=1 -I. -I. -I../../include -g -O2 -Wall -DNDEBUG -c thctype.c  -fPIC -DPIC -o .libs/thctype.o
/nix/store/cfqbabpc7xwg8akbcchqbq3cai6qq2vs-bash-5.2p37/bin/bash ../../libtool  --tag=CC   --mode=compile clang -DPACKAGE_NAME=\"libthai\" -DPACKAGE_TARNAME=\"libthai\" -DPACKAGE_VERSION=\"0.1.29\" -DPACKAGE_STRING=\"libthai\ 0.1.29\" -DPACKAGE_BUGREPORT=\"https://github.com/tlwg/libthai/issues\" -DPACKAGE_URL=\"\" -DPACKAGE=\"libthai\" -DVERSION=\"0.1.29\" -DHAVE_STDIO_H=1 -DHAVE_STDLIB_H=1 -DHAVE_STRING_H=1 -DHAVE_INTTYPES_H=1 -DHAVE_STDINT_H=1 -DHAVE_STRINGS_H=1 -DHAVE_SYS_STAT_H=1 -DHAVE_SYS_TYPES_H=1 -DHAVE_UNISTD_H=1 -DSTDC_HEADERS=1 -DHAVE_DLFCN_H=1 -DLT_OBJDIR=\".libs/\" -DHAVE_STDDEF_H=1 -DHAVE_STDLIB_H=1 -DHAVE_STRING_H=1 -DHAVE_WCHAR_H=1 -I.  -I. -I../../include   -g -O2 -Wall -DNDEBUG -c -o wtt.lo wtt.c
libtool: compile:  clang -DPACKAGE_NAME=\"libthai\" -DPACKAGE_TARNAME=\"libthai\" -DPACKAGE_VERSION=\"0.1.29\" "-DPACKAGE_STRING=\"libthai 0.1.29\"" -DPACKAGE_BUGREPORT=\"https://github.com/tlwg/libthai/issues\" -DPACKAGE_URL=\"\" -DPACKAGE=\"libthai\" -DVERSION=\"0.1.29\" -DHAVE_STDIO_H=1 -DHAVE_STDLIB_H=1 -DHAVE_STRING_H=1 -DHAVE_INTTYPES_H=1 -DHAVE_STDINT_H=1 -DHAVE_STRINGS_H=1 -DHAVE_SYS_STAT_H=1 -DHAVE_SYS_TYPES_H=1 -DHAVE_UNISTD_H=1 -DSTDC_HEADERS=1 -DHAVE_DLFCN_H=1 -DLT_OBJDIR=\".libs/\" -DHAVE_STDDEF_H=1 -DHAVE_STDLIB_H=1 -DHAVE_STRING_H=1 -DHAVE_WCHAR_H=1 -I. -I. -I../../include -g -O2 -Wall -DNDEBUG -c wtt.c  -fPIC -DPIC -o .libs/wtt.o
/nix/store/cfqbabpc7xwg8akbcchqbq3cai6qq2vs-bash-5.2p37/bin/bash ../../libtool  --tag=CC   --mode=link clang  -g -O2 -Wall -DNDEBUG   -o libthctype.la  thctype.lo wtt.lo  
libtool: link: ar cr .libs/libthctype.a .libs/thctype.o .libs/wtt.o 
libtool: link: ranlib .libs/libthctype.a
libtool: link: ( cd ".libs" && rm -f "libthctype.la" && ln -s "../libthctype.la" "libthctype.la" )
make[2]: Leaving directory '/build/libthai-0.1.29/src/thctype'
Making all in thstr
make[2]: Entering directory '/build/libthai-0.1.29/src/thstr'
```

```
-- Performing Test CC_HAS_NO_ARRAY_BOUNDS - Success
-- Performing Test CC_HAS_FAST_MATH
-- Performing Test CC_HAS_FAST_MATH - Success
-- Performing Test CC_HAS_STACK_REALIGN
-- Performing Test CC_HAS_STACK_REALIGN - Success
-- Performing Test CC_HAS_FNO_EXCEPTIONS_FLAG
-- Performing Test CC_HAS_FNO_EXCEPTIONS_FLAG - Success
-- Found nasm: /nix/store/8xc100z1a3s6ilg4f5y1c7hbvvgv1y8r-nasm-2.16.03/bin/nasm (found version "2.16.03")
-- Found Nasm 2.16.03 to build assembly primitives
-- SOURCE CODE IS FROM x265 GIT ARCHIVED ZIP OR TAR BALL
-- GIT ARCHIVAL INFORMATION PROCESSED
-- X265 RELEASE VERSION 4.1+1-1d117be
-- The ASM_NASM compiler identification is NASM
-- Found assembler: /nix/store/8xc100z1a3s6ilg4f5y1c7hbvvgv1y8r-nasm-2.16.03/bin/nasm
-- Looking for strtok_r
-- Looking for strtok_r - found
-- Looking for include file getopt.h
-- Looking for include file getopt.h - found
-- Looking for __rdtsc
-- Looking for __rdtsc - not found
-- Configuring done (1.2s)
-- Generating done (0.0s)
CMake Warning:
  Manually-specified variables were not used by the project:

    CMAKE_EXPORT_NO_PACKAGE_REGISTRY
    CMAKE_INSTALL_BINDIR
    CMAKE_INSTALL_DOCDIR
    CMAKE_INSTALL_INCLUDEDIR
    CMAKE_INSTALL_INFODIR
    CMAKE_INSTALL_LIBDIR
    CMAKE_INSTALL_LIBEXECDIR
    CMAKE_INSTALL_LOCALEDIR
    CMAKE_INSTALL_MANDIR
    CMAKE_INSTALL_SBINDIR


-- Build files have been written to: /build/x265_4.1/source/build
cmake: enabled parallel building
cmake: enabled parallel installing
Running phase: buildPhase
make: Entering directory '/build/x265_4.1/source/build-10bits'
-- cmake version 3.31.6
-- Detected x86_64 target processor
-- Could NOT find NUMA (missing: NUMA_ROOT_DIR NUMA_INCLUDE_DIR NUMA_LIBRARY) 
-- Found Nasm 2.16.03 to build assembly primitives
-- HG LIVE REPO STATUS CHECK DONE
-- X265 RELEASE VERSION 4.1
-- Configuring done (0.0s)
-- Generating done (0.0s)
-- Build files have been written to: /build/x265_4.1/source/build-10bits
[  5%] Building CXX object encoder/CMakeFiles/encoder.dir/motion.cpp.o
[ 17%] Building CXX object encoder/CMakeFiles/encoder.dir/slicetype.cpp.o
[ 21%] Building CXX object encoder/CMakeFiles/encoder.dir/level.cpp.o
[ 26%] Building ASM_NASM object common/CMakeFiles/common.dir/x86/ssd-a.asm.o
[ 28%] Building CXX object encoder/CMakeFiles/encoder.dir/sao.cpp.o
[ 14%] Building ASM_NASM object common/CMakeFiles/common.dir/x86/pixeladd8.asm.o
[ 30%] Building CXX object encoder/CMakeFiles/encoder.dir/ratecontrol.cpp.o
[ 33%] Building ASM_NASM object common/CMakeFiles/common.dir/x86/sad16-a.asm.o
[ 33%] Building CXX object encoder/CMakeFiles/encoder.dir/encoder.cpp.o
[ 34%] Building ASM_NASM object common/CMakeFiles/common.dir/x86/blockcopy8.asm.o
[ 14%] Building CXX object encoder/CMakeFiles/encoder.dir/frameencoder.cpp.o
[ 14%] Building CXX object encoder/CMakeFiles/encoder.dir/analysis.cpp.o
[ 14%] Building ASM_NASM object common/CMakeFiles/common.dir/x86/mc-a.asm.o
[ 14%] Building ASM_NASM object common/CMakeFiles/common.dir/x86/pixel-util8.asm.o
[ 14%] Building CXX object encoder/CMakeFiles/encoder.dir/dpb.cpp.o
[ 17%] Building ASM_NASM object common/CMakeFiles/common.dir/x86/const-a.asm.o
[  6%] Building ASM_NASM object common/CMakeFiles/common.dir/x86/pixel-a.asm.o
[ 25%] Building CXX object encoder/CMakeFiles/encoder.dir/sei.cpp.o
[ 24%] Building CXX object encoder/CMakeFiles/encoder.dir/framefilter.cpp.o
[ 21%] Building ASM_NASM object common/CMakeFiles/common.dir/x86/cpu-a.asm.o
[ 40%] Building CXX object encoder/CMakeFiles/encoder.dir/weightPrediction.cpp.o
[ 41%] Building ASM_NASM object common/CMakeFiles/common.dir/x86/seaintegral.asm.o
[ 37%] Building CXX object encoder/CMakeFiles/encoder.dir/reference.cpp.o
[ 38%] Building ASM_NASM object common/CMakeFiles/common.dir/x86/mc-a2.asm.o
[ 26%] Building CXX object encoder/CMakeFiles/encoder.dir/search.cpp.o
[ 38%] Building ASM_NASM object common/CMakeFiles/common.dir/x86/v4-ipfilter16.asm.o
[ 34%] Building CXX object encoder/CMakeFiles/encoder.dir/nal.cpp.o
[ 42%] Building CXX object encoder/CMakeFiles/encoder.dir/api.cpp.o
[ 38%] Building ASM_NASM object common/CMakeFiles/common.dir/x86/intrapred16.asm.o
```

Phase: `fixupPhase`

```
Running phase: patchPhase
Running phase: updateAutotoolsGnuConfigScriptsPhase
Running phase: updateAutotoolsGnuConfigScriptsPhase
Running phase: installPhase
Running phase: fixupPhase
shrinking RPATHs of ELF executables and libraries in /nix/store/f606q9irr1ccdd1053pmmfmmxac0qn8i-pkgconf-wrapper-2.4.3
checking for references to /build/ in /nix/store/f606q9irr1ccdd1053pmmfmmxac0qn8i-pkgconf-wrapper-2.4.3...
patching script interpreter paths in /nix/store/f606q9irr1ccdd1053pmmfmmxac0qn8i-pkgconf-wrapper-2.4.3
```

```
../src/feature/x86/vif_avx512.c:205:32: warning: unused variable 'dis' [-Wunused-variable]
  205 |                 const uint8_t *dis = (uint8_t*)buf.dis;
      |                                ^~~
../src/feature/x86/vif_avx512.c:187:28: warning: unused variable 'ref' [-Wunused-variable]
  187 |             const uint8_t *ref = (uint8_t*)buf.ref;
      |                            ^~~
../src/feature/x86/vif_avx512.c:188:28: warning: unused variable 'dis' [-Wunused-variable]
  188 |             const uint8_t *dis = (uint8_t*)buf.dis;
      |                            ^~~
../src/feature/x86/vif_avx512.c:265:25: warning: unused variable 'dst_stride' [-Wunused-variable]
  265 |         const ptrdiff_t dst_stride = buf.stride_32 / sizeof(uint32_t);
      |                         ^~~~~~~~~~
../src/feature/x86/vif_avx512.c:148:20: warning: unused variable 'ref' [-Wunused-variable]
  148 |     const uint8_t *ref = (uint8_t*)buf.ref;
      |                    ^~~
../src/feature/x86/vif_avx512.c:149:20: warning: unused variable 'dis' [-Wunused-variable]
  149 |     const uint8_t *dis = (uint8_t*)buf.dis;
      |                    ^~~
../src/feature/x86/vif_avx512.c:163:26: warning: unused variable 'sigma_nsq' [-Wunused-variable]
  163 |     static const int32_t sigma_nsq = 65536 << 1;
      |                          ^~~~~~~~~
../src/feature/x86/vif_avx512.c:470:32: warning: unused variable 'fcoeff' [-Wunused-variable]
  470 |                 const uint16_t fcoeff = vif_filt[fi];
      |                                ^~~~~~
../src/feature/x86/vif_avx512.c:401:21: warning: unused variable 'dst_stride' [-Wunused-variable]
  401 |     const ptrdiff_t dst_stride = buf.stride_32 / sizeof(uint32_t);
      |                     ^~~~~~~~~~
../src/feature/x86/vif_avx512.c:405:13: warning: variable 'add_shift_round_HP' set but not used [-Wunused-but-set-variable]
  405 |     int32_t add_shift_round_HP, shift_HP;
      |             ^
../src/feature/x86/vif_avx512.c:405:33: warning: variable 'shift_HP' set but not used [-Wunused-but-set-variable]
  405 |     int32_t add_shift_round_HP, shift_HP;
      |                                 ^
../src/feature/x86/vif_avx512.c:413:26: warning: unused variable 'sigma_nsq' [-Wunused-variable]
  413 |     static const int32_t sigma_nsq = 65536 << 1;
      |                          ^~~~~~~~~
../src/feature/x86/vif_avx512.c:454:32: warning: comparison of integers of different signs: 'unsigned int' and 'int' [-Wsign-compare]
  454 |         for (unsigned j = 0; j < n << 5; j = j + 32)
      |                              ~ ^ ~~~~~~
../src/feature/x86/vif_avx512.c:628:32: warning: comparison of integers of different signs: 'unsigned int' and 'int' [-Wsign-compare]
  628 |         for (unsigned j = 0; j < n << 4; j = j + 16)
      |                              ~ ^ ~~~~~~
../src/feature/x86/vif_avx512.c:743:22: warning: comparison of integers of different signs: 'int' and 'unsigned int' [-Wsign-compare]
  743 |         if ((n << 4) != w) {
      |              ~~~~~~  ^  ~
../src/feature/x86/vif_avx512.c:782:9: warning: unused variable 'fwidth_x' [-Wunused-variable]
  782 |     int fwidth_x = (fwidth % 2 == 0) ? fwidth : fwidth + 1;
      |         ^~~~~~~~
../src/feature/x86/vif_avx512.c:820:32: warning: comparison of integers of different signs: 'unsigned int' and 'int' [-Wsign-compare]
  820 |         for (unsigned j = 0; j < n << 5; j = j + 32)
      |                              ~ ^ ~~~~~~
../src/feature/x86/vif_avx512.c:954:32: warning: comparison of integers of different signs: 'unsigned int' and 'int' [-Wsign-compare]
  954 |         for (unsigned j = 0; j < n << 4; j = j + 16)
      |                              ~ ^ ~~~~~~
../src/feature/x86/vif_avx512.c:1164:32: warning: unused variable 'fcoeff' [-Wunused-variable]
 1164 |                 const uint16_t fcoeff = vif_filt[fi];
      |                                ^~~~~~
../src/feature/x86/vif_avx512.c:1229:29: warning: unused variable 'ref' [-Wunused-variable]
 1229 |             const uint16_t *ref = (uint16_t *)buf.tmp.ref_convol;
      |                             ^~~
../src/feature/x86/vif_avx512.c:1230:29: warning: unused variable 'dis' [-Wunused-variable]
 1230 |             const uint16_t *dis = (uint16_t *)buf.dis;
      |                             ^~~
../src/feature/x86/vif_avx512.c:1154:32: warning: comparison of integers of different signs: 'unsigned int' and 'int' [-Wsign-compare]
 1154 |         for (unsigned j = 0; j < n << 4; j = j + 32)
      |                              ~ ^ ~~~~~~
../src/feature/x86/vif_avx512.c:1223:32: warning: comparison of integers of different signs: 'unsigned int' and 'int' [-Wsign-compare]
 1223 |         for (unsigned j = 0; j < n << 4; j = j + 16)
      |                              ~ ^ ~~~~~~
24 warnings generated.
[22/165] Compiling C object src/liblibvmaf_feature.a.p/feature_feature_extractor.c.o
[23/165] Compiling C object src/liblibvmaf_feature.a.p/feature_integer_adm.c.o
[24/165] Compiling C object src/liblibvmaf_feature.a.p/feature_integer_motion.c.o
[25/165] Compiling C object src/liblibvmaf_feature.a.p/feature_integer_vif.c.o
../src/feature/integer_vif.c:496:13: warning: variable 'add_shift_round_VP' set but not used [-Wunused-but-set-variable]
  496 |     int32_t add_shift_round_VP, shift_VP;
      |             ^
../src/feature/integer_vif.c:496:33: warning: variable 'shift_VP' set but not used [-Wunused-but-set-variable]
  496 |     int32_t add_shift_round_VP, shift_VP;
      |                                 ^
```

```
Running phase: unpackPhase
unpacking source archive /nix/store/7a7vgg8m8nb28mfq2v49alzlnyl50qyk-rustc-1.86.0-src.tar.gz
```

```
Running phase: unpackPhase
$CPATH is `'
$LIBRARY_PATH is `'
/nix/store/a2rjq6pbcp2y3gbmm1904nr6mcfr8s8m-stdenv-linux/setup: line 303: /nix/store/87zpmcmwvn48z4lbrfba74b312h22s6c-binutils-wrapper-2.44/nix-support/libc-ldflags-before: No such file or directory
/nix/store/a2rjq6pbcp2y3gbmm1904nr6mcfr8s8m-stdenv-linux/setup: line 303: /nix/store/wlzvi1mvdx5ifpaxpw1hc1hcm3ia4wj2-binutils-wrapper-2.44/nix-support/libc-ldflags-before: No such file or directory
unpacking source archive /nix/store/bdnxgjaj28ga549imawzkassy3i1icxg-gcc-14.3.0.tar.xz
```

</details>

<details>
<summary>✅ <strong>rpam2</strong>: build failed</summary>

```
./libtool --mode=link clang -O3  -o db_sql  db_sql.lo parse.lo preparser.lo parsefuncs.lo tokenize.lo sqlprintf.lo buildpt.lo utils.lo generate.lo generate_test.lo generation_utils.lo generate_verification.lo hint_comment.lo \
            libdb-4.8.la -lpthread
./libtool --mode=link clang++ -avoid-version -O -rpath /nix/store/ffy0frz8p4spayvhfy9wgqlp45yhgz50-db-x86_64-unknown-linux-gnufilc0-4.8.30/lib  \
    -o libdb_cxx-4.8.la cxx_db.lo cxx_dbc.lo cxx_dbt.lo cxx_env.lo cxx_except.lo cxx_lock.lo cxx_logc.lo cxx_mpool.lo cxx_multi.lo cxx_seq.lo cxx_txn.lo db185.lo mut_pthread.lo  bt_compare.lo bt_compress.lo bt_conv.lo bt_curadj.lo bt_cursor.lo bt_delete.lo bt_method.lo bt_open.lo bt_put.lo bt_rec.lo bt_reclaim.lo bt_recno.lo bt_rsearch.lo bt_search.lo bt_split.lo bt_stat.lo bt_compact.lo bt_upgrade.lo btree_auto.lo hash.lo hash_auto.lo hash_conv.lo hash_dup.lo hash_meta.lo hash_method.lo hash_open.lo hash_page.lo hash_rec.lo hash_reclaim.lo hash_stat.lo hash_upgrade.lo hash_verify.lo qam.lo qam_auto.lo qam_conv.lo qam_files.lo qam_method.lo qam_open.lo qam_rec.lo qam_stat.lo qam_upgrade.lo qam_verify.lo rep_auto.lo rep_backup.lo rep_elect.lo rep_lease.lo rep_log.lo rep_method.lo rep_record.lo rep_region.lo rep_stat.lo rep_util.lo rep_verify.lo os_addrinfo.lo repmgr_auto.lo repmgr_elect.lo repmgr_method.lo repmgr_msg.lo repmgr_net.lo repmgr_posix.lo repmgr_queue.lo repmgr_sel.lo repmgr_stat.lo repmgr_util.lo db_ovfl_vrfy.lo db_vrfy.lo db_vrfyutil.lo bt_verify.lo lock.lo lock_deadlock.lo lock_failchk.lo lock_id.lo lock_list.lo lock_method.lo lock_region.lo lock_stat.lo lock_timer.lo lock_util.lo mut_alloc.lo mut_failchk.lo mut_method.lo mut_region.lo mut_stat.lo  aes_method.lo crypto.lo mt19937db.lo rijndael-alg-fst.lo rijndael-api-fst.lo crdel_auto.lo crdel_rec.lo db.lo db_am.lo db_auto.lo db_byteorder.lo db_cam.lo db_cds.lo db_compint.lo db_conv.lo db_dispatch.lo db_dup.lo db_err.lo db_getlong.lo db_idspace.lo db_iface.lo db_join.lo db_log2.lo db_meta.lo db_method.lo db_open.lo db_overflow.lo db_pr.lo db_rec.lo db_reclaim.lo db_remove.lo db_rename.lo db_ret.lo db_setid.lo db_setlsn.lo db_shash.lo db_sort_multiple.lo db_stati.lo db_truncate.lo db_upg.lo db_upg_opd.lo dbm.lo dbreg.lo dbreg_auto.lo dbreg_rec.lo dbreg_stat.lo dbreg_util.lo dbt.lo env_alloc.lo env_config.lo env_failchk.lo env_file.lo env_globals.lo env_method.lo env_name.lo env_open.lo env_recover.lo env_region.lo env_register.lo env_sig.lo env_stat.lo fileops_auto.lo fop_basic.lo fop_rec.lo fop_util.lo hash_func.lo hmac.lo hsearch.lo log.lo log_archive.lo log_compare.lo log_debug.lo log_get.lo log_method.lo log_put.lo log_stat.lo mkpath.lo mp_alloc.lo mp_bh.lo mp_fget.lo mp_fmethod.lo mp_fopen.lo mp_fput.lo mp_fset.lo mp_method.lo mp_mvcc.lo mp_region.lo mp_register.lo mp_resize.lo mp_stat.lo mp_sync.lo mp_trickle.lo openflags.lo os_abort.lo os_abs.lo os_alloc.lo os_clock.lo os_cpu.lo os_ctime.lo os_config.lo os_dir.lo os_errno.lo os_fid.lo os_flock.lo os_fsync.lo os_getenv.lo os_handle.lo os_map.lo os_method.lo os_mkdir.lo os_open.lo os_pid.lo os_rename.lo os_root.lo os_rpath.lo os_rw.lo os_seek.lo os_stack.lo os_stat.lo os_tmpdir.lo os_truncate.lo os_uid.lo os_unlink.lo os_yield.lo partition.lo seq_stat.lo sequence.lo sha1.lo snprintf.lo txn.lo txn_auto.lo txn_chkpt.lo txn_failchk.lo txn_method.lo txn_rec.lo txn_recover.lo txn_region.lo txn_stat.lo txn_util.lo zerofill.lo -lpthread
libtool: link: clang -O3 -o .libs/db_sql .libs/db_sql.o .libs/parse.o .libs/preparser.o .libs/parsefuncs.o .libs/tokenize.o .libs/sqlprintf.o .libs/buildpt.o .libs/utils.o .libs/generate.o .libs/generate_test.o .libs/generation_utils.o .libs/generate_verification.o .libs/hint_comment.o  ./.libs/libdb-4.8.so -lpthread -Wl,-rpath -Wl,/nix/store/ffy0frz8p4spayvhfy9wgqlp45yhgz50-db-x86_64-unknown-linux-gnufilc0-4.8.30/lib
./libtool --mode=execute true db_sql
libtool: link: clang++  -fPIC -DPIC -shared -nostdlib /nix/store/gcgh62nhmd12bf9vzsbwa9gkpypr1jvg-filc-crt-lib/crti.o /nix/store/gcgh62nhmd12bf9vzsbwa9gkpypr1jvg-filc-crt-lib/crtbegin.o  .libs/cxx_db.o .libs/cxx_dbc.o .libs/cxx_dbt.o .libs/cxx_env.o .libs/cxx_except.o .libs/cxx_lock.o .libs/cxx_logc.o .libs/cxx_mpool.o .libs/cxx_multi.o .libs/cxx_seq.o .libs/cxx_txn.o .libs/db185.o .libs/mut_pthread.o .libs/bt_compare.o .libs/bt_compress.o .libs/bt_conv.o .libs/bt_curadj.o .libs/bt_cursor.o .libs/bt_delete.o .libs/bt_method.o .libs/bt_open.o .libs/bt_put.o .libs/bt_rec.o .libs/bt_reclaim.o .libs/bt_recno.o .libs/bt_rsearch.o .libs/bt_search.o .libs/bt_split.o .libs/bt_stat.o .libs/bt_compact.o .libs/bt_upgrade.o .libs/btree_auto.o .libs/hash.o .libs/hash_auto.o .libs/hash_conv.o .libs/hash_dup.o .libs/hash_meta.o .libs/hash_method.o .libs/hash_open.o .libs/hash_page.o .libs/hash_rec.o .libs/hash_reclaim.o .libs/hash_stat.o .libs/hash_upgrade.o .libs/hash_verify.o .libs/qam.o .libs/qam_auto.o .libs/qam_conv.o .libs/qam_files.o .libs/qam_method.o .libs/qam_open.o .libs/qam_rec.o .libs/qam_stat.o .libs/qam_upgrade.o .libs/qam_verify.o .libs/rep_auto.o .libs/rep_backup.o .libs/rep_elect.o .libs/rep_lease.o .libs/rep_log.o .libs/rep_method.o .libs/rep_record.o .libs/rep_region.o .libs/rep_stat.o .libs/rep_util.o .libs/rep_verify.o .libs/os_addrinfo.o .libs/repmgr_auto.o .libs/repmgr_elect.o .libs/repmgr_method.o .libs/repmgr_msg.o .libs/repmgr_net.o .libs/repmgr_posix.o .libs/repmgr_queue.o .libs/repmgr_sel.o .libs/repmgr_stat.o .libs/repmgr_util.o .libs/db_ovfl_vrfy.o .libs/db_vrfy.o .libs/db_vrfyutil.o .libs/bt_verify.o .libs/lock.o .libs/lock_deadlock.o .libs/lock_failchk.o .libs/lock_id.o .libs/lock_list.o .libs/lock_method.o .libs/lock_region.o .libs/lock_stat.o .libs/lock_timer.o .libs/lock_util.o .libs/mut_alloc.o .libs/mut_failchk.o .libs/mut_method.o .libs/mut_region.o .libs/mut_stat.o .libs/aes_method.o .libs/crypto.o .libs/mt19937db.o .libs/rijndael-alg-fst.o .libs/rijndael-api-fst.o .libs/crdel_auto.o .libs/crdel_rec.o .libs/db.o .libs/db_am.o .libs/db_auto.o .libs/db_byteorder.o .libs/db_cam.o .libs/db_cds.o .libs/db_compint.o .libs/db_conv.o .libs/db_dispatch.o .libs/db_dup.o .libs/db_err.o .libs/db_getlong.o .libs/db_idspace.o .libs/db_iface.o .libs/db_join.o .libs/db_log2.o .libs/db_meta.o .libs/db_method.o .libs/db_open.o .libs/db_overflow.o .libs/db_pr.o .libs/db_rec.o .libs/db_reclaim.o .libs/db_remove.o .libs/db_rename.o .libs/db_ret.o .libs/db_setid.o .libs/db_setlsn.o .libs/db_shash.o .libs/db_sort_multiple.o .libs/db_stati.o .libs/db_truncate.o .libs/db_upg.o .libs/db_upg_opd.o .libs/dbm.o .libs/dbreg.o .libs/dbreg_auto.o .libs/dbreg_rec.o .libs/dbreg_stat.o .libs/dbreg_util.o .libs/dbt.o .libs/env_alloc.o .libs/env_config.o .libs/env_failchk.o .libs/env_file.o .libs/env_globals.o .libs/env_method.o .libs/env_name.o .libs/env_open.o .libs/env_recover.o .libs/env_region.o .libs/env_register.o .libs/env_sig.o .libs/env_stat.o .libs/fileops_auto.o .libs/fop_basic.o .libs/fop_rec.o .libs/fop_util.o .libs/hash_func.o .libs/hmac.o .libs/hsearch.o .libs/log.o .libs/log_archive.o .libs/log_compare.o .libs/log_debug.o .libs/log_get.o .libs/log_method.o .libs/log_put.o .libs/log_stat.o .libs/mkpath.o .libs/mp_alloc.o .libs/mp_bh.o .libs/mp_fget.o .libs/mp_fmethod.o .libs/mp_fopen.o .libs/mp_fput.o .libs/mp_fset.o .libs/mp_method.o .libs/mp_mvcc.o .libs/mp_region.o .libs/mp_register.o .libs/mp_resize.o .libs/mp_stat.o .libs/mp_sync.o .libs/mp_trickle.o .libs/openflags.o .libs/os_abort.o .libs/os_abs.o .libs/os_alloc.o .libs/os_clock.o .libs/os_cpu.o .libs/os_ctime.o .libs/os_config.o .libs/os_dir.o .libs/os_errno.o .libs/os_fid.o .libs/os_flock.o .libs/os_fsync.o .libs/os_getenv.o .libs/os_handle.o .libs/os_map.o .libs/os_method.o .libs/os_mkdir.o .libs/os_open.o .libs/os_pid.o .libs/os_rename.o .libs/os_root.o .libs/os_rpath.o .libs/os_rw.o .libs/os_seek.o .libs/os_stack.o .libs/os_stat.o .libs/os_tmpdir.o .libs/os_truncate.o .libs/os_uid.o .libs/os_unlink.o .libs/os_yield.o .libs/partition.o .libs/seq_stat.o .libs/sequence.o .libs/sha1.o .libs/snprintf.o .libs/txn.o .libs/txn_auto.o .libs/txn_chkpt.o .libs/txn_failchk.o .libs/txn_method.o .libs/txn_rec.o .libs/txn_recover.o .libs/txn_region.o .libs/txn_stat.o .libs/txn_util.o .libs/zerofill.o   -lpthread -L/nix/store/r50h8fzrcx4h59jspwrfy08iicvp1vlg-filc-glibc-2.40/lib -L/nix/store/jxw48plk32hg0gy3b2dgji2p55jg7ss2-filc-libcxx-git/lib -L/nix/store/6ql65jl6flp8qbikcpjn15hycghvqg29-filc-sysroot-with-metadata/lib -L/nix/store/gy2di95906x5rgl25ck3d3xhsp7srz8b-filc-cc/lib -L/nix/store/gcgh62nhmd12bf9vzsbwa9gkpypr1jvg-filc-crt-lib -lc++ -lc++abi -lc -lpizlo -lyoloc -lyolom -lyolort -lyolounwind /nix/store/gcgh62nhmd12bf9vzsbwa9gkpypr1jvg-filc-crt-lib/crtend.o /nix/store/gcgh62nhmd12bf9vzsbwa9gkpypr1jvg-filc-crt-lib/crtn.o  -O   -Wl,-soname -Wl,libdb_cxx-4.8.so -o .libs/libdb_cxx-4.8.so
libtool: link: ( cd ".libs" && rm -f "libdb_cxx-4.8.la" && ln -s "../libdb_cxx-4.8.la" "libdb_cxx-4.8.la" )
rm -f libdb_cxx.a
ln -s .libs/libdb_cxx-4.8.a libdb_cxx.a
Running phase: installPhase
install flags: -j32 SHELL=/nix/store/cfqbabpc7xwg8akbcchqbq3cai6qq2vs-bash-5.2p37/bin/bash pkgconfigdir=/nix/store/ddiv231mk2i22wnk0v279phk8jaw0c8c-db-x86_64-unknown-linux-gnufilc0-4.8.30-dev/lib/pkgconfig m4datadir=/nix/store/ddiv231mk2i22wnk0v279phk8jaw0c8c-db-x86_64-unknown-linux-gnufilc0-4.8.30-dev/share/aclocal aclocaldir=/nix/store/ddiv231mk2i22wnk0v279phk8jaw0c8c-db-x86_64-unknown-linux-gnufilc0-4.8.30-dev/share/aclocal install
Installing DB include files: /nix/store/ddiv231mk2i22wnk0v279phk8jaw0c8c-db-x86_64-unknown-linux-gnufilc0-4.8.30-dev/include ...
Installing DB library: /nix/store/ffy0frz8p4spayvhfy9wgqlp45yhgz50-db-x86_64-unknown-linux-gnufilc0-4.8.30/lib ...
Installing documentation: /nix/store/ffy0frz8p4spayvhfy9wgqlp45yhgz50-db-x86_64-unknown-linux-gnufilc0-4.8.30/docs ...
Installing DB utilities: /nix/store/ablfl8fq5p97lk7zl9pvp5w8q7c80s4j-db-x86_64-unknown-linux-gnufilc0-4.8.30-bin/bin ...
libtool: install: cp -p .libs/libdb-4.8.so /nix/store/ffy0frz8p4spayvhfy9wgqlp45yhgz50-db-x86_64-unknown-linux-gnufilc0-4.8.30/lib/libdb-4.8.so
libtool: warning: 'libdb-4.8.la' has not been installed in '/nix/store/ffy0frz8p4spayvhfy9wgqlp45yhgz50-db-x86_64-unknown-linux-gnufilc0-4.8.30/lib'
libtool: install: cp -p .libs/libdb-4.8.lai /nix/store/ffy0frz8p4spayvhfy9wgqlp45yhgz50-db-x86_64-unknown-linux-gnufilc0-4.8.30/lib/libdb-4.8.la
libtool: install: cp -p .libs/db_archive /nix/store/ablfl8fq5p97lk7zl9pvp5w8q7c80s4j-db-x86_64-unknown-linux-gnufilc0-4.8.30-bin/bin/db_archive
libtool: install: cp -p .libs/libdb_cxx-4.8.so /nix/store/ffy0frz8p4spayvhfy9wgqlp45yhgz50-db-x86_64-unknown-linux-gnufilc0-4.8.30/lib/libdb_cxx-4.8.so
libtool: install: cp -p .libs/libdb_cxx-4.8.lai /nix/store/ffy0frz8p4spayvhfy9wgqlp45yhgz50-db-x86_64-unknown-linux-gnufilc0-4.8.30/lib/libdb_cxx-4.8.la
libtool: finish: PATH="/nix/store/v3l2zqz13i63nzkd2nrqps0y2i74pr10-autoconf-2.72/bin:/nix/store/3ah4cvhhimlxvb2dqk07n1xlbb0dk81f-automake-1.16.5/bin:/nix/store/ava9h9a35fg419f4r1h3ib2hwqx6lr8k-gettext-0.22.5/bin:/nix/store/b7kv2xx2ga3w0fa4h7g0c3y64wkr3i57-libtool-2.5.4/bin:/nix/store/16yz1jny3j9irq4g8zkcx39nr77xwnvx-gnum4-1.4.19/bin:/nix/store/9rsc6g3vlfnp7lvq3pl1xpir5acd1ax0-file-5.45/bin:/nix/store/g7i75czfbw9sy5f8v7rjbama6lr3ya3s-patchelf-0.15.0/bin:/nix/store/a0nc03czg70yaj0p9qphx5b3ppnb939i-filc-cc-wrapper-/bin:/nix/store/gy2di95906x5rgl25ck3d3xhsp7srz8b-filc-cc/bin:/nix/store/6ql65jl6flp8qbikcpjn15hycghvqg29-filc-sysroot-with-metadata/bin:/nix/store/rry6qingvsrqmc7ll7jgaqpybcbdgf5v-coreutils-9.7/bin:/nix/store/bjmp5s6kl068x3vmjg2cbycfwx21hcd2-binutils-wrapper-2.43.1/bin:/nix/store/fmj1ilm5jk1hba6s3cv6gkpgsjvkxaqv-binutils-2.43.1/bin:/nix/store/rry6qingvsrqmc7ll7jgaqpybcbdgf5v-coreutils-9.7/bin:/nix/store/392hs9nhm6wfw4imjllbvb1wil1n39qx-findutils-4.10.0/bin:/nix/store/xw0mf3shymq3k7zlncf09rm8917sdi4h-diffutils-3.12/bin:/nix/store/4rpiqv9yr2pw5094v4wc33ijkqjpm9sa-gnused-4.9/bin:/nix/store/l2wvwyg680h0v2la18hz3yiznxy2naqw-gnugrep-3.11/bin:/nix/store/c1z5j28ndxljf1ihqzag57bwpfpzms0g-gawk-5.3.2/bin:/nix/store/w60s4xh1pjg6dwbw7j0b4xzlpp88q5qg-gnutar-1.35/bin:/nix/store/xd9m9jkvrs8pbxvmkzkwviql33rd090j-gzip-1.14/bin:/nix/store/w1pxx760yidi7n9vbi5bhpii9xxl5vdj-bzip2-1.0.8-bin/bin:/nix/store/xk0d14zpm0njxzdm182dd722aqhav2cc-gnumake-4.4.1/bin:/nix/store/cfqbabpc7xwg8akbcchqbq3cai6qq2vs-bash-5.2p37/bin:/nix/store/gj54zvf7vxll1mzzmqhqi1p4jiws3mfb-patch-2.7.6/bin:/nix/store/22rpb6790f346c55iqi6s9drr5qgmyjf-xz-5.8.1-bin/bin:/nix/store/xlmpcglsq8l09qh03rf0virz0331pjdc-file-5.45/bin:/sbin" ldconfig -n /nix/store/ffy0frz8p4spayvhfy9wgqlp45yhgz50-db-x86_64-unknown-linux-gnufilc0-4.8.30/lib
/build/db-4.8.30/build_unix/libtool: line 1900: ldconfig: command not found
libtool: install: cp -p .libs/db_checkpoint /nix/store/ablfl8fq5p97lk7zl9pvp5w8q7c80s4j-db-x86_64-unknown-linux-gnufilc0-4.8.30-bin/bin/db_checkpoint
----------------------------------------------------------------------
Libraries have been installed in:
   /nix/store/ffy0frz8p4spayvhfy9wgqlp45yhgz50-db-x86_64-unknown-linux-gnufilc0-4.8.30/lib

If you ever happen to want to link against installed libraries
in a given directory, LIBDIR, you must either use libtool, and
specify the full pathname of the library, or use the '-LLIBDIR'
flag during linking and do at least one of the following:
   - add LIBDIR to the 'LD_LIBRARY_PATH' environment variable
     during execution
   - add LIBDIR to the 'LD_RUN_PATH' environment variable
     during linking
   - use the '-Wl,-rpath -Wl,LIBDIR' linker flag
   - have your system administrator run these commands:


See any operating system documentation about shared libraries for
more information, such as the ld(1) and ld.so(8) manual pages.
----------------------------------------------------------------------
libtool: install: cp -p .libs/db_deadlock /nix/store/ablfl8fq5p97lk7zl9pvp5w8q7c80s4j-db-x86_64-unknown-linux-gnufilc0-4.8.30-bin/bin/db_deadlock
libtool: install: cp -p .libs/db_dump /nix/store/ablfl8fq5p97lk7zl9pvp5w8q7c80s4j-db-x86_64-unknown-linux-gnufilc0-4.8.30-bin/bin/db_dump
libtool: install: cp -p .libs/db_hotbackup /nix/store/ablfl8fq5p97lk7zl9pvp5w8q7c80s4j-db-x86_64-unknown-linux-gnufilc0-4.8.30-bin/bin/db_hotbackup
libtool: install: cp -p .libs/db_load /nix/store/ablfl8fq5p97lk7zl9pvp5w8q7c80s4j-db-x86_64-unknown-linux-gnufilc0-4.8.30-bin/bin/db_load
libtool: install: cp -p .libs/db_printlog /nix/store/ablfl8fq5p97lk7zl9pvp5w8q7c80s4j-db-x86_64-unknown-linux-gnufilc0-4.8.30-bin/bin/db_printlog
libtool: install: cp -p .libs/db_recover /nix/store/ablfl8fq5p97lk7zl9pvp5w8q7c80s4j-db-x86_64-unknown-linux-gnufilc0-4.8.30-bin/bin/db_recover
libtool: install: cp -p .libs/db_sql /nix/store/ablfl8fq5p97lk7zl9pvp5w8q7c80s4j-db-x86_64-unknown-linux-gnufilc0-4.8.30-bin/bin/db_sql
libtool: install: cp -p .libs/db_stat /nix/store/ablfl8fq5p97lk7zl9pvp5w8q7c80s4j-db-x86_64-unknown-linux-gnufilc0-4.8.30-bin/bin/db_stat
libtool: install: cp -p .libs/db_upgrade /nix/store/ablfl8fq5p97lk7zl9pvp5w8q7c80s4j-db-x86_64-unknown-linux-gnufilc0-4.8.30-bin/bin/db_upgrade
libtool: install: cp -p .libs/db_verify /nix/store/ablfl8fq5p97lk7zl9pvp5w8q7c80s4j-db-x86_64-unknown-linux-gnufilc0-4.8.30-bin/bin/db_verify
Running phase: fixupPhase
shrinking RPATHs of ELF executables and libraries in /nix/store/ablfl8fq5p97lk7zl9pvp5w8q7c80s4j-db-x86_64-unknown-linux-gnufilc0-4.8.30-bin
shrinking /nix/store/ablfl8fq5p97lk7zl9pvp5w8q7c80s4j-db-x86_64-unknown-linux-gnufilc0-4.8.30-bin/bin/db_archive
shrinking /nix/store/ablfl8fq5p97lk7zl9pvp5w8q7c80s4j-db-x86_64-unknown-linux-gnufilc0-4.8.30-bin/bin/db_checkpoint
shrinking /nix/store/ablfl8fq5p97lk7zl9pvp5w8q7c80s4j-db-x86_64-unknown-linux-gnufilc0-4.8.30-bin/bin/db_deadlock
shrinking /nix/store/ablfl8fq5p97lk7zl9pvp5w8q7c80s4j-db-x86_64-unknown-linux-gnufilc0-4.8.30-bin/bin/db_dump
shrinking /nix/store/ablfl8fq5p97lk7zl9pvp5w8q7c80s4j-db-x86_64-unknown-linux-gnufilc0-4.8.30-bin/bin/db_hotbackup
shrinking /nix/store/ablfl8fq5p97lk7zl9pvp5w8q7c80s4j-db-x86_64-unknown-linux-gnufilc0-4.8.30-bin/bin/db_load
shrinking /nix/store/ablfl8fq5p97lk7zl9pvp5w8q7c80s4j-db-x86_64-unknown-linux-gnufilc0-4.8.30-bin/bin/db_printlog
shrinking /nix/store/ablfl8fq5p97lk7zl9pvp5w8q7c80s4j-db-x86_64-unknown-linux-gnufilc0-4.8.30-bin/bin/db_recover
shrinking /nix/store/ablfl8fq5p97lk7zl9pvp5w8q7c80s4j-db-x86_64-unknown-linux-gnufilc0-4.8.30-bin/bin/db_sql
shrinking /nix/store/ablfl8fq5p97lk7zl9pvp5w8q7c80s4j-db-x86_64-unknown-linux-gnufilc0-4.8.30-bin/bin/db_stat
shrinking /nix/store/ablfl8fq5p97lk7zl9pvp5w8q7c80s4j-db-x86_64-unknown-linux-gnufilc0-4.8.30-bin/bin/db_upgrade
shrinking /nix/store/ablfl8fq5p97lk7zl9pvp5w8q7c80s4j-db-x86_64-unknown-linux-gnufilc0-4.8.30-bin/bin/db_verify
checking for references to /build/ in /nix/store/ablfl8fq5p97lk7zl9pvp5w8q7c80s4j-db-x86_64-unknown-linux-gnufilc0-4.8.30-bin...
patching script interpreter paths in /nix/store/ablfl8fq5p97lk7zl9pvp5w8q7c80s4j-db-x86_64-unknown-linux-gnufilc0-4.8.30-bin
stripping (with command strip and flags -S -p) in  /nix/store/ablfl8fq5p97lk7zl9pvp5w8q7c80s4j-db-x86_64-unknown-linux-gnufilc0-4.8.30-bin/bin
shrinking RPATHs of ELF executables and libraries in /nix/store/ffy0frz8p4spayvhfy9wgqlp45yhgz50-db-x86_64-unknown-linux-gnufilc0-4.8.30
shrinking /nix/store/ffy0frz8p4spayvhfy9wgqlp45yhgz50-db-x86_64-unknown-linux-gnufilc0-4.8.30/lib/libdb-4.8.so
shrinking /nix/store/ffy0frz8p4spayvhfy9wgqlp45yhgz50-db-x86_64-unknown-linux-gnufilc0-4.8.30/lib/libdb_cxx-4.8.so
checking for references to /build/ in /nix/store/ffy0frz8p4spayvhfy9wgqlp45yhgz50-db-x86_64-unknown-linux-gnufilc0-4.8.30...
patching script interpreter paths in /nix/store/ffy0frz8p4spayvhfy9wgqlp45yhgz50-db-x86_64-unknown-linux-gnufilc0-4.8.30
stripping (with command strip and flags -S -p) in  /nix/store/ffy0frz8p4spayvhfy9wgqlp45yhgz50-db-x86_64-unknown-linux-gnufilc0-4.8.30/lib
shrinking RPATHs of ELF executables and libraries in /nix/store/ddiv231mk2i22wnk0v279phk8jaw0c8c-db-x86_64-unknown-linux-gnufilc0-4.8.30-dev
checking for references to /build/ in /nix/store/ddiv231mk2i22wnk0v279phk8jaw0c8c-db-x86_64-unknown-linux-gnufilc0-4.8.30-dev...
patching script interpreter paths in /nix/store/ddiv231mk2i22wnk0v279phk8jaw0c8c-db-x86_64-unknown-linux-gnufilc0-4.8.30-dev
```

```
 /nix/store/rry6qingvsrqmc7ll7jgaqpybcbdgf5v-coreutils-9.7/bin/mkdir -p '/nix/store/dqc8a873q14w0yfc2w1cvs9x2fij3zw1-audit-x86_64-unknown-linux-gnufilc0-4.1.0-dev/share/aclocal'
 /nix/store/rry6qingvsrqmc7ll7jgaqpybcbdgf5v-coreutils-9.7/bin/install -c -m 644 audit.m4 '/nix/store/dqc8a873q14w0yfc2w1cvs9x2fij3zw1-audit-x86_64-unknown-linux-gnufilc0-4.1.0-dev/share/aclocal'
make[2]: Leaving directory '/build/source/m4'
make[1]: Leaving directory '/build/source/m4'
Making install in docs
make[1]: Entering directory '/build/source/docs'
make[2]: Entering directory '/build/source/docs'
make[2]: Nothing to be done for 'install-exec-am'.
 /nix/store/rry6qingvsrqmc7ll7jgaqpybcbdgf5v-coreutils-9.7/bin/mkdir -p '/nix/store/fd4fkvq3lnnr8pykay7i3ap64ipwv0zx-audit-x86_64-unknown-linux-gnufilc0-4.1.0-man/share/man/man5'
 /nix/store/rry6qingvsrqmc7ll7jgaqpybcbdgf5v-coreutils-9.7/bin/mkdir -p '/nix/store/fd4fkvq3lnnr8pykay7i3ap64ipwv0zx-audit-x86_64-unknown-linux-gnufilc0-4.1.0-man/share/man/man3'
 /nix/store/rry6qingvsrqmc7ll7jgaqpybcbdgf5v-coreutils-9.7/bin/mkdir -p '/nix/store/fd4fkvq3lnnr8pykay7i3ap64ipwv0zx-audit-x86_64-unknown-linux-gnufilc0-4.1.0-man/share/man/man8'
 /nix/store/rry6qingvsrqmc7ll7jgaqpybcbdgf5v-coreutils-9.7/bin/mkdir -p '/nix/store/fd4fkvq3lnnr8pykay7i3ap64ipwv0zx-audit-x86_64-unknown-linux-gnufilc0-4.1.0-man/share/man/man7'
 /nix/store/rry6qingvsrqmc7ll7jgaqpybcbdgf5v-coreutils-9.7/bin/install -c -m 644 auditd.conf.5 auditd-plugins.5 ausearch-expression.5 libaudit.conf.5 zos-remote.conf.5 auditd.cron.5 '/nix/store/fd4fkvq3lnnr8pykay7i3ap64ipwv0zx-audit-x86_64-unknown-linux-gnufilc0-4.1.0-man/share/man/man5'
 /nix/store/rry6qingvsrqmc7ll7jgaqpybcbdgf5v-coreutils-9.7/bin/install -c -m 644 auditctl.8 auditd.8 aureport.8 ausearch.8 audispd-zos-remote.8 augenrules.8 '/nix/store/fd4fkvq3lnnr8pykay7i3ap64ipwv0zx-audit-x86_64-unknown-linux-gnufilc0-4.1.0-man/share/man/man8'
 /nix/store/rry6qingvsrqmc7ll7jgaqpybcbdgf5v-coreutils-9.7/bin/install -c -m 644 audit.rules.7 '/nix/store/fd4fkvq3lnnr8pykay7i3ap64ipwv0zx-audit-x86_64-unknown-linux-gnufilc0-4.1.0-man/share/man/man7'
 /nix/store/rry6qingvsrqmc7ll7jgaqpybcbdgf5v-coreutils-9.7/bin/install -c -m 644 audit_add_rule_data.3 audit_add_watch.3 audit_delete_rule_data.3 audit_detect_machine.3 audit_encode_nv_string.3 audit_getloginuid.3 audit_get_reply.3 audit_get_session.3 audit_log_acct_message.3 audit_log_user_avc_message.3 audit_log_user_command.3 audit_log_user_comm_message.3 audit_log_user_message.3 audit_log_semanage_message.3 auparse_new_buffer.3 audit_open.3 audit_close.3 audit_is_enabled.3 audit_request_rules_list_data.3 audit_request_signal_info.3 audit_request_status.3 audit_set_backlog_limit.3 audit_set_enabled.3 audit_set_failure.3 audit_setloginuid.3 audit_set_pid.3 audit_set_rate_limit.3 audit_update_watch_perms.3 audit_value_needs_encoding.3 audit_encode_value.3 auparse_add_callback.3 audit_name_to_syscall.3 audit_syscall_to_name.3 audit_name_to_errno.3 audit_fstype_to_name.3 audit_name_to_fstype.3 audit_name_to_action.3 audit_flag_to_name.3 audit_name_to_flag.3 auplugin_fgets.3 '/nix/store/fd4fkvq3lnnr8pykay7i3ap64ipwv0zx-audit-x86_64-unknown-linux-gnufilc0-4.1.0-man/share/man/man3'
 /nix/store/rry6qingvsrqmc7ll7jgaqpybcbdgf5v-coreutils-9.7/bin/install -c -m 644 auplugin.3 auparse_destroy.3 auparse_feed.3 auparse_feed_age_events.3 auparse_feed_has_data.3 auparse_find_field.3 auparse_find_field_next.3 auparse_first_field.3 auparse_first_record.3 auparse_flush_feed.3 auparse_get_field_int.3 auparse_get_field_name.3 auparse_get_field_str.3 auparse_get_field_type.3 auparse_get_filename.3 auparse_get_line_number.3 auparse_get_milli.3 auparse_get_node.3 auparse_get_num_fields.3 auparse_get_num_records.3 auparse_get_record_text.3 auparse_get_serial.3 auparse_get_time.3 auparse_get_timestamp.3 auparse_get_type.3 auparse_get_type_name.3 auparse_get_field_num.3 auparse_get_record_num.3 auparse_goto_field_num.3 auparse_goto_record_num.3 auparse_init.3 auparse_interpret_field.3 auparse_metrics.3 auparse_next_event.3 auparse_next_field.3 auparse_next_record.3 auparse_node_compare.3 auparse_reset.3 auparse_set_escape_mode.3 auparse_normalize.3 '/nix/store/fd4fkvq3lnnr8pykay7i3ap64ipwv0zx-audit-x86_64-unknown-linux-gnufilc0-4.1.0-man/share/man/man3'
 /nix/store/rry6qingvsrqmc7ll7jgaqpybcbdgf5v-coreutils-9.7/bin/install -c -m 644 auparse_normalize_functions.3 auparse_timestamp_compare.3 auparse_set_eoe_timeout.3 ausearch_add_item.3 ausearch_add_interpreted_item.3 ausearch_add_expression.3 ausearch_add_timestamp_item.3 ausearch_add_regex.3 ausearch_add_timestamp_item_ex.3 ausearch_clear.3 ausearch_next_event.3 ausearch_cur_event.3 ausearch_set_stop.3 get_auditfail_action.3 set_aumessage_mode.3 audit_set_backlog_wait_time.3 '/nix/store/fd4fkvq3lnnr8pykay7i3ap64ipwv0zx-audit-x86_64-unknown-linux-gnufilc0-4.1.0-man/share/man/man3'
make[2]: Leaving directory '/build/source/docs'
make[1]: Leaving directory '/build/source/docs'
Making install in rules
make[1]: Entering directory '/build/source/rules'
make[2]: Entering directory '/build/source/rules'
make[2]: Nothing to be done for 'install-exec-am'.
 /nix/store/rry6qingvsrqmc7ll7jgaqpybcbdgf5v-coreutils-9.7/bin/mkdir -p '/nix/store/82b7alx2gwav01k9fzr4rhwvp8nrh6yy-audit-x86_64-unknown-linux-gnufilc0-4.1.0/share/audit-rules'
 /nix/store/rry6qingvsrqmc7ll7jgaqpybcbdgf5v-coreutils-9.7/bin/install -c -m 644 10-base-config.rules 10-no-audit.rules 11-loginuid.rules 12-ignore-error.rules 12-cont-fail.rules 20-dont-audit.rules 21-no32bit.rules 22-ignore-chrony.rules 23-ignore-filesystems.rules 30-stig.rules 30-pci-dss-v31.rules 30-ospp-v42.rules 30-ospp-v42-1-create-failed.rules 30-ospp-v42-1-create-success.rules 30-ospp-v42-2-modify-failed.rules 30-ospp-v42-2-modify-success.rules 30-ospp-v42-3-access-failed.rules 30-ospp-v42-3-access-success.rules 30-ospp-v42-4-delete-failed.rules 30-ospp-v42-4-delete-success.rules 30-ospp-v42-5-perm-change-failed.rules 30-ospp-v42-5-perm-change-success.rules 30-ospp-v42-6-owner-change-failed.rules 30-ospp-v42-6-owner-change-success.rules 31-privileged.rules 32-power-abuse.rules 40-local.rules 41-containers.rules 42-injection.rules 43-module-load.rules 44-installers.rules 70-einval.rules 71-networking.rules 99-finalize.rules README-rules '/nix/store/82b7alx2gwav01k9fzr4rhwvp8nrh6yy-audit-x86_64-unknown-linux-gnufilc0-4.1.0/share/audit-rules'
make[2]: Leaving directory '/build/source/rules'
make[1]: Leaving directory '/build/source/rules'
make[1]: Entering directory '/build/source'
make[2]: Entering directory '/build/source'
make[2]: Nothing to be done for 'install-exec-am'.
make[2]: Nothing to be done for 'install-data-am'.
make[2]: Leaving directory '/build/source'
make[1]: Leaving directory '/build/source'
Running phase: fixupPhase
Patching '/nix/store/dqc8a873q14w0yfc2w1cvs9x2fij3zw1-audit-x86_64-unknown-linux-gnufilc0-4.1.0-dev/lib/pkgconfig/audit.pc' includedir to output /nix/store/dqc8a873q14w0yfc2w1cvs9x2fij3zw1-audit-x86_64-unknown-linux-gnufilc0-4.1.0-dev
Patching '/nix/store/dqc8a873q14w0yfc2w1cvs9x2fij3zw1-audit-x86_64-unknown-linux-gnufilc0-4.1.0-dev/lib/pkgconfig/auparse.pc' includedir to output /nix/store/dqc8a873q14w0yfc2w1cvs9x2fij3zw1-audit-x86_64-unknown-linux-gnufilc0-4.1.0-dev
shrinking RPATHs of ELF executables and libraries in /nix/store/55hgpdcpvxncmn11dnbl3pibj2vm1w0l-audit-x86_64-unknown-linux-gnufilc0-4.1.0-bin
shrinking /nix/store/55hgpdcpvxncmn11dnbl3pibj2vm1w0l-audit-x86_64-unknown-linux-gnufilc0-4.1.0-bin/sbin/audisp-af_unix
shrinking /nix/store/55hgpdcpvxncmn11dnbl3pibj2vm1w0l-audit-x86_64-unknown-linux-gnufilc0-4.1.0-bin/sbin/audisp-remote
shrinking /nix/store/55hgpdcpvxncmn11dnbl3pibj2vm1w0l-audit-x86_64-unknown-linux-gnufilc0-4.1.0-bin/sbin/audisp-syslog
shrinking /nix/store/55hgpdcpvxncmn11dnbl3pibj2vm1w0l-audit-x86_64-unknown-linux-gnufilc0-4.1.0-bin/sbin/audisp-filter
shrinking /nix/store/55hgpdcpvxncmn11dnbl3pibj2vm1w0l-audit-x86_64-unknown-linux-gnufilc0-4.1.0-bin/sbin/auditd
shrinking /nix/store/55hgpdcpvxncmn11dnbl3pibj2vm1w0l-audit-x86_64-unknown-linux-gnufilc0-4.1.0-bin/sbin/auditctl
shrinking /nix/store/55hgpdcpvxncmn11dnbl3pibj2vm1w0l-audit-x86_64-unknown-linux-gnufilc0-4.1.0-bin/sbin/aureport
shrinking /nix/store/55hgpdcpvxncmn11dnbl3pibj2vm1w0l-audit-x86_64-unknown-linux-gnufilc0-4.1.0-bin/sbin/ausearch
shrinking /nix/store/55hgpdcpvxncmn11dnbl3pibj2vm1w0l-audit-x86_64-unknown-linux-gnufilc0-4.1.0-bin/bin/aulast
shrinking /nix/store/55hgpdcpvxncmn11dnbl3pibj2vm1w0l-audit-x86_64-unknown-linux-gnufilc0-4.1.0-bin/bin/aulastlog
shrinking /nix/store/55hgpdcpvxncmn11dnbl3pibj2vm1w0l-audit-x86_64-unknown-linux-gnufilc0-4.1.0-bin/bin/ausyscall
checking for references to /build/ in /nix/store/55hgpdcpvxncmn11dnbl3pibj2vm1w0l-audit-x86_64-unknown-linux-gnufilc0-4.1.0-bin...
moving /nix/store/55hgpdcpvxncmn11dnbl3pibj2vm1w0l-audit-x86_64-unknown-linux-gnufilc0-4.1.0-bin/sbin/* to /nix/store/55hgpdcpvxncmn11dnbl3pibj2vm1w0l-audit-x86_64-unknown-linux-gnufilc0-4.1.0-bin/bin
patching script interpreter paths in /nix/store/55hgpdcpvxncmn11dnbl3pibj2vm1w0l-audit-x86_64-unknown-linux-gnufilc0-4.1.0-bin
/nix/store/55hgpdcpvxncmn11dnbl3pibj2vm1w0l-audit-x86_64-unknown-linux-gnufilc0-4.1.0-bin/bin/augenrules: interpreter directive changed from "#!/bin/sh" to "/nix/store/rj6fa766w36f8rx9j5hib25j2vm113vz-bash-interactive-x86_64-unknown-linux-gnufilc0-5.2p37/bin/sh"
stripping (with command strip and flags -S -p) in  /nix/store/55hgpdcpvxncmn11dnbl3pibj2vm1w0l-audit-x86_64-unknown-linux-gnufilc0-4.1.0-bin/bin /nix/store/55hgpdcpvxncmn11dnbl3pibj2vm1w0l-audit-x86_64-unknown-linux-gnufilc0-4.1.0-bin/sbin
shrinking RPATHs of ELF executables and libraries in /nix/store/ipv5ghb8pnhxiai812b919l7xisyqbpr-audit-x86_64-unknown-linux-gnufilc0-4.1.0-lib
shrinking /nix/store/ipv5ghb8pnhxiai812b919l7xisyqbpr-audit-x86_64-unknown-linux-gnufilc0-4.1.0-lib/lib/libaudit.so.1.0.0
shrinking /nix/store/ipv5ghb8pnhxiai812b919l7xisyqbpr-audit-x86_64-unknown-linux-gnufilc0-4.1.0-lib/lib/libauparse.so.0.0.0
shrinking /nix/store/ipv5ghb8pnhxiai812b919l7xisyqbpr-audit-x86_64-unknown-linux-gnufilc0-4.1.0-lib/lib/libauplugin.so.1.0.0
checking for references to /build/ in /nix/store/ipv5ghb8pnhxiai812b919l7xisyqbpr-audit-x86_64-unknown-linux-gnufilc0-4.1.0-lib...
patching script interpreter paths in /nix/store/ipv5ghb8pnhxiai812b919l7xisyqbpr-audit-x86_64-unknown-linux-gnufilc0-4.1.0-lib
/nix/store/ipv5ghb8pnhxiai812b919l7xisyqbpr-audit-x86_64-unknown-linux-gnufilc0-4.1.0-lib/libexec/initscripts/legacy-actions/auditd/rotate: interpreter directive changed from "#!/bin/sh" to "/nix/store/rj6fa766w36f8rx9j5hib25j2vm113vz-bash-interactive-x86_64-unknown-linux-gnufilc0-5.2p37/bin/sh"
/nix/store/ipv5ghb8pnhxiai812b919l7xisyqbpr-audit-x86_64-unknown-linux-gnufilc0-4.1.0-lib/libexec/initscripts/legacy-actions/auditd/resume: interpreter directive changed from "#!/bin/sh" to "/nix/store/rj6fa766w36f8rx9j5hib25j2vm113vz-bash-interactive-x86_64-unknown-linux-gnufilc0-5.2p37/bin/sh"
/nix/store/ipv5ghb8pnhxiai812b919l7xisyqbpr-audit-x86_64-unknown-linux-gnufilc0-4.1.0-lib/libexec/initscripts/legacy-actions/auditd/reload: interpreter directive changed from "#!/bin/sh" to "/nix/store/rj6fa766w36f8rx9j5hib25j2vm113vz-bash-interactive-x86_64-unknown-linux-gnufilc0-5.2p37/bin/sh"
/nix/store/ipv5ghb8pnhxiai812b919l7xisyqbpr-audit-x86_64-unknown-linux-gnufilc0-4.1.0-lib/libexec/initscripts/legacy-actions/auditd/state: interpreter directive changed from "#!/bin/sh" to "/nix/store/rj6fa766w36f8rx9j5hib25j2vm113vz-bash-interactive-x86_64-unknown-linux-gnufilc0-5.2p37/bin/sh"
/nix/store/ipv5ghb8pnhxiai812b919l7xisyqbpr-audit-x86_64-unknown-linux-gnufilc0-4.1.0-lib/libexec/initscripts/legacy-actions/auditd/stop: interpreter directive changed from "#!/bin/sh" to "/nix/store/rj6fa766w36f8rx9j5hib25j2vm113vz-bash-interactive-x86_64-unknown-linux-gnufilc0-5.2p37/bin/sh"
/nix/store/ipv5ghb8pnhxiai812b919l7xisyqbpr-audit-x86_64-unknown-linux-gnufilc0-4.1.0-lib/libexec/initscripts/legacy-actions/auditd/restart: interpreter directive changed from "#!/bin/sh" to "/nix/store/rj6fa766w36f8rx9j5hib25j2vm113vz-bash-interactive-x86_64-unknown-linux-gnufilc0-5.2p37/bin/sh"
/nix/store/ipv5ghb8pnhxiai812b919l7xisyqbpr-audit-x86_64-unknown-linux-gnufilc0-4.1.0-lib/libexec/initscripts/legacy-actions/auditd/condrestart: interpreter directive changed from "#!/bin/sh" to "/nix/store/rj6fa766w36f8rx9j5hib25j2vm113vz-bash-interactive-x86_64-unknown-linux-gnufilc0-5.2p37/bin/sh"
stripping (with command strip and flags -S -p) in  /nix/store/ipv5ghb8pnhxiai812b919l7xisyqbpr-audit-x86_64-unknown-linux-gnufilc0-4.1.0-lib/lib /nix/store/ipv5ghb8pnhxiai812b919l7xisyqbpr-audit-x86_64-unknown-linux-gnufilc0-4.1.0-lib/libexec
shrinking RPATHs of ELF executables and libraries in /nix/store/dqc8a873q14w0yfc2w1cvs9x2fij3zw1-audit-x86_64-unknown-linux-gnufilc0-4.1.0-dev
checking for references to /build/ in /nix/store/dqc8a873q14w0yfc2w1cvs9x2fij3zw1-audit-x86_64-unknown-linux-gnufilc0-4.1.0-dev...
patching script interpreter paths in /nix/store/dqc8a873q14w0yfc2w1cvs9x2fij3zw1-audit-x86_64-unknown-linux-gnufilc0-4.1.0-dev
stripping (with command strip and flags -S -p) in  /nix/store/dqc8a873q14w0yfc2w1cvs9x2fij3zw1-audit-x86_64-unknown-linux-gnufilc0-4.1.0-dev/lib
shrinking RPATHs of ELF executables and libraries in /nix/store/82b7alx2gwav01k9fzr4rhwvp8nrh6yy-audit-x86_64-unknown-linux-gnufilc0-4.1.0
checking for references to /build/ in /nix/store/82b7alx2gwav01k9fzr4rhwvp8nrh6yy-audit-x86_64-unknown-linux-gnufilc0-4.1.0...
patching script interpreter paths in /nix/store/82b7alx2gwav01k9fzr4rhwvp8nrh6yy-audit-x86_64-unknown-linux-gnufilc0-4.1.0
stripping (with command strip and flags -S -p) in  /nix/store/82b7alx2gwav01k9fzr4rhwvp8nrh6yy-audit-x86_64-unknown-linux-gnufilc0-4.1.0/lib
shrinking RPATHs of ELF executables and libraries in /nix/store/fd4fkvq3lnnr8pykay7i3ap64ipwv0zx-audit-x86_64-unknown-linux-gnufilc0-4.1.0-man
checking for references to /build/ in /nix/store/fd4fkvq3lnnr8pykay7i3ap64ipwv0zx-audit-x86_64-unknown-linux-gnufilc0-4.1.0-man...
gzipping man pages under /nix/store/fd4fkvq3lnnr8pykay7i3ap64ipwv0zx-audit-x86_64-unknown-linux-gnufilc0-4.1.0-man/share/man/
patching script interpreter paths in /nix/store/fd4fkvq3lnnr8pykay7i3ap64ipwv0zx-audit-x86_64-unknown-linux-gnufilc0-4.1.0-man
```

```
Making install in examples
make[1]: Entering directory '/build/Linux-PAM-1.6.1/examples'
make[2]: Entering directory '/build/Linux-PAM-1.6.1/examples'
make[2]: Nothing to be done for 'install-exec-am'.
make[2]: Nothing to be done for 'install-data-am'.
make[2]: Leaving directory '/build/Linux-PAM-1.6.1/examples'
make[1]: Leaving directory '/build/Linux-PAM-1.6.1/examples'
make[1]: Entering directory '/build/Linux-PAM-1.6.1'
make[2]: Entering directory '/build/Linux-PAM-1.6.1'
make[2]: Nothing to be done for 'install-exec-am'.
make[2]: Nothing to be done for 'install-data-am'.
make[2]: Leaving directory '/build/Linux-PAM-1.6.1'
make[1]: Leaving directory '/build/Linux-PAM-1.6.1'
Running phase: fixupPhase
Patching '/nix/store/zbsh67jk6fd1xnylmazx1vqhkhqps30l-linux-pam-x86_64-unknown-linux-gnufilc0-1.6.1/lib/pkgconfig/pam.pc' includedir to output /nix/store/zbsh67jk6fd1xnylmazx1vqhkhqps30l-linux-pam-x86_64-unknown-linux-gnufilc0-1.6.1
Patching '/nix/store/zbsh67jk6fd1xnylmazx1vqhkhqps30l-linux-pam-x86_64-unknown-linux-gnufilc0-1.6.1/lib/pkgconfig/pam_misc.pc' includedir to output /nix/store/zbsh67jk6fd1xnylmazx1vqhkhqps30l-linux-pam-x86_64-unknown-linux-gnufilc0-1.6.1
Patching '/nix/store/zbsh67jk6fd1xnylmazx1vqhkhqps30l-linux-pam-x86_64-unknown-linux-gnufilc0-1.6.1/lib/pkgconfig/pamc.pc' includedir to output /nix/store/zbsh67jk6fd1xnylmazx1vqhkhqps30l-linux-pam-x86_64-unknown-linux-gnufilc0-1.6.1
shrinking RPATHs of ELF executables and libraries in /nix/store/zbsh67jk6fd1xnylmazx1vqhkhqps30l-linux-pam-x86_64-unknown-linux-gnufilc0-1.6.1
shrinking /nix/store/zbsh67jk6fd1xnylmazx1vqhkhqps30l-linux-pam-x86_64-unknown-linux-gnufilc0-1.6.1/lib/libpam.so.0.85.1
shrinking /nix/store/zbsh67jk6fd1xnylmazx1vqhkhqps30l-linux-pam-x86_64-unknown-linux-gnufilc0-1.6.1/lib/libpamc.so.0.82.1
shrinking /nix/store/zbsh67jk6fd1xnylmazx1vqhkhqps30l-linux-pam-x86_64-unknown-linux-gnufilc0-1.6.1/lib/libpam_misc.so.0.82.1
shrinking /nix/store/zbsh67jk6fd1xnylmazx1vqhkhqps30l-linux-pam-x86_64-unknown-linux-gnufilc0-1.6.1/lib/security/pam_access.so
shrinking /nix/store/zbsh67jk6fd1xnylmazx1vqhkhqps30l-linux-pam-x86_64-unknown-linux-gnufilc0-1.6.1/lib/security/pam_canonicalize_user.so
shrinking /nix/store/zbsh67jk6fd1xnylmazx1vqhkhqps30l-linux-pam-x86_64-unknown-linux-gnufilc0-1.6.1/lib/security/pam_debug.so
shrinking /nix/store/zbsh67jk6fd1xnylmazx1vqhkhqps30l-linux-pam-x86_64-unknown-linux-gnufilc0-1.6.1/lib/security/pam_deny.so
shrinking /nix/store/zbsh67jk6fd1xnylmazx1vqhkhqps30l-linux-pam-x86_64-unknown-linux-gnufilc0-1.6.1/lib/security/pam_echo.so
shrinking /nix/store/zbsh67jk6fd1xnylmazx1vqhkhqps30l-linux-pam-x86_64-unknown-linux-gnufilc0-1.6.1/lib/security/pam_env.so
shrinking /nix/store/zbsh67jk6fd1xnylmazx1vqhkhqps30l-linux-pam-x86_64-unknown-linux-gnufilc0-1.6.1/lib/security/pam_exec.so
shrinking /nix/store/zbsh67jk6fd1xnylmazx1vqhkhqps30l-linux-pam-x86_64-unknown-linux-gnufilc0-1.6.1/lib/security/pam_faildelay.so
shrinking /nix/store/zbsh67jk6fd1xnylmazx1vqhkhqps30l-linux-pam-x86_64-unknown-linux-gnufilc0-1.6.1/lib/security/pam_faillock.so
shrinking /nix/store/zbsh67jk6fd1xnylmazx1vqhkhqps30l-linux-pam-x86_64-unknown-linux-gnufilc0-1.6.1/lib/security/pam_filter/upperLOWER
shrinking /nix/store/zbsh67jk6fd1xnylmazx1vqhkhqps30l-linux-pam-x86_64-unknown-linux-gnufilc0-1.6.1/lib/security/pam_filter.so
shrinking /nix/store/zbsh67jk6fd1xnylmazx1vqhkhqps30l-linux-pam-x86_64-unknown-linux-gnufilc0-1.6.1/lib/security/pam_ftp.so
shrinking /nix/store/zbsh67jk6fd1xnylmazx1vqhkhqps30l-linux-pam-x86_64-unknown-linux-gnufilc0-1.6.1/lib/security/pam_group.so
shrinking /nix/store/zbsh67jk6fd1xnylmazx1vqhkhqps30l-linux-pam-x86_64-unknown-linux-gnufilc0-1.6.1/lib/security/pam_issue.so
shrinking /nix/store/zbsh67jk6fd1xnylmazx1vqhkhqps30l-linux-pam-x86_64-unknown-linux-gnufilc0-1.6.1/lib/security/pam_keyinit.so
shrinking /nix/store/zbsh67jk6fd1xnylmazx1vqhkhqps30l-linux-pam-x86_64-unknown-linux-gnufilc0-1.6.1/lib/security/pam_lastlog.so
shrinking /nix/store/zbsh67jk6fd1xnylmazx1vqhkhqps30l-linux-pam-x86_64-unknown-linux-gnufilc0-1.6.1/lib/security/pam_limits.so
shrinking /nix/store/zbsh67jk6fd1xnylmazx1vqhkhqps30l-linux-pam-x86_64-unknown-linux-gnufilc0-1.6.1/lib/security/pam_listfile.so
shrinking /nix/store/zbsh67jk6fd1xnylmazx1vqhkhqps30l-linux-pam-x86_64-unknown-linux-gnufilc0-1.6.1/lib/security/pam_localuser.so
shrinking /nix/store/zbsh67jk6fd1xnylmazx1vqhkhqps30l-linux-pam-x86_64-unknown-linux-gnufilc0-1.6.1/lib/security/pam_loginuid.so
shrinking /nix/store/zbsh67jk6fd1xnylmazx1vqhkhqps30l-linux-pam-x86_64-unknown-linux-gnufilc0-1.6.1/lib/security/pam_mail.so
shrinking /nix/store/zbsh67jk6fd1xnylmazx1vqhkhqps30l-linux-pam-x86_64-unknown-linux-gnufilc0-1.6.1/lib/security/pam_mkhomedir.so
shrinking /nix/store/zbsh67jk6fd1xnylmazx1vqhkhqps30l-linux-pam-x86_64-unknown-linux-gnufilc0-1.6.1/lib/security/pam_motd.so
shrinking /nix/store/zbsh67jk6fd1xnylmazx1vqhkhqps30l-linux-pam-x86_64-unknown-linux-gnufilc0-1.6.1/lib/security/pam_namespace.so
shrinking /nix/store/zbsh67jk6fd1xnylmazx1vqhkhqps30l-linux-pam-x86_64-unknown-linux-gnufilc0-1.6.1/lib/security/pam_nologin.so
shrinking /nix/store/zbsh67jk6fd1xnylmazx1vqhkhqps30l-linux-pam-x86_64-unknown-linux-gnufilc0-1.6.1/lib/security/pam_permit.so
shrinking /nix/store/zbsh67jk6fd1xnylmazx1vqhkhqps30l-linux-pam-x86_64-unknown-linux-gnufilc0-1.6.1/lib/security/pam_pwhistory.so
shrinking /nix/store/zbsh67jk6fd1xnylmazx1vqhkhqps30l-linux-pam-x86_64-unknown-linux-gnufilc0-1.6.1/lib/security/pam_rhosts.so
shrinking /nix/store/zbsh67jk6fd1xnylmazx1vqhkhqps30l-linux-pam-x86_64-unknown-linux-gnufilc0-1.6.1/lib/security/pam_rootok.so
shrinking /nix/store/zbsh67jk6fd1xnylmazx1vqhkhqps30l-linux-pam-x86_64-unknown-linux-gnufilc0-1.6.1/lib/security/pam_securetty.so
shrinking /nix/store/zbsh67jk6fd1xnylmazx1vqhkhqps30l-linux-pam-x86_64-unknown-linux-gnufilc0-1.6.1/lib/security/pam_setquota.so
shrinking /nix/store/zbsh67jk6fd1xnylmazx1vqhkhqps30l-linux-pam-x86_64-unknown-linux-gnufilc0-1.6.1/lib/security/pam_shells.so
shrinking /nix/store/zbsh67jk6fd1xnylmazx1vqhkhqps30l-linux-pam-x86_64-unknown-linux-gnufilc0-1.6.1/lib/security/pam_stress.so
shrinking /nix/store/zbsh67jk6fd1xnylmazx1vqhkhqps30l-linux-pam-x86_64-unknown-linux-gnufilc0-1.6.1/lib/security/pam_succeed_if.so
shrinking /nix/store/zbsh67jk6fd1xnylmazx1vqhkhqps30l-linux-pam-x86_64-unknown-linux-gnufilc0-1.6.1/lib/security/pam_time.so
shrinking /nix/store/zbsh67jk6fd1xnylmazx1vqhkhqps30l-linux-pam-x86_64-unknown-linux-gnufilc0-1.6.1/lib/security/pam_timestamp.so
shrinking /nix/store/zbsh67jk6fd1xnylmazx1vqhkhqps30l-linux-pam-x86_64-unknown-linux-gnufilc0-1.6.1/lib/security/pam_tty_audit.so
shrinking /nix/store/zbsh67jk6fd1xnylmazx1vqhkhqps30l-linux-pam-x86_64-unknown-linux-gnufilc0-1.6.1/lib/security/pam_umask.so
shrinking /nix/store/zbsh67jk6fd1xnylmazx1vqhkhqps30l-linux-pam-x86_64-unknown-linux-gnufilc0-1.6.1/lib/security/pam_unix.so
shrinking /nix/store/zbsh67jk6fd1xnylmazx1vqhkhqps30l-linux-pam-x86_64-unknown-linux-gnufilc0-1.6.1/lib/security/pam_userdb.so
shrinking /nix/store/zbsh67jk6fd1xnylmazx1vqhkhqps30l-linux-pam-x86_64-unknown-linux-gnufilc0-1.6.1/lib/security/pam_usertype.so
shrinking /nix/store/zbsh67jk6fd1xnylmazx1vqhkhqps30l-linux-pam-x86_64-unknown-linux-gnufilc0-1.6.1/lib/security/pam_warn.so
shrinking /nix/store/zbsh67jk6fd1xnylmazx1vqhkhqps30l-linux-pam-x86_64-unknown-linux-gnufilc0-1.6.1/lib/security/pam_wheel.so
shrinking /nix/store/zbsh67jk6fd1xnylmazx1vqhkhqps30l-linux-pam-x86_64-unknown-linux-gnufilc0-1.6.1/lib/security/pam_xauth.so
shrinking /nix/store/zbsh67jk6fd1xnylmazx1vqhkhqps30l-linux-pam-x86_64-unknown-linux-gnufilc0-1.6.1/sbin/faillock
shrinking /nix/store/zbsh67jk6fd1xnylmazx1vqhkhqps30l-linux-pam-x86_64-unknown-linux-gnufilc0-1.6.1/sbin/mkhomedir_helper
shrinking /nix/store/zbsh67jk6fd1xnylmazx1vqhkhqps30l-linux-pam-x86_64-unknown-linux-gnufilc0-1.6.1/sbin/pam_timestamp_check
shrinking /nix/store/zbsh67jk6fd1xnylmazx1vqhkhqps30l-linux-pam-x86_64-unknown-linux-gnufilc0-1.6.1/sbin/unix_chkpwd
checking for references to /build/ in /nix/store/zbsh67jk6fd1xnylmazx1vqhkhqps30l-linux-pam-x86_64-unknown-linux-gnufilc0-1.6.1...
moving /nix/store/zbsh67jk6fd1xnylmazx1vqhkhqps30l-linux-pam-x86_64-unknown-linux-gnufilc0-1.6.1/sbin/* to /nix/store/zbsh67jk6fd1xnylmazx1vqhkhqps30l-linux-pam-x86_64-unknown-linux-gnufilc0-1.6.1/bin
patching script interpreter paths in /nix/store/zbsh67jk6fd1xnylmazx1vqhkhqps30l-linux-pam-x86_64-unknown-linux-gnufilc0-1.6.1
stripping (with command strip and flags -S -p) in  /nix/store/zbsh67jk6fd1xnylmazx1vqhkhqps30l-linux-pam-x86_64-unknown-linux-gnufilc0-1.6.1/lib /nix/store/zbsh67jk6fd1xnylmazx1vqhkhqps30l-linux-pam-x86_64-unknown-linux-gnufilc0-1.6.1/bin /nix/store/zbsh67jk6fd1xnylmazx1vqhkhqps30l-linux-pam-x86_64-unknown-linux-gnufilc0-1.6.1/sbin
shrinking RPATHs of ELF executables and libraries in /nix/store/pb52h2w6prvfqfirk6i3w6mbyphbm6xn-linux-pam-x86_64-unknown-linux-gnufilc0-1.6.1-doc
checking for references to /build/ in /nix/store/pb52h2w6prvfqfirk6i3w6mbyphbm6xn-linux-pam-x86_64-unknown-linux-gnufilc0-1.6.1-doc...
patching script interpreter paths in /nix/store/pb52h2w6prvfqfirk6i3w6mbyphbm6xn-linux-pam-x86_64-unknown-linux-gnufilc0-1.6.1-doc
shrinking RPATHs of ELF executables and libraries in /nix/store/2g53j0ynm96x2yax8krapd9hwxbc4jip-linux-pam-x86_64-unknown-linux-gnufilc0-1.6.1-man
checking for references to /build/ in /nix/store/2g53j0ynm96x2yax8krapd9hwxbc4jip-linux-pam-x86_64-unknown-linux-gnufilc0-1.6.1-man...
gzipping man pages under /nix/store/2g53j0ynm96x2yax8krapd9hwxbc4jip-linux-pam-x86_64-unknown-linux-gnufilc0-1.6.1-man/share/man/
patching script interpreter paths in /nix/store/2g53j0ynm96x2yax8krapd9hwxbc4jip-linux-pam-x86_64-unknown-linux-gnufilc0-1.6.1-man
```

```
Running phase: unpackPhase
Running phase: patchPhase
Running phase: updateAutotoolsGnuConfigScriptsPhase
Running phase: updateAutotoolsGnuConfigScriptsPhase
Running phase: configurePhase
no configure script, doing nothing
Running phase: installPhase
buildFlags: 
WARNING:  You build with buildroot.
  Build root: /
  Bin dir: /nix/store/g33gqryldigavhjckj711knryg3b4b98-ruby3.3-rpam2-4.0.2-x86_64-unknown-linux-gnufilc0/lib/ruby/gems/3.3.0/bin
  Gem home: /nix/store/g33gqryldigavhjckj711knryg3b4b98-ruby3.3-rpam2-4.0.2-x86_64-unknown-linux-gnufilc0/lib/ruby/gems/3.3.0
  Plugins dir: /nix/store/g33gqryldigavhjckj711knryg3b4b98-ruby3.3-rpam2-4.0.2-x86_64-unknown-linux-gnufilc0/lib/ruby/gems/3.3.0/plugins
Building native extensions. This could take a while...
Successfully installed rpam2-4.0.2
1 gem installed
/nix/store/g33gqryldigavhjckj711knryg3b4b98-ruby3.3-rpam2-4.0.2-x86_64-unknown-linux-gnufilc0/lib/ruby/gems/3.3.0 /build
gems/rpam2-4.0.2/ext/rpam2/Makefile
extensions/x86_64-linux/3.3.0/rpam2-4.0.2/mkmf.log
extensions/x86_64-linux/3.3.0/rpam2-4.0.2/gem_make.out
removed 'cache/rpam2-4.0.2.gem'
removed directory 'cache'
/build
Running phase: fixupPhase
shrinking RPATHs of ELF executables and libraries in /nix/store/g33gqryldigavhjckj711knryg3b4b98-ruby3.3-rpam2-4.0.2-x86_64-unknown-linux-gnufilc0
shrinking /nix/store/g33gqryldigavhjckj711knryg3b4b98-ruby3.3-rpam2-4.0.2-x86_64-unknown-linux-gnufilc0/lib/ruby/gems/3.3.0/extensions/x86_64-linux/3.3.0/rpam2-4.0.2/rpam2/rpam2.so
shrinking /nix/store/g33gqryldigavhjckj711knryg3b4b98-ruby3.3-rpam2-4.0.2-x86_64-unknown-linux-gnufilc0/lib/ruby/gems/3.3.0/gems/rpam2-4.0.2/lib/rpam2/rpam2.so
checking for references to /build/ in /nix/store/g33gqryldigavhjckj711knryg3b4b98-ruby3.3-rpam2-4.0.2-x86_64-unknown-linux-gnufilc0...
patching script interpreter paths in /nix/store/g33gqryldigavhjckj711knryg3b4b98-ruby3.3-rpam2-4.0.2-x86_64-unknown-linux-gnufilc0
stripping (with command strip and flags -S -p) in  /nix/store/g33gqryldigavhjckj711knryg3b4b98-ruby3.3-rpam2-4.0.2-x86_64-unknown-linux-gnufilc0/lib /nix/store/g33gqryldigavhjckj711knryg3b4b98-ruby3.3-rpam2-4.0.2-x86_64-unknown-linux-gnufilc0/bin
rewriting symlink /nix/store/g33gqryldigavhjckj711knryg3b4b98-ruby3.3-rpam2-4.0.2-x86_64-unknown-linux-gnufilc0/nix-support/gem-meta/spec to be relative to /nix/store/g33gqryldigavhjckj711knryg3b4b98-ruby3.3-rpam2-4.0.2-x86_64-unknown-linux-gnufilc0
```

```
created 1 symlinks in user environment
```

```
Running phase: patchPhase
Running phase: updateAutotoolsGnuConfigScriptsPhase
Running phase: updateAutotoolsGnuConfigScriptsPhase
Running phase: configurePhase
no configure script, doing nothing
Running phase: buildPhase
no Makefile or custom buildPhase, doing nothing
Running phase: installPhase
Running phase: fixupPhase
shrinking RPATHs of ELF executables and libraries in /nix/store/fnqbkxb0mnv133rdvbbc0gncf46xb5kq-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0
shrinking /nix/store/fnqbkxb0mnv133rdvbbc0gncf46xb5kq-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0/bin/bundle
shrinking /nix/store/fnqbkxb0mnv133rdvbbc0gncf46xb5kq-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0/bin/bundler
shrinking /nix/store/fnqbkxb0mnv133rdvbbc0gncf46xb5kq-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0/bin/erb
shrinking /nix/store/fnqbkxb0mnv133rdvbbc0gncf46xb5kq-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0/bin/gem
shrinking /nix/store/fnqbkxb0mnv133rdvbbc0gncf46xb5kq-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0/bin/irb
shrinking /nix/store/fnqbkxb0mnv133rdvbbc0gncf46xb5kq-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0/bin/racc
shrinking /nix/store/fnqbkxb0mnv133rdvbbc0gncf46xb5kq-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0/bin/rake
shrinking /nix/store/fnqbkxb0mnv133rdvbbc0gncf46xb5kq-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0/bin/rbs
shrinking /nix/store/fnqbkxb0mnv133rdvbbc0gncf46xb5kq-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0/bin/rdbg
shrinking /nix/store/fnqbkxb0mnv133rdvbbc0gncf46xb5kq-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0/bin/rdoc
shrinking /nix/store/fnqbkxb0mnv133rdvbbc0gncf46xb5kq-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0/bin/ri
shrinking /nix/store/fnqbkxb0mnv133rdvbbc0gncf46xb5kq-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0/bin/ruby
shrinking /nix/store/fnqbkxb0mnv133rdvbbc0gncf46xb5kq-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0/bin/syntax_suggest
shrinking /nix/store/fnqbkxb0mnv133rdvbbc0gncf46xb5kq-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0/bin/typeprof
checking for references to /build/ in /nix/store/fnqbkxb0mnv133rdvbbc0gncf46xb5kq-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0...
patching script interpreter paths in /nix/store/fnqbkxb0mnv133rdvbbc0gncf46xb5kq-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0
stripping (with command strip and flags -S -p) in  /nix/store/fnqbkxb0mnv133rdvbbc0gncf46xb5kq-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0/bin
```

</details>

<details>
<summary>❌ <strong>rszr</strong>: build failed</summary>

</details>

<details>
<summary>❌ <strong>ruby-libvirt</strong>: build failed</summary>

</details>

<details>
<summary>❌ <strong>ruby-lxc</strong>: build failed</summary>

</details>

<details>
<summary>✅ <strong>ruby-terminfo</strong>: build failed</summary>

```
Running phase: unpackPhase
Unpacked gem: '/build/container/ncrwpv8ip9ijc5i74r4awc8308qghzz0-ruby-terminfo-0.1.1'
Running phase: patchPhase
substituteStream() in derivation ruby3.3-ruby-terminfo-0.1.1-x86_64-unknown-linux-gnufilc0: WARNING: '--replace' is deprecated, use --replace-{fail,warn,quiet}. (file 'extconf.rb')
Running phase: updateAutotoolsGnuConfigScriptsPhase
Running phase: updateAutotoolsGnuConfigScriptsPhase
Running phase: configurePhase
no configure script, doing nothing
Running phase: buildPhase
WARNING:  expected RubyGems version 3.6.6, was 1.3.5
WARNING:  licenses is empty, but is recommended. Use an license identifier from
https://spdx.org/licenses or 'Nonstandard' for a nonstandard license,
or set it to nil if you don't want to specify a license.
WARNING:  description and summary are identical
WARNING:  make sure you specify the oldest ruby version constraint (like ">= 3.0") that you want your gem to support by setting the `required_ruby_version` gemspec attribute
WARNING:  See https://guides.rubygems.org/specification-reference/ for help
  Successfully built RubyGem
  Name: ruby-terminfo
  Version: 0.1.1
  File: ruby-terminfo-0.1.1.gem
gem package built: ruby-terminfo-0.1.1.gem
Running phase: installPhase
buildFlags: --with-cflags=-I/nix/store/gsqm8q3ibkc95dh282hxq6vflry2x0jv-ncurses-x86_64-unknown-linux-gnufilc0-6.5-dev/include --with-ldflags=-L/nix/store/6gbniiz3fkg0z8fj5bdbpx9gkncdn0iv-ncurses-x86_64-unknown-linux-gnufilc0-6.5/lib
WARNING:  You build with buildroot.
  Build root: /
  Bin dir: /nix/store/x1b44c2a3sflxv26q0375z6r6wpzl1sf-ruby3.3-ruby-terminfo-0.1.1-x86_64-unknown-linux-gnufilc0/lib/ruby/gems/3.3.0/bin
  Gem home: /nix/store/x1b44c2a3sflxv26q0375z6r6wpzl1sf-ruby3.3-ruby-terminfo-0.1.1-x86_64-unknown-linux-gnufilc0/lib/ruby/gems/3.3.0
  Plugins dir: /nix/store/x1b44c2a3sflxv26q0375z6r6wpzl1sf-ruby3.3-ruby-terminfo-0.1.1-x86_64-unknown-linux-gnufilc0/lib/ruby/gems/3.3.0/plugins
Building native extensions with: '--with-cflags=-I/nix/store/gsqm8q3ibkc95dh282hxq6vflry2x0jv-ncurses-x86_64-unknown-linux-gnufilc0-6.5-dev/include --with-ldflags=-L/nix/store/6gbniiz3fkg0z8fj5bdbpx9gkncdn0iv-ncurses-x86_64-unknown-linux-gnufilc0-6.5/lib'
This could take a while...
Successfully installed ruby-terminfo-0.1.1
1 gem installed
/nix/store/x1b44c2a3sflxv26q0375z6r6wpzl1sf-ruby3.3-ruby-terminfo-0.1.1-x86_64-unknown-linux-gnufilc0/lib/ruby/gems/3.3.0 /build/source
extensions/x86_64-linux/3.3.0/ruby-terminfo-0.1.1/mkmf.log
extensions/x86_64-linux/3.3.0/ruby-terminfo-0.1.1/gem_make.out
removed 'cache/ruby-terminfo-0.1.1.gem'
removed directory 'cache'
/build/source
Running phase: fixupPhase
shrinking RPATHs of ELF executables and libraries in /nix/store/x1b44c2a3sflxv26q0375z6r6wpzl1sf-ruby3.3-ruby-terminfo-0.1.1-x86_64-unknown-linux-gnufilc0
shrinking /nix/store/x1b44c2a3sflxv26q0375z6r6wpzl1sf-ruby3.3-ruby-terminfo-0.1.1-x86_64-unknown-linux-gnufilc0/lib/ruby/gems/3.3.0/extensions/x86_64-linux/3.3.0/ruby-terminfo-0.1.1/terminfo.so
shrinking /nix/store/x1b44c2a3sflxv26q0375z6r6wpzl1sf-ruby3.3-ruby-terminfo-0.1.1-x86_64-unknown-linux-gnufilc0/lib/ruby/gems/3.3.0/gems/ruby-terminfo-0.1.1/lib/terminfo.so
checking for references to /build/ in /nix/store/x1b44c2a3sflxv26q0375z6r6wpzl1sf-ruby3.3-ruby-terminfo-0.1.1-x86_64-unknown-linux-gnufilc0...
patching script interpreter paths in /nix/store/x1b44c2a3sflxv26q0375z6r6wpzl1sf-ruby3.3-ruby-terminfo-0.1.1-x86_64-unknown-linux-gnufilc0
stripping (with command strip and flags -S -p) in  /nix/store/x1b44c2a3sflxv26q0375z6r6wpzl1sf-ruby3.3-ruby-terminfo-0.1.1-x86_64-unknown-linux-gnufilc0/lib /nix/store/x1b44c2a3sflxv26q0375z6r6wpzl1sf-ruby3.3-ruby-terminfo-0.1.1-x86_64-unknown-linux-gnufilc0/bin
rewriting symlink /nix/store/x1b44c2a3sflxv26q0375z6r6wpzl1sf-ruby3.3-ruby-terminfo-0.1.1-x86_64-unknown-linux-gnufilc0/nix-support/gem-meta/spec to be relative to /nix/store/x1b44c2a3sflxv26q0375z6r6wpzl1sf-ruby3.3-ruby-terminfo-0.1.1-x86_64-unknown-linux-gnufilc0
```

```
created 1 symlinks in user environment
```

```
Running phase: patchPhase
Running phase: updateAutotoolsGnuConfigScriptsPhase
Running phase: updateAutotoolsGnuConfigScriptsPhase
Running phase: configurePhase
no configure script, doing nothing
Running phase: buildPhase
no Makefile or custom buildPhase, doing nothing
Running phase: installPhase
Running phase: fixupPhase
shrinking RPATHs of ELF executables and libraries in /nix/store/4gsfilvwsqkwnsr0a4bfbxkbzpwhfg2b-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0
shrinking /nix/store/4gsfilvwsqkwnsr0a4bfbxkbzpwhfg2b-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0/bin/bundle
shrinking /nix/store/4gsfilvwsqkwnsr0a4bfbxkbzpwhfg2b-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0/bin/bundler
shrinking /nix/store/4gsfilvwsqkwnsr0a4bfbxkbzpwhfg2b-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0/bin/erb
shrinking /nix/store/4gsfilvwsqkwnsr0a4bfbxkbzpwhfg2b-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0/bin/gem
shrinking /nix/store/4gsfilvwsqkwnsr0a4bfbxkbzpwhfg2b-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0/bin/irb
shrinking /nix/store/4gsfilvwsqkwnsr0a4bfbxkbzpwhfg2b-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0/bin/racc
shrinking /nix/store/4gsfilvwsqkwnsr0a4bfbxkbzpwhfg2b-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0/bin/rake
shrinking /nix/store/4gsfilvwsqkwnsr0a4bfbxkbzpwhfg2b-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0/bin/rbs
shrinking /nix/store/4gsfilvwsqkwnsr0a4bfbxkbzpwhfg2b-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0/bin/rdbg
shrinking /nix/store/4gsfilvwsqkwnsr0a4bfbxkbzpwhfg2b-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0/bin/rdoc
shrinking /nix/store/4gsfilvwsqkwnsr0a4bfbxkbzpwhfg2b-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0/bin/ri
shrinking /nix/store/4gsfilvwsqkwnsr0a4bfbxkbzpwhfg2b-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0/bin/ruby
shrinking /nix/store/4gsfilvwsqkwnsr0a4bfbxkbzpwhfg2b-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0/bin/syntax_suggest
shrinking /nix/store/4gsfilvwsqkwnsr0a4bfbxkbzpwhfg2b-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0/bin/typeprof
checking for references to /build/ in /nix/store/4gsfilvwsqkwnsr0a4bfbxkbzpwhfg2b-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0...
patching script interpreter paths in /nix/store/4gsfilvwsqkwnsr0a4bfbxkbzpwhfg2b-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0
stripping (with command strip and flags -S -p) in  /nix/store/4gsfilvwsqkwnsr0a4bfbxkbzpwhfg2b-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0/bin
```

</details>

<details>
<summary>❌ <strong>ruby-vips</strong>: build failed</summary>

</details>

<details>
<summary>❌ <strong>rugged</strong>: build failed</summary>

```
libtool: install: (cd /nix/store/y6clsqwaz6gk1glzd8a85dakk1fplzm7-libssh2-x86_64-unknown-linux-gnufilc0-1.11.1/lib && { ln -s -f libssh2.so.1.0.1 libssh2.so || { rm -f libssh2.so && ln -s libssh2.so.1.0.1 libssh2.so; }; })
libtool: install: /nix/store/rry6qingvsrqmc7ll7jgaqpybcbdgf5v-coreutils-9.7/bin/install -c .libs/libssh2.lai /nix/store/y6clsqwaz6gk1glzd8a85dakk1fplzm7-libssh2-x86_64-unknown-linux-gnufilc0-1.11.1/lib/libssh2.la
libtool: finish: PATH="/nix/store/smxj57lphrh2fcpfkacw7idqj3n6yn67-nm/bin:/nix/store/g7i75czfbw9sy5f8v7rjbama6lr3ya3s-patchelf-0.15.0/bin:/nix/store/a0nc03czg70yaj0p9qphx5b3ppnb939i-filc-cc-wrapper-/bin:/nix/store/gy2di95906x5rgl25ck3d3xhsp7srz8b-filc-cc/bin:/nix/store/6ql65jl6flp8qbikcpjn15hycghvqg29-filc-sysroot-with-metadata/bin:/nix/store/rry6qingvsrqmc7ll7jgaqpybcbdgf5v-coreutils-9.7/bin:/nix/store/bjmp5s6kl068x3vmjg2cbycfwx21hcd2-binutils-wrapper-2.43.1/bin:/nix/store/fmj1ilm5jk1hba6s3cv6gkpgsjvkxaqv-binutils-2.43.1/bin:/nix/store/rry6qingvsrqmc7ll7jgaqpybcbdgf5v-coreutils-9.7/bin:/nix/store/392hs9nhm6wfw4imjllbvb1wil1n39qx-findutils-4.10.0/bin:/nix/store/xw0mf3shymq3k7zlncf09rm8917sdi4h-diffutils-3.12/bin:/nix/store/4rpiqv9yr2pw5094v4wc33ijkqjpm9sa-gnused-4.9/bin:/nix/store/l2wvwyg680h0v2la18hz3yiznxy2naqw-gnugrep-3.11/bin:/nix/store/c1z5j28ndxljf1ihqzag57bwpfpzms0g-gawk-5.3.2/bin:/nix/store/w60s4xh1pjg6dwbw7j0b4xzlpp88q5qg-gnutar-1.35/bin:/nix/store/xd9m9jkvrs8pbxvmkzkwviql33rd090j-gzip-1.14/bin:/nix/store/w1pxx760yidi7n9vbi5bhpii9xxl5vdj-bzip2-1.0.8-bin/bin:/nix/store/xk0d14zpm0njxzdm182dd722aqhav2cc-gnumake-4.4.1/bin:/nix/store/cfqbabpc7xwg8akbcchqbq3cai6qq2vs-bash-5.2p37/bin:/nix/store/gj54zvf7vxll1mzzmqhqi1p4jiws3mfb-patch-2.7.6/bin:/nix/store/22rpb6790f346c55iqi6s9drr5qgmyjf-xz-5.8.1-bin/bin:/nix/store/xlmpcglsq8l09qh03rf0virz0331pjdc-file-5.45/bin:/sbin" ldconfig -n /nix/store/y6clsqwaz6gk1glzd8a85dakk1fplzm7-libssh2-x86_64-unknown-linux-gnufilc0-1.11.1/lib
/build/libssh2-1.11.1/libtool: line 1903: ldconfig: command not found
----------------------------------------------------------------------
Libraries have been installed in:
   /nix/store/y6clsqwaz6gk1glzd8a85dakk1fplzm7-libssh2-x86_64-unknown-linux-gnufilc0-1.11.1/lib

If you ever happen to want to link against installed libraries
in a given directory, LIBDIR, you must either use libtool, and
specify the full pathname of the library, or use the '-LLIBDIR'
flag during linking and do at least one of the following:
   - add LIBDIR to the 'LD_LIBRARY_PATH' environment variable
     during execution
   - add LIBDIR to the 'LD_RUN_PATH' environment variable
     during linking
   - use the '-Wl,-rpath -Wl,LIBDIR' linker flag
   - have your system administrator run these commands:


See any operating system documentation about shared libraries for
more information, such as the ld(1) and ld.so(8) manual pages.
----------------------------------------------------------------------
make[2]: Nothing to be done for 'install-data-am'.
make[2]: Leaving directory '/build/libssh2-1.11.1/src'
make[1]: Leaving directory '/build/libssh2-1.11.1/src'
Making install in docs
make[1]: Entering directory '/build/libssh2-1.11.1/docs'
make[2]: Entering directory '/build/libssh2-1.11.1/docs'
make[2]: Nothing to be done for 'install-exec-am'.
 /nix/store/rry6qingvsrqmc7ll7jgaqpybcbdgf5v-coreutils-9.7/bin/mkdir -p '/nix/store/y6clsqwaz6gk1glzd8a85dakk1fplzm7-libssh2-x86_64-unknown-linux-gnufilc0-1.11.1/share/man/man3'
 /nix/store/rry6qingvsrqmc7ll7jgaqpybcbdgf5v-coreutils-9.7/bin/install -c -m 644 libssh2_agent_connect.3 libssh2_agent_disconnect.3 libssh2_agent_free.3 libssh2_agent_get_identity.3 libssh2_agent_get_identity_path.3 libssh2_agent_init.3 libssh2_agent_list_identities.3 libssh2_agent_set_identity_path.3 libssh2_agent_sign.3 libssh2_agent_userauth.3 libssh2_banner_set.3 libssh2_base64_decode.3 libssh2_channel_close.3 libssh2_channel_direct_streamlocal_ex.3 libssh2_channel_direct_tcpip.3 libssh2_channel_direct_tcpip_ex.3 libssh2_channel_eof.3 libssh2_channel_exec.3 libssh2_channel_flush.3 libssh2_channel_flush_ex.3 libssh2_channel_flush_stderr.3 libssh2_channel_forward_accept.3 libssh2_channel_forward_cancel.3 libssh2_channel_forward_listen.3 libssh2_channel_forward_listen_ex.3 libssh2_channel_free.3 libssh2_channel_get_exit_signal.3 libssh2_channel_get_exit_status.3 libssh2_channel_handle_extended_data.3 libssh2_channel_handle_extended_data2.3 libssh2_channel_ignore_extended_data.3 libssh2_channel_open_ex.3 libssh2_channel_open_session.3 libssh2_channel_process_startup.3 libssh2_channel_read.3 libssh2_channel_read_ex.3 libssh2_channel_read_stderr.3 libssh2_channel_receive_window_adjust.3 libssh2_channel_receive_window_adjust2.3 libssh2_channel_request_auth_agent.3 '/nix/store/y6clsqwaz6gk1glzd8a85dakk1fplzm7-libssh2-x86_64-unknown-linux-gnufilc0-1.11.1/share/man/man3'
 /nix/store/rry6qingvsrqmc7ll7jgaqpybcbdgf5v-coreutils-9.7/bin/install -c -m 644 libssh2_channel_request_pty.3 libssh2_channel_request_pty_ex.3 libssh2_channel_request_pty_size.3 libssh2_channel_request_pty_size_ex.3 libssh2_channel_send_eof.3 libssh2_channel_set_blocking.3 libssh2_channel_setenv.3 libssh2_channel_setenv_ex.3 libssh2_channel_shell.3 libssh2_channel_signal_ex.3 libssh2_channel_subsystem.3 libssh2_channel_wait_closed.3 libssh2_channel_wait_eof.3 libssh2_channel_window_read.3 libssh2_channel_window_read_ex.3 libssh2_channel_window_write.3 libssh2_channel_window_write_ex.3 libssh2_channel_write.3 libssh2_channel_write_ex.3 libssh2_channel_write_stderr.3 libssh2_channel_x11_req.3 libssh2_channel_x11_req_ex.3 libssh2_crypto_engine.3 libssh2_exit.3 libssh2_free.3 libssh2_hostkey_hash.3 libssh2_init.3 libssh2_keepalive_config.3 libssh2_keepalive_send.3 libssh2_knownhost_add.3 libssh2_knownhost_addc.3 libssh2_knownhost_check.3 libssh2_knownhost_checkp.3 libssh2_knownhost_del.3 libssh2_knownhost_free.3 libssh2_knownhost_get.3 libssh2_knownhost_init.3 libssh2_knownhost_readfile.3 libssh2_knownhost_readline.3 libssh2_knownhost_writefile.3 '/nix/store/y6clsqwaz6gk1glzd8a85dakk1fplzm7-libssh2-x86_64-unknown-linux-gnufilc0-1.11.1/share/man/man3'
 /nix/store/rry6qingvsrqmc7ll7jgaqpybcbdgf5v-coreutils-9.7/bin/install -c -m 644 libssh2_knownhost_writeline.3 libssh2_poll.3 libssh2_poll_channel_read.3 libssh2_publickey_add.3 libssh2_publickey_add_ex.3 libssh2_publickey_init.3 libssh2_publickey_list_fetch.3 libssh2_publickey_list_free.3 libssh2_publickey_remove.3 libssh2_publickey_remove_ex.3 libssh2_publickey_shutdown.3 libssh2_scp_recv.3 libssh2_scp_recv2.3 libssh2_scp_send.3 libssh2_scp_send64.3 libssh2_scp_send_ex.3 libssh2_session_abstract.3 libssh2_session_banner_get.3 libssh2_session_banner_set.3 libssh2_session_block_directions.3 libssh2_session_callback_set.3 libssh2_session_callback_set2.3 libssh2_session_disconnect.3 libssh2_session_disconnect_ex.3 libssh2_session_flag.3 libssh2_session_free.3 libssh2_session_get_blocking.3 libssh2_session_get_read_timeout.3 libssh2_session_get_timeout.3 libssh2_session_handshake.3 libssh2_session_hostkey.3 libssh2_session_init.3 libssh2_session_init_ex.3 libssh2_session_last_errno.3 libssh2_session_last_error.3 libssh2_session_method_pref.3 libssh2_session_methods.3 libssh2_session_set_blocking.3 libssh2_session_set_last_error.3 libssh2_session_set_read_timeout.3 '/nix/store/y6clsqwaz6gk1glzd8a85dakk1fplzm7-libssh2-x86_64-unknown-linux-gnufilc0-1.11.1/share/man/man3'
 /nix/store/rry6qingvsrqmc7ll7jgaqpybcbdgf5v-coreutils-9.7/bin/install -c -m 644 libssh2_session_set_timeout.3 libssh2_session_startup.3 libssh2_session_supported_algs.3 libssh2_sftp_close.3 libssh2_sftp_close_handle.3 libssh2_sftp_closedir.3 libssh2_sftp_fsetstat.3 libssh2_sftp_fstat.3 libssh2_sftp_fstat_ex.3 libssh2_sftp_fstatvfs.3 libssh2_sftp_fsync.3 libssh2_sftp_get_channel.3 libssh2_sftp_init.3 libssh2_sftp_last_error.3 libssh2_sftp_lstat.3 libssh2_sftp_mkdir.3 libssh2_sftp_mkdir_ex.3 libssh2_sftp_open.3 libssh2_sftp_open_ex.3 libssh2_sftp_open_ex_r.3 libssh2_sftp_open_r.3 libssh2_sftp_opendir.3 libssh2_sftp_posix_rename.3 libssh2_sftp_posix_rename_ex.3 libssh2_sftp_read.3 libssh2_sftp_readdir.3 libssh2_sftp_readdir_ex.3 libssh2_sftp_readlink.3 libssh2_sftp_realpath.3 libssh2_sftp_rename.3 libssh2_sftp_rename_ex.3 libssh2_sftp_rewind.3 libssh2_sftp_rmdir.3 libssh2_sftp_rmdir_ex.3 libssh2_sftp_seek.3 libssh2_sftp_seek64.3 libssh2_sftp_setstat.3 libssh2_sftp_shutdown.3 libssh2_sftp_stat.3 libssh2_sftp_stat_ex.3 '/nix/store/y6clsqwaz6gk1glzd8a85dakk1fplzm7-libssh2-x86_64-unknown-linux-gnufilc0-1.11.1/share/man/man3'
 /nix/store/rry6qingvsrqmc7ll7jgaqpybcbdgf5v-coreutils-9.7/bin/install -c -m 644 libssh2_sftp_statvfs.3 libssh2_sftp_symlink.3 libssh2_sftp_symlink_ex.3 libssh2_sftp_tell.3 libssh2_sftp_tell64.3 libssh2_sftp_unlink.3 libssh2_sftp_unlink_ex.3 libssh2_sftp_write.3 libssh2_sign_sk.3 libssh2_trace.3 libssh2_trace_sethandler.3 libssh2_userauth_authenticated.3 libssh2_userauth_banner.3 libssh2_userauth_hostbased_fromfile.3 libssh2_userauth_hostbased_fromfile_ex.3 libssh2_userauth_keyboard_interactive.3 libssh2_userauth_keyboard_interactive_ex.3 libssh2_userauth_list.3 libssh2_userauth_password.3 libssh2_userauth_password_ex.3 libssh2_userauth_publickey.3 libssh2_userauth_publickey_fromfile.3 libssh2_userauth_publickey_fromfile_ex.3 libssh2_userauth_publickey_frommemory.3 libssh2_userauth_publickey_sk.3 libssh2_version.3 '/nix/store/y6clsqwaz6gk1glzd8a85dakk1fplzm7-libssh2-x86_64-unknown-linux-gnufilc0-1.11.1/share/man/man3'
make[2]: Leaving directory '/build/libssh2-1.11.1/docs'
make[1]: Leaving directory '/build/libssh2-1.11.1/docs'
Making install in tests
make[1]: Entering directory '/build/libssh2-1.11.1/tests'
Making install in ossfuzz
make[2]: Entering directory '/build/libssh2-1.11.1/tests/ossfuzz'
make[3]: Entering directory '/build/libssh2-1.11.1/tests/ossfuzz'
make[3]: Nothing to be done for 'install-exec-am'.
make[3]: Nothing to be done for 'install-data-am'.
make[3]: Leaving directory '/build/libssh2-1.11.1/tests/ossfuzz'
make[2]: Leaving directory '/build/libssh2-1.11.1/tests/ossfuzz'
make[2]: Entering directory '/build/libssh2-1.11.1/tests'
make[3]: Entering directory '/build/libssh2-1.11.1/tests'
make[3]: Nothing to be done for 'install-exec-am'.
make[3]: Nothing to be done for 'install-data-am'.
make[3]: Leaving directory '/build/libssh2-1.11.1/tests'
make[2]: Leaving directory '/build/libssh2-1.11.1/tests'
make[1]: Leaving directory '/build/libssh2-1.11.1/tests'
make[1]: Entering directory '/build/libssh2-1.11.1'
make[2]: Entering directory '/build/libssh2-1.11.1'
make[2]: Nothing to be done for 'install-exec-am'.
 /nix/store/rry6qingvsrqmc7ll7jgaqpybcbdgf5v-coreutils-9.7/bin/mkdir -p '/nix/store/fkfdgch44hhz8viy1qqngv4sfpcs5nsx-libssh2-x86_64-unknown-linux-gnufilc0-1.11.1-dev/include'
 /nix/store/rry6qingvsrqmc7ll7jgaqpybcbdgf5v-coreutils-9.7/bin/install -c -m 644 include/libssh2.h include/libssh2_publickey.h include/libssh2_sftp.h '/nix/store/fkfdgch44hhz8viy1qqngv4sfpcs5nsx-libssh2-x86_64-unknown-linux-gnufilc0-1.11.1-dev/include'
 /nix/store/rry6qingvsrqmc7ll7jgaqpybcbdgf5v-coreutils-9.7/bin/mkdir -p '/nix/store/fkfdgch44hhz8viy1qqngv4sfpcs5nsx-libssh2-x86_64-unknown-linux-gnufilc0-1.11.1-dev/lib/pkgconfig'
 /nix/store/rry6qingvsrqmc7ll7jgaqpybcbdgf5v-coreutils-9.7/bin/install -c -m 644 libssh2.pc '/nix/store/fkfdgch44hhz8viy1qqngv4sfpcs5nsx-libssh2-x86_64-unknown-linux-gnufilc0-1.11.1-dev/lib/pkgconfig'
make[2]: Leaving directory '/build/libssh2-1.11.1'
make[1]: Leaving directory '/build/libssh2-1.11.1'
Running phase: fixupPhase
Moving /nix/store/y6clsqwaz6gk1glzd8a85dakk1fplzm7-libssh2-x86_64-unknown-linux-gnufilc0-1.11.1/share/man/man3 to /nix/store/cmqp43zs3wgx4h3mq9s99ygdzbdifafv-libssh2-x86_64-unknown-linux-gnufilc0-1.11.1-devdoc/share/man/man3
Removing empty /nix/store/y6clsqwaz6gk1glzd8a85dakk1fplzm7-libssh2-x86_64-unknown-linux-gnufilc0-1.11.1/share/man/ and (possibly) its parents
Patching '/nix/store/fkfdgch44hhz8viy1qqngv4sfpcs5nsx-libssh2-x86_64-unknown-linux-gnufilc0-1.11.1-dev/lib/pkgconfig/libssh2.pc' includedir to output /nix/store/fkfdgch44hhz8viy1qqngv4sfpcs5nsx-libssh2-x86_64-unknown-linux-gnufilc0-1.11.1-dev
shrinking RPATHs of ELF executables and libraries in /nix/store/y6clsqwaz6gk1glzd8a85dakk1fplzm7-libssh2-x86_64-unknown-linux-gnufilc0-1.11.1
shrinking /nix/store/y6clsqwaz6gk1glzd8a85dakk1fplzm7-libssh2-x86_64-unknown-linux-gnufilc0-1.11.1/lib/libssh2.so.1.0.1
checking for references to /build/ in /nix/store/y6clsqwaz6gk1glzd8a85dakk1fplzm7-libssh2-x86_64-unknown-linux-gnufilc0-1.11.1...
patching script interpreter paths in /nix/store/y6clsqwaz6gk1glzd8a85dakk1fplzm7-libssh2-x86_64-unknown-linux-gnufilc0-1.11.1
stripping (with command strip and flags -S -p) in  /nix/store/y6clsqwaz6gk1glzd8a85dakk1fplzm7-libssh2-x86_64-unknown-linux-gnufilc0-1.11.1/lib
shrinking RPATHs of ELF executables and libraries in /nix/store/fkfdgch44hhz8viy1qqngv4sfpcs5nsx-libssh2-x86_64-unknown-linux-gnufilc0-1.11.1-dev
checking for references to /build/ in /nix/store/fkfdgch44hhz8viy1qqngv4sfpcs5nsx-libssh2-x86_64-unknown-linux-gnufilc0-1.11.1-dev...
patching script interpreter paths in /nix/store/fkfdgch44hhz8viy1qqngv4sfpcs5nsx-libssh2-x86_64-unknown-linux-gnufilc0-1.11.1-dev
stripping (with command strip and flags -S -p) in  /nix/store/fkfdgch44hhz8viy1qqngv4sfpcs5nsx-libssh2-x86_64-unknown-linux-gnufilc0-1.11.1-dev/lib
shrinking RPATHs of ELF executables and libraries in /nix/store/cmqp43zs3wgx4h3mq9s99ygdzbdifafv-libssh2-x86_64-unknown-linux-gnufilc0-1.11.1-devdoc
checking for references to /build/ in /nix/store/cmqp43zs3wgx4h3mq9s99ygdzbdifafv-libssh2-x86_64-unknown-linux-gnufilc0-1.11.1-devdoc...
gzipping man pages under /nix/store/cmqp43zs3wgx4h3mq9s99ygdzbdifafv-libssh2-x86_64-unknown-linux-gnufilc0-1.11.1-devdoc/share/man/
patching script interpreter paths in /nix/store/cmqp43zs3wgx4h3mq9s99ygdzbdifafv-libssh2-x86_64-unknown-linux-gnufilc0-1.11.1-devdoc
```

```
Running phase: unpackPhase
Running phase: patchPhase
Running phase: updateAutotoolsGnuConfigScriptsPhase
Running phase: updateAutotoolsGnuConfigScriptsPhase
Running phase: configurePhase
no configure script, doing nothing
Running phase: installPhase
buildFlags: 
WARNING:  You build with buildroot.
  Build root: /
  Bin dir: /nix/store/iizys7x8a3k8bd5s1w6kv0b66jsacphp-ruby3.3-rugged-1.9.0-x86_64-unknown-linux-gnufilc0/lib/ruby/gems/3.3.0/bin
  Gem home: /nix/store/iizys7x8a3k8bd5s1w6kv0b66jsacphp-ruby3.3-rugged-1.9.0-x86_64-unknown-linux-gnufilc0/lib/ruby/gems/3.3.0
  Plugins dir: /nix/store/iizys7x8a3k8bd5s1w6kv0b66jsacphp-ruby3.3-rugged-1.9.0-x86_64-unknown-linux-gnufilc0/lib/ruby/gems/3.3.0/plugins
Building native extensions. This could take a while...
ERROR:  Error installing /nix/store/b7vv8q1gxx4jb69lg1h763jv7r142p53-rugged-1.9.0.gem:
        ERROR: Failed to build gem native extension.

    current directory: /nix/store/iizys7x8a3k8bd5s1w6kv0b66jsacphp-ruby3.3-rugged-1.9.0-x86_64-unknown-linux-gnufilc0/lib/ruby/gems/3.3.0/gems/rugged-1.9.0/ext/rugged
/nix/store/65in3amyafclxn1lg3yjb1v9a3ngk1rm-ruby-3.3.10-x86_64-unknown-linux-gnufilc0/bin/ruby extconf.rb
checking for gmake... no
checking for make... yes
checking for cmake... yes
checking for pkg-config... no
ERROR: pkg-config is required to build Rugged.
*** extconf.rb failed ***
Could not create Makefile due to some reason, probably lack of necessary
libraries and/or headers.  Check the mkmf.log file for more details.  You may
need configuration options.

Provided configuration options:
        --with-opt-dir
        --without-opt-dir
        --with-opt-include=${opt-dir}/include
        --without-opt-include
        --with-opt-lib=${opt-dir}/lib
        --without-opt-lib
        --with-make-prog
        --without-make-prog
        --srcdir=.
        --curdir
        --ruby=/nix/store/65in3amyafclxn1lg3yjb1v9a3ngk1rm-ruby-3.3.10-x86_64-unknown-linux-gnufilc0/bin/$(RUBY_BASE_NAME)
        --with-sha1dc
        --without-sha1dc
        --with-ssh
        --without-ssh
        --use-system-libraries

To see why this extension failed to compile, please check the mkmf.log which can be found here:

  /nix/store/iizys7x8a3k8bd5s1w6kv0b66jsacphp-ruby3.3-rugged-1.9.0-x86_64-unknown-linux-gnufilc0/lib/ruby/gems/3.3.0/extensions/x86_64-linux/3.3.0/rugged-1.9.0/mkmf.log

extconf failed, exit code 1

Gem files will remain installed in /nix/store/iizys7x8a3k8bd5s1w6kv0b66jsacphp-ruby3.3-rugged-1.9.0-x86_64-unknown-linux-gnufilc0/lib/ruby/gems/3.3.0/gems/rugged-1.9.0 for inspection.
Results logged to /nix/store/iizys7x8a3k8bd5s1w6kv0b66jsacphp-ruby3.3-rugged-1.9.0-x86_64-unknown-linux-gnufilc0/lib/ruby/gems/3.3.0/extensions/x86_64-linux/3.3.0/rugged-1.9.0/gem_make.out
```

</details>

<details>
<summary>✅ <strong>sassc</strong>: build failed</summary>

```
libtool: compile:  clang++ -DHAVE_CONFIG_H -I. -I../include -Wall -O2 -std=c++11 -g -O2 -c ast2c.cpp  -fPIC -DPIC -o .libs/ast2c.o
/nix/store/cfqbabpc7xwg8akbcchqbq3cai6qq2vs-bash-5.2p37/bin/bash ../libtool  --tag=CXX   --mode=compile clang++ -DHAVE_CONFIG_H -I.  -I../include  -Wall -O2 -std=c++11 -g -O2 -c -o c2ast.lo c2ast.cpp
/nix/store/cfqbabpc7xwg8akbcchqbq3cai6qq2vs-bash-5.2p37/bin/bash ../libtool  --tag=CXX   --mode=compile clang++ -DHAVE_CONFIG_H -I.  -I../include  -Wall -O2 -std=c++11 -g -O2 -c -o to_value.lo to_value.cpp
libtool: compile:  clang++ -DHAVE_CONFIG_H -I. -I../include -Wall -O2 -std=c++11 -g -O2 -c c2ast.cpp  -fPIC -DPIC -o .libs/c2ast.o
libtool: compile:  clang++ -DHAVE_CONFIG_H -I. -I../include -Wall -O2 -std=c++11 -g -O2 -c to_value.cpp  -fPIC -DPIC -o .libs/to_value.o
/nix/store/cfqbabpc7xwg8akbcchqbq3cai6qq2vs-bash-5.2p37/bin/bash ../libtool  --tag=CXX   --mode=compile clang++ -DHAVE_CONFIG_H -I.  -I../include  -Wall -O2 -std=c++11 -g -O2 -c -o source_map.lo source_map.cpp
libtool: compile:  clang++ -DHAVE_CONFIG_H -I. -I../include -Wall -O2 -std=c++11 -g -O2 -c source_map.cpp  -fPIC -DPIC -o .libs/source_map.o
/nix/store/cfqbabpc7xwg8akbcchqbq3cai6qq2vs-bash-5.2p37/bin/bash ../libtool  --tag=CXX   --mode=compile clang++ -DHAVE_CONFIG_H -I.  -I../include  -Wall -O2 -std=c++11 -g -O2 -c -o error_handling.lo error_handling.cpp
libtool: compile:  clang++ -DHAVE_CONFIG_H -I. -I../include -Wall -O2 -std=c++11 -g -O2 -c error_handling.cpp  -fPIC -DPIC -o .libs/error_handling.o
/nix/store/cfqbabpc7xwg8akbcchqbq3cai6qq2vs-bash-5.2p37/bin/bash ../libtool  --tag=CXX   --mode=compile clang++ -DHAVE_CONFIG_H -I.  -I../include  -Wall -O2 -std=c++11 -g -O2 -c -o allocator.lo `test -f 'memory/allocator.cpp' || echo './'`memory/allocator.cpp
/nix/store/cfqbabpc7xwg8akbcchqbq3cai6qq2vs-bash-5.2p37/bin/bash ../libtool  --tag=CXX   --mode=compile clang++ -DHAVE_CONFIG_H -I.  -I../include  -Wall -O2 -std=c++11 -g -O2 -c -o shared_ptr.lo `test -f 'memory/shared_ptr.cpp' || echo './'`memory/shared_ptr.cpp
libtool: compile:  clang++ -DHAVE_CONFIG_H -I. -I../include -Wall -O2 -std=c++11 -g -O2 -c memory/allocator.cpp  -fPIC -DPIC -o .libs/allocator.o
libtool: compile:  clang++ -DHAVE_CONFIG_H -I. -I../include -Wall -O2 -std=c++11 -g -O2 -c memory/shared_ptr.cpp  -fPIC -DPIC -o .libs/shared_ptr.o
/nix/store/cfqbabpc7xwg8akbcchqbq3cai6qq2vs-bash-5.2p37/bin/bash ../libtool  --tag=CXX   --mode=compile clang++ -DHAVE_CONFIG_H -I.  -I../include  -Wall -O2 -std=c++11 -g -O2 -c -o utf8_string.lo utf8_string.cpp
libtool: compile:  clang++ -DHAVE_CONFIG_H -I. -I../include -Wall -O2 -std=c++11 -g -O2 -c utf8_string.cpp  -fPIC -DPIC -o .libs/utf8_string.o
/nix/store/cfqbabpc7xwg8akbcchqbq3cai6qq2vs-bash-5.2p37/bin/bash ../libtool  --tag=CXX   --mode=compile clang++ -DHAVE_CONFIG_H -I.  -I../include  -Wall -O2 -std=c++11 -g -O2 -c -o base64vlq.lo base64vlq.cpp
libtool: compile:  clang++ -DHAVE_CONFIG_H -I. -I../include -Wall -O2 -std=c++11 -g -O2 -c base64vlq.cpp  -fPIC -DPIC -o .libs/base64vlq.o
/nix/store/cfqbabpc7xwg8akbcchqbq3cai6qq2vs-bash-5.2p37/bin/bash ../libtool  --tag=CXX   --mode=link clang++ -Wall -O2 -std=c++11 -g -O2 -Wall -O2  -no-undefined -version-info 1:0:0  -o libsass.la -rpath /nix/store/9pbyis59racn3fy7b7d8d2m6d5ip1j7m-libsass-x86_64-unknown-linux-gnufilc0-3.6.6/lib cencode.lo ast.lo ast_values.lo ast_supports.lo ast_sel_cmp.lo ast_sel_unify.lo ast_sel_super.lo ast_sel_weave.lo ast_selectors.lo context.lo constants.lo fn_utils.lo fn_miscs.lo fn_maps.lo fn_lists.lo fn_colors.lo fn_numbers.lo fn_strings.lo fn_selectors.lo color_maps.lo environment.lo ast_fwd_decl.lo bind.lo file.lo util.lo util_string.lo json.lo units.lo values.lo plugins.lo source.lo position.lo lexer.lo parser.lo parser_selectors.lo prelexer.lo eval.lo eval_selectors.lo expand.lo listize.lo cssize.lo extender.lo extension.lo stylesheet.lo output.lo inspect.lo emitter.lo check_nesting.lo remove_placeholders.lo sass.lo sass_values.lo sass_context.lo sass_functions.lo sass2scss.lo backtrace.lo operators.lo ast2c.lo c2ast.lo to_value.lo source_map.lo error_handling.lo allocator.lo shared_ptr.lo utf8_string.lo base64vlq.lo  
libtool: link: clang++  -fPIC -DPIC -shared -nostdlib /nix/store/gcgh62nhmd12bf9vzsbwa9gkpypr1jvg-filc-crt-lib/crti.o /nix/store/gcgh62nhmd12bf9vzsbwa9gkpypr1jvg-filc-crt-lib/crtbegin.o  .libs/cencode.o .libs/ast.o .libs/ast_values.o .libs/ast_supports.o .libs/ast_sel_cmp.o .libs/ast_sel_unify.o .libs/ast_sel_super.o .libs/ast_sel_weave.o .libs/ast_selectors.o .libs/context.o .libs/constants.o .libs/fn_utils.o .libs/fn_miscs.o .libs/fn_maps.o .libs/fn_lists.o .libs/fn_colors.o .libs/fn_numbers.o .libs/fn_strings.o .libs/fn_selectors.o .libs/color_maps.o .libs/environment.o .libs/ast_fwd_decl.o .libs/bind.o .libs/file.o .libs/util.o .libs/util_string.o .libs/json.o .libs/units.o .libs/values.o .libs/plugins.o .libs/source.o .libs/position.o .libs/lexer.o .libs/parser.o .libs/parser_selectors.o .libs/prelexer.o .libs/eval.o .libs/eval_selectors.o .libs/expand.o .libs/listize.o .libs/cssize.o .libs/extender.o .libs/extension.o .libs/stylesheet.o .libs/output.o .libs/inspect.o .libs/emitter.o .libs/check_nesting.o .libs/remove_placeholders.o .libs/sass.o .libs/sass_values.o .libs/sass_context.o .libs/sass_functions.o .libs/sass2scss.o .libs/backtrace.o .libs/operators.o .libs/ast2c.o .libs/c2ast.o .libs/to_value.o .libs/source_map.o .libs/error_handling.o .libs/allocator.o .libs/shared_ptr.o .libs/utf8_string.o .libs/base64vlq.o   -L/nix/store/r50h8fzrcx4h59jspwrfy08iicvp1vlg-filc-glibc-2.40/lib -L/nix/store/jxw48plk32hg0gy3b2dgji2p55jg7ss2-filc-libcxx-git/lib -L/nix/store/6ql65jl6flp8qbikcpjn15hycghvqg29-filc-sysroot-with-metadata/lib -L/nix/store/gy2di95906x5rgl25ck3d3xhsp7srz8b-filc-cc/lib -L/nix/store/gcgh62nhmd12bf9vzsbwa9gkpypr1jvg-filc-crt-lib -lc++ -lc++abi -lc -lpizlo -lyoloc -lyolom -lyolort -lyolounwind /nix/store/gcgh62nhmd12bf9vzsbwa9gkpypr1jvg-filc-crt-lib/crtend.o /nix/store/gcgh62nhmd12bf9vzsbwa9gkpypr1jvg-filc-crt-lib/crtn.o  -O2 -g -O2 -O2   -Wl,-soname -Wl,libsass.so.1 -o .libs/libsass.so.1.0.0
libtool: link: (cd ".libs" && rm -f "libsass.so.1" && ln -s "libsass.so.1.0.0" "libsass.so.1")
libtool: link: (cd ".libs" && rm -f "libsass.so" && ln -s "libsass.so.1.0.0" "libsass.so")
libtool: link: ( cd ".libs" && rm -f "libsass.la" && ln -s "../libsass.la" "libsass.la" )
make[2]: Leaving directory '/build/source/src'
make[1]: Leaving directory '/build/source/src'
make[1]: Entering directory '/build/source'
make[1]: Nothing to be done for 'all-am'.
make[1]: Leaving directory '/build/source'
buildPhase completed in 59 seconds
Running phase: installPhase
install flags: -j32 SHELL=/nix/store/cfqbabpc7xwg8akbcchqbq3cai6qq2vs-bash-5.2p37/bin/bash install
Making install in src
make[1]: Entering directory '/build/source/src'
make[2]: Entering directory '/build/source/src'
 /nix/store/rry6qingvsrqmc7ll7jgaqpybcbdgf5v-coreutils-9.7/bin/mkdir -p '/nix/store/9pbyis59racn3fy7b7d8d2m6d5ip1j7m-libsass-x86_64-unknown-linux-gnufilc0-3.6.6/lib'
 /nix/store/rry6qingvsrqmc7ll7jgaqpybcbdgf5v-coreutils-9.7/bin/mkdir -p '/nix/store/9pbyis59racn3fy7b7d8d2m6d5ip1j7m-libsass-x86_64-unknown-linux-gnufilc0-3.6.6/include'
 /nix/store/rry6qingvsrqmc7ll7jgaqpybcbdgf5v-coreutils-9.7/bin/mkdir -p '/nix/store/9pbyis59racn3fy7b7d8d2m6d5ip1j7m-libsass-x86_64-unknown-linux-gnufilc0-3.6.6/lib/pkgconfig'
 /nix/store/cfqbabpc7xwg8akbcchqbq3cai6qq2vs-bash-5.2p37/bin/bash ../libtool   --mode=install /nix/store/rry6qingvsrqmc7ll7jgaqpybcbdgf5v-coreutils-9.7/bin/install -c   libsass.la '/nix/store/9pbyis59racn3fy7b7d8d2m6d5ip1j7m-libsass-x86_64-unknown-linux-gnufilc0-3.6.6/lib'
 /nix/store/rry6qingvsrqmc7ll7jgaqpybcbdgf5v-coreutils-9.7/bin/mkdir -p '/nix/store/9pbyis59racn3fy7b7d8d2m6d5ip1j7m-libsass-x86_64-unknown-linux-gnufilc0-3.6.6/include/sass'
 /nix/store/rry6qingvsrqmc7ll7jgaqpybcbdgf5v-coreutils-9.7/bin/install -c -m 644 ../include/sass.h ../include/sass2scss.h '/nix/store/9pbyis59racn3fy7b7d8d2m6d5ip1j7m-libsass-x86_64-unknown-linux-gnufilc0-3.6.6/include'
 /nix/store/rry6qingvsrqmc7ll7jgaqpybcbdgf5v-coreutils-9.7/bin/install -c -m 644 support/libsass.pc '/nix/store/9pbyis59racn3fy7b7d8d2m6d5ip1j7m-libsass-x86_64-unknown-linux-gnufilc0-3.6.6/lib/pkgconfig'
 /nix/store/rry6qingvsrqmc7ll7jgaqpybcbdgf5v-coreutils-9.7/bin/install -c -m 644 ../include/sass/base.h ../include/sass/values.h ../include/sass/version.h ../include/sass/context.h ../include/sass/functions.h '/nix/store/9pbyis59racn3fy7b7d8d2m6d5ip1j7m-libsass-x86_64-unknown-linux-gnufilc0-3.6.6/include/sass'
libtool: install: /nix/store/rry6qingvsrqmc7ll7jgaqpybcbdgf5v-coreutils-9.7/bin/install -c .libs/libsass.so.1.0.0 /nix/store/9pbyis59racn3fy7b7d8d2m6d5ip1j7m-libsass-x86_64-unknown-linux-gnufilc0-3.6.6/lib/libsass.so.1.0.0
libtool: install: (cd /nix/store/9pbyis59racn3fy7b7d8d2m6d5ip1j7m-libsass-x86_64-unknown-linux-gnufilc0-3.6.6/lib && { ln -s -f libsass.so.1.0.0 libsass.so.1 || { rm -f libsass.so.1 && ln -s libsass.so.1.0.0 libsass.so.1; }; })
libtool: install: (cd /nix/store/9pbyis59racn3fy7b7d8d2m6d5ip1j7m-libsass-x86_64-unknown-linux-gnufilc0-3.6.6/lib && { ln -s -f libsass.so.1.0.0 libsass.so || { rm -f libsass.so && ln -s libsass.so.1.0.0 libsass.so; }; })
libtool: install: /nix/store/rry6qingvsrqmc7ll7jgaqpybcbdgf5v-coreutils-9.7/bin/install -c .libs/libsass.lai /nix/store/9pbyis59racn3fy7b7d8d2m6d5ip1j7m-libsass-x86_64-unknown-linux-gnufilc0-3.6.6/lib/libsass.la
libtool: finish: PATH="/nix/store/v3l2zqz13i63nzkd2nrqps0y2i74pr10-autoconf-2.72/bin:/nix/store/3ah4cvhhimlxvb2dqk07n1xlbb0dk81f-automake-1.16.5/bin:/nix/store/ava9h9a35fg419f4r1h3ib2hwqx6lr8k-gettext-0.22.5/bin:/nix/store/b7kv2xx2ga3w0fa4h7g0c3y64wkr3i57-libtool-2.5.4/bin:/nix/store/16yz1jny3j9irq4g8zkcx39nr77xwnvx-gnum4-1.4.19/bin:/nix/store/9rsc6g3vlfnp7lvq3pl1xpir5acd1ax0-file-5.45/bin:/nix/store/g7i75czfbw9sy5f8v7rjbama6lr3ya3s-patchelf-0.15.0/bin:/nix/store/a0nc03czg70yaj0p9qphx5b3ppnb939i-filc-cc-wrapper-/bin:/nix/store/gy2di95906x5rgl25ck3d3xhsp7srz8b-filc-cc/bin:/nix/store/6ql65jl6flp8qbikcpjn15hycghvqg29-filc-sysroot-with-metadata/bin:/nix/store/rry6qingvsrqmc7ll7jgaqpybcbdgf5v-coreutils-9.7/bin:/nix/store/bjmp5s6kl068x3vmjg2cbycfwx21hcd2-binutils-wrapper-2.43.1/bin:/nix/store/fmj1ilm5jk1hba6s3cv6gkpgsjvkxaqv-binutils-2.43.1/bin:/nix/store/rry6qingvsrqmc7ll7jgaqpybcbdgf5v-coreutils-9.7/bin:/nix/store/392hs9nhm6wfw4imjllbvb1wil1n39qx-findutils-4.10.0/bin:/nix/store/xw0mf3shymq3k7zlncf09rm8917sdi4h-diffutils-3.12/bin:/nix/store/4rpiqv9yr2pw5094v4wc33ijkqjpm9sa-gnused-4.9/bin:/nix/store/l2wvwyg680h0v2la18hz3yiznxy2naqw-gnugrep-3.11/bin:/nix/store/c1z5j28ndxljf1ihqzag57bwpfpzms0g-gawk-5.3.2/bin:/nix/store/w60s4xh1pjg6dwbw7j0b4xzlpp88q5qg-gnutar-1.35/bin:/nix/store/xd9m9jkvrs8pbxvmkzkwviql33rd090j-gzip-1.14/bin:/nix/store/w1pxx760yidi7n9vbi5bhpii9xxl5vdj-bzip2-1.0.8-bin/bin:/nix/store/xk0d14zpm0njxzdm182dd722aqhav2cc-gnumake-4.4.1/bin:/nix/store/cfqbabpc7xwg8akbcchqbq3cai6qq2vs-bash-5.2p37/bin:/nix/store/gj54zvf7vxll1mzzmqhqi1p4jiws3mfb-patch-2.7.6/bin:/nix/store/22rpb6790f346c55iqi6s9drr5qgmyjf-xz-5.8.1-bin/bin:/nix/store/xlmpcglsq8l09qh03rf0virz0331pjdc-file-5.45/bin:/sbin" ldconfig -n /nix/store/9pbyis59racn3fy7b7d8d2m6d5ip1j7m-libsass-x86_64-unknown-linux-gnufilc0-3.6.6/lib
/build/source/libtool: line 1900: ldconfig: command not found
----------------------------------------------------------------------
Libraries have been installed in:
   /nix/store/9pbyis59racn3fy7b7d8d2m6d5ip1j7m-libsass-x86_64-unknown-linux-gnufilc0-3.6.6/lib

If you ever happen to want to link against installed libraries
in a given directory, LIBDIR, you must either use libtool, and
specify the full pathname of the library, or use the '-LLIBDIR'
flag during linking and do at least one of the following:
   - add LIBDIR to the 'LD_LIBRARY_PATH' environment variable
     during execution
   - add LIBDIR to the 'LD_RUN_PATH' environment variable
     during linking
   - use the '-Wl,-rpath -Wl,LIBDIR' linker flag
   - have your system administrator run these commands:


See any operating system documentation about shared libraries for
more information, such as the ld(1) and ld.so(8) manual pages.
----------------------------------------------------------------------
make[2]: Leaving directory '/build/source/src'
make[1]: Leaving directory '/build/source/src'
make[1]: Entering directory '/build/source'
make[2]: Entering directory '/build/source'
make[2]: Nothing to be done for 'install-exec-am'.
make[2]: Nothing to be done for 'install-data-am'.
make[2]: Leaving directory '/build/source'
make[1]: Leaving directory '/build/source'
Running phase: fixupPhase
shrinking RPATHs of ELF executables and libraries in /nix/store/9pbyis59racn3fy7b7d8d2m6d5ip1j7m-libsass-x86_64-unknown-linux-gnufilc0-3.6.6
shrinking /nix/store/9pbyis59racn3fy7b7d8d2m6d5ip1j7m-libsass-x86_64-unknown-linux-gnufilc0-3.6.6/lib/libsass.so.1.0.0
checking for references to /build/ in /nix/store/9pbyis59racn3fy7b7d8d2m6d5ip1j7m-libsass-x86_64-unknown-linux-gnufilc0-3.6.6...
patching script interpreter paths in /nix/store/9pbyis59racn3fy7b7d8d2m6d5ip1j7m-libsass-x86_64-unknown-linux-gnufilc0-3.6.6
stripping (with command strip and flags -S -p) in  /nix/store/9pbyis59racn3fy7b7d8d2m6d5ip1j7m-libsass-x86_64-unknown-linux-gnufilc0-3.6.6/lib
```

```
copying path '/nix/store/adjsn8m1l8qdicmf70ch6wq4jkla6swn-gemfile-and-lockfile' from 'https://cache.nixos.org'...
copying path '/nix/store/1vv4a5lvy4wgqnlwi3ji7zw4cbbw00ig-sassc-2.4.0.gem' from 'https://cache.nixos.org'...
copying path '/nix/store/790phmghdk6q9sh6dy5c4dszvwqzbisc-bundler-2.6.6' from 'https://cache.nixos.org'...
copying path '/nix/store/fss9fchxa72vmihvp6b71m2z906rk6wh-ruby3.3-rake-13.2.1' from 'https://cache.nixos.org'...
copying path '/nix/store/blg8zdb58n2dra9jb4a9hg3bxfy3z1b3-rake-13.2.1' from 'https://cache.nixos.org'...
copying path '/nix/store/j5jdqz84rzi3p9h7dlvp2hnf23d9ymfr-rake-13.2.1' from 'https://cache.nixos.org'...
Running phase: unpackPhase
Unpacked gem: '/build/container/1vv4a5lvy4wgqnlwi3ji7zw4cbbw00ig-sassc-2.4.0'
Running phase: patchPhase
substituteStream() in derivation ruby3.3-sassc-2.4.0-x86_64-unknown-linux-gnufilc0: WARNING: '--replace' is deprecated, use --replace-{fail,warn,quiet}. (file 'lib/sassc/native.rb')
substituteStream() in derivation ruby3.3-sassc-2.4.0-x86_64-unknown-linux-gnufilc0: WARNING: pattern gem_root\ =\ spec.gem_dir doesn't match anything in file 'lib/sassc/native.rb'
Running phase: updateAutotoolsGnuConfigScriptsPhase
Running phase: updateAutotoolsGnuConfigScriptsPhase
Running phase: configurePhase
no configure script, doing nothing
Running phase: buildPhase
WARNING:  expected RubyGems version 3.6.6, was 3.1.2
WARNING:  description and summary are identical
WARNING:  open-ended dependency on minitest-around (>= 0, development) is not recommended
  use a bounded requirement, such as "~> x.y"
WARNING:  open-ended dependency on test_construct (>= 0, development) is not recommended
  use a bounded requirement, such as "~> x.y"
WARNING:  open-ended dependency on pry (>= 0, development) is not recommended
  use a bounded requirement, such as "~> x.y"
WARNING:  open-ended dependency on bundler (>= 0, development) is not recommended
  use a bounded requirement, such as "~> x.y"
WARNING:  open-ended dependency on rake (>= 0, development) is not recommended
  use a bounded requirement, such as "~> x.y"
WARNING:  open-ended dependency on rake-compiler (>= 0, development) is not recommended
  use a bounded requirement, such as "~> x.y"
WARNING:  open-ended dependency on rake-compiler-dock (>= 0, development) is not recommended
  use a bounded requirement, such as "~> x.y"
WARNING:  See https://guides.rubygems.org/specification-reference/ for help
  Successfully built RubyGem
  Name: sassc
  Version: 2.4.0
  File: sassc-2.4.0.gem
gem package built: sassc-2.4.0.gem
Running phase: installPhase
buildFlags: 
WARNING:  You build with buildroot.
  Build root: /
  Bin dir: /nix/store/d6rpgxh65461nb5fwc6lgiibmgv3lihb-ruby3.3-sassc-2.4.0-x86_64-unknown-linux-gnufilc0/lib/ruby/gems/3.3.0/bin
  Gem home: /nix/store/d6rpgxh65461nb5fwc6lgiibmgv3lihb-ruby3.3-sassc-2.4.0-x86_64-unknown-linux-gnufilc0/lib/ruby/gems/3.3.0
  Plugins dir: /nix/store/d6rpgxh65461nb5fwc6lgiibmgv3lihb-ruby3.3-sassc-2.4.0-x86_64-unknown-linux-gnufilc0/lib/ruby/gems/3.3.0/plugins
Building native extensions. This could take a while...
Successfully installed sassc-2.4.0
1 gem installed
/nix/store/d6rpgxh65461nb5fwc6lgiibmgv3lihb-ruby3.3-sassc-2.4.0-x86_64-unknown-linux-gnufilc0/lib/ruby/gems/3.3.0 /build/source
gems/sassc-2.4.0/ext/Makefile
extensions/x86_64-linux/3.3.0/sassc-2.4.0/gem_make.out
removed 'cache/sassc-2.4.0.gem'
removed directory 'cache'
/build/source
installPhase completed in 2 minutes 32 seconds
Running phase: fixupPhase
shrinking RPATHs of ELF executables and libraries in /nix/store/d6rpgxh65461nb5fwc6lgiibmgv3lihb-ruby3.3-sassc-2.4.0-x86_64-unknown-linux-gnufilc0
shrinking /nix/store/d6rpgxh65461nb5fwc6lgiibmgv3lihb-ruby3.3-sassc-2.4.0-x86_64-unknown-linux-gnufilc0/lib/ruby/gems/3.3.0/extensions/x86_64-linux/3.3.0/sassc-2.4.0/sassc/libsass.so
shrinking /nix/store/d6rpgxh65461nb5fwc6lgiibmgv3lihb-ruby3.3-sassc-2.4.0-x86_64-unknown-linux-gnufilc0/lib/ruby/gems/3.3.0/gems/sassc-2.4.0/lib/sassc/libsass.so
checking for references to /build/ in /nix/store/d6rpgxh65461nb5fwc6lgiibmgv3lihb-ruby3.3-sassc-2.4.0-x86_64-unknown-linux-gnufilc0...
patching script interpreter paths in /nix/store/d6rpgxh65461nb5fwc6lgiibmgv3lihb-ruby3.3-sassc-2.4.0-x86_64-unknown-linux-gnufilc0
stripping (with command strip and flags -S -p) in  /nix/store/d6rpgxh65461nb5fwc6lgiibmgv3lihb-ruby3.3-sassc-2.4.0-x86_64-unknown-linux-gnufilc0/lib /nix/store/d6rpgxh65461nb5fwc6lgiibmgv3lihb-ruby3.3-sassc-2.4.0-x86_64-unknown-linux-gnufilc0/bin
rewriting symlink /nix/store/d6rpgxh65461nb5fwc6lgiibmgv3lihb-ruby3.3-sassc-2.4.0-x86_64-unknown-linux-gnufilc0/nix-support/gem-meta/spec to be relative to /nix/store/d6rpgxh65461nb5fwc6lgiibmgv3lihb-ruby3.3-sassc-2.4.0-x86_64-unknown-linux-gnufilc0
```

```
created 6 symlinks in user environment
```

```
Running phase: patchPhase
Running phase: updateAutotoolsGnuConfigScriptsPhase
Running phase: updateAutotoolsGnuConfigScriptsPhase
Running phase: configurePhase
no configure script, doing nothing
Running phase: buildPhase
no Makefile or custom buildPhase, doing nothing
Running phase: installPhase
Running phase: fixupPhase
shrinking RPATHs of ELF executables and libraries in /nix/store/f4iiivm8pjhzgrbwb3y8p45xa1j575fp-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0
shrinking /nix/store/f4iiivm8pjhzgrbwb3y8p45xa1j575fp-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0/bin/bundle
shrinking /nix/store/f4iiivm8pjhzgrbwb3y8p45xa1j575fp-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0/bin/bundler
shrinking /nix/store/f4iiivm8pjhzgrbwb3y8p45xa1j575fp-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0/bin/erb
shrinking /nix/store/f4iiivm8pjhzgrbwb3y8p45xa1j575fp-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0/bin/gem
shrinking /nix/store/f4iiivm8pjhzgrbwb3y8p45xa1j575fp-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0/bin/irb
shrinking /nix/store/f4iiivm8pjhzgrbwb3y8p45xa1j575fp-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0/bin/racc
shrinking /nix/store/f4iiivm8pjhzgrbwb3y8p45xa1j575fp-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0/bin/rake
shrinking /nix/store/f4iiivm8pjhzgrbwb3y8p45xa1j575fp-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0/bin/rbs
shrinking /nix/store/f4iiivm8pjhzgrbwb3y8p45xa1j575fp-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0/bin/rdbg
shrinking /nix/store/f4iiivm8pjhzgrbwb3y8p45xa1j575fp-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0/bin/rdoc
shrinking /nix/store/f4iiivm8pjhzgrbwb3y8p45xa1j575fp-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0/bin/ri
shrinking /nix/store/f4iiivm8pjhzgrbwb3y8p45xa1j575fp-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0/bin/ruby
shrinking /nix/store/f4iiivm8pjhzgrbwb3y8p45xa1j575fp-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0/bin/syntax_suggest
shrinking /nix/store/f4iiivm8pjhzgrbwb3y8p45xa1j575fp-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0/bin/typeprof
checking for references to /build/ in /nix/store/f4iiivm8pjhzgrbwb3y8p45xa1j575fp-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0...
patching script interpreter paths in /nix/store/f4iiivm8pjhzgrbwb3y8p45xa1j575fp-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0
stripping (with command strip and flags -S -p) in  /nix/store/f4iiivm8pjhzgrbwb3y8p45xa1j575fp-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0/bin
```

</details>

<details>
<summary>✅ <strong>scrypt</strong>: build succeeded</summary>

</details>

<details>
<summary>✅ <strong>semian</strong>: build failed</summary>

```
copying path '/nix/store/z21633p8iskh7ljnfhk4497n1f5p6hr3-semian-0.22.1.gem' from 'https://cache.nixos.org'...
Running phase: unpackPhase
Running phase: patchPhase
Running phase: updateAutotoolsGnuConfigScriptsPhase
Running phase: updateAutotoolsGnuConfigScriptsPhase
Running phase: configurePhase
no configure script, doing nothing
Running phase: installPhase
buildFlags: 
WARNING:  You build with buildroot.
  Build root: /
  Bin dir: /nix/store/003q39rgp3ancrk6sm0hs73v3gg97sjs-ruby3.3-semian-0.22.1-x86_64-unknown-linux-gnufilc0/lib/ruby/gems/3.3.0/bin
  Gem home: /nix/store/003q39rgp3ancrk6sm0hs73v3gg97sjs-ruby3.3-semian-0.22.1-x86_64-unknown-linux-gnufilc0/lib/ruby/gems/3.3.0
  Plugins dir: /nix/store/003q39rgp3ancrk6sm0hs73v3gg97sjs-ruby3.3-semian-0.22.1-x86_64-unknown-linux-gnufilc0/lib/ruby/gems/3.3.0/plugins
Building native extensions. This could take a while...
Successfully installed semian-0.22.1
1 gem installed
/nix/store/003q39rgp3ancrk6sm0hs73v3gg97sjs-ruby3.3-semian-0.22.1-x86_64-unknown-linux-gnufilc0/lib/ruby/gems/3.3.0 /build
gems/semian-0.22.1/ext/semian/Makefile
extensions/x86_64-linux/3.3.0/semian-0.22.1/mkmf.log
extensions/x86_64-linux/3.3.0/semian-0.22.1/gem_make.out
removed 'cache/semian-0.22.1.gem'
removed directory 'cache'
/build
Running phase: fixupPhase
shrinking RPATHs of ELF executables and libraries in /nix/store/003q39rgp3ancrk6sm0hs73v3gg97sjs-ruby3.3-semian-0.22.1-x86_64-unknown-linux-gnufilc0
shrinking /nix/store/003q39rgp3ancrk6sm0hs73v3gg97sjs-ruby3.3-semian-0.22.1-x86_64-unknown-linux-gnufilc0/lib/ruby/gems/3.3.0/extensions/x86_64-linux/3.3.0/semian-0.22.1/semian/semian.so
shrinking /nix/store/003q39rgp3ancrk6sm0hs73v3gg97sjs-ruby3.3-semian-0.22.1-x86_64-unknown-linux-gnufilc0/lib/ruby/gems/3.3.0/gems/semian-0.22.1/lib/semian/semian.so
checking for references to /build/ in /nix/store/003q39rgp3ancrk6sm0hs73v3gg97sjs-ruby3.3-semian-0.22.1-x86_64-unknown-linux-gnufilc0...
patching script interpreter paths in /nix/store/003q39rgp3ancrk6sm0hs73v3gg97sjs-ruby3.3-semian-0.22.1-x86_64-unknown-linux-gnufilc0
stripping (with command strip and flags -S -p) in  /nix/store/003q39rgp3ancrk6sm0hs73v3gg97sjs-ruby3.3-semian-0.22.1-x86_64-unknown-linux-gnufilc0/lib /nix/store/003q39rgp3ancrk6sm0hs73v3gg97sjs-ruby3.3-semian-0.22.1-x86_64-unknown-linux-gnufilc0/bin
rewriting symlink /nix/store/003q39rgp3ancrk6sm0hs73v3gg97sjs-ruby3.3-semian-0.22.1-x86_64-unknown-linux-gnufilc0/nix-support/gem-meta/spec to be relative to /nix/store/003q39rgp3ancrk6sm0hs73v3gg97sjs-ruby3.3-semian-0.22.1-x86_64-unknown-linux-gnufilc0
```

```
created 1 symlinks in user environment
```

```
Running phase: patchPhase
Running phase: updateAutotoolsGnuConfigScriptsPhase
Running phase: updateAutotoolsGnuConfigScriptsPhase
Running phase: configurePhase
no configure script, doing nothing
Running phase: buildPhase
no Makefile or custom buildPhase, doing nothing
Running phase: installPhase
Running phase: fixupPhase
shrinking RPATHs of ELF executables and libraries in /nix/store/85akd8sqcfx76pnckx9mggwj0vsw6ajg-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0
shrinking /nix/store/85akd8sqcfx76pnckx9mggwj0vsw6ajg-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0/bin/bundle
shrinking /nix/store/85akd8sqcfx76pnckx9mggwj0vsw6ajg-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0/bin/bundler
shrinking /nix/store/85akd8sqcfx76pnckx9mggwj0vsw6ajg-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0/bin/erb
shrinking /nix/store/85akd8sqcfx76pnckx9mggwj0vsw6ajg-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0/bin/gem
shrinking /nix/store/85akd8sqcfx76pnckx9mggwj0vsw6ajg-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0/bin/irb
shrinking /nix/store/85akd8sqcfx76pnckx9mggwj0vsw6ajg-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0/bin/racc
shrinking /nix/store/85akd8sqcfx76pnckx9mggwj0vsw6ajg-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0/bin/rake
shrinking /nix/store/85akd8sqcfx76pnckx9mggwj0vsw6ajg-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0/bin/rbs
shrinking /nix/store/85akd8sqcfx76pnckx9mggwj0vsw6ajg-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0/bin/rdbg
shrinking /nix/store/85akd8sqcfx76pnckx9mggwj0vsw6ajg-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0/bin/rdoc
shrinking /nix/store/85akd8sqcfx76pnckx9mggwj0vsw6ajg-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0/bin/ri
shrinking /nix/store/85akd8sqcfx76pnckx9mggwj0vsw6ajg-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0/bin/ruby
shrinking /nix/store/85akd8sqcfx76pnckx9mggwj0vsw6ajg-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0/bin/syntax_suggest
shrinking /nix/store/85akd8sqcfx76pnckx9mggwj0vsw6ajg-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0/bin/typeprof
checking for references to /build/ in /nix/store/85akd8sqcfx76pnckx9mggwj0vsw6ajg-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0...
patching script interpreter paths in /nix/store/85akd8sqcfx76pnckx9mggwj0vsw6ajg-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0
stripping (with command strip and flags -S -p) in  /nix/store/85akd8sqcfx76pnckx9mggwj0vsw6ajg-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0/bin
```

</details>

<details>
<summary>❌ <strong>sequel_pg</strong>: build failed</summary>

```
checking sys/epoll.h presence... yes
checking for sys/epoll.h... yes
checking sys/event.h usability... no
checking sys/event.h presence... no
checking for sys/event.h... no
checking sys/personality.h usability... yes
checking sys/personality.h presence... yes
checking for sys/personality.h... yes
checking sys/prctl.h usability... yes
checking sys/prctl.h presence... yes
checking for sys/prctl.h... yes
checking sys/procctl.h usability... no
checking sys/procctl.h presence... no
checking for sys/procctl.h... no
checking sys/signalfd.h usability... yes
checking sys/signalfd.h presence... yes
checking for sys/signalfd.h... yes
checking sys/ucred.h usability... no
checking sys/ucred.h presence... no
checking for sys/ucred.h... no
checking termios.h usability... yes
checking termios.h presence... yes
checking for termios.h... yes
checking ucred.h usability... no
checking ucred.h presence... no
checking for ucred.h... no
checking zlib.h usability... yes
checking zlib.h presence... yes
checking for zlib.h... yes
checking for lz4... no
checking for zstd... no
checking gssapi/gssapi.h usability... yes
checking gssapi/gssapi.h presence... yes
checking for gssapi/gssapi.h... yes
checking gssapi/gssapi_ext.h usability... yes
checking gssapi/gssapi_ext.h presence... yes
checking for gssapi/gssapi_ext.h... yes
checking for openssl... no
configure: using openssl: openssl not found
checking openssl/ssl.h usability... yes
checking openssl/ssl.h presence... yes
checking for openssl/ssl.h... yes
checking openssl/err.h usability... yes
checking openssl/err.h presence... yes
checking for openssl/err.h... yes
checking whether byte ordering is bigendian... no
checking for inline... inline
checking for printf format archetype... printf
checking for _Static_assert... yes
checking for typeof... typeof
checking for __builtin_types_compatible_p... yes
checking for __builtin_constant_p... yes
checking for __builtin_unreachable... yes
checking for computed goto support... yes
checking for struct tm.tm_zone... yes
checking for union semun... no
checking for socklen_t... yes
checking for struct sockaddr.sa_len... no
checking for locale_t... yes
checking for C/C++ restrict keyword... __restrict
checking for struct option... yes
checking whether assembler supports x86_64 popcntq... yes
checking for special C compiler options needed for large files... no
checking for _FILE_OFFSET_BITS value needed for large files... no
checking size of off_t... 8
checking size of bool... 1
checking for int timezone... yes
checking for wcstombs_l declaration... no
checking for backtrace_symbols... yes
checking for copyfile... no
checking for copy_file_range... yes
checking for getifaddrs... yes
checking for getpeerucred... no
checking for inet_pton... yes
checking for kqueue... no
checking for mbstowcs_l... no
checking for posix_fallocate... yes
checking for ppoll... yes
checking for pthread_is_threaded_np... no
checking for setproctitle... no
```

```
      |                                       ~~~~~~~~~~~
 3092 |                  RB_OBJ_CLASSNAME(vexp));
      |                  ^~~~~~~~~~~~~~~~~~~~~~
bigdecimal.c:104:32: note: expanded from macro 'RB_OBJ_CLASSNAME'
  104 | # define RB_OBJ_CLASSNAME(obj) rb_obj_class(obj)
      |                                ^~~~~~~~~~~~~~~~~
bigdecimal.c:3465:18: warning: format specifies type 'long' but the argument has type 'VALUE' (aka 'struct rb_value_unit_struct *') [-Wformat]
 3464 |                  "can't omit precision for a %"PRIsVALUE".",
      |                                              ~~~~~~~~~~~
 3465 |                  CLASS_OF(val));
      |                  ^~~~~~~~~~~~~
/nix/store/65in3amyafclxn1lg3yjb1v9a3ngk1rm-ruby-3.3.10-x86_64-unknown-linux-gnufilc0/include/ruby-3.3.0/ruby/internal/globals.h:203:18: note: expanded from macro 'CLASS_OF'
  203 | #define CLASS_OF rb_class_of /**< @old{rb_class_of} */
      |                  ^
bigdecimal.c:3600:18: warning: format specifies type 'long' but the argument has type 'VALUE' (aka 'struct rb_value_unit_struct *') [-Wformat]
 3599 |                  "can't omit precision for a %"PRIsVALUE".",
      |                                              ~~~~~~~~~~~
 3600 |                  CLASS_OF(val));
      |                  ^~~~~~~~~~~~~
/nix/store/65in3amyafclxn1lg3yjb1v9a3ngk1rm-ruby-3.3.10-x86_64-unknown-linux-gnufilc0/include/ruby-3.3.0/ruby/internal/globals.h:203:18: note: expanded from macro 'CLASS_OF'
  203 | #define CLASS_OF rb_class_of /**< @old{rb_class_of} */
      |                  ^
bigdecimal.c:3630:5: error: statement requires expression of integer type ('VALUE' (aka 'struct rb_value_unit_struct *') invalid)
 3630 |     switch (val) {
      |     ^       ~~~
bigdecimal.c:3631:12: error: integer constant expression must have integer type, not 'VALUE' (aka 'struct rb_value_unit_struct *')
 3631 |       case Qnil:
      |            ^~~~
/nix/store/65in3amyafclxn1lg3yjb1v9a3ngk1rm-ruby-3.3.10-x86_64-unknown-linux-gnufilc0/include/ruby-3.3.0/ruby/internal/special_consts.h:60:25: note: expanded from macro 'Qnil'
   60 | #define Qnil            RUBY_Qnil              /**< @old{RUBY_Qnil} */
      |                         ^~~~~~~~~
/nix/store/65in3amyafclxn1lg3yjb1v9a3ngk1rm-ruby-3.3.10-x86_64-unknown-linux-gnufilc0/include/ruby-3.3.0/ruby/internal/special_consts.h:347:21: note: expanded from macro 'RUBY_Qnil'
  347 | #define RUBY_Qnil   RBIMPL_CAST((VALUE)RUBY_Qnil)
      |                     ^~~~~~~~~~~~~~~~~~~~~~~~~~~~~
/nix/store/65in3amyafclxn1lg3yjb1v9a3ngk1rm-ruby-3.3.10-x86_64-unknown-linux-gnufilc0/include/ruby-3.3.0/ruby/internal/cast.h:31:28: note: expanded from macro 'RBIMPL_CAST'
   31 | # define RBIMPL_CAST(expr) (expr)
      |                            ^~~~~~
bigdecimal.c:3632:12: error: integer constant expression must have integer type, not 'VALUE' (aka 'struct rb_value_unit_struct *')
 3632 |       case Qtrue:
      |            ^~~~~
/nix/store/65in3amyafclxn1lg3yjb1v9a3ngk1rm-ruby-3.3.10-x86_64-unknown-linux-gnufilc0/include/ruby-3.3.0/ruby/internal/special_consts.h:61:25: note: expanded from macro 'Qtrue'
   61 | #define Qtrue           RUBY_Qtrue             /**< @old{RUBY_Qtrue} */
      |                         ^~~~~~~~~~
/nix/store/65in3amyafclxn1lg3yjb1v9a3ngk1rm-ruby-3.3.10-x86_64-unknown-linux-gnufilc0/include/ruby-3.3.0/ruby/internal/special_consts.h:346:21: note: expanded from macro 'RUBY_Qtrue'
  346 | #define RUBY_Qtrue  RBIMPL_CAST((VALUE)RUBY_Qtrue)
      |                     ^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
/nix/store/65in3amyafclxn1lg3yjb1v9a3ngk1rm-ruby-3.3.10-x86_64-unknown-linux-gnufilc0/include/ruby-3.3.0/ruby/internal/cast.h:31:28: note: expanded from macro 'RBIMPL_CAST'
   31 | # define RBIMPL_CAST(expr) (expr)
      |                            ^~~~~~
bigdecimal.c:3633:12: error: integer constant expression must have integer type, not 'VALUE' (aka 'struct rb_value_unit_struct *')
 3633 |       case Qfalse:
      |            ^~~~~~
/nix/store/65in3amyafclxn1lg3yjb1v9a3ngk1rm-ruby-3.3.10-x86_64-unknown-linux-gnufilc0/include/ruby-3.3.0/ruby/internal/special_consts.h:59:25: note: expanded from macro 'Qfalse'
   59 | #define Qfalse          RUBY_Qfalse            /**< @old{RUBY_Qfalse} */
      |                         ^~~~~~~~~~~
/nix/store/65in3amyafclxn1lg3yjb1v9a3ngk1rm-ruby-3.3.10-x86_64-unknown-linux-gnufilc0/include/ruby-3.3.0/ruby/internal/special_consts.h:345:21: note: expanded from macro 'RUBY_Qfalse'
  345 | #define RUBY_Qfalse RBIMPL_CAST((VALUE)RUBY_Qfalse)
      |                     ^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
/nix/store/65in3amyafclxn1lg3yjb1v9a3ngk1rm-ruby-3.3.10-x86_64-unknown-linux-gnufilc0/include/ruby-3.3.0/ruby/internal/cast.h:31:28: note: expanded from macro 'RBIMPL_CAST'
   31 | # define RBIMPL_CAST(expr) (expr)
      |                            ^~~~~~
bigdecimal.c:3690:68: warning: format specifies type 'long' but the argument has type 'VALUE' (aka 'struct rb_value_unit_struct *') [-Wformat]
 3690 |                      "can't convert %"PRIsVALUE" into BigDecimal", rb_obj_class(val));
      |                                     ~~~~~~~~~~~                    ^~~~~~~~~~~~~~~~~
bigdecimal.c:5235:10: warning: cast to 'VALUE' (aka 'struct rb_value_unit_struct *') from smaller integer type 'int' [-Wint-to-pointer-cast]
 5235 |   return (VALUE)VpCtoV(x->a, x->int_chr, x->ni, x->frac, x->nf, x->exp_chr, x->ne);
      |          ^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
bigdecimal.c:5260:10: warning: cast to smaller integer type 'int' from 'VALUE' (aka 'struct rb_value_unit_struct *') [-Wpointer-to-int-cast]
 5260 |   return (int)result;
      |          ^~~~~~~~~~~
bigdecimal.c:5466:84: warning: format specifies type 'long' but the argument has type 'VALUE' (aka 'struct rb_value_unit_struct *') [-Wformat]
 5466 |         rb_raise(rb_eArgError, "invalid value for BigDecimal(): \"%"PRIsVALUE"\"", str);
      |                                                                   ~~~~~~~~~~~      ^~~
10 warnings and 6 errors generated.
make: *** [Makefile:249: bigdecimal.o] Error 1

make failed, exit code 2

Gem files will remain installed in /nix/store/2b6hc2d4axi5855crclxxb8959rrqlqq-ruby3.3-bigdecimal-3.1.9-x86_64-unknown-linux-gnufilc0/lib/ruby/gems/3.3.0/gems/bigdecimal-3.1.9 for inspection.
Results logged to /nix/store/2b6hc2d4axi5855crclxxb8959rrqlqq-ruby3.3-bigdecimal-3.1.9-x86_64-unknown-linux-gnufilc0/lib/ruby/gems/3.3.0/extensions/x86_64-linux/3.3.0/bigdecimal-3.1.9/gem_make.out
```

</details>

<details>
<summary>✅ <strong>snappy</strong>: build failed</summary>

```
-- Performing Test HAVE_CLANG_MBMI2 - Success
-- Performing Test SNAPPY_HAVE_NO_MISSING_FIELD_INITIALIZERS
-- Performing Test SNAPPY_HAVE_NO_MISSING_FIELD_INITIALIZERS - Success
-- Performing Test SNAPPY_HAVE_NO_IMPLICIT_INT_FLOAT_CONVERSION
-- Performing Test SNAPPY_HAVE_NO_IMPLICIT_INT_FLOAT_CONVERSION - Success
-- Performing Test HAVE_BUILTIN_EXPECT
-- Performing Test HAVE_BUILTIN_EXPECT - Success
-- Performing Test HAVE_BUILTIN_CTZ
-- Performing Test HAVE_BUILTIN_CTZ - Success
-- Performing Test HAVE_BUILTIN_PREFETCH
-- Performing Test HAVE_BUILTIN_PREFETCH - Success
-- Performing Test HAVE_ATTRIBUTE_ALWAYS_INLINE
-- Performing Test HAVE_ATTRIBUTE_ALWAYS_INLINE - Success
-- Performing Test SNAPPY_HAVE_SSSE3
-- Performing Test SNAPPY_HAVE_SSSE3 - Success
-- Performing Test SNAPPY_HAVE_X86_CRC32
-- Performing Test SNAPPY_HAVE_X86_CRC32 - Success
-- Performing Test SNAPPY_HAVE_NEON_CRC32
-- Performing Test SNAPPY_HAVE_NEON_CRC32 - Failed
-- Performing Test SNAPPY_HAVE_BMI2
-- Performing Test SNAPPY_HAVE_BMI2 - Failed
-- Performing Test SNAPPY_HAVE_NEON
-- Performing Test SNAPPY_HAVE_NEON - Failed
-- Looking for mmap
-- Looking for mmap - found
-- Looking for sysconf
-- Looking for sysconf - found
-- Configuring done (3.0s)
-- Generating done (0.0s)
CMake Warning:
  Manually-specified variables were not used by the project:

    BUILD_TESTING
    CMAKE_CROSSCOMPILING_EMULATOR
    CMAKE_EXPORT_NO_PACKAGE_REGISTRY
    CMAKE_FIND_USE_PACKAGE_REGISTRY
    CMAKE_FIND_USE_SYSTEM_PACKAGE_REGISTRY
    CMAKE_POLICY_DEFAULT_CMP0025


-- Build files have been written to: /build/source/build
cmake: enabled parallel building
cmake: enabled parallel installing
Running phase: buildPhase
build flags: -j32 SHELL=/nix/store/cfqbabpc7xwg8akbcchqbq3cai6qq2vs-bash-5.2p37/bin/bash
[ 20%] Building CXX object CMakeFiles/snappy.dir/snappy-c.cc.o
[ 40%] Building CXX object CMakeFiles/snappy.dir/snappy-stubs-internal.cc.o
[ 60%] Building CXX object CMakeFiles/snappy.dir/snappy-sinksource.cc.o
[ 80%] Building CXX object CMakeFiles/snappy.dir/snappy.cc.o
[100%] Linking CXX shared library libsnappy.so
[100%] Built target snappy
Running phase: installPhase
install flags: -j32 SHELL=/nix/store/cfqbabpc7xwg8akbcchqbq3cai6qq2vs-bash-5.2p37/bin/bash install
[100%] Built target snappy
Install the project...
-- Install configuration: "Release"
-- Installing: /nix/store/y1cd3xqi0n28z6g5bpg8b73n82h94krj-snappy-x86_64-unknown-linux-gnufilc0-1.2.1/lib/libsnappy.so.1.2.1
-- Installing: /nix/store/y1cd3xqi0n28z6g5bpg8b73n82h94krj-snappy-x86_64-unknown-linux-gnufilc0-1.2.1/lib/libsnappy.so.1
-- Installing: /nix/store/y1cd3xqi0n28z6g5bpg8b73n82h94krj-snappy-x86_64-unknown-linux-gnufilc0-1.2.1/lib/libsnappy.so
-- Installing: /nix/store/0m20wrby9yyjsci2gpzcnih83gbgm8j8-snappy-x86_64-unknown-linux-gnufilc0-1.2.1-dev/include/snappy-c.h
-- Installing: /nix/store/0m20wrby9yyjsci2gpzcnih83gbgm8j8-snappy-x86_64-unknown-linux-gnufilc0-1.2.1-dev/include/snappy-sinksource.h
-- Installing: /nix/store/0m20wrby9yyjsci2gpzcnih83gbgm8j8-snappy-x86_64-unknown-linux-gnufilc0-1.2.1-dev/include/snappy.h
-- Installing: /nix/store/0m20wrby9yyjsci2gpzcnih83gbgm8j8-snappy-x86_64-unknown-linux-gnufilc0-1.2.1-dev/include/snappy-stubs-public.h
-- Installing: /nix/store/y1cd3xqi0n28z6g5bpg8b73n82h94krj-snappy-x86_64-unknown-linux-gnufilc0-1.2.1/lib/cmake/Snappy/SnappyTargets.cmake
-- Installing: /nix/store/y1cd3xqi0n28z6g5bpg8b73n82h94krj-snappy-x86_64-unknown-linux-gnufilc0-1.2.1/lib/cmake/Snappy/SnappyTargets-release.cmake
-- Installing: /nix/store/y1cd3xqi0n28z6g5bpg8b73n82h94krj-snappy-x86_64-unknown-linux-gnufilc0-1.2.1/lib/cmake/Snappy/SnappyConfig.cmake
-- Installing: /nix/store/y1cd3xqi0n28z6g5bpg8b73n82h94krj-snappy-x86_64-unknown-linux-gnufilc0-1.2.1/lib/cmake/Snappy/SnappyConfigVersion.cmake
substituteStream() in derivation snappy-x86_64-unknown-linux-gnufilc0-1.2.1: WARNING: '--replace' is deprecated, use --replace-{fail,warn,quiet}. (file '/nix/store/y1cd3xqi0n28z6g5bpg8b73n82h94krj-snappy-x86_64-unknown-linux-gnufilc0-1.2.1/lib/cmake/Snappy/SnappyTargets.cmake')
Running phase: fixupPhase
Moving /nix/store/y1cd3xqi0n28z6g5bpg8b73n82h94krj-snappy-x86_64-unknown-linux-gnufilc0-1.2.1/lib/cmake to /nix/store/0m20wrby9yyjsci2gpzcnih83gbgm8j8-snappy-x86_64-unknown-linux-gnufilc0-1.2.1-dev/lib/cmake
Patching '/nix/store/0m20wrby9yyjsci2gpzcnih83gbgm8j8-snappy-x86_64-unknown-linux-gnufilc0-1.2.1-dev/lib/pkgconfig/snappy.pc' includedir to output /nix/store/0m20wrby9yyjsci2gpzcnih83gbgm8j8-snappy-x86_64-unknown-linux-gnufilc0-1.2.1-dev
shrinking RPATHs of ELF executables and libraries in /nix/store/y1cd3xqi0n28z6g5bpg8b73n82h94krj-snappy-x86_64-unknown-linux-gnufilc0-1.2.1
shrinking /nix/store/y1cd3xqi0n28z6g5bpg8b73n82h94krj-snappy-x86_64-unknown-linux-gnufilc0-1.2.1/lib/libsnappy.so.1.2.1
checking for references to /build/ in /nix/store/y1cd3xqi0n28z6g5bpg8b73n82h94krj-snappy-x86_64-unknown-linux-gnufilc0-1.2.1...
patching script interpreter paths in /nix/store/y1cd3xqi0n28z6g5bpg8b73n82h94krj-snappy-x86_64-unknown-linux-gnufilc0-1.2.1
stripping (with command strip and flags -S -p) in  /nix/store/y1cd3xqi0n28z6g5bpg8b73n82h94krj-snappy-x86_64-unknown-linux-gnufilc0-1.2.1/lib
shrinking RPATHs of ELF executables and libraries in /nix/store/0m20wrby9yyjsci2gpzcnih83gbgm8j8-snappy-x86_64-unknown-linux-gnufilc0-1.2.1-dev
checking for references to /build/ in /nix/store/0m20wrby9yyjsci2gpzcnih83gbgm8j8-snappy-x86_64-unknown-linux-gnufilc0-1.2.1-dev...
patching script interpreter paths in /nix/store/0m20wrby9yyjsci2gpzcnih83gbgm8j8-snappy-x86_64-unknown-linux-gnufilc0-1.2.1-dev
stripping (with command strip and flags -S -p) in  /nix/store/0m20wrby9yyjsci2gpzcnih83gbgm8j8-snappy-x86_64-unknown-linux-gnufilc0-1.2.1-dev/lib
```

```
copying path '/nix/store/2d7b2x12scaddbl0pa3dld7xx7angzin-snappy-0.4.0.gem' from 'https://cache.nixos.org'...
Running phase: unpackPhase
Running phase: patchPhase
Running phase: updateAutotoolsGnuConfigScriptsPhase
Running phase: updateAutotoolsGnuConfigScriptsPhase
Running phase: configurePhase
no configure script, doing nothing
Running phase: installPhase
buildFlags: 
WARNING:  You build with buildroot.
  Build root: /
  Bin dir: /nix/store/xvl4b0gnm52hjd6qc4v0svzvk4xrz54k-ruby3.3-snappy-0.4.0-x86_64-unknown-linux-gnufilc0/lib/ruby/gems/3.3.0/bin
  Gem home: /nix/store/xvl4b0gnm52hjd6qc4v0svzvk4xrz54k-ruby3.3-snappy-0.4.0-x86_64-unknown-linux-gnufilc0/lib/ruby/gems/3.3.0
  Plugins dir: /nix/store/xvl4b0gnm52hjd6qc4v0svzvk4xrz54k-ruby3.3-snappy-0.4.0-x86_64-unknown-linux-gnufilc0/lib/ruby/gems/3.3.0/plugins
Building native extensions. This could take a while...
Successfully installed snappy-0.4.0
1 gem installed
/nix/store/xvl4b0gnm52hjd6qc4v0svzvk4xrz54k-ruby3.3-snappy-0.4.0-x86_64-unknown-linux-gnufilc0/lib/ruby/gems/3.3.0 /build
gems/snappy-0.4.0/ext/Makefile
extensions/x86_64-linux/3.3.0/snappy-0.4.0/mkmf.log
extensions/x86_64-linux/3.3.0/snappy-0.4.0/gem_make.out
removed 'cache/snappy-0.4.0.gem'
removed directory 'cache'
/build
Running phase: fixupPhase
shrinking RPATHs of ELF executables and libraries in /nix/store/xvl4b0gnm52hjd6qc4v0svzvk4xrz54k-ruby3.3-snappy-0.4.0-x86_64-unknown-linux-gnufilc0
shrinking /nix/store/xvl4b0gnm52hjd6qc4v0svzvk4xrz54k-ruby3.3-snappy-0.4.0-x86_64-unknown-linux-gnufilc0/lib/ruby/gems/3.3.0/extensions/x86_64-linux/3.3.0/snappy-0.4.0/snappy_ext.so
shrinking /nix/store/xvl4b0gnm52hjd6qc4v0svzvk4xrz54k-ruby3.3-snappy-0.4.0-x86_64-unknown-linux-gnufilc0/lib/ruby/gems/3.3.0/gems/snappy-0.4.0/lib/snappy_ext.so
checking for references to /build/ in /nix/store/xvl4b0gnm52hjd6qc4v0svzvk4xrz54k-ruby3.3-snappy-0.4.0-x86_64-unknown-linux-gnufilc0...
patching script interpreter paths in /nix/store/xvl4b0gnm52hjd6qc4v0svzvk4xrz54k-ruby3.3-snappy-0.4.0-x86_64-unknown-linux-gnufilc0
stripping (with command strip and flags -S -p) in  /nix/store/xvl4b0gnm52hjd6qc4v0svzvk4xrz54k-ruby3.3-snappy-0.4.0-x86_64-unknown-linux-gnufilc0/lib /nix/store/xvl4b0gnm52hjd6qc4v0svzvk4xrz54k-ruby3.3-snappy-0.4.0-x86_64-unknown-linux-gnufilc0/bin
rewriting symlink /nix/store/xvl4b0gnm52hjd6qc4v0svzvk4xrz54k-ruby3.3-snappy-0.4.0-x86_64-unknown-linux-gnufilc0/nix-support/gem-meta/spec to be relative to /nix/store/xvl4b0gnm52hjd6qc4v0svzvk4xrz54k-ruby3.3-snappy-0.4.0-x86_64-unknown-linux-gnufilc0
```

```
created 1 symlinks in user environment
```

```
Running phase: patchPhase
Running phase: updateAutotoolsGnuConfigScriptsPhase
Running phase: updateAutotoolsGnuConfigScriptsPhase
Running phase: configurePhase
no configure script, doing nothing
Running phase: buildPhase
no Makefile or custom buildPhase, doing nothing
Running phase: installPhase
Running phase: fixupPhase
shrinking RPATHs of ELF executables and libraries in /nix/store/ndxkzp7zsia8csqpk1x8dbyk7w9aw0q9-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0
shrinking /nix/store/ndxkzp7zsia8csqpk1x8dbyk7w9aw0q9-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0/bin/bundle
shrinking /nix/store/ndxkzp7zsia8csqpk1x8dbyk7w9aw0q9-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0/bin/bundler
shrinking /nix/store/ndxkzp7zsia8csqpk1x8dbyk7w9aw0q9-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0/bin/erb
shrinking /nix/store/ndxkzp7zsia8csqpk1x8dbyk7w9aw0q9-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0/bin/gem
shrinking /nix/store/ndxkzp7zsia8csqpk1x8dbyk7w9aw0q9-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0/bin/irb
shrinking /nix/store/ndxkzp7zsia8csqpk1x8dbyk7w9aw0q9-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0/bin/racc
shrinking /nix/store/ndxkzp7zsia8csqpk1x8dbyk7w9aw0q9-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0/bin/rake
shrinking /nix/store/ndxkzp7zsia8csqpk1x8dbyk7w9aw0q9-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0/bin/rbs
shrinking /nix/store/ndxkzp7zsia8csqpk1x8dbyk7w9aw0q9-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0/bin/rdbg
shrinking /nix/store/ndxkzp7zsia8csqpk1x8dbyk7w9aw0q9-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0/bin/rdoc
shrinking /nix/store/ndxkzp7zsia8csqpk1x8dbyk7w9aw0q9-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0/bin/ri
shrinking /nix/store/ndxkzp7zsia8csqpk1x8dbyk7w9aw0q9-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0/bin/ruby
shrinking /nix/store/ndxkzp7zsia8csqpk1x8dbyk7w9aw0q9-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0/bin/syntax_suggest
shrinking /nix/store/ndxkzp7zsia8csqpk1x8dbyk7w9aw0q9-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0/bin/typeprof
checking for references to /build/ in /nix/store/ndxkzp7zsia8csqpk1x8dbyk7w9aw0q9-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0...
patching script interpreter paths in /nix/store/ndxkzp7zsia8csqpk1x8dbyk7w9aw0q9-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0
stripping (with command strip and flags -S -p) in  /nix/store/ndxkzp7zsia8csqpk1x8dbyk7w9aw0q9-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0/bin
```

</details>

<details>
<summary>✅ <strong>sqlite3</strong>: build succeeded</summary>

</details>

<details>
<summary>❌ <strong>tiny_tds</strong>: bigdecimal.c:2921:9: error: incompatible pointer to integer conversion returning 'VALUE' (aka 'struc...</summary>

```
      |                                       ~~~~~~~~~~~
 3092 |                  RB_OBJ_CLASSNAME(vexp));
      |                  ^~~~~~~~~~~~~~~~~~~~~~
bigdecimal.c:104:32: note: expanded from macro 'RB_OBJ_CLASSNAME'
  104 | # define RB_OBJ_CLASSNAME(obj) rb_obj_class(obj)
      |                                ^~~~~~~~~~~~~~~~~
bigdecimal.c:3465:18: warning: format specifies type 'long' but the argument has type 'VALUE' (aka 'struct rb_value_unit_struct *') [-Wformat]
 3464 |                  "can't omit precision for a %"PRIsVALUE".",
      |                                              ~~~~~~~~~~~
 3465 |                  CLASS_OF(val));
      |                  ^~~~~~~~~~~~~
/nix/store/65in3amyafclxn1lg3yjb1v9a3ngk1rm-ruby-3.3.10-x86_64-unknown-linux-gnufilc0/include/ruby-3.3.0/ruby/internal/globals.h:203:18: note: expanded from macro 'CLASS_OF'
  203 | #define CLASS_OF rb_class_of /**< @old{rb_class_of} */
      |                  ^
bigdecimal.c:3600:18: warning: format specifies type 'long' but the argument has type 'VALUE' (aka 'struct rb_value_unit_struct *') [-Wformat]
 3599 |                  "can't omit precision for a %"PRIsVALUE".",
      |                                              ~~~~~~~~~~~
 3600 |                  CLASS_OF(val));
      |                  ^~~~~~~~~~~~~
/nix/store/65in3amyafclxn1lg3yjb1v9a3ngk1rm-ruby-3.3.10-x86_64-unknown-linux-gnufilc0/include/ruby-3.3.0/ruby/internal/globals.h:203:18: note: expanded from macro 'CLASS_OF'
  203 | #define CLASS_OF rb_class_of /**< @old{rb_class_of} */
      |                  ^
bigdecimal.c:3630:5: error: statement requires expression of integer type ('VALUE' (aka 'struct rb_value_unit_struct *') invalid)
 3630 |     switch (val) {
      |     ^       ~~~
bigdecimal.c:3631:12: error: integer constant expression must have integer type, not 'VALUE' (aka 'struct rb_value_unit_struct *')
 3631 |       case Qnil:
      |            ^~~~
/nix/store/65in3amyafclxn1lg3yjb1v9a3ngk1rm-ruby-3.3.10-x86_64-unknown-linux-gnufilc0/include/ruby-3.3.0/ruby/internal/special_consts.h:60:25: note: expanded from macro 'Qnil'
   60 | #define Qnil            RUBY_Qnil              /**< @old{RUBY_Qnil} */
      |                         ^~~~~~~~~
/nix/store/65in3amyafclxn1lg3yjb1v9a3ngk1rm-ruby-3.3.10-x86_64-unknown-linux-gnufilc0/include/ruby-3.3.0/ruby/internal/special_consts.h:347:21: note: expanded from macro 'RUBY_Qnil'
  347 | #define RUBY_Qnil   RBIMPL_CAST((VALUE)RUBY_Qnil)
      |                     ^~~~~~~~~~~~~~~~~~~~~~~~~~~~~
/nix/store/65in3amyafclxn1lg3yjb1v9a3ngk1rm-ruby-3.3.10-x86_64-unknown-linux-gnufilc0/include/ruby-3.3.0/ruby/internal/cast.h:31:28: note: expanded from macro 'RBIMPL_CAST'
   31 | # define RBIMPL_CAST(expr) (expr)
      |                            ^~~~~~
bigdecimal.c:3632:12: error: integer constant expression must have integer type, not 'VALUE' (aka 'struct rb_value_unit_struct *')
 3632 |       case Qtrue:
      |            ^~~~~
/nix/store/65in3amyafclxn1lg3yjb1v9a3ngk1rm-ruby-3.3.10-x86_64-unknown-linux-gnufilc0/include/ruby-3.3.0/ruby/internal/special_consts.h:61:25: note: expanded from macro 'Qtrue'
   61 | #define Qtrue           RUBY_Qtrue             /**< @old{RUBY_Qtrue} */
      |                         ^~~~~~~~~~
/nix/store/65in3amyafclxn1lg3yjb1v9a3ngk1rm-ruby-3.3.10-x86_64-unknown-linux-gnufilc0/include/ruby-3.3.0/ruby/internal/special_consts.h:346:21: note: expanded from macro 'RUBY_Qtrue'
  346 | #define RUBY_Qtrue  RBIMPL_CAST((VALUE)RUBY_Qtrue)
      |                     ^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
/nix/store/65in3amyafclxn1lg3yjb1v9a3ngk1rm-ruby-3.3.10-x86_64-unknown-linux-gnufilc0/include/ruby-3.3.0/ruby/internal/cast.h:31:28: note: expanded from macro 'RBIMPL_CAST'
   31 | # define RBIMPL_CAST(expr) (expr)
      |                            ^~~~~~
bigdecimal.c:3633:12: error: integer constant expression must have integer type, not 'VALUE' (aka 'struct rb_value_unit_struct *')
 3633 |       case Qfalse:
      |            ^~~~~~
/nix/store/65in3amyafclxn1lg3yjb1v9a3ngk1rm-ruby-3.3.10-x86_64-unknown-linux-gnufilc0/include/ruby-3.3.0/ruby/internal/special_consts.h:59:25: note: expanded from macro 'Qfalse'
   59 | #define Qfalse          RUBY_Qfalse            /**< @old{RUBY_Qfalse} */
      |                         ^~~~~~~~~~~
/nix/store/65in3amyafclxn1lg3yjb1v9a3ngk1rm-ruby-3.3.10-x86_64-unknown-linux-gnufilc0/include/ruby-3.3.0/ruby/internal/special_consts.h:345:21: note: expanded from macro 'RUBY_Qfalse'
  345 | #define RUBY_Qfalse RBIMPL_CAST((VALUE)RUBY_Qfalse)
      |                     ^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
/nix/store/65in3amyafclxn1lg3yjb1v9a3ngk1rm-ruby-3.3.10-x86_64-unknown-linux-gnufilc0/include/ruby-3.3.0/ruby/internal/cast.h:31:28: note: expanded from macro 'RBIMPL_CAST'
   31 | # define RBIMPL_CAST(expr) (expr)
      |                            ^~~~~~
bigdecimal.c:3690:68: warning: format specifies type 'long' but the argument has type 'VALUE' (aka 'struct rb_value_unit_struct *') [-Wformat]
 3690 |                      "can't convert %"PRIsVALUE" into BigDecimal", rb_obj_class(val));
      |                                     ~~~~~~~~~~~                    ^~~~~~~~~~~~~~~~~
bigdecimal.c:5235:10: warning: cast to 'VALUE' (aka 'struct rb_value_unit_struct *') from smaller integer type 'int' [-Wint-to-pointer-cast]
 5235 |   return (VALUE)VpCtoV(x->a, x->int_chr, x->ni, x->frac, x->nf, x->exp_chr, x->ne);
      |          ^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
bigdecimal.c:5260:10: warning: cast to smaller integer type 'int' from 'VALUE' (aka 'struct rb_value_unit_struct *') [-Wpointer-to-int-cast]
 5260 |   return (int)result;
      |          ^~~~~~~~~~~
bigdecimal.c:5466:84: warning: format specifies type 'long' but the argument has type 'VALUE' (aka 'struct rb_value_unit_struct *') [-Wformat]
 5466 |         rb_raise(rb_eArgError, "invalid value for BigDecimal(): \"%"PRIsVALUE"\"", str);
      |                                                                   ~~~~~~~~~~~      ^~~
10 warnings and 6 errors generated.
make: *** [Makefile:249: bigdecimal.o] Error 1

make failed, exit code 2

Gem files will remain installed in /nix/store/2b6hc2d4axi5855crclxxb8959rrqlqq-ruby3.3-bigdecimal-3.1.9-x86_64-unknown-linux-gnufilc0/lib/ruby/gems/3.3.0/gems/bigdecimal-3.1.9 for inspection.
Results logged to /nix/store/2b6hc2d4axi5855crclxxb8959rrqlqq-ruby3.3-bigdecimal-3.1.9-x86_64-unknown-linux-gnufilc0/lib/ruby/gems/3.3.0/extensions/x86_64-linux/3.3.0/bigdecimal-3.1.9/gem_make.out
```

```
checking for argz_append... yes
checking for argz_count... yes
checking for argz_create_sep... yes
checking for argz_insert... yes
checking for argz_next... yes
checking for argz_stringify... yes
checking if argz actually works... yes
checking whether libtool supports -dlopen/-dlpreopen... no
checking for ltdl.h... no
checking where to find libltdl headers... -I$(top_srcdir)/libltdl
checking where to find libltdl library... $(top_build_prefix)libltdl/libltdlc.la
checking for unistd.h... (cached) yes
checking for dl.h... no
checking for sys/dl.h... no
checking for dld.h... no
checking for mach-o/dyld.h... no
checking for dirent.h... yes
checking for closedir... yes
checking for opendir... yes
checking for readdir... yes
checking for strlcat... yes
checking for strlcpy... yes
checking for shared lib extension... .so
checking for iconv... yes
checking for iconv declaration... 
         extern size_t iconv (iconv_t cd, char * *inbuf, size_t *inbytesleft, char * *outbuf, size_t *outbytesleft);
checking for encoding to use for CHAR representations ... auto-search 
checking for encoding to use for UNICODE representations ... auto-search 
checking Are we using per driver iconv ... no 
checking for crypt in -lcrypt... no
checking for pow in -lm... yes
checking for readline in -lreadline ... no
checking for readline in -lreadline -lcurses ... no
checking Are we using ini caching ... yes 
checking Are we using utf8 ini encoding ... no 
checking Are we using single shared env handle ... no 
checking for intptr_t... yes
checking whether time.h and sys/time.h may both be included... yes
checking sys/time.h usability... yes
checking sys/time.h presence... yes
checking for sys/time.h... yes
checking size of long... 8
checking if platform is 64 bit... Yes 
checking for long long... yes
checking size of long int... 8
checking for ptrdiff_t... yes
checking for special C compiler options needed for large files... no
checking for _FILE_OFFSET_BITS value needed for large files... no
checking for _LARGEFILE_SOURCE value needed for large files... no
checking for strcasecmp... yes
checking for strncasecmp... yes
checking for snprintf... yes
checking for vsnprintf... yes
checking for strtol... yes
checking for atoll... yes
checking for strtoll... yes
checking for endpwent... yes
checking for gettimeofday... yes
checking for ftime... yes
checking for time... yes
checking for stricmp... no
checking for strnicmp... no
checking for getuid... yes
checking for getpwuid... yes
checking for getpwuid_r... yes
checking for nl_langinfo... yes
checking for fseeko... yes
checking for setvbuf... yes
checking for clock_gettime... yes
checking for nl_langinfo and CODESET... yes
checking if os is AIX ... no - enable check for libthread 
checking for mutex_lock in -lthread ... no
checking for pthread_mutex_lock in -lpthread... yes
checking if compiler accepts -pthread... yes
checking for localtime_r in -lc... yes
checking for ANSI C header files... (cached) yes
checking malloc.h usability... yes
checking malloc.h presence... yes
checking for malloc.h... yes
checking for unistd.h... (cached) yes
```

</details>

<details>
<summary>✅ <strong>typhoeus</strong>: build failed</summary>

```
copying path '/nix/store/rn2mlxanhc9v7ppqz47q3w8zfxg504a7-typhoeus-1.4.1.gem' from 'https://cache.nixos.org'...
Running phase: unpackPhase
Running phase: patchPhase
Running phase: updateAutotoolsGnuConfigScriptsPhase
Running phase: updateAutotoolsGnuConfigScriptsPhase
Running phase: configurePhase
no configure script, doing nothing
Running phase: installPhase
buildFlags: 
WARNING:  You build with buildroot.
  Build root: /
  Bin dir: /nix/store/jjp9w7pkpfd14079srsdjwr2q64q44la-ruby3.3-typhoeus-1.4.1-x86_64-unknown-linux-gnufilc0/lib/ruby/gems/3.3.0/bin
  Gem home: /nix/store/jjp9w7pkpfd14079srsdjwr2q64q44la-ruby3.3-typhoeus-1.4.1-x86_64-unknown-linux-gnufilc0/lib/ruby/gems/3.3.0
  Plugins dir: /nix/store/jjp9w7pkpfd14079srsdjwr2q64q44la-ruby3.3-typhoeus-1.4.1-x86_64-unknown-linux-gnufilc0/lib/ruby/gems/3.3.0/plugins
Successfully installed typhoeus-1.4.1
1 gem installed
/nix/store/jjp9w7pkpfd14079srsdjwr2q64q44la-ruby3.3-typhoeus-1.4.1-x86_64-unknown-linux-gnufilc0/lib/ruby/gems/3.3.0 /build
removed 'cache/typhoeus-1.4.1.gem'
removed directory 'cache'
/build
Running phase: fixupPhase
shrinking RPATHs of ELF executables and libraries in /nix/store/jjp9w7pkpfd14079srsdjwr2q64q44la-ruby3.3-typhoeus-1.4.1-x86_64-unknown-linux-gnufilc0
checking for references to /build/ in /nix/store/jjp9w7pkpfd14079srsdjwr2q64q44la-ruby3.3-typhoeus-1.4.1-x86_64-unknown-linux-gnufilc0...
patching script interpreter paths in /nix/store/jjp9w7pkpfd14079srsdjwr2q64q44la-ruby3.3-typhoeus-1.4.1-x86_64-unknown-linux-gnufilc0
stripping (with command strip and flags -S -p) in  /nix/store/jjp9w7pkpfd14079srsdjwr2q64q44la-ruby3.3-typhoeus-1.4.1-x86_64-unknown-linux-gnufilc0/lib /nix/store/jjp9w7pkpfd14079srsdjwr2q64q44la-ruby3.3-typhoeus-1.4.1-x86_64-unknown-linux-gnufilc0/bin
rewriting symlink /nix/store/jjp9w7pkpfd14079srsdjwr2q64q44la-ruby3.3-typhoeus-1.4.1-x86_64-unknown-linux-gnufilc0/nix-support/gem-meta/spec to be relative to /nix/store/jjp9w7pkpfd14079srsdjwr2q64q44la-ruby3.3-typhoeus-1.4.1-x86_64-unknown-linux-gnufilc0
```

```
created 7 symlinks in user environment
```

```
Running phase: patchPhase
Running phase: updateAutotoolsGnuConfigScriptsPhase
Running phase: updateAutotoolsGnuConfigScriptsPhase
Running phase: configurePhase
no configure script, doing nothing
Running phase: buildPhase
no Makefile or custom buildPhase, doing nothing
Running phase: installPhase
Running phase: fixupPhase
shrinking RPATHs of ELF executables and libraries in /nix/store/cgrsvma0a0w8ig2xskz5f7bwl755q25s-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0
shrinking /nix/store/cgrsvma0a0w8ig2xskz5f7bwl755q25s-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0/bin/bundle
shrinking /nix/store/cgrsvma0a0w8ig2xskz5f7bwl755q25s-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0/bin/bundler
shrinking /nix/store/cgrsvma0a0w8ig2xskz5f7bwl755q25s-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0/bin/erb
shrinking /nix/store/cgrsvma0a0w8ig2xskz5f7bwl755q25s-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0/bin/gem
shrinking /nix/store/cgrsvma0a0w8ig2xskz5f7bwl755q25s-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0/bin/irb
shrinking /nix/store/cgrsvma0a0w8ig2xskz5f7bwl755q25s-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0/bin/racc
shrinking /nix/store/cgrsvma0a0w8ig2xskz5f7bwl755q25s-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0/bin/rake
shrinking /nix/store/cgrsvma0a0w8ig2xskz5f7bwl755q25s-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0/bin/rbs
shrinking /nix/store/cgrsvma0a0w8ig2xskz5f7bwl755q25s-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0/bin/rdbg
shrinking /nix/store/cgrsvma0a0w8ig2xskz5f7bwl755q25s-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0/bin/rdoc
shrinking /nix/store/cgrsvma0a0w8ig2xskz5f7bwl755q25s-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0/bin/ri
shrinking /nix/store/cgrsvma0a0w8ig2xskz5f7bwl755q25s-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0/bin/ruby
shrinking /nix/store/cgrsvma0a0w8ig2xskz5f7bwl755q25s-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0/bin/syntax_suggest
shrinking /nix/store/cgrsvma0a0w8ig2xskz5f7bwl755q25s-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0/bin/typeprof
checking for references to /build/ in /nix/store/cgrsvma0a0w8ig2xskz5f7bwl755q25s-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0...
patching script interpreter paths in /nix/store/cgrsvma0a0w8ig2xskz5f7bwl755q25s-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0
stripping (with command strip and flags -S -p) in  /nix/store/cgrsvma0a0w8ig2xskz5f7bwl755q25s-ruby-3.3.10-x86_64-unknown-linux-gnufilc0-with-packages-x86_64-unknown-linux-gnufilc0/bin
```

</details>

<details>
<summary>❌ <strong>uuid4r</strong>: build failed</summary>

```
config.status: creating Makefile
config.status: creating uuid-config
config.status: creating uuid.pc
config.status: creating uuid.h
config.status: creating config.h
config.status: executing libtool commands
config.status: executing adjustment commands
Running phase: buildPhase
build flags: SHELL=/nix/store/cfqbabpc7xwg8akbcchqbq3cai6qq2vs-bash-5.2p37/bin/bash
libtool: compile:  clang -I. -I. -DHAVE_CONFIG_H -O2 -pipe -c uuid.c  -fPIC -DPIC -o .libs/uuid.o
uuid.c:176:25: warning: comparison of function 'uuid_clone' equal to a null pointer is always false [-Wtautological-pointer-compare]
  176 |     if (uuid == NULL || uuid_clone == NULL)
      |                         ^~~~~~~~~~    ~~~~
uuid.c:176:25: note: prefix with the address-of operator to silence this warning
  176 |     if (uuid == NULL || uuid_clone == NULL)
      |                         ^
      |                         &
1 warning generated.
libtool: compile:  clang -I. -I. -DHAVE_CONFIG_H -O2 -pipe -c uuid_md5.c  -fPIC -DPIC -o .libs/uuid_md5.o
libtool: compile:  clang -I. -I. -DHAVE_CONFIG_H -O2 -pipe -c uuid_sha1.c  -fPIC -DPIC -o .libs/uuid_sha1.o
libtool: compile:  clang -I. -I. -DHAVE_CONFIG_H -O2 -pipe -c uuid_prng.c  -fPIC -DPIC -o .libs/uuid_prng.o
libtool: compile:  clang -I. -I. -DHAVE_CONFIG_H -O2 -pipe -c uuid_mac.c  -fPIC -DPIC -o .libs/uuid_mac.o
libtool: compile:  clang -I. -I. -DHAVE_CONFIG_H -O2 -pipe -c uuid_time.c  -fPIC -DPIC -o .libs/uuid_time.o
libtool: compile:  clang -I. -I. -DHAVE_CONFIG_H -O2 -pipe -c uuid_ui64.c  -fPIC -DPIC -o .libs/uuid_ui64.o
libtool: compile:  clang -I. -I. -DHAVE_CONFIG_H -O2 -pipe -c uuid_ui128.c  -fPIC -DPIC -o .libs/uuid_ui128.o
libtool: compile:  clang -I. -I. -DHAVE_CONFIG_H -O2 -pipe -c uuid_str.c  -fPIC -DPIC -o .libs/uuid_str.o
libtool: link: clang -shared  .libs/uuid.o .libs/uuid_md5.o .libs/uuid_sha1.o .libs/uuid_prng.o .libs/uuid_mac.o .libs/uuid_time.o .libs/uuid_ui64.o .libs/uuid_ui128.o .libs/uuid_str.o      -Wl,-soname -Wl,libuuid.so.16 -o .libs/libuuid.so.16.0.22
libtool: link: (cd ".libs" && rm -f "libuuid.so.16" && ln -s "libuuid.so.16.0.22" "libuuid.so.16")
libtool: link: (cd ".libs" && rm -f "libuuid.so" && ln -s "libuuid.so.16.0.22" "libuuid.so")
libtool: link: ( cd ".libs" && rm -f "libuuid.la" && ln -s "../libuuid.la" "libuuid.la" )
clang -I. -I.  -DHAVE_CONFIG_H -O2 -pipe -c uuid_cli.c
libtool: link: clang -o .libs/uuid uuid_cli.o  ./.libs/libuuid.so -Wl,-rpath -Wl,/nix/store/npj761fqw4m8m560bn33l4idzg15p7y8-libossp-uuid-x86_64-unknown-linux-gnufilc0-1.6.2/lib
Running phase: installPhase
install flags: SHELL=/nix/store/cfqbabpc7xwg8akbcchqbq3cai6qq2vs-bash-5.2p37/bin/bash install
./shtool mkdir -f -p -m 755 /nix/store/npj761fqw4m8m560bn33l4idzg15p7y8-libossp-uuid-x86_64-unknown-linux-gnufilc0-1.6.2
./shtool mkdir -f -p -m 755 /nix/store/npj761fqw4m8m560bn33l4idzg15p7y8-libossp-uuid-x86_64-unknown-linux-gnufilc0-1.6.2/bin
./shtool mkdir -f -p -m 755 /nix/store/npj761fqw4m8m560bn33l4idzg15p7y8-libossp-uuid-x86_64-unknown-linux-gnufilc0-1.6.2/include
./shtool mkdir -f -p -m 755 /nix/store/npj761fqw4m8m560bn33l4idzg15p7y8-libossp-uuid-x86_64-unknown-linux-gnufilc0-1.6.2/lib/pkgconfig
./shtool mkdir -f -p -m 755 /nix/store/npj761fqw4m8m560bn33l4idzg15p7y8-libossp-uuid-x86_64-unknown-linux-gnufilc0-1.6.2/share/man/man3
./shtool mkdir -f -p -m 755 /nix/store/npj761fqw4m8m560bn33l4idzg15p7y8-libossp-uuid-x86_64-unknown-linux-gnufilc0-1.6.2/share/man/man1
./shtool install -c -m 755 uuid-config /nix/store/npj761fqw4m8m560bn33l4idzg15p7y8-libossp-uuid-x86_64-unknown-linux-gnufilc0-1.6.2/bin/
./shtool install -c -m 644 ./uuid-config.1 /nix/store/npj761fqw4m8m560bn33l4idzg15p7y8-libossp-uuid-x86_64-unknown-linux-gnufilc0-1.6.2/share/man/man1/
./shtool install -c -m 644 ./uuid.pc /nix/store/npj761fqw4m8m560bn33l4idzg15p7y8-libossp-uuid-x86_64-unknown-linux-gnufilc0-1.6.2/lib/pkgconfig/
./shtool install -c -m 644 uuid.h /nix/store/npj761fqw4m8m560bn33l4idzg15p7y8-libossp-uuid-x86_64-unknown-linux-gnufilc0-1.6.2/include/
./shtool install -c -m 644 ./uuid.3 /nix/store/npj761fqw4m8m560bn33l4idzg15p7y8-libossp-uuid-x86_64-unknown-linux-gnufilc0-1.6.2/share/man/man3/
libtool: install: ./shtool install -c -m 644 .libs/libuuid.so.16.0.22 /nix/store/npj761fqw4m8m560bn33l4idzg15p7y8-libossp-uuid-x86_64-unknown-linux-gnufilc0-1.6.2/lib/libuuid.so.16.0.22
libtool: install: (cd /nix/store/npj761fqw4m8m560bn33l4idzg15p7y8-libossp-uuid-x86_64-unknown-linux-gnufilc0-1.6.2/lib && { ln -s -f libuuid.so.16.0.22 libuuid.so.16 || { rm -f libuuid.so.16 && ln -s libuuid.so.16.0.22 libuuid.so.16; }; })
libtool: install: (cd /nix/store/npj761fqw4m8m560bn33l4idzg15p7y8-libossp-uuid-x86_64-unknown-linux-gnufilc0-1.6.2/lib && { ln -s -f libuuid.so.16.0.22 libuuid.so || { rm -f libuuid.so && ln -s libuuid.so.16.0.22 libuuid.so; }; })
libtool: install: ./shtool install -c -m 644 .libs/libuuid.lai /nix/store/npj761fqw4m8m560bn33l4idzg15p7y8-libossp-uuid-x86_64-unknown-linux-gnufilc0-1.6.2/lib/libuuid.la
libtool: finish: PATH="/nix/store/g7i75czfbw9sy5f8v7rjbama6lr3ya3s-patchelf-0.15.0/bin:/nix/store/a0nc03czg70yaj0p9qphx5b3ppnb939i-filc-cc-wrapper-/bin:/nix/store/gy2di95906x5rgl25ck3d3xhsp7srz8b-filc-cc/bin:/nix/store/6ql65jl6flp8qbikcpjn15hycghvqg29-filc-sysroot-with-metadata/bin:/nix/store/rry6qingvsrqmc7ll7jgaqpybcbdgf5v-coreutils-9.7/bin:/nix/store/bjmp5s6kl068x3vmjg2cbycfwx21hcd2-binutils-wrapper-2.43.1/bin:/nix/store/fmj1ilm5jk1hba6s3cv6gkpgsjvkxaqv-binutils-2.43.1/bin:/nix/store/rry6qingvsrqmc7ll7jgaqpybcbdgf5v-coreutils-9.7/bin:/nix/store/392hs9nhm6wfw4imjllbvb1wil1n39qx-findutils-4.10.0/bin:/nix/store/xw0mf3shymq3k7zlncf09rm8917sdi4h-diffutils-3.12/bin:/nix/store/4rpiqv9yr2pw5094v4wc33ijkqjpm9sa-gnused-4.9/bin:/nix/store/l2wvwyg680h0v2la18hz3yiznxy2naqw-gnugrep-3.11/bin:/nix/store/c1z5j28ndxljf1ihqzag57bwpfpzms0g-gawk-5.3.2/bin:/nix/store/w60s4xh1pjg6dwbw7j0b4xzlpp88q5qg-gnutar-1.35/bin:/nix/store/xd9m9jkvrs8pbxvmkzkwviql33rd090j-gzip-1.14/bin:/nix/store/w1pxx760yidi7n9vbi5bhpii9xxl5vdj-bzip2-1.0.8-bin/bin:/nix/store/xk0d14zpm0njxzdm182dd722aqhav2cc-gnumake-4.4.1/bin:/nix/store/cfqbabpc7xwg8akbcchqbq3cai6qq2vs-bash-5.2p37/bin:/nix/store/gj54zvf7vxll1mzzmqhqi1p4jiws3mfb-patch-2.7.6/bin:/nix/store/22rpb6790f346c55iqi6s9drr5qgmyjf-xz-5.8.1-bin/bin:/nix/store/xlmpcglsq8l09qh03rf0virz0331pjdc-file-5.45/bin:/sbin" ldconfig -n /nix/store/npj761fqw4m8m560bn33l4idzg15p7y8-libossp-uuid-x86_64-unknown-linux-gnufilc0-1.6.2/lib
/build/uuid-1.6.2/libtool: line 952: ldconfig: command not found
----------------------------------------------------------------------
Libraries have been installed in:
   /nix/store/npj761fqw4m8m560bn33l4idzg15p7y8-libossp-uuid-x86_64-unknown-linux-gnufilc0-1.6.2/lib

If you ever happen to want to link against installed libraries
in a given directory, LIBDIR, you must either use libtool, and
specify the full pathname of the library, or use the `-LLIBDIR'
flag during linking and do at least one of the following:
   - add LIBDIR to the `LD_LIBRARY_PATH' environment variable
     during execution
   - add LIBDIR to the `LD_RUN_PATH' environment variable
     during linking
   - use the `-Wl,-rpath -Wl,LIBDIR' linker flag
   - have your system administrator run these commands:


See any operating system documentation about shared libraries for
more information, such as the ld(1) and ld.so(8) manual pages.
----------------------------------------------------------------------
libtool: install: ./shtool install -c -m 755 -s .libs/uuid /nix/store/npj761fqw4m8m560bn33l4idzg15p7y8-libossp-uuid-x86_64-unknown-linux-gnufilc0-1.6.2/bin/uuid
./shtool install -c -m 644 ./uuid.1 /nix/store/npj761fqw4m8m560bn33l4idzg15p7y8-libossp-uuid-x86_64-unknown-linux-gnufilc0-1.6.2/share/man/man1/
Running phase: fixupPhase
shrinking RPATHs of ELF executables and libraries in /nix/store/npj761fqw4m8m560bn33l4idzg15p7y8-libossp-uuid-x86_64-unknown-linux-gnufilc0-1.6.2
shrinking /nix/store/npj761fqw4m8m560bn33l4idzg15p7y8-libossp-uuid-x86_64-unknown-linux-gnufilc0-1.6.2/bin/uuid
shrinking /nix/store/npj761fqw4m8m560bn33l4idzg15p7y8-libossp-uuid-x86_64-unknown-linux-gnufilc0-1.6.2/lib/libuuid.so.16.0.22
checking for references to /build/ in /nix/store/npj761fqw4m8m560bn33l4idzg15p7y8-libossp-uuid-x86_64-unknown-linux-gnufilc0-1.6.2...
gzipping man pages under /nix/store/npj761fqw4m8m560bn33l4idzg15p7y8-libossp-uuid-x86_64-unknown-linux-gnufilc0-1.6.2/share/man/
patching script interpreter paths in /nix/store/npj761fqw4m8m560bn33l4idzg15p7y8-libossp-uuid-x86_64-unknown-linux-gnufilc0-1.6.2
stripping (with command strip and flags -S -p) in  /nix/store/npj761fqw4m8m560bn33l4idzg15p7y8-libossp-uuid-x86_64-unknown-linux-gnufilc0-1.6.2/lib /nix/store/npj761fqw4m8m560bn33l4idzg15p7y8-libossp-uuid-x86_64-unknown-linux-gnufilc0-1.6.2/bin
```

```
copying path '/nix/store/mrj621lj3kaaq81zwh6vd02ac0gql14k-uuid4r-0.2.0.gem' from 'https://cache.nixos.org'...
Running phase: unpackPhase
Running phase: patchPhase
Running phase: updateAutotoolsGnuConfigScriptsPhase
Running phase: updateAutotoolsGnuConfigScriptsPhase
Running phase: configurePhase
no configure script, doing nothing
Running phase: installPhase
buildFlags: 
WARNING:  You build with buildroot.
  Build root: /
  Bin dir: /nix/store/8zjnjzinjx797ylmfkvr9xl7d92nm97i-ruby3.3-uuid4r-0.2.0-x86_64-unknown-linux-gnufilc0/lib/ruby/gems/3.3.0/bin
  Gem home: /nix/store/8zjnjzinjx797ylmfkvr9xl7d92nm97i-ruby3.3-uuid4r-0.2.0-x86_64-unknown-linux-gnufilc0/lib/ruby/gems/3.3.0
  Plugins dir: /nix/store/8zjnjzinjx797ylmfkvr9xl7d92nm97i-ruby3.3-uuid4r-0.2.0-x86_64-unknown-linux-gnufilc0/lib/ruby/gems/3.3.0/plugins
Building native extensions. This could take a while...
ERROR:  Error installing /nix/store/mrj621lj3kaaq81zwh6vd02ac0gql14k-uuid4r-0.2.0.gem:
        ERROR: Failed to build gem native extension.

    current directory: /nix/store/8zjnjzinjx797ylmfkvr9xl7d92nm97i-ruby3.3-uuid4r-0.2.0-x86_64-unknown-linux-gnufilc0/lib/ruby/gems/3.3.0/gems/uuid4r-0.2.0/ext
/nix/store/65in3amyafclxn1lg3yjb1v9a3ngk1rm-ruby-3.3.10-x86_64-unknown-linux-gnufilc0/bin/ruby extconf.rb
*** extconf.rb failed ***
Could not create Makefile due to some reason, probably lack of necessary
libraries and/or headers.  Check the mkmf.log file for more details.  You may
need configuration options.

Provided configuration options:
        --with-opt-dir
        --without-opt-dir
        --with-opt-include=${opt-dir}/include
        --without-opt-include
        --with-opt-lib=${opt-dir}/lib
        --without-opt-lib
        --with-make-prog
        --without-make-prog
        --srcdir=.
        --curdir
        --ruby=/nix/store/65in3amyafclxn1lg3yjb1v9a3ngk1rm-ruby-3.3.10-x86_64-unknown-linux-gnufilc0/bin/$(RUBY_BASE_NAME)
extconf.rb:5:in ``': No such file or directory - which (Errno::ENOENT)
        from extconf.rb:5:in `<main>'

extconf failed, exit code 1

Gem files will remain installed in /nix/store/8zjnjzinjx797ylmfkvr9xl7d92nm97i-ruby3.3-uuid4r-0.2.0-x86_64-unknown-linux-gnufilc0/lib/ruby/gems/3.3.0/gems/uuid4r-0.2.0 for inspection.
Results logged to /nix/store/8zjnjzinjx797ylmfkvr9xl7d92nm97i-ruby3.3-uuid4r-0.2.0-x86_64-unknown-linux-gnufilc0/lib/ruby/gems/3.3.0/extensions/x86_64-linux/3.3.0/uuid4r-0.2.0/gem_make.out
```

</details>

<details>
<summary>❌ <strong>xapian-ruby</strong>: build failed</summary>

</details>

<details>
<summary>❌ <strong>zlib</strong>: build failed</summary>

</details>

<details>
<summary>❌ <strong>zookeeper</strong>: build failed</summary>

```
/nix/store/4rpiqv9yr2pw5094v4wc33ijkqjpm9sa-gnused-4.9/bin/sed: -e expression #1, char 0: no previous regular expression
/nix/store/4rpiqv9yr2pw5094v4wc33ijkqjpm9sa-gnused-4.9/bin/sed: -e expression #1, char 0: no previous regular expression
/nix/store/4rpiqv9yr2pw5094v4wc33ijkqjpm9sa-gnused-4.9/bin/sed: -e expression #1, char 0: no previous regular expression
ar cru .libs/libzkst.a .libs/zookeeper.o .libs/recordio.o .libs/zookeeper.jute.o .libs/zk_log.o .libs/zk_hashtable.o .libs/st_adaptor.o
ar: `u' modifier ignored since `D' is the default (see `U')
ranlib .libs/libzkst.a
creating libzkst.la
(cd .libs && rm -f libzkst.la && ln -s ../libzkst.la libzkst.la)
/nix/store/cfqbabpc7xwg8akbcchqbq3cai6qq2vs-bash-5.2p37/bin/bash ./libtool --tag=CC --mode=compile clang -DHAVE_CONFIG_H -I. -I. -I.  -I./include -I./tests -I./generated  -Wall -Werror  -g -O2 -D_GNU_SOURCE -c -o hashtable_itr.lo `test -f 'src/hashtable/hashtable_itr.c' || echo './'`src/hashtable/hashtable_itr.c
./libtool: line 96: gcc: command not found
./libtool: line 97: gcc: command not found
/nix/store/4rpiqv9yr2pw5094v4wc33ijkqjpm9sa-gnused-4.9/bin/sed: -e expression #1, char 0: no previous regular expression
/nix/store/4rpiqv9yr2pw5094v4wc33ijkqjpm9sa-gnused-4.9/bin/sed: -e expression #1, char 0: no previous regular expression
/nix/store/4rpiqv9yr2pw5094v4wc33ijkqjpm9sa-gnused-4.9/bin/sed: -e expression #1, char 0: no previous regular expression
/nix/store/4rpiqv9yr2pw5094v4wc33ijkqjpm9sa-gnused-4.9/bin/sed: -e expression #1, char 0: no previous regular expression
 clang -DHAVE_CONFIG_H -I. -I. -I. -I./include -I./tests -I./generated -Wall -Werror -g -O2 -D_GNU_SOURCE -c src/hashtable/hashtable_itr.c  -fPIC -DPIC -o .libs/hashtable_itr.o
 clang -DHAVE_CONFIG_H -I. -I. -I. -I./include -I./tests -I./generated -Wall -Werror -g -O2 -D_GNU_SOURCE -c src/hashtable/hashtable_itr.c  -fPIC -DPIC -o hashtable_itr.o >/dev/null 2>&1
/nix/store/cfqbabpc7xwg8akbcchqbq3cai6qq2vs-bash-5.2p37/bin/bash ./libtool --tag=CC --mode=compile clang -DHAVE_CONFIG_H -I. -I. -I.  -I./include -I./tests -I./generated  -Wall -Werror  -g -O2 -D_GNU_SOURCE -c -o hashtable.lo `test -f 'src/hashtable/hashtable.c' || echo './'`src/hashtable/hashtable.c
./libtool: line 96: gcc: command not found
./libtool: line 97: gcc: command not found
/nix/store/4rpiqv9yr2pw5094v4wc33ijkqjpm9sa-gnused-4.9/bin/sed: -e expression #1, char 0: no previous regular expression
/nix/store/4rpiqv9yr2pw5094v4wc33ijkqjpm9sa-gnused-4.9/bin/sed: -e expression #1, char 0: no previous regular expression
/nix/store/4rpiqv9yr2pw5094v4wc33ijkqjpm9sa-gnused-4.9/bin/sed: -e expression #1, char 0: no previous regular expression
/nix/store/4rpiqv9yr2pw5094v4wc33ijkqjpm9sa-gnused-4.9/bin/sed: -e expression #1, char 0: no previous regular expression
 clang -DHAVE_CONFIG_H -I. -I. -I. -I./include -I./tests -I./generated -Wall -Werror -g -O2 -D_GNU_SOURCE -c src/hashtable/hashtable.c  -fPIC -DPIC -o .libs/hashtable.o
 clang -DHAVE_CONFIG_H -I. -I. -I. -I./include -I./tests -I./generated -Wall -Werror -g -O2 -D_GNU_SOURCE -c src/hashtable/hashtable.c  -fPIC -DPIC -o hashtable.o >/dev/null 2>&1
/nix/store/cfqbabpc7xwg8akbcchqbq3cai6qq2vs-bash-5.2p37/bin/bash ./libtool --tag=CC --mode=link clang -Wall -Werror  -g -O2 -D_GNU_SOURCE   -o libhashtable.la   hashtable_itr.lo hashtable.lo  
./libtool: line 96: gcc: command not found
./libtool: line 97: gcc: command not found
/nix/store/4rpiqv9yr2pw5094v4wc33ijkqjpm9sa-gnused-4.9/bin/sed: -e expression #1, char 0: no previous regular expression
/nix/store/4rpiqv9yr2pw5094v4wc33ijkqjpm9sa-gnused-4.9/bin/sed: -e expression #1, char 0: no previous regular expression
/nix/store/4rpiqv9yr2pw5094v4wc33ijkqjpm9sa-gnused-4.9/bin/sed: -e expression #1, char 0: no previous regular expression
/nix/store/4rpiqv9yr2pw5094v4wc33ijkqjpm9sa-gnused-4.9/bin/sed: -e expression #1, char 0: no previous regular expression
ar cru .libs/libhashtable.a .libs/hashtable_itr.o .libs/hashtable.o
ar: `u' modifier ignored since `D' is the default (see `U')
ranlib .libs/libhashtable.a
creating libhashtable.la
(cd .libs && rm -f libhashtable.la && ln -s ../libhashtable.la libhashtable.la)
/nix/store/cfqbabpc7xwg8akbcchqbq3cai6qq2vs-bash-5.2p37/bin/bash ./libtool --tag=CC --mode=link clang -Wall -Werror  -g -O2 -D_GNU_SOURCE   -o libzookeeper_st.la -rpath /nix/store/rzzh48j9nilmkrx6d6nb35i9a5ii7yrw-ruby3.3-zookeeper-1.5.5-x86_64-unknown-linux-gnufilc0/lib/ruby/gems/3.3.0/gems/zookeeper-1.5.5/ext/lib -no-undefined -version-info 2 -export-symbols-regex '(zoo_|zookeeper_|zhandle|Z|format_log_message|log_message|logLevel|deallocate_|zerror|is_unrecoverable)'  libzkst.la libhashtable.la 
./libtool: line 96: gcc: command not found
./libtool: line 97: gcc: command not found
/nix/store/4rpiqv9yr2pw5094v4wc33ijkqjpm9sa-gnused-4.9/bin/sed: -e expression #1, char 0: no previous regular expression
/nix/store/4rpiqv9yr2pw5094v4wc33ijkqjpm9sa-gnused-4.9/bin/sed: -e expression #1, char 0: no previous regular expression
/nix/store/4rpiqv9yr2pw5094v4wc33ijkqjpm9sa-gnused-4.9/bin/sed: -e expression #1, char 0: no previous regular expression
/nix/store/4rpiqv9yr2pw5094v4wc33ijkqjpm9sa-gnused-4.9/bin/sed: -e expression #1, char 0: no previous regular expression
generating symbol list for `libzookeeper_st.la'
nm   ./.libs/libzkst.a ./.libs/libhashtable.a |  | /nix/store/4rpiqv9yr2pw5094v4wc33ijkqjpm9sa-gnused-4.9/bin/sed 's/.* //' | sort | uniq > .libs/libzookeeper_st.exp
./libtool: eval: line 4326: syntax error near unexpected token `|'
./libtool: eval: line 4326: `nm   ./.libs/libzkst.a ./.libs/libhashtable.a |  | /nix/store/4rpiqv9yr2pw5094v4wc33ijkqjpm9sa-gnused-4.9/bin/sed 's/.* //' | sort | uniq > .libs/libzookeeper_st.exp'
make[1]: *** [Makefile:567: libzookeeper_st.la] Error 2
make[1]: Leaving directory '/nix/store/rzzh48j9nilmkrx6d6nb35i9a5ii7yrw-ruby3.3-zookeeper-1.5.5-x86_64-unknown-linux-gnufilc0/lib/ruby/gems/3.3.0/gems/zookeeper-1.5.5/ext/zkc-3.4.5/c'
make: *** [Makefile:468: all] Error 2
*** extconf.rb failed ***
Could not create Makefile due to some reason, probably lack of necessary
libraries and/or headers.  Check the mkmf.log file for more details.  You may
need configuration options.

Provided configuration options:
        --with-opt-dir
        --without-opt-dir
        --with-opt-include=${opt-dir}/include
        --without-opt-include
        --with-opt-lib=${opt-dir}/lib
        --without-opt-lib
        --with-make-prog
        --without-make-prog
        --srcdir=.
        --curdir
        --ruby=/nix/store/65in3amyafclxn1lg3yjb1v9a3ngk1rm-ruby-3.3.10-x86_64-unknown-linux-gnufilc0/bin/$(RUBY_BASE_NAME)
extconf.rb:51:in `safe_sh': command failed! make  2>&1 (RuntimeError)
        from extconf.rb:76:in `block (2 levels) in <main>'
        from extconf.rb:71:in `chdir'
        from extconf.rb:71:in `block in <main>'
        from extconf.rb:55:in `chdir'
        from extconf.rb:55:in `<main>'

extconf failed, exit code 1

Gem files will remain installed in /nix/store/rzzh48j9nilmkrx6d6nb35i9a5ii7yrw-ruby3.3-zookeeper-1.5.5-x86_64-unknown-linux-gnufilc0/lib/ruby/gems/3.3.0/gems/zookeeper-1.5.5 for inspection.
Results logged to /nix/store/rzzh48j9nilmkrx6d6nb35i9a5ii7yrw-ruby3.3-zookeeper-1.5.5-x86_64-unknown-linux-gnufilc0/lib/ruby/gems/3.3.0/extensions/x86_64-linux/3.3.0/zookeeper-1.5.5/gem_make.out
```

</details>

