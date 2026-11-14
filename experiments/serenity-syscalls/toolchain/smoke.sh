#!/bin/Shell
# Runs in place of Serenity's run-tests-and-shutdown.sh when
# serenity-clang23.sh boots the image in self-test mode. Its output goes to
# the serial console, and the boot stage looks for the last line.
echo
echo "==== clang 23 SerenityOS smoke ===="
uname -a
true && echo "true exited $?"
echo "echo works" | cat
ls /usr/lib/libc.so /usr/lib/Loader.so
expr 6 \* 7
js -c 'console.log([1, 2, 3].map(x => x * 14).join(" "))'
/usr/Tests/AK/TestVector
/usr/Tests/AK/TestString
echo "==== smoke done ===="
sync
shutdown -n
