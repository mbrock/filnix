// The second glibc spike program: main writes a string to standard
// output with glibc's own write, whose IR calls libpizlo's zsys_write,
// after measuring it with glibc's own strlen. Both come from nanofil's
// IR of user glibc; only zsys_write is a contract (ZsysWrite.v).
// Proved safe, with that contract, in rocq/glibc/SayLogic.v (say_logic_safe).
#include <string.h>
#include <unistd.h>

static const char msg[] = "hello, glibc\n";

int main(void) {
  write(1, msg, strlen(msg));
  return 0;
}
