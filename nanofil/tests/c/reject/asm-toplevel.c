// error: top-level asm ".globl g; g = f" is not supported; only .symver is
/* filcc's compileModuleAsm crashes on any directive but .symver and its
   own .filc_* ones; nanofil refuses it. */
int f(void) { return 0; }
__asm__(".globl g; g = f");
