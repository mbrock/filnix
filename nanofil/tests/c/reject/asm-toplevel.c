// error: top-level asm ".globl g; g = f" is not supported; only .symver and .filc_rename, .filc_alias, .filc_weak_alias, .filc_weak and .filc_globl are
/* filcc's compileModuleAsm crashes on any directive but .symver and its
   own .filc_* ones (nanofil reads those, tests/c/prog/filc-asm.c);
   nanofil refuses the rest. */
int f(void) { return 0; }
__asm__(".globl g; g = f");
