#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdatomic.h>
#include <setjmp.h>
#include <signal.h>
#include <unistd.h>
#include <sys/wait.h>
/* Which pointer-tagging patterns keep Fil-C capabilities; see
   docs/filc-findings.md. Exits nonzero if any outcome changes. */
#define NI __attribute__((noinline))
#ifdef __OPTIMIZE__
#define O2 1
#else
#define O2 0
#endif
typedef struct { long v; } obj;
static obj* mk(long v) { obj* o = malloc(sizeof *o); o->v = v; return o; }

struct ui { uintptr_t w; };
struct vp { void* w; };
union un { void* p; uintptr_t w; };
static struct ui gui; static struct vp gvp; static union un gun; static _Atomic uintptr_t gat;

NI long t1(void){ obj* o=mk(1); uintptr_t w=(uintptr_t)o|1; return ((obj*)(w&~(uintptr_t)1))->v; }
NI void s2(struct ui* s, obj* o){ s->w=(uintptr_t)o|1; }
NI long t2(void){ s2(&gui,mk(2)); asm volatile("":::"memory"); return ((obj*)(gui.w&~(uintptr_t)1))->v; }
NI void s3(struct vp* s, obj* o){ s->w=(char*)o+1; }
NI long t3(void){ s3(&gvp,mk(3)); asm volatile("":::"memory"); return ((obj*)((uintptr_t)gvp.w&~(uintptr_t)1))->v; }
NI long t3b(void){ s3(&gvp,mk(31)); asm volatile("":::"memory"); return ((obj*)((char*)gvp.w-1))->v; }
NI void s4(union un* u, obj* o){ u->w=(uintptr_t)o|1; }
NI long t4(void){ s4(&gun,mk(4)); asm volatile("":::"memory"); return ((obj*)(gun.w&~(uintptr_t)1))->v; }
NI long t4b(void){ s4(&gun,mk(41)); asm volatile("":::"memory"); return ((obj*)((uintptr_t)gun.p&~(uintptr_t)1))->v; }
NI void s5(obj* o){ atomic_store(&gat,(uintptr_t)o|1); }
NI long t5(void){ s5(mk(5)); return ((obj*)(atomic_load(&gat)&~(uintptr_t)1))->v; }
NI long u6(uintptr_t w){ return ((obj*)(w&~(uintptr_t)1))->v; }
NI long t6(void){ return u6((uintptr_t)mk(6)|1); }
NI uintptr_t r7(void){ return (uintptr_t)mk(7)|1; }
NI long t7(void){ return ((obj*)(r7()&~(uintptr_t)1))->v; }
NI void s8(struct ui* s, obj* o){ s->w=(uintptr_t)o|(1ull<<48); }
NI long t8(void){ s8(&gui,mk(8)); asm volatile("":::"memory"); return ((obj*)(gui.w&((1ull<<48)-1)))->v; }
/* heap array of uintptr_t words (like a VM stack / cons cell) */
NI void s9(uintptr_t* a, obj* o){ a[3]=(uintptr_t)o|2; }
NI long t9(void){ uintptr_t* a=calloc(8,sizeof *a); s9(a,mk(9)); asm volatile("":::"memory"); return ((obj*)(a[3]&~(uintptr_t)7))->v; }
/* store via memcpy of pointer bytes, then retag as integer in place */
NI long t10(void){ uintptr_t* a=calloc(2,sizeof *a); obj* o=mk(10); *(obj**)a=o; asm volatile("":::"memory"); a[0]|=1; asm volatile("":::"memory"); return ((obj*)(a[0]&~(uintptr_t)1))->v; }

/* ptr stored, int |= 1 in place, then loaded as a pointer and untagged by ptr arithmetic */
NI long t11(void){ uintptr_t* a=calloc(2,sizeof *a); *(obj**)a=mk(11); asm volatile("":::"memory"); a[0]|=1; asm volatile("":::"memory");
  char* q=*(char**)a; return ((obj*)(q-((uintptr_t)q&7)))->v; }
/* as t11, untag via int mask of a pointer-typed load */
NI long t12(void){ uintptr_t* a=calloc(2,sizeof *a); *(obj**)a=mk(12); asm volatile("":::"memory"); a[0]|=1; asm volatile("":::"memory");
  char* q=*(char**)a; return ((obj*)((uintptr_t)q&~(uintptr_t)7))->v; }
/* pointer-typed union slot tagged by ptr arith, stored and loaded in another function */
NI void s13(union un* u, obj* o){ u->p=(char*)o+2; }
NI long t13(void){ s13(&gun,mk(13)); asm volatile("":::"memory"); char* q=gun.p; long tag=(uintptr_t)q&7; return ((obj*)(q-tag))->v; }
typedef long (*fn)(void);
int main(void){
  int bad=0;
  struct { const char* n; fn f; long want; int works; } T[]={
   {"local tag/untag",t1,1,O2},{"uintptr_t field (int store)",t2,2,0},{"void* field, tag by ptr arith, untag via int",t3,3,1},
   {"void* field, tag/untag by ptr arith",t3b,31,1},{"union written as int, read as int",t4,4,0},{"union written as int, read as ptr",t4b,41,0},
   {"atomic uintptr_t",t5,5,0},{"tagged uintptr_t argument",t6,6,0},{"tagged uintptr_t return",t7,7,0},{"high-bit tag in uintptr_t field",t8,8,0},
   {"heap uintptr_t array",t9,9,0},{"ptr stored, then |= 1 as int in place",t10,10,0},{"...then loaded as ptr, untag by ptr arith",t11,11,1},{"...then loaded as ptr, untag via int mask",t12,12,1},{"ptr slot tagged by ptr arith (tag read as int)",t13,13,1}};
  for(unsigned i=0;i<sizeof T/sizeof *T;i++){
    fflush(stdout); pid_t p=fork();
    if(!p){ long r=T[i].f(); _exit(r==T[i].want?0:3); }
    int st; waitpid(p,&st,0);
    int ok=WIFEXITED(st)&&WEXITSTATUS(st)==0;
    printf("%-48s %s%s\n",T[i].n, ok?"ok":WIFEXITED(st)?"WRONG":"TRAP", ok==T[i].works?"":"  (unexpected)");
    if(ok!=T[i].works) bad=1;
  }
  return bad;
}
