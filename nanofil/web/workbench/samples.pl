/*  Terms nanofil made of a small C file, for the dterm workbench
    (workbench.pl): two items of its syntax (c_parse/2), the IR of one
    function and the first lines of its assembly, each with the AT&T text
    it prints as. From the playground's pipeline (play.pl) on

        struct point { int x, y; };

        static int clamp(int v, int lo, int hi) {
            return v < lo ? lo : v > hi ? hi : v;
        }

    in October 2026. They are samples of shape, not a test: when the IR
    changes they need not follow.
*/

sample_c(decl('sample.c':1, [su(struct, some(point), [field([tspec(int)], dcl(some(x), base, none), none), field([tspec(int)], dcl(some(y), base, none), none)], [])], [])).
sample_c(fundef('sample.c':3, [storage(static), tspec(int)], dcl(some(clamp), func(base, params([param([tspec(int)], dcl(some(v), base, none)), param([tspec(int)], dcl(some(lo), base, none)), param([tspec(int)], dcl(some(hi), base, none))], fixed)), none), at('sample.c':3, block([at('sample.c':4, return(cond(bin(lt, id(v), id(lo)), id(lo), cond(bin(gt, id(v), id(hi)), id(hi), id(v)))))])))).
sample_ir(func(clamp, local, w, [par(w, t(v0)), par(w, t(v2)), par(w, t(v4))], [blk(start, [], [ins(t(v1), p, alloc(4), [c(4)]), ins(t(v3), p, alloc(4), [c(4)]), ins(t(v5), p, alloc(4), [c(4)]), store(w, t(v0), t(v1)), store(w, t(v2), t(v3)), store(w, t(v4), t(v5)), ins(t(v9), w, load(sw), [t(v1)]), ins(t(v10), w, load(sw), [t(v3)]), ins(t(v11), w, cmp(slt, w), [t(v9), t(v10)])], jnz(t(v11), 'L6', 'L7')), blk('L6', [], [ins(t(v12), w, load(sw), [t(v3)])], jmp('L8')), blk('L7', [], [ins(t(v16), w, load(sw), [t(v1)]), ins(t(v17), w, load(sw), [t(v5)]), ins(t(v18), w, cmp(sgt, w), [t(v16), t(v17)])], jnz(t(v18), 'L13', 'L14')), blk('L13', [], [ins(t(v19), w, load(sw), [t(v5)])], jmp('L15')), blk('L14', [], [ins(t(v20), w, load(sw), [t(v1)])], jmp('L15')), blk('L15', [phi(t(v21), w, ['L13'-t(v19), 'L14'-t(v20)])], [], jmp('L8')), blk('L8', [phi(t(v22), w, ['L6'-t(v12), 'L15'-t(v21)])], [], ret(t(v22)))])).
sample_asm(section(text), "\t.text").
sample_asm(p2align(4), "\t.p2align 4").
sample_asm(type(pizlonatedFIP17691_clamp, function), "\t.type pizlonatedFIP17691_clamp, @function").
sample_asm(label(pizlonatedFIP17691_clamp), "pizlonatedFIP17691_clamp:").
sample_asm(ins(push, q, [reg(rbp)]), "\tpushq %rbp").
sample_asm(ins(mov, q, [reg(rsp), reg(rbp)]), "\tmovq %rsp, %rbp").
sample_asm(ins(sub, q, [imm(128), reg(rsp)]), "\tsubq $128, %rsp").
sample_asm(ins(cmp, q, [reg(rsp), mem(0, rdi)]), "\tcmpq %rsp, (%rdi)").
sample_asm(ins(jae, none, [plt(filc_stack_overflow_failure)]), "\tjae filc_stack_overflow_failure@PLT").
sample_asm(ins(mov, q, [reg(rdi), mem(-72, rbp)]), "\tmovq %rdi, -72(%rbp)").
sample_asm(ins(xor, l, [reg(eax), reg(eax)]), "\txorl %eax, %eax").
sample_asm(ins(mov, q, [reg(rax), mem(-104, rbp)]), "\tmovq %rax, -104(%rbp)").
sample_asm(ins(mov, q, [reg(rax), mem(-96, rbp)]), "\tmovq %rax, -96(%rbp)").
sample_asm(ins(mov, q, [reg(rax), mem(-88, rbp)]), "\tmovq %rax, -88(%rbp)").
sample_asm(ins(mov, q, [mem(16, rdi), reg(rax)]), "\tmovq 16(%rdi), %rax").
sample_asm(ins(mov, q, [reg(rax), mem(-120, rbp)]), "\tmovq %rax, -120(%rbp)").
sample_asm(ins(lea, q, [rip('.Lclamp..origin_c'), reg(rax)]), "\tleaq .Lclamp..origin_c(%rip), %rax").
sample_asm(ins(mov, q, [reg(rax), mem(-112, rbp)]), "\tmovq %rax, -112(%rbp)").
sample_asm(ins(lea, q, [mem(-120, rbp), reg(rax)]), "\tleaq -120(%rbp), %rax").
sample_asm(ins(mov, q, [reg(rax), mem(16, rdi)]), "\tmovq %rax, 16(%rdi)").
sample_asm(ins(mov, q, [reg(rdx), mem(-8, rbp)]), "\tmovq %rdx, -8(%rbp)").
sample_asm(ins(mov, q, [reg(rcx), mem(-16, rbp)]), "\tmovq %rcx, -16(%rbp)").
sample_asm(ins(mov, q, [reg(r8), mem(-24, rbp)]), "\tmovq %r8, -24(%rbp)").
sample_asm(label('.Lclamp.start'), ".Lclamp.start:").
sample_asm(ins(movabs, q, [imm(4), reg(rsi)]), "\tmovabsq $4, %rsi").
sample_asm(ins(mov, q, [mem(-72, rbp), reg(rdi)]), "\tmovq -72(%rbp), %rdi").
