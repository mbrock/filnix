:- use_module('flags.pl', []).
:- use_module('x86-flags.pl', []).
:- use_module('x86-cfg.pl', []).
:- use_module('x86_64.pl', []).
:- initialization(main).
main :-
    write('#include <stdint.h>'),nl,
    write('int main(void) {'),nl,
    write('  uint64_t sp_b0_r_rax=123, sp_b0_r_rdx=456;'),nl,
    write('  unsigned char left=7, right=11;'),nl,
    write('  const unsigned char *sp_b0_r_rdi=&left, *sp_b0_r_rsi=&right;'),nl,
    % Execute an actual cycle of assignments. Both address and capability
    % must survive the swap before any destination is overwritten.
    sp_x86_cfg:emit_edge(edge(0,[
        set(param(0,reg(rdi)),pointer,param(0,reg(rsi))),
        set(param(0,reg(rsi)),pointer,param(0,reg(rdi))),
        set(param(0,reg(rax)),integer,param(0,reg(rdx))),
        set(param(0,reg(rdx)),integer,param(0,reg(rax)))])),
    write('sp_block0:'),nl,
    write('  if (*sp_b0_r_rdi != 11 || *sp_b0_r_rsi != 7) return 1;'),nl,
    write('  if (sp_b0_r_rax != 456 || sp_b0_r_rdx != 123) return 2;'),nl,
    write('  return 0;'),nl,write('}'),nl,halt.
