:- module(sp_x86_flags, [emit_helpers/0, emit_values/6, emit_condition/1]).

% Unsigned bit-pattern arithmetic avoids signed C overflow. Undefined flags
% have no usable IR value even though the helper returns a deterministic word.
:- use_module(library(lists)).
emit_helpers :- maplist(line,[
  'static uint32_t sp_flag_values(unsigned kind, unsigned width, uint64_t a, uint64_t b) {',
  '  if (width != 32 && width != 64) __builtin_trap();',
  '  uint64_t mask = width == 64 ? UINT64_MAX : UINT32_MAX;',
  '  uint64_t sign = UINT64_C(1) << (width - 1);',
  '  uint64_t r;',
  '  unsigned cf = 0, of = 0, af = 0;',
  '  a &= mask;',
  '  b &= mask;',
  '  if (kind == 0) {',
  '    r = (a + b) & mask;',
  '    cf = r < a;',
  '    of = ((~(a ^ b) & (a ^ r)) & sign) != 0;',
  '    af = ((a ^ b ^ r) & 16) != 0;',
  '  } else if (kind == 1) {',
  '    r = (a - b) & mask;',
  '    cf = a < b;',
  '    of = (((a ^ b) & (a ^ r)) & sign) != 0;',
  '    af = ((a ^ b ^r) & 16) != 0;',
  '  } else if (kind == 2) r = a & b;',
  '  else if (kind == 3) r = a | b;',
  '  else if (kind == 4) r = a ^ b;',
  '  else if (kind == 5 || kind == 6) {',
  '    if (b == 0 || b >= width) __builtin_trap();',
  '    if (kind == 5) {',
  '      r = (a << b) & mask;',
  '      cf = (a >> (width - b)) & 1;',
  '      if (b == 1) of = ((r & sign) != 0) ^ cf;',
  '    } else {',
  '      r = a >> b;',
  '      cf = (a >> (b - 1)) & 1;',
  '      if (b == 1) of = (a & sign) != 0;',
  '    }',
  '  } else { __builtin_trap(); }',
  '  unsigned pf = (0x9669u >> ((r ^ (r >> 4)) & 15)) & 1;',
  '  return cf | (pf << 2) | (af << 4) | ((r == 0) << 6)',
  '    | (((r & sign) != 0) << 7) | (of << 11);',
  '}']).
line(X) :- write(X),nl.
kind(add,0). kind(sub,1). kind(and,2). kind(or,3). kind(xor,4). kind(shl,5). kind(shr,6).
emit_values(N,K,W,A,B,L) :-
    kind(K,Code),sp_x86_64:origin(L),
    format('  uint32_t flags~d = sp_flag_values(~d, ~d, ',[N,Code,W]),
    sp_x86_64:value(A),write(', '),sp_x86_64:value(B),write(');'),nl.
emit_condition(truth(V)) :- sp_x86_64:value(V).
emit_condition(not(A)) :- write('!('),emit_condition(A),write(')').
emit_condition(either(A,B)) :- write('('),emit_condition(A),write(' || '),emit_condition(B),write(')').
emit_condition(different(A,B)) :- write('('),emit_condition(A),write(' != '),emit_condition(B),write(')').
