:- module(sp_target, [emit/2]).
% Explicit architecture dispatch; no fallback to another target's semantics.
emit(x86_64, Functions) :- !, sp_x86_64:emit_c(Functions).
emit(arm64, _) :- !, throw(error(unsupported_target(aarch64))).
emit(aarch64, _) :- !, throw(error(unsupported_target(aarch64))).
emit(Other, _) :- throw(error(unknown_target(Other))).
