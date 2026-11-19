(** This file defines checked IR from glibc’s `stdio-common/wprintf_function_invoke.os` object.
    The glibc code generator reproduces this file. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term Syntax.
From Glibc Require Import IRNotation.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.
Local Abbreviation a := TAtom.
Local Notation "'t' s" := (Tmp (TAtom s)) (at level 10, s at next level).

Definition fn___wprintf_function_invoke : func :=
  ir_fn{ "export" "__wprintf_function_invoke"(P %"v0", P %"v2", P %"v4", L %"v6", P %"v8") -> (RClass W) {
  @"start":
    %"v10" : P = (Alloc 8) #32;
    %"v52" : P = (Alloc 8) #464;
    %"v19" : W = (Cmp Ule L) %"v6", #4
    => br %"v19" ? "L14" : "L13";
  @"L13":
    call %"v21" : P = $"calloc"(L %"v6", L #8);
    %"v26" : L = Ptoi %"v21";
    %"v27" : L = Ptoi #0;
    %"v28" : W = (Cmp Eq L) %"v26", %"v27"
    => br %"v28" ? "L22" : "L14";
  @"L22":
    => ret #4294967295;
  @"L14" [%"pr.1" : P = phi("start" => %"v10", "L13" => %"v21")]:
    => goto "L32";
  @"L32" [%"pr.2" : W = phi("L14" => #0, "L33" => %"v51")]:
    %"v38" : L = (Ext Uw) %"pr.2";
    %"v39" : W = (Cmp Ult L) %"v38", %"v6"
    => br %"v39" ? "L33" : "L35";
  @"L33":
    %"v43" : L = Shl %"v38", #3;
    %"v44" = %"pr.1" +p %"v43";
    %"v48" : L = Shl %"v38", #4;
    %"v49" = %"v4" +p %"v48";
    %"chk0" : A = (Check 0 8 Write 8) %"v44";
    store.ptr [%"chk0" + 0] <- %"v49";
    %"v51" : W = Add %"pr.2", #1
    => goto poll "L32";
  @"L35":
    call void $"__wprintf_buffer_as_file_init"(P %"v52", P %"v0");
    %"chk1" : F = CheckFunction %"v2";
    rawcall %"v59" : W = %"chk1"(P %"v52", P %"v8", P %"pr.1");
    call %"v63" : W = $"__wprintf_buffer_as_file_terminate"(P %"v52");
    %"v64" : W = (Ext Ub) %"v63";
    %"v65" : W = (Cmp Eq W) %"v64", #0
    => br %"v65" ? "L62" : "L61";
  @"L61":
    => goto "L62";
  @"L62" [%"pr.3" : W = phi("L61" => %"v59", "L35" => #4294967295)]:
    %"v71" : L = Ptoi %"pr.1";
    %"v72" : L = Ptoi %"v10";
    %"v73" : W = (Cmp Ne L) %"v71", %"v72"
    => br %"v73" ? "L67" : "L69";
  @"L67":
    call void $"free"(P %"pr.1")
    => goto "L69";
  @"L69":
    => ret %"pr.3"
} }.
