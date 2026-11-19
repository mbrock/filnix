(** This file defines checked IR from glibc’s `posix/sched_cpucount.os` object.
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

Definition fn___GI___sched_cpucount : func :=
  ir_fn{ "export" "__GI___sched_cpucount"(L %"v0", P %"v2") -> (RClass W) {
  @"start":
    => goto "L6";
  @"L6" [%"pr.2" : W = phi("iw_1.join" => %"v25", "start" => #0); %"pr.1" : W = phi("iw_1.join" => %"v23", "start" => #0)]:
    %"v12" : L = Shr %"v0", #3;
    %"v13" : L = (Ext Sw) %"pr.2";
    %"v14" : W = (Cmp Ult L) %"v13", %"v12"
    => br %"v14" ? "L7" : "L9";
  @"L7":
    %"v19" : L = Shl %"v13", #3;
    %"v20" = %"v2" +p %"v19";
    %"chk0" : A = (Check 0 8 Read 1) %"v20";
    %"v21" : L = (RawLoad LdL 0) %"chk0"
    => goto "iw_1.L3";
  @"iw_1.L3" [%"iw_1.pr.2" : W = phi("iw_1.L4" => %"iw_1.v14", "L7" => #0); %"iw_1.pr.1" : L = phi("iw_1.L4" => %"iw_1.v12", "L7" => %"v21")]:
    %"iw_1.v8" : W = (Cmp Ne L) %"iw_1.pr.1", #0
    => br %"iw_1.v8" ? "iw_1.L4" : "iw_1.join";
  @"iw_1.L4":
    %"iw_1.v11" : L = Sub %"iw_1.pr.1", #1;
    %"iw_1.v12" : L = And %"iw_1.pr.1", %"iw_1.v11";
    %"iw_1.v14" : W = Add %"iw_1.pr.2", #1
    => goto poll "iw_1.L3";
  @"iw_1.join":
    %"v23" : W = Add %"pr.1", %"iw_1.pr.2";
    %"v25" : W = Add %"pr.2", #1
    => goto poll "L6";
  @"L9":
    => ret %"pr.1"
} }.
