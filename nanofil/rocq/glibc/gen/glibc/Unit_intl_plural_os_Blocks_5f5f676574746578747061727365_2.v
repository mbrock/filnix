(** These blocks form part of one captured function.
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

Definition fn___gettextparse'blocks2 : list block :=
  [ir_blk{ @"L636":
    %"v657" : P = Copy $"glibc_plural#yytable";
    %"v659" : L = (Ext Sw) %"v635";
    %"v660" = %"v657" +p %"v659";
    %"chk152" : A = (Check 0 1 Read 1) %"v660";
    %"v661" : W = (RawLoad (LdNarrow Sb) 0) %"chk152";
    %"v666" : W = (Cmp Sgt W) %"v661", #0
    => br %"v666" ? "L621" : "L629" };
  ir_blk{ @"L629":
    %"v673" : L = Ptoi %"pr.35";
    %"v674" : L = Ptoi %"pr.28";
    %"v675" : W = (Cmp Eq L) %"v673", %"v674"
    => br %"v675" ? "L695" : "L670" };
  ir_blk{ @"L670":
    %"v677" : P = Copy $"glibc_plural#str.128";
    %"v678" : P = Copy $"glibc_plural#yystos";
    %"v681" = %"v678" +p %"v624";
    %"chk153" : A = (Check 0 1 Read 1) %"v681";
    %"v682" : W = (RawLoad (LdNarrow Sb) 0) %"chk153";
    %"iw_14.v14" : L = Ptoi %"v677";
    %"iw_14.v16" : W = (Cmp Eq L) %"iw_14.v14", #0
    => br %"iw_14.v16" ? "iw_14.L10" : "iw_14.join" };
  ir_blk{ @"iw_14.L10":
    %"iw_14.v17" : P = Copy $"glibc_plural#str.124"
    => goto "iw_14.join" };
  ir_blk{ @"iw_14.join":
    (Flight (a "v686") Sub [(FAddress (t "pr.45")); (FValue (Const 8))] (LowerOf (t "pr.45")));
    (Flight (a "v688") Sub [(FAddress (t "pr.35")); (FValue (Const 1))] (LowerOf (t "pr.35")));
    %"chk154" : A = (Check 0 1 Read 1) %"v688";
    %"v690" : W = (RawLoad (LdNarrow Sb) 0) %"chk154"
    => goto poll "L618" };
  ir_blk{ @"L621":
    %"v692" = %"pr.45" +p #8;
    %"chk155" : A = (CheckLocal (a "v3") 0 8 Read 8);
    %"v693" : P = (RawLoadPointer 0 local_load_effects) %"chk155";
    %"chk156" : A = (Check 0 8 Write 8) %"v692";
    store.ptr [%"chk156" + 0] <- %"v693"
    => goto poll "L25" };
  ir_blk{ @"L66":
    %"v697" : P = Copy $"glibc_plural#str.129"
    => goto "L695" };
  ir_blk{ @"L695" [%"pr.55" : W = phi("L45" => %"pr.53", "L132" => %"pr.53", "L300" => %"v289", "L585" => %"pr.53", "L629" => %"pr.53", "L66" => %"pr.53"); %"pr.49" : W = phi("L45" => #0, "L132" => #1, "L300" => #1, "L585" => #1, "L629" => #1, "L66" => #2); %"pr.36" : P = phi("L45" => %"pr.34", "L132" => %"v141", "L300" => %"pr.34", "L585" => %"pr.34", "L629" => %"pr.35", "L66" => %"pr.32"); %"pr.29" : P = phi("L45" => %"pr.28", "L132" => %"v83", "L300" => %"pr.28", "L585" => %"pr.28", "L629" => %"pr.28", "L66" => %"pr.27"); %"pr.12" : W = phi("L45" => %"pr.6", "L132" => %"pr.6", "L300" => %"pr.9", "L585" => %"pr.2", "L629" => %"pr.5", "L66" => %"pr.6")]:
    %"v703" : W = (Cmp Ne W) %"pr.12", #4294967294
    => br %"v703" ? "L698" : "L700" };
  ir_blk{ @"L698":
    %"v708" : W = (Cmp Sge W) %"pr.12", #0
    => br %"v708" ? "L709" : "L710" };
  ir_blk{ @"L709":
    %"v712" : W = (Cmp Sle W) %"pr.12", #262
    => goto "L710" };
  ir_blk{ @"L710" [%"v714" : W = phi("L698" => #0, "L709" => %"v712")]:
    => br %"v714" ? "L704" : "L706" };
  ir_blk{ @"L704":
    %"v715" : P = Copy $"glibc_plural#yytranslate";
    %"v717" : L = (Ext Sw) %"pr.12";
    %"v718" = %"v715" +p %"v717";
    %"chk157" : A = (Check 0 1 Read 1) %"v718";
    %"v719" : W = (RawLoad (LdNarrow Sb) 0) %"chk157"
    => goto "L706" };
  ir_blk{ @"L706":
    %"v721" : P = Copy $"glibc_plural#str.130";
    %"iw_16.v14" : L = Ptoi %"v721";
    %"iw_16.v16" : W = (Cmp Eq L) %"iw_16.v14", #0
    => br %"iw_16.v16" ? "iw_16.L10" : "L700" };
  ir_blk{ @"iw_16.L10":
    %"iw_16.v17" : P = Copy $"glibc_plural#str.124"
    => goto "L700" };
  ir_blk{ @"L700":
    %"v726" : L = (Ext Sw) %"pr.55";
    (Flight (a "v732") Sub [(FAddress (t "pr.36")); (FValue (t "v726"))] (LowerOf (t "pr.36")))
    => goto "L733" };
  ir_blk{ @"L733" [%"pr.37" : P = phi("L700" => %"v732", "iw_17.join" => %"v753")]:
    %"v738" : L = Ptoi %"pr.37";
    %"v739" : L = Ptoi %"pr.29";
    %"v740" : W = (Cmp Ne L) %"v738", %"v739"
    => br %"v740" ? "L734" : "L735" };
  ir_blk{ @"L734":
    %"v741" : P = Copy $"glibc_plural#str.131";
    %"v742" : P = Copy $"glibc_plural#yystos";
    %"chk158" : A = (Check 0 1 Read 1) %"pr.37";
    %"v744" : W = (RawLoad (LdNarrow Sb) 0) %"chk158";
    %"v745" : L = (Ext Sw) %"v744";
    %"v746" = %"v742" +p %"v745";
    %"chk159" : A = (Check 0 1 Read 1) %"v746";
    %"v747" : W = (RawLoad (LdNarrow Sb) 0) %"chk159";
    %"iw_17.v14" : L = Ptoi %"v741";
    %"iw_17.v16" : W = (Cmp Eq L) %"iw_17.v14", #0
    => br %"iw_17.v16" ? "iw_17.L10" : "iw_17.join" };
  ir_blk{ @"iw_17.L10":
    %"iw_17.v17" : P = Copy $"glibc_plural#str.124"
    => goto "iw_17.join" };
  ir_blk{ @"iw_17.join":
    (Flight (a "v753") Sub [(FAddress (t "pr.37")); (FValue (Const 1))] (LowerOf (t "pr.37")))
    => goto poll "L733" };
  ir_blk{ @"L735":
    %"v759" : L = Ptoi %"v10";
    %"v760" : W = (Cmp Ne L) %"v739", %"v759"
    => br %"v760" ? "L754" : "L756" };
  ir_blk{ @"L754":
    call void $"free"(P %"pr.29")
    => goto "L756" };
  ir_blk{ @"L756":
    => ret %"pr.49" }].
