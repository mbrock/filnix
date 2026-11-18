(** This file contains checked IR from the linked image. The glibc code
    generator reproduces it from the capture. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term Syntax.
From Glibc Require Import IRNotation.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.
Local Abbreviation a := TAtom.
Local Notation "'t' s" := (Tmp (TAtom s)) (at level 10, s at next level).

Definition hello_image_fn___GI___wmemchr : func :=
  ir_fn{ "export" "__GI___wmemchr"(P %"v0", W %"v2", L %"v4") -> (RClass P) {
  @"start":
    => goto "L6";
  @"L6" [%"pr.4" : L = phi("L45" => %"v57", "start" => %"v4"); %"pr.1" : P = phi("L45" => %"v55", "start" => %"v0")]:
    %"v10" : W = (Cmp Uge L) %"pr.4", #4
    => br %"v10" ? "L7" : "L8";
  @"L7":
    %"chk0" : A = (Check 0 4 Read 1) %"pr.1";
    %"v16" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    %"v18" : W = (Cmp Eq W) %"v16", %"v2"
    => br %"v18" ? "L11" : "L13";
  @"L11":
    => ret %"pr.1";
  @"L13":
    %"v25" = %"pr.1" +p #4;
    %"chk1" : A = (HalfCheck Upper 0 4 Read 1) %"chk0", %"v25";
    %"v26" : W = (RawLoad (LdNarrow Sw) 0) %"chk1";
    %"v28" : W = (Cmp Eq W) %"v26", %"v2"
    => br %"v28" ? "L21" : "L23";
  @"L21":
    %"v30" = %"pr.1" +p #4
    => ret %"v30";
  @"L23":
    %"v36" = %"pr.1" +p #8;
    %"chk2" : A = (HalfCheck Upper 0 4 Read 1) %"chk0", %"v36";
    %"v37" : W = (RawLoad (LdNarrow Sw) 0) %"chk2";
    %"v39" : W = (Cmp Eq W) %"v37", %"v2"
    => br %"v39" ? "L32" : "L34";
  @"L32":
    %"v41" = %"pr.1" +p #8
    => ret %"v41";
  @"L34":
    %"v47" = %"pr.1" +p #12;
    %"chk3" : A = (HalfCheck Upper 0 4 Read 1) %"chk0", %"v47";
    %"v48" : W = (RawLoad (LdNarrow Sw) 0) %"chk3";
    %"v50" : W = (Cmp Eq W) %"v48", %"v2"
    => br %"v50" ? "L43" : "L45";
  @"L43":
    %"v52" = %"pr.1" +p #12
    => ret %"v52";
  @"L45":
    %"v55" = %"pr.1" +p #16;
    %"v57" : L = Sub %"pr.4", #4
    => goto poll "L6";
  @"L8":
    %"v62" : W = (Cmp Ugt L) %"pr.4", #0
    => br %"v62" ? "L58" : "L60";
  @"L58":
    %"chk4" : A = (Check 0 4 Read 1) %"pr.1";
    %"v67" : W = (RawLoad (LdNarrow Sw) 0) %"chk4";
    %"v69" : W = (Cmp Eq W) %"v67", %"v2"
    => br %"v69" ? "L63" : "L65";
  @"L63":
    => ret %"pr.1";
  @"L65":
    %"v73" = %"pr.1" +p #4;
    %"v75" : L = Sub %"pr.4", #1
    => goto "L60";
  @"L60" [%"pr.5" : L = phi("L65" => %"v75", "L8" => %"pr.4"); %"pr.2" : P = phi("L65" => %"v73", "L8" => %"pr.1")]:
    %"v80" : W = (Cmp Ugt L) %"pr.5", #0
    => br %"v80" ? "L76" : "L78";
  @"L76":
    %"chk5" : A = (Check 0 4 Read 1) %"pr.2";
    %"v85" : W = (RawLoad (LdNarrow Sw) 0) %"chk5";
    %"v87" : W = (Cmp Eq W) %"v85", %"v2"
    => br %"v87" ? "L81" : "L83";
  @"L81":
    => ret %"pr.2";
  @"L83":
    %"v91" = %"pr.2" +p #4;
    %"v93" : L = Sub %"pr.5", #1
    => goto "L78";
  @"L78" [%"pr.6" : L = phi("L83" => %"v93", "L60" => %"pr.5"); %"pr.3" : P = phi("L83" => %"v91", "L60" => %"pr.2")]:
    %"v98" : W = (Cmp Ugt L) %"pr.6", #0
    => br %"v98" ? "L94" : "L96";
  @"L94":
    %"chk6" : A = (Check 0 4 Read 1) %"pr.3";
    %"v103" : W = (RawLoad (LdNarrow Sw) 0) %"chk6";
    %"v105" : W = (Cmp Eq W) %"v103", %"v2"
    => br %"v105" ? "L99" : "L96";
  @"L99":
    => ret %"pr.3";
  @"L96":
    => ret #0
} }.

Definition hello_image_fn___wmemcpy : func :=
  ir_fn{ "export" "__wmemcpy"(P %"v0", P %"v2", L %"v4") -> (RClass P) {
  @"start":
    %"v9" : L = Shl %"v4", #2;
    call %"v10" : P = $"__GI_memcpy"(P %"v0", P %"v2", L %"v9")
    => ret %"v10"
} }.

Definition hello_image_fn___wmempcpy : func :=
  ir_fn{ "export" "__wmempcpy"(P %"v0", P %"v2", L %"v4") -> (RClass P) {
  @"start":
    %"v9" : L = Shl %"v4", #2;
    call %"v10" : P = $"__GI_mempcpy"(P %"v0", P %"v2", L %"v9")
    => ret %"v10"
} }.

Definition hello_image_fn___GI___wmemset : func :=
  ir_fn{ "export" "__GI___wmemset"(P %"v0", W %"v2", L %"v4") -> (RClass P) {
  @"start":
    => goto "L8";
  @"L8" [%"pr.2" : P = phi("L9" => %"v26", "start" => %"v0"); %"pr.1" : L = phi("L9" => %"v28", "start" => %"v4")]:
    %"v12" : W = (Cmp Uge L) %"pr.1", #4
    => br %"v12" ? "L9" : "L10";
  @"L9":
    %"chk0" : A = (Check 0 4 Write 1) %"pr.2";
    store Ww [%"chk0" + 0] <- %"v2";
    %"v17" = %"pr.2" +p #4;
    %"chk1" : A = (HalfCheck Upper 0 4 Write 1) %"chk0", %"v17";
    store Ww [%"chk1" + 0] <- %"v2";
    %"v20" = %"pr.2" +p #8;
    %"chk2" : A = (HalfCheck Upper 0 4 Write 1) %"chk0", %"v20";
    store Ww [%"chk2" + 0] <- %"v2";
    %"v23" = %"pr.2" +p #12;
    %"chk3" : A = (HalfCheck Upper 0 4 Write 1) %"chk0", %"v23";
    store Ww [%"chk3" + 0] <- %"v2";
    %"v26" = %"pr.2" +p #16;
    %"v28" : L = Sub %"pr.1", #4
    => goto poll "L8";
  @"L10":
    %"v33" : W = (Cmp Ugt L) %"pr.1", #0
    => br %"v33" ? "L29" : "L31";
  @"L29":
    %"chk4" : A = (Check 0 4 Write 1) %"pr.2";
    store Ww [%"chk4" + 0] <- %"v2";
    %"v41" : W = (Cmp Ugt L) %"pr.1", #1
    => br %"v41" ? "L37" : "L31";
  @"L37":
    %"v43" = %"pr.2" +p #4;
    %"chk5" : A = (HalfCheck Upper 0 4 Write 1) %"chk4", %"v43";
    store Ww [%"chk5" + 0] <- %"v2";
    %"v49" : W = (Cmp Ugt L) %"pr.1", #2
    => br %"v49" ? "L45" : "L31";
  @"L45":
    %"v51" = %"pr.2" +p #8;
    %"chk6" : A = (HalfCheck Upper 0 4 Write 1) %"chk4", %"v51";
    store Ww [%"chk6" + 0] <- %"v2"
    => goto "L31";
  @"L31":
    => ret %"v0"
} }.

Definition hello_image_fn___wmemmove : func :=
  ir_fn{ "export" "__wmemmove"(P %"v0", P %"v2", L %"v4") -> (RClass P) {
  @"start":
    %"v9" : L = Shl %"v4", #2;
    call %"v10" : P = $"__GI_memmove"(P %"v0", P %"v2", L %"v9")
    => ret %"v10"
} }.
