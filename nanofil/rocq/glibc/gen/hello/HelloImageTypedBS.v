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

Definition hello_image_fn_glibc_dcigettext'23__bswap_32 : func :=
  ir_fn{ "local" "glibc_dcigettext#__bswap_32"(W %"v0") -> (RClass W) {
  @"start":
    %"v3" : W = And %"v0", #4278190080;
    %"v4" : W = Shr %"v3", #24;
    %"v6" : W = And %"v0", #16711680;
    %"v7" : W = Shr %"v6", #8;
    %"v8" : W = Or %"v4", %"v7";
    %"v10" : W = And %"v0", #65280;
    %"v11" : W = Shl %"v10", #8;
    %"v12" : W = Or %"v8", %"v11";
    %"v14" : W = And %"v0", #255;
    %"v15" : W = Shl %"v14", #24;
    %"v16" : W = Or %"v12", %"v15"
    => ret %"v16"
} }.

Definition hello_image_fn___GI_bsearch : func :=
  ir_fn{ "export" "__GI_bsearch"(P %"v0", P %"v2", L %"v4", L %"v6", P %"v8") -> (RClass P) {
  @"start":
    => goto "L12";
  @"L12" [%"pr.3" : L = phi("L36" => %"v45", "start" => %"v4"); %"pr.1" : P = phi("L36" => %"pr.2", "start" => %"v2")]:
    %"v16" : W = (Cmp Ne L) %"pr.3", #0
    => br %"v16" ? "L13" : "L14";
  @"L13":
    %"v19" : L = Shr %"pr.3", #1;
    %"v21" : L = Mul %"v19", %"v6";
    %"v22" = %"pr.1" +p %"v21";
    %"chk0" : F = CheckFunction %"v8";
    rawcall %"v26" : W = %"chk0"(P %"v0", P %"v22");
    %"v31" : W = (Cmp Eq W) %"v26", #0
    => br %"v31" ? "L27" : "L29";
  @"L27":
    => ret %"v22";
  @"L29":
    %"v38" : W = (Cmp Sgt W) %"v26", #0
    => br %"v38" ? "L34" : "L36";
  @"L34":
    %"v41" = %"v22" +p %"v6";
    %"v43" : L = Sub %"pr.3", #1
    => goto "L36";
  @"L36" [%"pr.4" : L = phi("L34" => %"v43", "L29" => %"pr.3"); %"pr.2" : P = phi("L34" => %"v41", "L29" => %"pr.1")]:
    %"v45" : L = Shr %"pr.4", #1
    => goto poll "L12";
  @"L14":
    => ret #0
} }.
