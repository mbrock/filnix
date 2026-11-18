(** This file contains checked IR from the linked image. The glibc code
    generator reproduces it from the capture. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term Syntax.
From Glibc Require Import HelloImageTypedQUBlocks28x1 HelloImageTypedQUBlocks28x2 IRNotation.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.
Local Abbreviation a := TAtom.
Local Notation "'t' s" := (Tmp (TAtom s)) (at level 10, s at next level).

Definition hello_image_fn_quotearg'23quotearg_buffer_restyled : func :=
  ir_fn{ "local" "quotearg#quotearg_buffer_restyled"(P %"v0", L %"v2", P %"v4", L %"v6", W %"v8", W %"v10", P %"v12", P %"v14", P %"v16") -> (RClass L) blocks (hello_image_fn_quotearg'23quotearg_buffer_restyled'blocks1 ++ hello_image_fn_quotearg'23quotearg_buffer_restyled'blocks2) }.

Definition hello_image_fn_quotearg_char_mem : func :=
  ir_fn{ "export" "quotearg_char_mem"(P %"v0", L %"v2", W %"v4") -> (RClass P) {
  @"start":
    %"v6" : P = (Alloc 8) #56;
    %"v7" : P = Copy $"quotearg#default_quoting_options";
    call void $"zmemmove"(P %"v6", P %"v7", L #56);
    %"v8" : W = (Ext Sb) %"v4";
    call %"v9" : W = $"set_char_quoting"(P %"v6", W %"v8", W #1);
    %"iw_1.v47" : P = (Alloc 8) #8;
    call %"iw_1.v9" : P = $"__errno_location"();
    %"chk0" : A = (Check 0 4 Read 1) %"iw_1.v9";
    %"iw_1.v10" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    %"iw_1.v12" : P = Copy $"quotearg#slotvec";
    %"chk1" : A = (Check 0 8 Read 8) %"iw_1.v12";
    %"iw_1.v13" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"iw_1.v36" : P = Copy $"quotearg#nslots";
    %"chk2" : A = (Check 0 4 Read 1) %"iw_1.v36";
    %"iw_1.v37" : W = (RawLoad (LdNarrow Sw) 0) %"chk2";
    %"iw_1.v39" : W = (Cmp Sle W) %"iw_1.v37", #0
    => br %"iw_1.v39" ? "iw_1.L33" : "iw_1.L35";
  @"iw_1.L33":
    %"iw_1.v42" : P = Copy $"quotearg#slotvec0";
    %"iw_1.v43" : L = Ptoi %"iw_1.v13";
    %"iw_1.v44" : L = Ptoi %"iw_1.v42";
    %"iw_1.v45" : W = (Cmp Eq L) %"iw_1.v43", %"iw_1.v44";
    %"iw_1.v48" : P = Copy $"quotearg#nslots";
    %"chk3" : A = (Check 0 4 Read 1) %"iw_1.v48";
    %"iw_1.v49" : W = (RawLoad (LdNarrow Sw) 0) %"chk3";
    %"iw_1.v50" : L = (Ext Sw) %"iw_1.v49";
    %"chk4" : A = (Check 0 8 Write 1) %"iw_1.v47";
    store Wl [%"chk4" + 0] <- %"iw_1.v50";
    %"iw_1.v51" : P = Copy $"quotearg#slotvec"
    => br %"iw_1.v45" ? "iw_1.L54" : "iw_1.L53";
  @"iw_1.L53":
    => goto "iw_1.L54";
  @"iw_1.L54" [%"iw_1.v57" : P = phi("iw_1.L53" => %"iw_1.v13", "iw_1.L33" => #0)]:
    %"iw_1.v59" : P = Copy $"quotearg#nslots";
    %"chk5" : A = (Check 0 4 Read 1) %"iw_1.v59";
    %"iw_1.v60" : W = (RawLoad (LdNarrow Sw) 0) %"chk5";
    %"iw_1.v61" : W = Sub #0, %"iw_1.v60";
    %"iw_1.v62" : W = Add %"iw_1.v61", #1;
    %"iw_1.v63" : L = (Ext Sw) %"iw_1.v62";
    call %"iw_1.v66" : P = $"xpalloc"(P %"iw_1.v57", P %"iw_1.v47", L %"iw_1.v63", L #2147483647, L #16);
    %"chk6" : A = (Check 0 8 Write 8) %"iw_1.v51";
    store.ptr [%"chk6" + 0] <- %"iw_1.v66"
    => br %"iw_1.v45" ? "iw_1.L67" : "iw_1.L69";
  @"iw_1.L67":
    %"iw_1.v72" : P = Copy $"quotearg#slotvec0";
    %"chk7" : A = (Check 0 8 Read 1) %"iw_1.v72";
    %"iw_1.v73" : L = (RawLoad LdL 0) %"chk7";
    %"chk8" : A = (Check 0 8 Write 1) %"iw_1.v66";
    store Wl [%"chk8" + 0] <- %"iw_1.v73";
    %"iw_1.v74" = %"iw_1.v72" +p #8;
    %"iw_1.v75" = %"iw_1.v66" +p #8;
    %"chk9" : A = (HalfCheck Upper 0 8 Read 8) %"chk7", %"iw_1.v74";
    %"iw_1.v76" : P = (RawLoadPointer 0 load_effects) %"chk9";
    %"chk10" : A = (HalfCheck Upper 0 8 Write 8) %"chk8", %"iw_1.v75";
    store.ptr [%"chk10" + 0] <- %"iw_1.v76"
    => goto "iw_1.L69";
  @"iw_1.L69":
    %"iw_1.v78" : P = Copy $"quotearg#nslots";
    %"chk11" : A = (Check 0 4 Read 1) %"iw_1.v78";
    %"iw_1.v79" : W = (RawLoad (LdNarrow Sw) 0) %"chk11";
    %"iw_1.v80" : L = (Ext Sw) %"iw_1.v79";
    %"iw_1.v81" : L = Shl %"iw_1.v80", #4;
    %"iw_1.v82" = %"iw_1.v66" +p %"iw_1.v81";
    %"chk12" : A = (Renew 0 8 Read 1) %"chk4", %"iw_1.v47";
    %"iw_1.v83" : L = (RawLoad LdL 0) %"chk12";
    %"iw_1.v84" : P = Copy $"quotearg#nslots";
    %"chk13" : A = (Check 0 4 Read 1) %"iw_1.v84";
    %"iw_1.v85" : W = (RawLoad (LdNarrow Sw) 0) %"chk13";
    %"iw_1.v86" : L = (Ext Sw) %"iw_1.v85";
    %"iw_1.v87" : L = Sub %"iw_1.v83", %"iw_1.v86";
    %"iw_1.v88" : L = Shl %"iw_1.v87", #4;
    call %"iw_1.v89" : P = $"memset"(P %"iw_1.v82", W #0, L %"iw_1.v88");
    %"iw_1.v90" : P = Copy $"quotearg#nslots";
    %"chk14" : A = (Renew 0 8 Read 1) %"chk4", %"iw_1.v47";
    %"iw_1.v91" : L = (RawLoad LdL 0) %"chk14";
    %"chk15" : A = (Check 0 4 Write 1) %"iw_1.v90";
    store Ww [%"chk15" + 0] <- %"iw_1.v91"
    => goto "iw_1.L35";
  @"iw_1.L35" [%"iw_1.pr.1" : P = phi("iw_1.L69" => %"iw_1.v66", "start" => %"iw_1.v13")]:
    %"chk16" : A = (Check 0 8 Read 1) %"iw_1.pr.1";
    %"iw_1.v98" : L = (RawLoad LdL 0) %"chk16";
    %"iw_1.v105" = %"iw_1.pr.1" +p #8;
    %"chk17" : A = (HalfCheck Upper 0 8 Read 8) %"chk16", %"iw_1.v105";
    %"iw_1.v106" : P = (RawLoadPointer 0 load_effects) %"chk17";
    %"iw_1.v109" = %"v6" +p #4;
    %"chk18" : A = (Check 0 4 Read 1) %"iw_1.v109";
    %"iw_1.v110" : W = (RawLoad (LdNarrow Sw) 0) %"chk18";
    %"iw_1.v111" : W = Or %"iw_1.v110", #1;
    %"chk19" : A = (HalfCheck Lower 0 4 Read 1) %"chk18", %"v6";
    %"iw_1.v118" : W = (RawLoad (LdNarrow Uw) 0) %"chk19";
    %"iw_1.v121" = %"v6" +p #8;
    %"iw_1.v123" = %"v6" +p #40;
    %"chk20" : A = (HalfCheck Upper 0 8 Read 8) %"chk18", %"iw_1.v123";
    %"iw_1.v124" : P = (RawLoadPointer 0 load_effects) %"chk20";
    %"iw_1.v126" = %"v6" +p #48;
    %"chk21" : A = (HalfCheck Upper 0 8 Read 8) %"chk18", %"iw_1.v126";
    %"iw_1.v127" : P = (RawLoadPointer 0 load_effects) %"chk21";
    call %"iw_1.v128" : L = $"quotearg#quotearg_buffer_restyled"(P %"iw_1.v106", L %"iw_1.v98", P %"v0", L %"v2", W %"iw_1.v118", W %"iw_1.v111", P %"iw_1.v121", P %"iw_1.v124", P %"iw_1.v127");
    %"iw_1.v134" : W = (Cmp Ule L) %"iw_1.v98", %"iw_1.v128"
    => br %"iw_1.v134" ? "iw_1.L129" : "iw_1.L131";
  @"iw_1.L129":
    %"iw_1.v141" : L = Add %"iw_1.v128", #1;
    %"chk22" : A = (Renew 0 8 Write 1) %"chk16", %"iw_1.pr.1";
    store Wl [%"chk22" + 0] <- %"iw_1.v141";
    %"iw_1.v146" : P = Copy $"quotearg#slot0";
    %"iw_1.v147" : L = Ptoi %"iw_1.v106";
    %"iw_1.v148" : L = Ptoi %"iw_1.v146";
    %"iw_1.v149" : W = (Cmp Ne L) %"iw_1.v147", %"iw_1.v148"
    => br %"iw_1.v149" ? "iw_1.L142" : "iw_1.L144";
  @"iw_1.L142":
    call void $"free"(P %"iw_1.v106")
    => goto "iw_1.L144";
  @"iw_1.L144":
    %"iw_1.v156" = %"iw_1.pr.1" +p #8;
    call %"iw_1.v158" : P = $"xcharalloc"(L %"iw_1.v141");
    %"chk23" : A = (Renew 0 8 Write 8) %"chk17", %"iw_1.v156";
    store.ptr [%"chk23" + 0] <- %"iw_1.v158";
    %"chk24" : A = (Renew 0 4 Read 1) %"chk19", %"v6";
    %"iw_1.v164" : W = (RawLoad (LdNarrow Uw) 0) %"chk24";
    %"iw_1.v167" = %"v6" +p #8;
    %"iw_1.v169" = %"v6" +p #40;
    %"chk25" : A = (Renew 0 8 Read 8) %"chk20", %"iw_1.v169";
    %"iw_1.v170" : P = (RawLoadPointer 0 load_effects) %"chk25";
    %"iw_1.v172" = %"v6" +p #48;
    %"chk26" : A = (Renew 0 8 Read 8) %"chk21", %"iw_1.v172";
    %"iw_1.v173" : P = (RawLoadPointer 0 load_effects) %"chk26";
    call %"iw_1.v174" : L = $"quotearg#quotearg_buffer_restyled"(P %"iw_1.v158", L %"iw_1.v141", P %"v0", L %"v2", W %"iw_1.v164", W %"iw_1.v111", P %"iw_1.v167", P %"iw_1.v170", P %"iw_1.v173")
    => goto "iw_1.L131";
  @"iw_1.L131" [%"iw_1.pr.2" : P = phi("iw_1.L144" => %"iw_1.v158", "iw_1.L35" => %"iw_1.v106")]:
    call %"iw_1.v175" : P = $"__errno_location"();
    %"chk27" : A = (Check 0 4 Write 1) %"iw_1.v175";
    store Ww [%"chk27" + 0] <- %"iw_1.v10"
    => ret %"iw_1.pr.2"
} }.

Definition hello_image_fn_quotearg_char : func :=
  ir_fn{ "export" "quotearg_char"(P %"v0", W %"v2") -> (RClass P) {
  @"start":
    %"v5" : W = (Ext Sb) %"v2";
    call %"v6" : P = $"quotearg_char_mem"(P %"v0", L #18446744073709551615, W %"v5")
    => ret %"v6"
} }.

Definition hello_image_fn_quotearg_colon : func :=
  ir_fn{ "export" "quotearg_colon"(P %"v0") -> (RClass P) {
  @"start":
    call %"v3" : P = $"quotearg_char"(P %"v0", W #58)
    => ret %"v3"
} }.
