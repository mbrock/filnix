(** These checked bodies implement printf-buffer operations in user-glibc 2.44.
    They retain the source's failure paths and calls into stream operations;
    decoding these bodies does not establish contracts for those calls.

    rocq/glibc/stdio/buffer-code.sh reproduces these terms from the pinned
    capture with gallina.pl. Do not edit. *)

From Glibc Require Import GlibcTactics.
From Stdlib Require Import String ZArith List Ascii.
From Glibc Require Import CodePrelude.
From Nanofil Require Import CaptureNotation.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

(** This term contains the selected checked function bodies. *)
Definition printf_buffer_io_term : term :=
  TApp "module" [TList [
    cap_fn{ "export" "__printf_buffer_write" [param "p" %"v0"; param "p" %"v2"; param "l" %"v4"] -> "void"
      {
        @"start":
          %"iw_1.v3" = %"v0" +p #32;
          %"chk0" : "a" = op "check"(int 0, int 4, "read", int 1) %"iw_1.v3";
          %"iw_1.v4" : "w" = op "raw_load"("uw", int 0) %"chk0";
          %"iw_1.v5" : "w" = op "cmp"("eq", "w") %"iw_1.v4", #0
          => br %"iw_1.v5" ? "L6" : "L15";
        @"L6":
          => ret void;
        @"L15" [phi %"pr.2" : "l" = ("L68" => %"v89", "start" => %"v4"); phi %"pr.1" : "p" = ("L68" => %"v86", "start" => %"v2")]:
          %"v19" : "w" = op "cmp"("ugt", "l") %"pr.2", #0
          => br %"v19" ? "L16" : "L17";
        @"L16":
          %"v24" = %"v0" +p #8;
          %"chk1" : "a" = op "half_check"("lower", int 0, int 8, "read", int 8) %"chk0", %"v24";
          %"v25" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk1";
          %"v27" = %"v0" +p #16;
          %"chk2" : "a" = op "half_check"("lower", int 0, int 8, "read", int 8) %"chk0", %"v27";
          %"v28" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk2";
          %"v29" : "l" = "ptoi" %"v25";
          %"v30" : "l" = "ptoi" %"v28";
          %"v31" : "w" = op "cmp"("eq", "l") %"v29", %"v30"
          => br %"v31" ? "L32" : "L33";
        @"L32":
          call %"v35" : "w" = $"__printf_buffer_flush"("p" %"v0");
          %"v36" : "w" = op "ext"("ub") %"v35";
          %"v37" : "w" = op "cmp"("eq", "w") %"v36", #0
          => goto "L33";
        @"L33" [phi %"v39" : "w" = ("L16" => #0, "L32" => %"v37")]:
          => br %"v39" ? "L20" : "L22";
        @"L20":
          => ret void;
        @"L22":
          %"v45" = %"v0" +p #8;
          %"chk3" : "a" = op "renew"(int 0, int 8, "read", int 8) %"chk1", %"v45";
          %"v46" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk3";
          %"v48" = %"v0" +p #16;
          %"chk4" : "a" = op "renew"(int 0, int 8, "read", int 8) %"chk2", %"v48";
          %"v49" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk4";
          %"v50" : "l" = "ptoi" %"v46";
          %"v51" : "l" = "ptoi" %"v49";
          %"v52" : "w" = op "cmp"("ne", "l") %"v50", %"v51"
          => br %"v52" ? "L43" : "L42";
        @"L42":
          %"v53" : "p" = "copy" $"glibc_printf_buffer_write#str.41";
          %"v54" : "p" = "copy" $"glibc_printf_buffer_write#str.42";
          %"v55" : "p" = "copy" $"glibc_printf_buffer_write#str.43";
          call void $"__libc_assert_fail"("p" %"v53", "p" %"v54", "w" #35, "p" %"v55")
          => goto "L43";
        @"L43":
          %"v58" = %"v0" +p #16;
          %"chk5" : "a" = op "renew"(int 0, int 8, "read", int 8) %"chk2", %"v58";
          %"v59" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk5";
          %"v61" = %"v0" +p #8;
          %"chk6" : "a" = op "renew"(int 0, int 8, "read", int 8) %"chk1", %"v61";
          %"v62" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk6";
          %"v63" : "l" = "ptoi" %"v59";
          %"v64" : "l" = "ptoi" %"v62";
          %"v65" : "l" = "sub" %"v63", %"v64";
          %"v71" : "w" = op "cmp"("ugt", "l") %"v65", %"pr.2"
          => br %"v71" ? "L68" : "L67";
        @"L67":
          => goto "L68";
        @"L68" [phi %"pr.3" : "l" = ("L67" => %"v65", "L43" => %"pr.2")]:
          %"v74" = %"v0" +p #8;
          %"v75" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk6";
          call %"v78" : "p" = $"__GI_memcpy"("p" %"v75", "p" %"pr.1", "l" %"pr.3");
          %"chk8" : "a" = op "renew"(int 0, int 8, "read", int 8) %"chk1", %"v74";
          %"v81" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk8";
          %"v83" = %"v81" +p %"pr.3";
          %"chk9" : "a" = op "renew"(int 0, int 8, "write", int 8) %"chk1", %"v74";
          store.ptr [%"chk9" + 0] <- %"v83";
          %"v86" = %"pr.1" +p %"pr.3";
          %"v89" : "l" = "sub" %"pr.2", %"pr.3"
          => goto poll "L15";
        @"L17":
          => ret void
      } };
    cap_fn{ "export" "__printf_buffer_flush" [param "p" %"v0"] -> "w"
      {
        @"start":
          %"iw_1.v3" = %"v0" +p #32;
          %"chk0" : "a" = op "check"(int 0, int 4, "read", int 1) %"iw_1.v3";
          %"iw_1.v4" : "w" = op "raw_load"("uw", int 0) %"chk0";
          %"iw_1.v5" : "w" = op "cmp"("eq", "w") %"iw_1.v4", #0
          => br %"iw_1.v5" ? "L2" : "iw_2.start";
        @"L2":
          => ret #0;
        @"iw_2.start":
          %"iw_2.v3" = %"v0" +p #32;
          %"iw_2.v4" : "w" = op "raw_load"("uw", int 0) %"chk0";
          %"iw_2.v30" : "w" = op "cmp"("ult", "w") %"iw_2.v4", #6
          => br %"iw_2.v30" ? "iw_2.L31" : "iw_2.L32";
        @"iw_2.L9":
          call void $"__printf_buffer_flush_snprintf"("p" %"v0")
          => goto "iw_3.start";
        @"iw_2.L11":
          call void $"__GI___chk_fail"()
          => goto "iw_2.L6";
        @"iw_2.L12":
          call void $"__printf_buffer_flush_to_file"("p" %"v0")
          => goto "iw_3.start";
        @"iw_2.L14":
          call void $"__printf_buffer_flush_asprintf"("p" %"v0")
          => goto "iw_3.start";
        @"iw_2.L16":
          call void $"__printf_buffer_flush_dprintf"("p" %"v0")
          => goto "iw_3.start";
        @"iw_2.L18":
          %"iw_2.v19" : "p" = "copy" $"__libc_errno";
          %"chk2" : "a" = op "check"(int 0, int 4, "write", int 1) %"iw_2.v19";
          store "w" [%"chk2" + 0] <- #7;
          %"iw_2.iw_1.v3" = %"v0" +p #32;
          %"chk3" : "a" = op "renew"(int 0, int 4, "write", int 1) %"chk0", %"iw_2.iw_1.v3";
          store "w" [%"chk3" + 0] <- #0
          => goto "iw_3.start";
        @"iw_2.L21":
          call void $"__printf_buffer_flush_fp"("p" %"v0")
          => goto "iw_3.start";
        @"iw_2.L23":
          call void $"__printf_buffer_flush_fp_to_wide"("p" %"v0")
          => goto "iw_3.start";
        @"iw_2.L25":
          call void $"__printf_buffer_flush_fphex_to_wide"("p" %"v0")
          => goto "iw_3.start";
        @"iw_2.L27":
          call void $"__printf_buffer_flush_obstack"("p" %"v0")
          => goto "iw_3.start";
        @"iw_2.L31":
          %"iw_2.v33" : "w" = op "cmp"("ult", "w") %"iw_2.v4", #3
          => br %"iw_2.v33" ? "iw_2.L34" : "iw_2.L35";
        @"iw_2.L34":
          %"iw_2.v36" : "w" = op "cmp"("eq", "w") %"iw_2.v4", #0
          => br %"iw_2.v36" ? "iw_3.start" : "iw_2.L37";
        @"iw_2.L37":
          %"iw_2.v38" : "w" = op "cmp"("eq", "w") %"iw_2.v4", #1
          => br %"iw_2.v38" ? "iw_3.start" : "iw_2.L39";
        @"iw_2.L39":
          %"iw_2.v40" : "w" = op "cmp"("eq", "w") %"iw_2.v4", #2
          => br %"iw_2.v40" ? poll "iw_2.L9" : "iw_2.L6";
        @"iw_2.L35":
          %"iw_2.v42" : "w" = op "cmp"("eq", "w") %"iw_2.v4", #3
          => br %"iw_2.v42" ? poll "iw_2.L11" : "iw_2.L43";
        @"iw_2.L43":
          %"iw_2.v44" : "w" = op "cmp"("eq", "w") %"iw_2.v4", #4
          => br %"iw_2.v44" ? poll "iw_2.L12" : "iw_2.L45";
        @"iw_2.L45":
          %"iw_2.v46" : "w" = op "cmp"("eq", "w") %"iw_2.v4", #5
          => br %"iw_2.v46" ? poll "iw_2.L14" : "iw_2.L6";
        @"iw_2.L32":
          %"iw_2.v48" : "w" = op "cmp"("ult", "w") %"iw_2.v4", #9
          => br %"iw_2.v48" ? "iw_2.L49" : "iw_2.L50";
        @"iw_2.L49":
          %"iw_2.v51" : "w" = op "cmp"("eq", "w") %"iw_2.v4", #6
          => br %"iw_2.v51" ? poll "iw_2.L16" : "iw_2.L52";
        @"iw_2.L52":
          %"iw_2.v53" : "w" = op "cmp"("eq", "w") %"iw_2.v4", #7
          => br %"iw_2.v53" ? poll "iw_2.L18" : "iw_2.L54";
        @"iw_2.L54":
          %"iw_2.v55" : "w" = op "cmp"("eq", "w") %"iw_2.v4", #8
          => br %"iw_2.v55" ? poll "iw_2.L21" : "iw_2.L6";
        @"iw_2.L50":
          %"iw_2.v57" : "w" = op "cmp"("eq", "w") %"iw_2.v4", #9
          => br %"iw_2.v57" ? poll "iw_2.L23" : "iw_2.L58";
        @"iw_2.L58":
          %"iw_2.v59" : "w" = op "cmp"("eq", "w") %"iw_2.v4", #10
          => br %"iw_2.v59" ? poll "iw_2.L25" : "iw_2.L60";
        @"iw_2.L60":
          %"iw_2.v61" : "w" = op "cmp"("eq", "w") %"iw_2.v4", #11
          => br %"iw_2.v61" ? poll "iw_2.L27" : "iw_2.L6";
        @"iw_2.L6":
          => unreachable;
        @"iw_3.start":
          %"iw_3.v3" = %"v0" +p #32;
          %"chk4" : "a" = op "renew"(int 0, int 4, "read", int 1) %"chk0", %"iw_3.v3";
          %"iw_3.v4" : "w" = op "raw_load"("uw", int 0) %"chk4";
          %"iw_3.v5" : "w" = op "cmp"("eq", "w") %"iw_3.v4", #0
          => br %"iw_3.v5" ? "L13" : "L15";
        @"L13":
          => ret #0;
        @"L15":
          %"v25" = %"v0" +p #8;
          %"chk5" : "a" = op "half_check"("lower", int 0, int 8, "read", int 8) %"chk0", %"v25";
          %"v26" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk5";
          %"v28" = %"v0" +p #16;
          %"v29" : "p" = op "raw_load_pointer"(int 8, ["aux_read"; "lower_resolve"; "address_read"]) %"chk5";
          %"v30" : "l" = "ptoi" %"v26";
          %"v31" : "l" = "ptoi" %"v29";
          %"v32" : "w" = op "cmp"("ne", "l") %"v30", %"v31"
          => br %"v32" ? "L23" : "L22";
        @"L22":
          %"v33" : "p" = "copy" $"glibc_printf_buffer_flush#str.39";
          %"v34" : "p" = "copy" $"glibc_printf_buffer_flush#str.40";
          %"v35" : "p" = "copy" $"glibc_printf_buffer_flush#str.41";
          call void $"__libc_assert_fail"("p" %"v33", "p" %"v34", "w" #70, "p" %"v35")
          => goto "L23";
        @"L23":
          => ret #1
      } }
  ]].

From Nanofil Require Import Syntax Transport Semantics.

(** Decoding gives the actual checked bodies used by instruction proofs. *)
Definition printf_buffer_io_module : module := Eval vm_compute in
  code_module printf_buffer_io_term.

(** Computation rules out the empty fallback in the decoded module. *)
Lemma printf_buffer_io_decodes : decode_module printf_buffer_io_term = Some printf_buffer_io_module.
Proof. vm_compute. reflexivity. Qed.

(** Function lookup selects a checked body without supplying its specification. *)
Definition printf_buffer_io_fn (n : string) : func :=
  code_function printf_buffer_io_module n.

(** This definition selects the checked body of [__printf_buffer_write]. *)
Definition glibc___printf_buffer_write : func := Eval vm_compute in
  printf_buffer_io_fn "__printf_buffer_write".

(** Computation checks that lookup found the body rather than its fallback. *)
Lemma printf_buffer_io_find_printf_buffer_write :
  find_direct (TAtom "__printf_buffer_write") printf_buffer_io_module = Some (Defined glibc___printf_buffer_write).
Proof. vm_compute. reflexivity. Qed.

(** This definition selects the checked body of [__printf_buffer_flush]. *)
Definition glibc___printf_buffer_flush : func := Eval vm_compute in
  printf_buffer_io_fn "__printf_buffer_flush".

(** Computation checks that lookup found the body rather than its fallback. *)
Lemma printf_buffer_io_find_printf_buffer_flush :
  find_direct (TAtom "__printf_buffer_flush") printf_buffer_io_module = Some (Defined glibc___printf_buffer_flush).
Proof. vm_compute. reflexivity. Qed.
