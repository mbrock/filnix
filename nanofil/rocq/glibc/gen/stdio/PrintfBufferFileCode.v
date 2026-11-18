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
Definition printf_buffer_file_term : term :=
  TApp "module" [TList [
    cap_fn{ "export" "__printf_buffer_to_file_switch" [param "p" %"v0"] -> "void"
      {
        @"start":
          %"v6" = %"v0" +p #40;
          %"chk0" : "a" = op "check"(int 0, int 8, "read", int 8) %"v6";
          %"v7" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk0";
          %"v8" = %"v7" +p #40;
          %"chk1" : "a" = op "check"(int 0, int 8, "read", int 8) %"v8";
          %"v9" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk1";
          %"v12" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk0";
          %"v13" = %"v12" +p #48;
          %"chk3" : "a" = op "check"(int 0, int 8, "read", int 8) %"v13";
          %"v14" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk3";
          %"v15" : "l" = "ptoi" %"v9";
          %"v16" : "l" = "ptoi" %"v14";
          %"v17" : "w" = op "cmp"("ult", "l") %"v15", %"v16"
          => br %"v17" ? "L2" : "L3";
        @"L2":
          %"v19" = %"v0" +p #8;
          %"v21" = %"v0" +p #40;
          %"v22" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk0";
          %"v23" = %"v22" +p #40;
          %"chk5" : "a" = op "check"(int 0, int 8, "read", int 8) %"v23";
          %"v24" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk5";
          %"chk6" : "a" = op "half_check"("lower", int 0, int 8, "write", int 8) %"chk0", %"v19";
          store.ptr [%"chk6" + 0] <- %"v24";
          %"v26" = %"v0" +p #16;
          %"chk7" : "a" = op "renew"(int 0, int 8, "read", int 8) %"chk0", %"v21";
          %"v29" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk7";
          %"v30" = %"v29" +p #48;
          %"chk8" : "a" = op "check"(int 0, int 8, "read", int 8) %"v30";
          %"v31" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk8";
          %"chk9" : "a" = op "half_check"("lower", int 0, int 8, "write", int 8) %"chk0", %"v26";
          store.ptr [%"chk9" + 0] <- %"v31"
          => goto "L4";
        @"L3":
          %"v33" = %"v0" +p #8;
          %"v35" = %"v0" +p #48;
          %"chk10" : "a" = op "half_check"("lower", int 0, int 8, "write", int 8) %"chk0", %"v33";
          store.ptr [%"chk10" + 0] <- %"v35";
          %"v37" = %"v0" +p #16;
          %"v43" = %"v35" +p #128;
          %"chk11" : "a" = op "half_check"("lower", int 0, int 8, "write", int 8) %"chk0", %"v37";
          store.ptr [%"chk11" + 0] <- %"v43"
          => goto "L4";
        @"L4":
          %"v46" = %"v0" +p #8;
          %"chk12" : "a" = op "half_check"("lower", int 0, int 8, "read", int 8) %"chk0", %"v46";
          %"v47" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk12";
          %"chk13" : "a" = op "half_check"("lower", int 0, int 8, "write", int 8) %"chk0", %"v0";
          store.ptr [%"chk13" + 0] <- %"v47"
          => ret void
      } };
    cap_fn{ "export" "__printf_buffer_flush_to_file" [param "p" %"v0"] -> "void"
      {
        @"start":
          %"v3" = %"v0" +p #24;
          %"chk0" : "a" = op "check"(int 0, int 8, "read", int 1) %"v3";
          %"v4" : "l" = op "raw_load"("l", int 0) %"chk0";
          %"v6" = %"v0" +p #8;
          %"chk1" : "a" = op "half_check"("lower", int 0, int 8, "read", int 8) %"chk0", %"v6";
          %"v7" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk1";
          %"chk2" : "a" = op "half_check"("lower", int 0, int 8, "read", int 8) %"chk0", %"v0";
          %"v9" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk2";
          %"v10" : "l" = "ptoi" %"v7";
          %"v11" : "l" = "ptoi" %"v9";
          %"v12" : "l" = "sub" %"v10", %"v11";
          %"v13" : "l" = "add" %"v4", %"v12";
          %"chk3" : "a" = op "renew"(int 0, int 8, "write", int 1) %"chk0", %"v3";
          store "l" [%"chk3" + 0] <- %"v13";
          %"v18" = %"v0" +p #16;
          %"v19" : "p" = op "raw_load_pointer"(int 8, ["aux_read"; "lower_resolve"; "address_read"]) %"chk1";
          %"v21" = %"v0" +p #48;
          %"v25" = %"v21" +p #128;
          %"v26" : "l" = "ptoi" %"v19";
          %"v27" : "l" = "ptoi" %"v25";
          %"v28" : "w" = op "cmp"("eq", "l") %"v26", %"v27"
          => br %"v28" ? "L14" : "L15";
        @"L14":
          %"v31" = %"v0" +p #8;
          %"v32" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk1";
          %"v34" = %"v0" +p #48;
          %"v35" : "l" = "ptoi" %"v32";
          %"v36" : "l" = "ptoi" %"v34";
          %"v37" : "l" = "sub" %"v35", %"v36";
          %"v42" = %"v0" +p #40;
          %"chk6" : "a" = op "half_check"("upper", int 0, int 8, "read", int 8) %"chk0", %"v42";
          %"v43" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk6";
          %"v44" = %"v43" +p #216;
          %"chk7" : "a" = op "check"(int 0, int 8, "read", int 8) %"v44";
          %"v45" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk7";
          %"iw_1.v4" : "l" = "ptoi" %"v45";
          %"iw_1.v7" : "p" = "copy" $"__io_vtables";
          %"iw_1.v8" : "l" = "ptoi" %"iw_1.v7";
          %"iw_1.v9" : "l" = "sub" %"iw_1.v4", %"iw_1.v8";
          %"iw_1.v15" : "w" = op "cmp"("uge", "l") %"iw_1.v9", #2352
          => br %"iw_1.v15" ? "iw_1.L10" : "iw_1.join";
        @"iw_1.L10":
          call void $"_IO_vtable_check"()
          => goto "iw_1.join";
        @"iw_1.join":
          %"v47" = %"v45" +p #56;
          %"chk8" : "a" = op "check"(int 0, int 8, "read", int 8) %"v47";
          %"v48" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk8";
          %"v50" = %"v0" +p #40;
          %"chk9" : "a" = op "renew"(int 0, int 8, "read", int 8) %"chk6", %"v50";
          %"v51" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk9";
          %"v53" = %"v0" +p #48;
          %"chk10" : "f" = "check_function" %"v48";
          rawcall %"v55" : "l" = %"chk10"("p" %"v51", "p" %"v53", "l" %"v37");
          %"v57" : "w" = op "cmp"("ne", "l") %"v55", %"v37"
          => br %"v57" ? "iw_2.start" : "L40";
        @"iw_2.start":
          %"iw_2.v3" = %"v0" +p #32;
          %"chk11" : "a" = op "half_check"("upper", int 0, int 4, "write", int 1) %"chk0", %"iw_2.v3";
          store "w" [%"chk11" + 0] <- #0
          => ret void;
        @"L40":
          call void $"__printf_buffer_to_file_switch"("p" %"v0")
          => ret void;
        @"L15":
          %"v66" = %"v0" +p #16;
          %"v67" : "p" = op "raw_load_pointer"(int 8, ["aux_read"; "lower_resolve"; "address_read"]) %"chk1";
          %"v69" = %"v0" +p #48;
          %"v70" = %"v69" +p #1;
          %"v71" : "l" = "ptoi" %"v67";
          %"v72" : "l" = "ptoi" %"v70";
          %"v73" : "w" = op "cmp"("eq", "l") %"v71", %"v72"
          => br %"v73" ? "L62" : "L16";
        @"L62":
          %"v78" = %"v0" +p #8;
          %"v79" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk1";
          %"v81" = %"v0" +p #16;
          %"v82" : "p" = op "raw_load_pointer"(int 8, ["aux_read"; "lower_resolve"; "address_read"]) %"chk1";
          %"v83" : "l" = "ptoi" %"v79";
          %"v84" : "l" = "ptoi" %"v82";
          %"v85" : "w" = op "cmp"("eq", "l") %"v83", %"v84"
          => br %"v85" ? "L74" : "L76";
        @"L74":
          %"v90" = %"v0" +p #40;
          %"chk15" : "a" = op "half_check"("upper", int 0, int 8, "read", int 8) %"chk0", %"v90";
          %"v91" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk15";
          %"v93" = %"v0" +p #48;
          %"chk16" : "a" = op "half_check"("upper", int 0, int 1, "read", int 1) %"chk0", %"v93";
          %"v94" : "w" = op "raw_load"("sb", int 0) %"chk16";
          %"v95" : "w" = op "ext"("ub") %"v94";
          call %"v96" : "w" = $"__GI___overflow"("p" %"v91", "w" %"v95");
          %"v98" : "w" = op "cmp"("eq", "w") %"v96", #4294967295
          => br %"v98" ? "iw_3.start" : "L88";
        @"iw_3.start":
          %"iw_3.v3" = %"v0" +p #32;
          %"chk17" : "a" = op "half_check"("upper", int 0, int 4, "write", int 1) %"chk0", %"iw_3.v3";
          store "w" [%"chk17" + 0] <- #0
          => ret void;
        @"L88":
          call void $"__printf_buffer_to_file_switch"("p" %"v0")
          => goto "L76";
        @"L76":
          => ret void;
        @"L16":
          %"v107" = %"v0" +p #16;
          %"v108" : "p" = op "raw_load_pointer"(int 8, ["aux_read"; "lower_resolve"; "address_read"]) %"chk1";
          %"v110" = %"v0" +p #40;
          %"chk19" : "a" = op "half_check"("upper", int 0, int 8, "read", int 8) %"chk0", %"v110";
          %"v111" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk19";
          %"v112" = %"v111" +p #48;
          %"chk20" : "a" = op "check"(int 0, int 8, "read", int 8) %"v112";
          %"v113" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk20";
          %"v114" : "l" = "ptoi" %"v108";
          %"v115" : "l" = "ptoi" %"v113";
          %"v116" : "w" = op "cmp"("eq", "l") %"v114", %"v115"
          => br %"v116" ? "L105" : "L104";
        @"L104":
          %"v117" : "p" = "copy" $"glibc_printf_buffer_to_file#str.266";
          %"v118" : "p" = "copy" $"glibc_printf_buffer_to_file#str.267";
          %"v119" : "p" = "copy" $"glibc_printf_buffer_to_file#str.268";
          call void $"__libc_assert_fail"("p" %"v117", "p" %"v118", "w" #86, "p" %"v119")
          => goto "L105";
        @"L105":
          %"v121" = %"v0" +p #40;
          %"chk21" : "a" = op "renew"(int 0, int 8, "read", int 8) %"chk19", %"v121";
          %"v122" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk21";
          %"v123" = %"v122" +p #40;
          %"v125" = %"v0" +p #8;
          %"chk22" : "a" = op "renew"(int 0, int 8, "read", int 8) %"chk1", %"v125";
          %"v126" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk22";
          %"chk23" : "a" = op "check"(int 0, int 8, "write", int 8) %"v123";
          store.ptr [%"chk23" + 0] <- %"v126";
          %"chk24" : "a" = op "renew"(int 0, int 8, "read", int 8) %"chk1", %"v125";
          %"v132" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk24";
          %"v134" = %"v0" +p #16;
          %"chk25" : "a" = op "half_check"("lower", int 0, int 8, "read", int 8) %"chk0", %"v134";
          %"v135" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk25";
          %"v136" : "l" = "ptoi" %"v132";
          %"v137" : "l" = "ptoi" %"v135";
          %"v138" : "w" = op "cmp"("eq", "l") %"v136", %"v137"
          => br %"v138" ? "L127" : "L129";
        @"L127":
          %"v140" = %"v0" +p #8;
          %"v142" = %"v0" +p #48;
          %"chk26" : "a" = op "renew"(int 0, int 8, "write", int 8) %"chk1", %"v140";
          store.ptr [%"chk26" + 0] <- %"v142";
          %"v144" = %"v0" +p #16;
          %"v147" = %"v142" +p #1;
          %"chk27" : "a" = op "renew"(int 0, int 8, "write", int 8) %"chk25", %"v144";
          store.ptr [%"chk27" + 0] <- %"v147"
          => goto "L129";
        @"L129":
          %"v150" = %"v0" +p #8;
          %"chk28" : "a" = op "renew"(int 0, int 8, "read", int 8) %"chk1", %"v150";
          %"v151" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk28";
          %"chk29" : "a" = op "renew"(int 0, int 8, "write", int 8) %"chk2", %"v0";
          store.ptr [%"chk29" + 0] <- %"v151"
          => ret void
      } };
    cap_fn{ "export" "__printf_buffer_to_file_init" [param "p" %"v0"; param "p" %"v2"] -> "void"
      {
        @"start":
          %"v6" = %"v0" +p #48;
          %"iw_1.v12" = %"v6" +p #128;
          %"chk0" : "a" = op "check"(int 0, int 8, "write", int 8) %"v0";
          store.ptr [%"chk0" + 0] <- %"v6";
          %"iw_1.iw_1.v11" = %"v0" +p #8;
          %"chk1" : "a" = op "half_check"("upper", int 0, int 8, "write", int 8) %"chk0", %"iw_1.iw_1.v11";
          store.ptr [%"chk1" + 0] <- %"v6";
          %"iw_1.iw_1.v14" = %"v0" +p #16;
          %"chk2" : "a" = op "half_check"("upper", int 0, int 8, "write", int 8) %"chk0", %"iw_1.iw_1.v14";
          store.ptr [%"chk2" + 0] <- %"iw_1.v12";
          %"iw_1.iw_1.v17" = %"v0" +p #24;
          %"chk3" : "a" = op "half_check"("upper", int 0, int 8, "write", int 1) %"chk0", %"iw_1.iw_1.v17";
          store "l" [%"chk3" + 0] <- #0;
          %"iw_1.iw_1.v19" = %"v0" +p #32;
          %"chk4" : "a" = op "half_check"("upper", int 0, int 4, "write", int 1) %"chk0", %"iw_1.iw_1.v19";
          store "w" [%"chk4" + 0] <- #4;
          %"v11" = %"v0" +p #40;
          %"chk5" : "a" = op "half_check"("upper", int 0, int 8, "write", int 8) %"chk0", %"v11";
          store.ptr [%"chk5" + 0] <- %"v2";
          call void $"__printf_buffer_to_file_switch"("p" %"v0")
          => ret void
      } };
    cap_fn{ "export" "__printf_buffer_to_file_done" [param "p" %"v0"] -> "w"
      {
        @"start":
          %"iw_1.v3" = %"v0" +p #32;
          %"chk0" : "a" = op "check"(int 0, int 4, "read", int 1) %"iw_1.v3";
          %"iw_1.v4" : "w" = op "raw_load"("uw", int 0) %"chk0";
          %"iw_1.v5" : "w" = op "cmp"("eq", "w") %"iw_1.v4", #0
          => br %"iw_1.v5" ? "L2" : "L4";
        @"L2":
          => ret #4294967295;
        @"L4":
          call void $"__printf_buffer_flush_to_file"("p" %"v0");
          call %"v12" : "w" = $"__printf_buffer_done"("p" %"v0")
          => ret %"v12"
      } }
  ]].

From Nanofil Require Import Syntax Transport Semantics.

(** Decoding gives the actual checked bodies used by instruction proofs. *)
Definition printf_buffer_file_module : module := Eval vm_compute in
  code_module printf_buffer_file_term.

(** Computation rules out the empty fallback in the decoded module. *)
Lemma printf_buffer_file_decodes : decode_module printf_buffer_file_term = Some printf_buffer_file_module.
Proof. vm_compute. reflexivity. Qed.

(** Function lookup selects a checked body without supplying its specification. *)
Definition printf_buffer_file_fn (n : string) : func :=
  code_function printf_buffer_file_module n.

(** This definition selects the checked body of [__printf_buffer_to_file_switch]. *)
Definition glibc___printf_buffer_to_file_switch : func := Eval vm_compute in
  printf_buffer_file_fn "__printf_buffer_to_file_switch".

(** Computation checks that lookup found the body rather than its fallback. *)
Lemma printf_buffer_file_find_printf_buffer_to_file_switch :
  find_direct (TAtom "__printf_buffer_to_file_switch") printf_buffer_file_module = Some (Defined glibc___printf_buffer_to_file_switch).
Proof. vm_compute. reflexivity. Qed.

(** This definition selects the checked body of [__printf_buffer_flush_to_file]. *)
Definition glibc___printf_buffer_flush_to_file : func := Eval vm_compute in
  printf_buffer_file_fn "__printf_buffer_flush_to_file".

(** Computation checks that lookup found the body rather than its fallback. *)
Lemma printf_buffer_file_find_printf_buffer_flush_to_file :
  find_direct (TAtom "__printf_buffer_flush_to_file") printf_buffer_file_module = Some (Defined glibc___printf_buffer_flush_to_file).
Proof. vm_compute. reflexivity. Qed.

(** This definition selects the checked body of [__printf_buffer_to_file_init]. *)
Definition glibc___printf_buffer_to_file_init : func := Eval vm_compute in
  printf_buffer_file_fn "__printf_buffer_to_file_init".

(** Computation checks that lookup found the body rather than its fallback. *)
Lemma printf_buffer_file_find_printf_buffer_to_file_init :
  find_direct (TAtom "__printf_buffer_to_file_init") printf_buffer_file_module = Some (Defined glibc___printf_buffer_to_file_init).
Proof. vm_compute. reflexivity. Qed.

(** This definition selects the checked body of [__printf_buffer_to_file_done]. *)
Definition glibc___printf_buffer_to_file_done : func := Eval vm_compute in
  printf_buffer_file_fn "__printf_buffer_to_file_done".

(** Computation checks that lookup found the body rather than its fallback. *)
Lemma printf_buffer_file_find_printf_buffer_to_file_done :
  find_direct (TAtom "__printf_buffer_to_file_done") printf_buffer_file_module = Some (Defined glibc___printf_buffer_to_file_done).
Proof. vm_compute. reflexivity. Qed.
