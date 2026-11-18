(** This file contains checked IR from the linked image. The glibc code
    generator reproduces it from the capture. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term Syntax.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.
Local Abbreviation a := TAtom.
Local Notation "'t' s" := (Tmp (TAtom s)) (at level 10, s at next level).

Definition hello_image_fn___GI___chk_fail : func :=
  mkFunc (a "__GI___chk_fail") (a "export") RVoid [] [(mkBlock (a "start") [] [(Let (a "v0") P Copy [(Global (a "glibc_chk_fail#str.134"))]);
      (Call CVoid (Global (a "__GI___fortify_fail")) [(Arg P (t "v0"))])] JRetVoid)].

Definition hello_image_fn_glibc_vtables'23check_stdfiles_vtables : func :=
  mkFunc (a "glibc_vtables#check_stdfiles_vtables") (a "local") RVoid [] [(mkBlock (a "start") [] [(Let (a "v3") P Copy [(Global (a "_IO_2_1_stdin_"))]);
      (Flight (a "v4") Add [(FAddress (t "v3")); (FValue (Const 216))] (LowerOf (t "v3")));
      (Let (a "chk0") A (Check 0 8 Read 8) [(t "v4")]);
      (Let (a "v5") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk0")]);
      (Let (a "v6") P Copy [(Global (a "__io_vtables"))]);
      (Flight (a "v7") Add [(FAddress (t "v6")); (FValue (Const 336))] (LowerOf (t "v6")));
      (Let (a "v8") L Ptoi [(t "v5")]);
      (Let (a "v9") L Ptoi [(t "v7")]);
      (Let (a "v10") W (Cmp Ne L) [(t "v8"); (t "v9")])] (JBranch (t "v10") (To (a "L12")) (To (a "L11"))));
  (mkBlock (a "L11") [] [(Let (a "v13") P Copy [(Global (a "_IO_2_1_stdout_"))]);
      (Flight (a "v14") Add [(FAddress (t "v13")); (FValue (Const 216))] (LowerOf (t "v13")));
      (Let (a "chk1") A (Check 0 8 Read 8) [(t "v14")]);
      (Let (a "v15") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk1")]);
      (Let (a "v16") P Copy [(Global (a "__io_vtables"))]);
      (Flight (a "v17") Add [(FAddress (t "v16")); (FValue (Const 336))] (LowerOf (t "v16")));
      (Let (a "v18") L Ptoi [(t "v15")]);
      (Let (a "v19") L Ptoi [(t "v17")]);
      (Let (a "v20") W (Cmp Ne L) [(t "v18"); (t "v19")])] (JGoto (To (a "L12"))));
  (mkBlock (a "L12") [(Phi (a "v22") W [((a "start"), (Const 1)); ((a "L11"), (t "v20"))])] [] (JBranch (t "v22") (To (a "L24")) (To (a "L23"))));
  (mkBlock (a "L23") [] [(Let (a "v25") P Copy [(Global (a "_IO_2_1_stderr_"))]);
      (Flight (a "v26") Add [(FAddress (t "v25")); (FValue (Const 216))] (LowerOf (t "v25")));
      (Let (a "chk2") A (Check 0 8 Read 8) [(t "v26")]);
      (Let (a "v27") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk2")]);
      (Let (a "v28") P Copy [(Global (a "__io_vtables"))]);
      (Flight (a "v29") Add [(FAddress (t "v28")); (FValue (Const 336))] (LowerOf (t "v28")));
      (Let (a "v30") L Ptoi [(t "v27")]);
      (Let (a "v31") L Ptoi [(t "v29")]);
      (Let (a "v32") W (Cmp Ne L) [(t "v30"); (t "v31")])] (JGoto (To (a "L24"))));
  (mkBlock (a "L24") [(Phi (a "v34") W [((a "L12"), (Const 1)); ((a "L23"), (t "v32"))])] [] (JBranch (t "v34") (To (a "L0")) (To (a "L2"))));
  (mkBlock (a "L0") [] [(Let (a "v35") P Copy [(Global (a "_IO_vtable_check"))]);
      (Let (a "iw_1.v6") P Copy [(Global (a "IO_accept_foreign_vtables"))]);
      (Let (a "chk3") A (Check 0 8 Write 8) [(t "iw_1.v6")]);
      (RawStorePointer 0 (t "v35") (t "chk3") [AtomicWrite])] (JGoto (To (a "L2"))));
  (mkBlock (a "L2") [] [] JRetVoid)].
