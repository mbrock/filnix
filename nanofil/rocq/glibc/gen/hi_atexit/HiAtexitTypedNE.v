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

Definition hi_fn___new_exitfn : func :=
  mkFunc (a "__new_exitfn") (a "export") (RClass P) [(P, (a "v0"))] [(mkBlock (a "start") [] [(Let (a "v9") P Copy [(Global (a "__exit_funcs_done"))]);
      (Let (a "chk0") A (Check 0 1 Read 1) [(t "v9")]);
      (Let (a "v10") W (RawLoad (LdNarrow Ub) 0) [(t "chk0")])] (JBranch (t "v10") (To (a "L6")) (To (a "L8"))));
  (mkBlock (a "L6") [] [] (JRet (Const 0)));
  (mkBlock (a "L8") [] [(Let (a "chk1") A (Check 0 8 Read 8) [(t "v0")]);
      (Let (a "v13") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk1")])] (JGoto (To (a "L14"))));
  (mkBlock (a "L14") [(Phi (a "pr.6") L [((a "L47"), (t "pr.8")); ((a "L8"), (Const 0))]); (Phi (a "pr.3") P [((a "L47"), (t "v55")); ((a "L8"), (t "v13"))]); (Phi (a "pr.1") P [((a "L47"), (t "pr.3")); ((a "L8"), (Const 0))])] [(Let (a "v19") L Ptoi [(t "pr.3")]);
      (Let (a "v20") L Ptoi [(Const 0)]);
      (Let (a "v21") W (Cmp Ne L) [(t "v19"); (t "v20")])] (JBranch (t "v21") (To (a "L15")) (To (a "L17"))));
  (mkBlock (a "L15") [] [(Flight (a "v23") Add [(FAddress (t "pr.3")); (FValue (Const 8))] (LowerOf (t "pr.3")));
      (Let (a "chk2") A (Check 0 8 Read 1) [(t "v23")]);
      (Let (a "v24") L (RawLoad LdL 0) [(t "chk2")])] (JGoto (To (a "L25"))));
  (mkBlock (a "L25") [(Phi (a "pr.8") L [((a "L15"), (t "v24")); ((a "L26"), (t "v37"))])] [(Let (a "v30") W (Cmp Ugt L) [(t "pr.8"); (Const 0)])] (JBranch (t "v30") (To (a "L26")) (To (a "L28"))));
  (mkBlock (a "L26") [] [(Flight (a "v35") Add [(FAddress (t "pr.3")); (FValue (Const 16))] (LowerOf (t "pr.3")));
      (Let (a "v37") L Sub [(t "pr.8"); (Const 1)]);
      (Let (a "v38") L Shl [(t "v37"); (Const 5)]);
      (Flight (a "v39") Add [(FAddress (t "v35")); (FValue (t "v38"))] (LowerOf (t "v35")));
      (Let (a "chk3") A (Check 0 8 Read 1) [(t "v39")]);
      (Let (a "v40") L (RawLoad LdL 0) [(t "chk3")]);
      (Let (a "v41") W (Cmp Ne L) [(t "v40"); (Const 0)])] (JBranch (t "v41") (To (a "L28")) (Poll (a "L25"))));
  (mkBlock (a "L28") [] [] (JBranch (t "v30") (To (a "L17")) (To (a "L47"))));
  (mkBlock (a "L47") [] [(Flight (a "v52") Add [(FAddress (t "pr.3")); (FValue (Const 8))] (LowerOf (t "pr.3")));
      (Let (a "chk4") A (Renew 0 8 Write 1) [(t "chk2"); (t "v52")]);
      (RawStore Wl 0 (Const 0) (t "chk4"));
      (Let (a "chk5") A (HalfCheck Lower 0 8 Read 8) [(t "chk2"); (t "pr.3")]);
      (Let (a "v55") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk5")])] (JGoto (Poll (a "L14"))));
  (mkBlock (a "L17") [(Phi (a "pr.7") L [((a "L14"), (t "pr.6")); ((a "L28"), (t "pr.8"))])] [(Let (a "v62") W (Cmp Eq L) [(t "v19"); (t "v20")])] (JBranch (t "v62") (To (a "L64")) (To (a "L63"))));
  (mkBlock (a "L63") [] [(Let (a "v67") W (Cmp Eq L) [(t "pr.7"); (Const 32)])] (JGoto (To (a "L64"))));
  (mkBlock (a "L64") [(Phi (a "v69") W [((a "L17"), (Const 1)); ((a "L63"), (t "v67"))])] [] (JBranch (t "v69") (To (a "L56")) (To (a "L57"))));
  (mkBlock (a "L56") [] [(Let (a "v74") L Ptoi [(t "pr.1")]);
      (Let (a "v76") W (Cmp Eq L) [(t "v74"); (t "v20")])] (JBranch (t "v76") (To (a "L70")) (To (a "L72"))));
  (mkBlock (a "L70") [] [] (JBranch (t "v21") (To (a "L79")) (To (a "L78"))));
  (mkBlock (a "L78") [] [(Let (a "v84") P Copy [(Global (a "glibc_cxa_atexit#str.236"))]);
      (Let (a "v85") P Copy [(Global (a "glibc_cxa_atexit#str.234"))]);
      (Let (a "v86") P Copy [(Global (a "glibc_cxa_atexit#str.237"))]);
      (Call CVoid (Global (a "__libc_assert_fail")) [(Arg P (t "v84")); (Arg P (t "v85")); (Arg W (Const 110)); (Arg P (t "v86"))])] (JGoto (To (a "L79"))));
  (mkBlock (a "L79") [] [(Call (CResult (a "v87") P) (Global (a "calloc")) [(Arg L (Const 1)); (Arg L (Const 1040))]);
      (Let (a "v92") L Ptoi [(t "v87")]);
      (Let (a "v94") W (Cmp Ne L) [(t "v92"); (t "v20")])] (JBranch (t "v94") (To (a "L88")) (To (a "L72"))));
  (mkBlock (a "L88") [] [(Let (a "chk6") A (Renew 0 8 Read 8) [(t "chk1"); (t "v0")]);
      (Let (a "v97") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk6")]);
      (Let (a "chk7") A (Check 0 8 Write 8) [(t "v87")]);
      (RawStorePointer 0 (t "v97") (t "chk7") [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite]);
      (Let (a "chk8") A (Renew 0 8 Write 8) [(t "chk1"); (t "v0")]);
      (RawStorePointer 0 (t "v87") (t "chk8") [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite])] (JGoto (To (a "L72"))));
  (mkBlock (a "L72") [(Phi (a "pr.2") P [((a "L88"), (t "v87")); ((a "L79"), (t "v87")); ((a "L56"), (t "pr.1"))])] [(Let (a "v104") L Ptoi [(t "pr.2")]);
      (Let (a "v106") W (Cmp Ne L) [(t "v104"); (t "v20")])] (JBranch (t "v106") (To (a "L100")) (To (a "L58"))));
  (mkBlock (a "L100") [] [(Flight (a "v108") Add [(FAddress (t "pr.2")); (FValue (Const 16))] (LowerOf (t "pr.2")));
      (Flight (a "v111") Add [(FAddress (t "pr.2")); (FValue (Const 8))] (LowerOf (t "pr.2")));
      (Let (a "chk9") A (Check 0 8 Write 1) [(t "v111")]);
      (RawStore Wl 0 (Const 1) (t "chk9"))] (JGoto (To (a "L58"))));
  (mkBlock (a "L57") [] [(Flight (a "v113") Add [(FAddress (t "pr.3")); (FValue (Const 16))] (LowerOf (t "pr.3")));
      (Let (a "v115") L Shl [(t "pr.7"); (Const 5)]);
      (Flight (a "v116") Add [(FAddress (t "v113")); (FValue (t "v115"))] (LowerOf (t "v113")));
      (Flight (a "v118") Add [(FAddress (t "pr.3")); (FValue (Const 8))] (LowerOf (t "pr.3")));
      (Let (a "v120") L Add [(t "pr.7"); (Const 1)]);
      (Let (a "chk10") A (Check 0 8 Write 1) [(t "v118")]);
      (RawStore Wl 0 (t "v120") (t "chk10"))] (JGoto (To (a "L58"))));
  (mkBlock (a "L58") [(Phi (a "pr.5") P [((a "L57"), (t "v116")); ((a "L100"), (t "v108")); ((a "L72"), (Const 0))])] [(Let (a "v125") L Ptoi [(t "pr.5")]);
      (Let (a "v127") W (Cmp Ne L) [(t "v125"); (t "v20")])] (JBranch (t "v127") (To (a "L121")) (To (a "L123"))));
  (mkBlock (a "L121") [] [(Let (a "chk11") A (Check 0 8 Write 1) [(t "pr.5")]);
      (RawStore Wl 0 (Const 1) (t "chk11"));
      (Let (a "v129") P Copy [(Global (a "__new_exitfn_called"))]);
      (Let (a "chk12") A (Check 0 8 Read 1) [(t "v129")]);
      (Let (a "v130") L (RawLoad LdL 0) [(t "chk12")]);
      (Let (a "v131") L Add [(t "v130"); (Const 1)]);
      (Let (a "chk13") A (Renew 0 8 Write 1) [(t "chk12"); (t "v129")]);
      (RawStore Wl 0 (t "v131") (t "chk13"))] (JGoto (To (a "L123"))));
  (mkBlock (a "L123") [] [] (JRet (t "pr.5")))].
