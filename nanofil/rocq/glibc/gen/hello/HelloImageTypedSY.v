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

Definition hello_image_fn___GI___sysconf : func :=
  mkFunc (a "__GI___sysconf") (a "export") (RClass L) [(W, (a "v0"))] [(mkBlock (a "start") [] [(Let (a "v6") W (Cmp Sge W) [(t "v0"); (Const 185)])] (JBranch (t "v6") (To (a "L7")) (To (a "L8"))));
  (mkBlock (a "L7") [] [(Let (a "v10") W (Cmp Sle W) [(t "v0"); (Const 199)])] (JGoto (To (a "L8"))));
  (mkBlock (a "L8") [(Phi (a "v12") W [((a "start"), (Const 0)); ((a "L7"), (t "v10"))])] [] (JBranch (t "v12") (To (a "L2")) (To (a "iw_1.start"))));
  (mkBlock (a "L2") [] [(Call (CResult (a "v14") L) (Global (a "__cache_sysconf")) [(Arg W (t "v0"))])] (JRet (t "v14")));
  (mkBlock (a "iw_1.start") [] [(Let (a "iw_1.v10") P (Alloc 8) [(Const 16)]);
      (Let (a "iw_1.v43") P (Alloc 8) [(Const 16)]);
      (Let (a "iw_1.v104") P (Alloc 4) [(Const 32)]);
      (Let (a "iw_1.v132") P (Alloc 8) [(Const 8)]);
      (Let (a "iw_1.v68") W (Cmp Slt W) [(t "v0"); (Const 139)])] (JBranch (t "iw_1.v68") (To (a "iw_1.L69")) (To (a "iw_1.L70"))));
  (mkBlock (a "iw_1.L9") [] [(Call (CResult (a "iw_1.v14") W) (Global (a "__GI___getrlimit")) [(Arg W (Const 3)); (Arg P (t "iw_1.v10"))]);
      (Let (a "iw_1.v15") W (Cmp Eq W) [(t "iw_1.v14"); (Const 0)])] (JBranch (t "iw_1.v15") (To (a "iw_1.L11")) (To (a "iw_1.join"))));
  (mkBlock (a "iw_1.L11") [] [(Let (a "chk0") A (Check 0 8 Read 1) [(t "iw_1.v10")]);
      (Let (a "iw_1.v20") L (RawLoad LdL 0) [(t "chk0")]);
      (Let (a "iw_1.v21") L Shr [(t "iw_1.v20"); (Const 2)]);
      (Let (a "iw_1.v22") W (Cmp Ult L) [(t "iw_1.v21"); (Const 131072)])] (JBranch (t "iw_1.v22") (To (a "iw_1.L19")) (To (a "iw_1.L18"))));
  (mkBlock (a "iw_1.L18") [] [(Let (a "iw_1.v23") L (RawLoad LdL 0) [(t "chk0")]);
      (Let (a "iw_1.v24") L Shr [(t "iw_1.v23"); (Const 2)])] (JGoto (To (a "iw_1.L19"))));
  (mkBlock (a "iw_1.L19") [(Phi (a "iw_1.v25") L [((a "iw_1.L18"), (t "iw_1.v24")); ((a "iw_1.L11"), (Const 131072))])] [(Let (a "iw_1.v33") W (Cmp Slt L) [(t "iw_1.v25"); (Const 6291456)])] (JBranch (t "iw_1.v33") (To (a "iw_1.join")) (To (a "iw_1.L27"))));
  (mkBlock (a "iw_1.L27") [] [] (JGoto (To (a "iw_1.join"))));
  (mkBlock (a "iw_1.L40") [] [(Let (a "iw_1.v41") P Copy [(Global (a "glibc_sysconf#str.305"))])] (JGoto (To (a "iw_1.L5"))));
  (mkBlock (a "iw_1.L42") [] [(Call (CResult (a "iw_1.v47") W) (Global (a "__GI___getrlimit")) [(Arg W (Const 11)); (Arg P (t "iw_1.v43"))]);
      (Let (a "iw_1.v48") W (Cmp Eq W) [(t "iw_1.v47"); (Const 0)])] (JBranch (t "iw_1.v48") (To (a "iw_1.L44")) (To (a "iw_1.L46"))));
  (mkBlock (a "iw_1.L44") [] [(Let (a "chk2") A (Check 0 8 Read 1) [(t "iw_1.v43")]);
      (Let (a "iw_1.v49") L (RawLoad LdL 0) [(t "chk2")])] (JGoto (To (a "iw_1.join"))));
  (mkBlock (a "iw_1.L46") [] [(Let (a "iw_1.v51") P Copy [(Global (a "glibc_sysconf#str.306"))])] (JGoto (To (a "iw_1.L5"))));
  (mkBlock (a "iw_1.L52") [] [(Let (a "iw_1.v56") P Copy [(Global (a "_dl_minsigstacksize"))]);
      (Let (a "chk3") A (Check 0 8 Read 1) [(t "iw_1.v56")]);
      (Let (a "iw_1.v57") L (RawLoad LdL 0) [(t "chk3")]);
      (Let (a "iw_1.v58") W (Cmp Ne L) [(t "iw_1.v57"); (Const 0)])] (JBranch (t "iw_1.v58") (To (a "iw_1.L55")) (To (a "iw_1.L54"))));
  (mkBlock (a "iw_1.L54") [] [(Let (a "iw_1.v59") P Copy [(Global (a "glibc_sysconf#str.307"))]);
      (Let (a "iw_1.v60") P Copy [(Global (a "glibc_sysconf#str.308"))]);
      (Let (a "iw_1.v61") P Copy [(Global (a "glibc_sysconf#str.309"))]);
      (Call CVoid (Global (a "__libc_assert_fail")) [(Arg P (t "iw_1.v59")); (Arg P (t "iw_1.v60")); (Arg W (Const 87)); (Arg P (t "iw_1.v61"))])] (JGoto (To (a "iw_1.L55"))));
  (mkBlock (a "iw_1.L55") [] [(Let (a "iw_1.v62") P Copy [(Global (a "_dl_minsigstacksize"))]);
      (Let (a "chk4") A (Check 0 8 Read 1) [(t "iw_1.v62")]);
      (Let (a "iw_1.v63") L (RawLoad LdL 0) [(t "chk4")])] (JGoto (To (a "iw_1.join"))));
  (mkBlock (a "iw_1.iw_1.start") [] [(Let (a "iw_1.iw_1.v1") P Copy [(Global (a "_dl_minsigstacksize"))]);
      (Let (a "chk5") A (Check 0 8 Read 1) [(t "iw_1.iw_1.v1")]);
      (Let (a "iw_1.iw_1.v2") L (RawLoad LdL 0) [(t "chk5")]);
      (Let (a "iw_1.iw_1.v7") W (Cmp Ne L) [(t "iw_1.iw_1.v2"); (Const 0)])] (JBranch (t "iw_1.iw_1.v7") (To (a "iw_1.iw_1.L5")) (To (a "iw_1.iw_1.L4"))));
  (mkBlock (a "iw_1.iw_1.L4") [] [(Let (a "iw_1.iw_1.v8") P Copy [(Global (a "glibc_sysconf#str.302"))]);
      (Let (a "iw_1.iw_1.v9") P Copy [(Global (a "glibc_sysconf#str.303"))]);
      (Let (a "iw_1.iw_1.v10") P Copy [(Global (a "glibc_sysconf#str.304"))]);
      (Call CVoid (Global (a "__libc_assert_fail")) [(Arg P (t "iw_1.iw_1.v8")); (Arg P (t "iw_1.iw_1.v9")); (Arg W (Const 25)); (Arg P (t "iw_1.iw_1.v10"))])] (JGoto (To (a "iw_1.iw_1.L5"))));
  (mkBlock (a "iw_1.iw_1.L5") [] [(Let (a "iw_1.iw_1.v15") W (Cmp Slt L) [(t "iw_1.iw_1.v2"); (Const 2048)])] (JBranch (t "iw_1.iw_1.v15") (To (a "iw_1.iw_1.L13")) (To (a "iw_1.iw_1.L12"))));
  (mkBlock (a "iw_1.iw_1.L12") [] [] (JGoto (To (a "iw_1.iw_1.L13"))));
  (mkBlock (a "iw_1.iw_1.L13") [(Phi (a "iw_1.iw_1.pr.1") L [((a "iw_1.iw_1.L12"), (t "iw_1.iw_1.v2")); ((a "iw_1.iw_1.L5"), (Const 2048))])] [(Let (a "iw_1.iw_1.v18") L Shl [(t "iw_1.iw_1.pr.1"); (Const 2)]);
      (Let (a "iw_1.iw_1.v23") W (Cmp Slt L) [(t "iw_1.iw_1.v18"); (Const 8192)])] (JBranch (t "iw_1.iw_1.v23") (To (a "iw_1.join")) (To (a "iw_1.iw_1.L20"))));
  (mkBlock (a "iw_1.iw_1.L20") [] [] (JGoto (To (a "iw_1.join"))));
  (mkBlock (a "iw_1.L69") [] [(Let (a "iw_1.v71") W (Cmp Eq W) [(t "v0"); (Const 0)])] (JBranch (t "iw_1.v71") (Poll (a "iw_1.L9")) (To (a "iw_1.L72"))));
  (mkBlock (a "iw_1.L72") [] [(Let (a "iw_1.v73") W (Cmp Eq W) [(t "v0"); (Const 3)])] (JBranch (t "iw_1.v73") (Poll (a "iw_1.L40")) (To (a "iw_1.L74"))));
  (mkBlock (a "iw_1.L74") [] [(Let (a "iw_1.v75") W (Cmp Eq W) [(t "v0"); (Const 34)])] (JBranch (t "iw_1.v75") (Poll (a "iw_1.L42")) (To (a "iw_1.L76"))));
  (mkBlock (a "iw_1.L76") [] [(Let (a "iw_1.v77") W (Cmp Eq W) [(t "v0"); (Const 138)])] (JBranch (t "iw_1.v77") (To (a "iw_1.join")) (To (a "iw_1.L5"))));
  (mkBlock (a "iw_1.L70") [] [(Let (a "iw_1.v79") W (Cmp Eq W) [(t "v0"); (Const 139)])] (JBranch (t "iw_1.v79") (To (a "iw_1.join")) (To (a "iw_1.L80"))));
  (mkBlock (a "iw_1.L80") [] [(Let (a "iw_1.v81") W (Cmp Eq W) [(t "v0"); (Const 149)])] (JBranch (t "iw_1.v81") (To (a "iw_1.join")) (To (a "iw_1.L82"))));
  (mkBlock (a "iw_1.L82") [] [(Let (a "iw_1.v83") W (Cmp Eq W) [(t "v0"); (Const 249)])] (JBranch (t "iw_1.v83") (Poll (a "iw_1.L52")) (To (a "iw_1.L84"))));
  (mkBlock (a "iw_1.L84") [] [(Let (a "iw_1.v85") W (Cmp Eq W) [(t "v0"); (Const 250)])] (JBranch (t "iw_1.v85") (Poll (a "iw_1.iw_1.start")) (To (a "iw_1.L5"))));
  (mkBlock (a "iw_1.L5") [(Phi (a "iw_1.pr.1") P [((a "iw_1.L40"), (t "iw_1.v41")); ((a "iw_1.L46"), (t "iw_1.v51")); ((a "iw_1.L76"), (Const 0)); ((a "iw_1.L84"), (Const 0))])] [(Let (a "iw_1.v91") L Ptoi [(t "iw_1.pr.1")]);
      (Let (a "iw_1.v92") L Ptoi [(Const 0)]);
      (Let (a "iw_1.v93") W (Cmp Ne L) [(t "iw_1.v91"); (t "iw_1.v92")])] (JBranch (t "iw_1.v93") (To (a "iw_1.L87")) (To (a "iw_1.L89"))));
  (mkBlock (a "iw_1.L87") [] [(Call (CResult (a "iw_1.v97") W) (Global (a "__GI___open_nocancel")) [(Arg P (t "iw_1.pr.1")); (Arg W (Const 524288))]);
      (Let (a "iw_1.v103") W (Cmp Ne W) [(t "iw_1.v97"); (Const 4294967295)])] (JBranch (t "iw_1.v103") (To (a "iw_1.L107")) (To (a "iw_1.L89"))));
  (mkBlock (a "iw_1.L107") [] [(Call (CResult (a "iw_1.v112") L) (Global (a "__GI___read_nocancel")) [(Arg W (t "iw_1.v97")); (Arg P (t "iw_1.v104")); (Arg L (Const 31))]);
      (Let (a "iw_1.v115") W (Cmp Eq L) [(t "iw_1.v112"); (Const 18446744073709551615)])] (JBranch (t "iw_1.v115") (To (a "iw_1.L116")) (To (a "iw_1.L117"))));
  (mkBlock (a "iw_1.L116") [] [(Let (a "iw_1.v118") P Copy [(Global (a "__libc_errno"))]);
      (Let (a "chk6") A (Check 0 4 Read 1) [(t "iw_1.v118")]);
      (Let (a "iw_1.v119") W (RawLoad (LdNarrow Sw) 0) [(t "chk6")]);
      (Let (a "iw_1.v120") W (Cmp Eq W) [(t "iw_1.v119"); (Const 4)])] (JGoto (To (a "iw_1.L117"))));
  (mkBlock (a "iw_1.L117") [(Phi (a "iw_1.v122") W [((a "iw_1.L107"), (Const 0)); ((a "iw_1.L116"), (t "iw_1.v120"))])] [] (JBranch (t "iw_1.v122") (Poll (a "iw_1.L107")) (To (a "iw_1.L109"))));
  (mkBlock (a "iw_1.L109") [] [(Call CVoid (Global (a "__GI___close_nocancel_nostatus")) [(Arg W (t "iw_1.v97"))]);
      (Let (a "iw_1.v129") W (Cmp Sgt L) [(t "iw_1.v112"); (Const 0)])] (JBranch (t "iw_1.v129") (To (a "iw_1.L125")) (To (a "iw_1.L89"))));
  (mkBlock (a "iw_1.L125") [] [(Flight (a "iw_1.v131") Add [(FAddress (t "iw_1.v104")); (FValue (t "iw_1.v112"))] (LowerOf (t "iw_1.v104")));
      (Let (a "chk7") A (Check 0 1 Write 1) [(t "iw_1.v131")]);
      (RawStore Wb 0 (Const 0) (t "chk7"));
      (Call (CResult (a "iw_1.v134") L) (Global (a "__GI___isoc23_strtol")) [(Arg P (t "iw_1.v104")); (Arg P (t "iw_1.v132")); (Arg W (Const 10))]);
      (Let (a "chk8") A (Check 0 8 Read 8) [(t "iw_1.v132")]);
      (Let (a "iw_1.v138") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk8")]);
      (Let (a "iw_1.v139") L Ptoi [(t "iw_1.v138")]);
      (Let (a "iw_1.v140") L Ptoi [(t "iw_1.v104")]);
      (Let (a "iw_1.v141") W (Cmp Ne L) [(t "iw_1.v139"); (t "iw_1.v140")])] (JBranch (t "iw_1.v141") (To (a "iw_1.L142")) (To (a "iw_1.L143"))));
  (mkBlock (a "iw_1.L142") [] [(Let (a "iw_1.v144") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk8")]);
      (Let (a "chk10") A (Check 0 1 Read 1) [(t "iw_1.v144")]);
      (Let (a "iw_1.v145") W (RawLoad (LdNarrow Sb) 0) [(t "chk10")]);
      (Let (a "iw_1.v146") W (Cmp Eq W) [(t "iw_1.v145"); (Const 0)])] (JBranch (t "iw_1.v146") (To (a "iw_1.L143")) (To (a "iw_1.L147"))));
  (mkBlock (a "iw_1.L147") [] [(Let (a "iw_1.v149") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk8")]);
      (Let (a "chk12") A (Check 0 1 Read 1) [(t "iw_1.v149")]);
      (Let (a "iw_1.v150") W (RawLoad (LdNarrow Sb) 0) [(t "chk12")]);
      (Let (a "iw_1.v151") W (Cmp Eq W) [(t "iw_1.v150"); (Const 10)])] (JGoto (To (a "iw_1.L143"))));
  (mkBlock (a "iw_1.L143") [(Phi (a "iw_1.v155") W [((a "iw_1.L125"), (Const 0)); ((a "iw_1.L142"), (Const 1)); ((a "iw_1.L147"), (t "iw_1.v151"))])] [] (JBranch (t "iw_1.v155") (To (a "iw_1.join")) (To (a "iw_1.L89"))));
  (mkBlock (a "iw_1.L89") [] [(Call (CResult (a "iw_1.v159") L) (Global (a "glibc_sysconf#posix_sysconf")) [(Arg W (t "v0"))])] (JGoto (To (a "iw_1.join"))));
  (mkBlock (a "iw_1.join") [(Phi (a "v17") L [((a "iw_1.L44"), (t "iw_1.v49")); ((a "iw_1.L55"), (t "iw_1.v63")); ((a "iw_1.L89"), (t "iw_1.v159")); ((a "iw_1.L76"), (Const 200809)); ((a "iw_1.L70"), (Const 200809)); ((a "iw_1.L80"), (Const 200809)); ((a "iw_1.L19"), (t "iw_1.v25")); ((a "iw_1.L27"), (Const 6291456)); ((a "iw_1.L9"), (Const 131072)); ((a "iw_1.iw_1.L13"), (Const 8192)); ((a "iw_1.iw_1.L20"), (t "iw_1.iw_1.v18")); ((a "iw_1.L143"), (t "iw_1.v134"))])] [] (JRet (t "v17")))].

Definition hello_image_fn_glibc_sysconf'23__sysconf_check_spec : func :=
  mkFunc (a "glibc_sysconf#__sysconf_check_spec") (a "local") (RClass L) [(P, (a "v0"))] [(mkBlock (a "start") [] [(Let (a "v36") P (Alloc 8) [(Const 144)]);
      (Let (a "v3") P Copy [(Global (a "__libc_errno"))]);
      (Let (a "chk0") A (Check 0 4 Read 1) [(t "v3")]);
      (Let (a "v4") W (RawLoad (LdNarrow Sw) 0) [(t "chk0")]);
      (Let (a "v6") P Copy [(Global (a "glibc_sysconf#str.350"))]);
      (Call (CResult (a "v7") P) (Global (a "__GI___libc_secure_getenv")) [(Arg P (t "v6"))]);
      (Let (a "v8") L Ptoi [(t "v7")]);
      (Let (a "v9") W (Cmp Ne L) [(t "v8"); (Const 0)])] (JBranch (t "v9") (To (a "L12")) (To (a "L11"))));
  (mkBlock (a "L11") [] [(Let (a "v13") P Copy [(Global (a "glibc_sysconf#str.351"))])] (JGoto (To (a "L12"))));
  (mkBlock (a "L12") [(Phi (a "v14") P [((a "L11"), (t "v13")); ((a "start"), (t "v7"))])] [(Call (CResult (a "v17") L) (Global (a "__GI_strlen")) [(Arg P (t "v14"))]);
      (Call (CResult (a "v20") L) (Global (a "__GI_strlen")) [(Arg P (t "v0"))]);
      (Let (a "v22") L Add [(t "v17"); (Const 11)]);
      (Let (a "v24") L Add [(t "v22"); (t "v20")]);
      (Let (a "v25") P (Alloc 4) [(t "v24")]);
      (Call (CResult (a "v28") P) (Global (a "__GI_mempcpy")) [(Arg P (t "v25")); (Arg P (t "v14")); (Arg L (t "v17"))]);
      (Let (a "v29") P Copy [(Global (a "glibc_sysconf#str.353"))]);
      (Call (CResult (a "v31") P) (Global (a "__GI_mempcpy")) [(Arg P (t "v28")); (Arg P (t "v29")); (Arg L (Const 10))]);
      (Let (a "v34") L Add [(t "v20"); (Const 1)]);
      (Call (CResult (a "v35") P) (Global (a "__GI_memcpy")) [(Arg P (t "v31")); (Arg P (t "v0")); (Arg L (t "v34"))]);
      (Call (CResult (a "v41") W) (Global (a "__GI___stat64")) [(Arg P (t "v25")); (Arg P (t "v36"))]);
      (Let (a "v42") W (Cmp Sge W) [(t "v41"); (Const 0)])] (JBranch (t "v42") (To (a "L40")) (To (a "L39"))));
  (mkBlock (a "L39") [] [] (JGoto (To (a "L40"))));
  (mkBlock (a "L40") [(Phi (a "v44") W [((a "L39"), (Const 4294967295)); ((a "L12"), (Const 1))])] [(Let (a "v45") L (Ext Sw) [(t "v44")]);
      (Let (a "v46") P Copy [(Global (a "__libc_errno"))]);
      (Let (a "chk1") A (Check 0 4 Write 1) [(t "v46")]);
      (RawStore Ww 0 (t "v4") (t "chk1"))] (JRet (t "v45")))].
