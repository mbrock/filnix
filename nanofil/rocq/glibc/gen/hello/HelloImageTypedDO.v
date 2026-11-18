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

Definition hello_image_fn_glibc_dl_tunables'23do_tunable_update_val : func :=
  mkFunc (a "glibc_dl_tunables#do_tunable_update_val") (a "local") RVoid [(P, (a "v0")); (P, (a "v2")); (P, (a "v4")); (P, (a "v6"))] [(mkBlock (a "start") [] [(Flight (a "v15") Add [(FAddress (t "v0")); (FValue (Const 105))] (LowerOf (t "v0")));
      (Let (a "chk0") A (Check 0 1 Read 1) [(t "v15")]);
      (Let (a "v16") W (RawLoad (LdNarrow Ub) 0) [(t "chk0")])] (JBranch (t "v16") (To (a "L11")) (To (a "L13"))));
  (mkBlock (a "L11") [] [] JRetVoid);
  (mkBlock (a "L13") [] [(Flight (a "v19") Add [(FAddress (t "v0")); (FValue (Const 48))] (LowerOf (t "v0")));
      (Let (a "chk1") A (HalfCheck Lower 0 4 Read 1) [(t "chk0"); (t "v19")]);
      (Let (a "v20") W (RawLoad (LdNarrow Uw) 0) [(t "chk1")]);
      (Let (a "v46") W (Cmp Eq W) [(t "v20"); (Const 3)])] (JBranch (t "v46") (To (a "L23")) (To (a "L47"))));
  (mkBlock (a "L23") [] [(Flight (a "v25") Add [(FAddress (t "v0")); (FValue (Const 88))] (LowerOf (t "v0")));
      (Let (a "chk2") A (Check 0 8 Read 8) [(t "v2")]);
      (Let (a "v27") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk2")]);
      (Let (a "chk3") A (HalfCheck Lower 0 8 Write 8) [(t "chk0"); (t "v25")]);
      (RawStorePointer 0 (t "v27") (t "chk3") [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite]);
      (Flight (a "v28") Add [(FAddress (t "v2")); (FValue (Const 8))] (LowerOf (t "v2")));
      (Flight (a "v29") Add [(FAddress (t "v25")); (FValue (Const 8))] (LowerOf (t "v25")));
      (Let (a "chk4") A (HalfCheck Upper 0 8 Read 1) [(t "chk2"); (t "v28")]);
      (Let (a "v30") L (RawLoad LdL 0) [(t "chk4")]);
      (Let (a "chk5") A (HalfCheck Upper 0 8 Write 1) [(t "chk3"); (t "v29")]);
      (RawStore Wl 0 (t "v30") (t "chk5"));
      (Flight (a "v32") Add [(FAddress (t "v0")); (FValue (Const 104))] (LowerOf (t "v0")));
      (Let (a "chk6") A (HalfCheck Lower 0 1 Write 1) [(t "chk0"); (t "v32")]);
      (RawStore Wb 0 (Const 1) (t "chk6"))] JRetVoid);
  (mkBlock (a "L34") [] [(Let (a "chk7") A (Check 0 8 Read 1) [(t "v2")]);
      (Let (a "v36") L (RawLoad LdL 0) [(t "chk7")]);
      (Let (a "v37") L (Ext Sw) [(t "v36")])] (JGoto (To (a "L22"))));
  (mkBlock (a "L38") [] [(Let (a "chk8") A (Check 0 8 Read 1) [(t "v2")]);
      (Let (a "v40") L (RawLoad LdL 0) [(t "chk8")])] (JGoto (To (a "L22"))));
  (mkBlock (a "L41") [] [(Let (a "chk9") A (Check 0 8 Read 1) [(t "v2")]);
      (Let (a "v43") L (RawLoad LdL 0) [(t "chk9")])] (JGoto (To (a "L22"))));
  (mkBlock (a "L44") [] [] JUnreachable);
  (mkBlock (a "L47") [] [(Let (a "v48") W (Cmp Eq W) [(t "v20"); (Const 0)])] (JBranch (t "v48") (Poll (a "L34")) (To (a "L49"))));
  (mkBlock (a "L49") [] [(Let (a "v50") W (Cmp Eq W) [(t "v20"); (Const 1)])] (JBranch (t "v50") (Poll (a "L38")) (To (a "L51"))));
  (mkBlock (a "L51") [] [(Let (a "v52") W (Cmp Eq W) [(t "v20"); (Const 2)])] (JBranch (t "v52") (Poll (a "L41")) (Poll (a "L44"))));
  (mkBlock (a "L22") [(Phi (a "pr.1") L [((a "L34"), (t "v37")); ((a "L38"), (t "v40")); ((a "L41"), (t "v43"))])] [(Flight (a "v56") Add [(FAddress (t "v0")); (FValue (Const 48))] (LowerOf (t "v0")));
      (Let (a "chk10") A (Renew 0 4 Read 1) [(t "chk1"); (t "v56")]);
      (Let (a "v57") W (RawLoad (LdNarrow Uw) 0) [(t "chk10")]);
      (Let (a "iw_1.v13") W (Cmp Eq W) [(t "v57"); (Const 0)])] (JBranch (t "iw_1.v13") (To (a "iw_1.join")) (To (a "iw_1.L14"))));
  (mkBlock (a "iw_1.L14") [] [(Let (a "iw_1.v15") W (Cmp Eq W) [(t "v57"); (Const 1)])] (JBranch (t "iw_1.v15") (To (a "iw_1.join")) (To (a "iw_1.L16"))));
  (mkBlock (a "iw_1.L16") [] [(Let (a "iw_1.v17") W (Cmp Eq W) [(t "v57"); (Const 2)])] (JBranch (t "iw_1.v17") (To (a "iw_1.join")) (To (a "iw_1.L18"))));
  (mkBlock (a "iw_1.L18") [] [(Let (a "iw_1.v19") W (Cmp Eq W) [(t "v57"); (Const 3)])] (JBranch (t "iw_1.v19") (To (a "iw_1.L4")) (To (a "iw_1.L20"))));
  (mkBlock (a "iw_1.L20") [] [] (JGoto (To (a "iw_1.L4"))));
  (mkBlock (a "iw_1.L4") [] [] JUnreachable);
  (mkBlock (a "iw_1.join") [(Phi (a "v58") W [((a "L22"), (Const 0)); ((a "iw_1.L14"), (Const 1)); ((a "iw_1.L16"), (Const 1))])] [(Let (a "v64") L Ptoi [(t "v4")]);
      (Let (a "v65") L Ptoi [(Const 0)]);
      (Let (a "v66") W (Cmp Ne L) [(t "v64"); (t "v65")])] (JBranch (t "v66") (To (a "L60")) (To (a "L61"))));
  (mkBlock (a "L60") [] [(Let (a "chk11") A (Check 0 8 Read 1) [(t "v4")]);
      (Let (a "v68") L (RawLoad LdL 0) [(t "chk11")])] (JGoto (To (a "L62"))));
  (mkBlock (a "L61") [] [(Flight (a "v70") Add [(FAddress (t "v0")); (FValue (Const 48))] (LowerOf (t "v0")));
      (Flight (a "v71") Add [(FAddress (t "v70")); (FValue (Const 8))] (LowerOf (t "v70")));
      (Let (a "chk12") A (HalfCheck Lower 0 8 Read 1) [(t "chk0"); (t "v71")]);
      (Let (a "v72") L (RawLoad LdL 0) [(t "chk12")])] (JGoto (To (a "L62"))));
  (mkBlock (a "L62") [(Phi (a "v73") L [((a "L60"), (t "v68")); ((a "L61"), (t "v72"))])] [(Let (a "v78") L Ptoi [(t "v6")]);
      (Let (a "v80") W (Cmp Ne L) [(t "v78"); (t "v65")])] (JBranch (t "v80") (To (a "L74")) (To (a "L75"))));
  (mkBlock (a "L74") [] [(Let (a "chk13") A (Check 0 8 Read 1) [(t "v6")]);
      (Let (a "v82") L (RawLoad LdL 0) [(t "chk13")])] (JGoto (To (a "L76"))));
  (mkBlock (a "L75") [] [(Flight (a "v84") Add [(FAddress (t "v0")); (FValue (Const 48))] (LowerOf (t "v0")));
      (Flight (a "v85") Add [(FAddress (t "v84")); (FValue (Const 16))] (LowerOf (t "v84")));
      (Let (a "chk14") A (HalfCheck Lower 0 8 Read 1) [(t "chk0"); (t "v85")]);
      (Let (a "v86") L (RawLoad LdL 0) [(t "chk14")])] (JGoto (To (a "L76"))));
  (mkBlock (a "L76") [(Phi (a "v87") L [((a "L74"), (t "v82")); ((a "L75"), (t "v86"))])] [(Flight (a "v93") Add [(FAddress (t "v0")); (FValue (Const 48))] (LowerOf (t "v0")));
      (Flight (a "v94") Add [(FAddress (t "v93")); (FValue (Const 8))] (LowerOf (t "v93")));
      (Let (a "chk15") A (HalfCheck Lower 0 8 Read 1) [(t "chk0"); (t "v94")]);
      (Let (a "v95") L (RawLoad LdL 0) [(t "chk15")])] (JBranch (t "v58") (To (a "iw_2.L6")) (To (a "iw_2.L7"))));
  (mkBlock (a "iw_2.L6") [] [(Let (a "iw_2.v12") W (Cmp Ult L) [(t "v73"); (t "v95")])] (JGoto (To (a "iw_2.join"))));
  (mkBlock (a "iw_2.L7") [] [(Let (a "iw_2.v17") W (Cmp Slt L) [(t "v73"); (t "v95")])] (JGoto (To (a "iw_2.join"))));
  (mkBlock (a "iw_2.join") [(Phi (a "v97") W [((a "iw_2.L6"), (t "iw_2.v12")); ((a "iw_2.L7"), (t "iw_2.v17"))])] [] (JBranch (t "v97") (To (a "L88")) (To (a "L90"))));
  (mkBlock (a "L88") [] [(Flight (a "v100") Add [(FAddress (t "v0")); (FValue (Const 48))] (LowerOf (t "v0")));
      (Flight (a "v101") Add [(FAddress (t "v100")); (FValue (Const 8))] (LowerOf (t "v100")));
      (Let (a "v102") L (RawLoad LdL 0) [(t "chk15")])] (JGoto (To (a "L90"))));
  (mkBlock (a "L90") [(Phi (a "pr.3") L [((a "L88"), (t "v102")); ((a "iw_2.join"), (t "v73"))])] [(Flight (a "v108") Add [(FAddress (t "v0")); (FValue (Const 48))] (LowerOf (t "v0")));
      (Flight (a "v109") Add [(FAddress (t "v108")); (FValue (Const 16))] (LowerOf (t "v108")));
      (Let (a "chk17") A (HalfCheck Lower 0 8 Read 1) [(t "chk0"); (t "v109")]);
      (Let (a "v110") L (RawLoad LdL 0) [(t "chk17")])] (JBranch (t "v58") (To (a "iw_3.L6")) (To (a "iw_3.L7"))));
  (mkBlock (a "iw_3.L6") [] [(Let (a "iw_3.v12") W (Cmp Ugt L) [(t "v87"); (t "v110")])] (JGoto (To (a "iw_3.join"))));
  (mkBlock (a "iw_3.L7") [] [(Let (a "iw_3.v17") W (Cmp Sgt L) [(t "v87"); (t "v110")])] (JGoto (To (a "iw_3.join"))));
  (mkBlock (a "iw_3.join") [(Phi (a "v112") W [((a "iw_3.L6"), (t "iw_3.v12")); ((a "iw_3.L7"), (t "iw_3.v17"))])] [] (JBranch (t "v112") (To (a "L103")) (To (a "L105"))));
  (mkBlock (a "L103") [] [(Flight (a "v115") Add [(FAddress (t "v0")); (FValue (Const 48))] (LowerOf (t "v0")));
      (Flight (a "v116") Add [(FAddress (t "v115")); (FValue (Const 16))] (LowerOf (t "v115")));
      (Let (a "v117") L (RawLoad LdL 0) [(t "chk17")])] (JGoto (To (a "L105"))));
  (mkBlock (a "L105") [(Phi (a "pr.4") L [((a "L103"), (t "v117")); ((a "iw_3.join"), (t "v87"))])] [] (JBranch (t "v58") (To (a "iw_4.L6")) (To (a "iw_4.L7"))));
  (mkBlock (a "iw_4.L6") [] [(Let (a "iw_4.v12") W (Cmp Ugt L) [(t "pr.3"); (t "pr.4")])] (JGoto (To (a "iw_4.join"))));
  (mkBlock (a "iw_4.L7") [] [(Let (a "iw_4.v17") W (Cmp Sgt L) [(t "pr.3"); (t "pr.4")])] (JGoto (To (a "iw_4.join"))));
  (mkBlock (a "iw_4.join") [(Phi (a "v124") W [((a "iw_4.L6"), (t "iw_4.v12")); ((a "iw_4.L7"), (t "iw_4.v17"))])] [] (JBranch (t "v124") (To (a "L118")) (To (a "L120"))));
  (mkBlock (a "L118") [] [(Flight (a "v127") Add [(FAddress (t "v0")); (FValue (Const 48))] (LowerOf (t "v0")));
      (Flight (a "v128") Add [(FAddress (t "v127")); (FValue (Const 8))] (LowerOf (t "v127")));
      (Let (a "v129") L (RawLoad LdL 0) [(t "chk15")]);
      (Flight (a "v132") Add [(FAddress (t "v127")); (FValue (Const 16))] (LowerOf (t "v127")));
      (Let (a "v133") L (RawLoad LdL 0) [(t "chk17")])] (JGoto (To (a "L120"))));
  (mkBlock (a "L120") [(Phi (a "pr.5") L [((a "L118"), (t "v133")); ((a "iw_4.join"), (t "pr.4"))]); (Phi (a "pr.2") L [((a "L118"), (t "v129")); ((a "iw_4.join"), (t "pr.3"))])] [] (JBranch (t "v58") (To (a "iw_5.L6")) (To (a "iw_5.L7"))));
  (mkBlock (a "iw_5.L6") [] [(Let (a "iw_5.v12") W (Cmp Ult L) [(t "pr.1"); (t "pr.2")])] (JGoto (To (a "iw_5.join"))));
  (mkBlock (a "iw_5.L7") [] [(Let (a "iw_5.v17") W (Cmp Slt L) [(t "pr.1"); (t "pr.2")])] (JGoto (To (a "iw_5.join"))));
  (mkBlock (a "iw_5.join") [(Phi (a "v140") W [((a "iw_5.L6"), (t "iw_5.v12")); ((a "iw_5.L7"), (t "iw_5.v17"))])] [] (JBranch (t "v140") (To (a "L143")) (To (a "iw_6.start"))));
  (mkBlock (a "iw_6.start") [] [] (JBranch (t "v58") (To (a "iw_6.L6")) (To (a "iw_6.L7"))));
  (mkBlock (a "iw_6.L6") [] [(Let (a "iw_6.v12") W (Cmp Ult L) [(t "pr.5"); (t "pr.1")])] (JGoto (To (a "L143"))));
  (mkBlock (a "iw_6.L7") [] [(Let (a "iw_6.v17") W (Cmp Slt L) [(t "pr.5"); (t "pr.1")])] (JGoto (To (a "L143"))));
  (mkBlock (a "L143") [(Phi (a "v150") W [((a "iw_5.join"), (Const 1)); ((a "iw_6.L6"), (t "iw_6.v12")); ((a "iw_6.L7"), (t "iw_6.v17"))])] [] (JBranch (t "v150") (To (a "L134")) (To (a "L136"))));
  (mkBlock (a "L134") [] [] JRetVoid);
  (mkBlock (a "L136") [] [(Flight (a "v153") Add [(FAddress (t "v0")); (FValue (Const 88))] (LowerOf (t "v0")));
      (Let (a "chk21") A (HalfCheck Lower 0 8 Write 1) [(t "chk0"); (t "v153")]);
      (RawStore Wl 0 (t "pr.1") (t "chk21"));
      (Flight (a "v156") Add [(FAddress (t "v0")); (FValue (Const 48))] (LowerOf (t "v0")));
      (Flight (a "v157") Add [(FAddress (t "v156")); (FValue (Const 8))] (LowerOf (t "v156")));
      (RawStore Wl 0 (t "pr.2") (t "chk15"));
      (Flight (a "v161") Add [(FAddress (t "v156")); (FValue (Const 16))] (LowerOf (t "v156")));
      (RawStore Wl 0 (t "pr.5") (t "chk17"));
      (Flight (a "v164") Add [(FAddress (t "v0")); (FValue (Const 104))] (LowerOf (t "v0")));
      (Let (a "chk24") A (HalfCheck Lower 0 1 Write 1) [(t "chk0"); (t "v164")]);
      (RawStore Wb 0 (Const 1) (t "chk24"))] JRetVoid)].

Definition hello_image_fn_glibc_gconv_dl'23do_release_shlib : func :=
  mkFunc (a "glibc_gconv_dl#do_release_shlib") (a "local") RVoid [(P, (a "v0")); (W, (a "v2")); (P, (a "v4"))] [(mkBlock (a "start") [] [(Let (a "chk0") A (Check 0 8 Read 8) [(t "v0")]);
      (Let (a "v10") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk0")]);
      (Let (a "v15") W (Cmp Ne W) [(t "v2"); (Const 0)])] (JBranch (t "v15") (To (a "L16")) (To (a "L17"))));
  (mkBlock (a "L16") [] [(Let (a "v19") W (Cmp Ne W) [(t "v2"); (Const 3)])] (JGoto (To (a "L17"))));
  (mkBlock (a "L17") [(Phi (a "v21") W [((a "start"), (Const 0)); ((a "L16"), (t "v19"))])] [] (JBranch (t "v21") (To (a "L11")) (To (a "L13"))));
  (mkBlock (a "L11") [] [] JRetVoid);
  (mkBlock (a "L13") [] [(Let (a "v28") L Ptoi [(t "v10")]);
      (Let (a "v29") L Ptoi [(t "v4")]);
      (Let (a "v30") W (Cmp Eq L) [(t "v28"); (t "v29")])] (JBranch (t "v30") (To (a "L23")) (To (a "L24"))));
  (mkBlock (a "L23") [] [(Flight (a "v35") Add [(FAddress (t "v10")); (FValue (Const 8))] (LowerOf (t "v10")));
      (Let (a "chk1") A (Check 0 4 Read 1) [(t "v35")]);
      (Let (a "v36") W (RawLoad (LdNarrow Sw) 0) [(t "chk1")]);
      (Let (a "v37") W (Cmp Sgt W) [(t "v36"); (Const 0)])] (JBranch (t "v37") (To (a "L33")) (To (a "L32"))));
  (mkBlock (a "L32") [] [(Let (a "v38") P Copy [(Global (a "glibc_gconv_dl#str.280"))]);
      (Let (a "v39") P Copy [(Global (a "glibc_gconv_dl#str.275"))]);
      (Let (a "v40") P Copy [(Global (a "glibc_gconv_dl#str.281"))]);
      (Call CVoid (Global (a "__libc_assert_fail")) [(Arg P (t "v38")); (Arg P (t "v39")); (Arg W (Const 162)); (Arg P (t "v40"))])] (JGoto (To (a "L33"))));
  (mkBlock (a "L33") [] [(Flight (a "v42") Add [(FAddress (t "v10")); (FValue (Const 8))] (LowerOf (t "v10")));
      (Let (a "chk2") A (Renew 0 4 Read 1) [(t "chk1"); (t "v42")]);
      (Let (a "v43") W (RawLoad (LdNarrow Sw) 0) [(t "chk2")]);
      (Let (a "v44") W Sub [(t "v43"); (Const 1)]);
      (Let (a "chk3") A (Renew 0 4 Write 1) [(t "chk1"); (t "v42")]);
      (RawStore Ww 0 (t "v44") (t "chk3"))] (JGoto (To (a "L25"))));
  (mkBlock (a "L24") [] [(Flight (a "v49") Add [(FAddress (t "v10")); (FValue (Const 8))] (LowerOf (t "v10")));
      (Let (a "chk4") A (Check 0 4 Read 1) [(t "v49")]);
      (Let (a "v50") W (RawLoad (LdNarrow Sw) 0) [(t "chk4")]);
      (Let (a "v51") W (Cmp Sle W) [(t "v50"); (Const 0)])] (JBranch (t "v51") (To (a "L52")) (To (a "L53"))));
  (mkBlock (a "L52") [] [(Flight (a "v55") Add [(FAddress (t "v10")); (FValue (Const 8))] (LowerOf (t "v10")));
      (Let (a "v56") W (RawLoad (LdNarrow Sw) 0) [(t "chk4")]);
      (Let (a "v58") W (Cmp Sge W) [(t "v56"); (Const 4294967294)])] (JGoto (To (a "L53"))));
  (mkBlock (a "L53") [(Phi (a "v60") W [((a "L24"), (Const 0)); ((a "L52"), (t "v58"))])] [] (JBranch (t "v60") (To (a "L61")) (To (a "L62"))));
  (mkBlock (a "L61") [] [(Flight (a "v64") Add [(FAddress (t "v10")); (FValue (Const 8))] (LowerOf (t "v10")));
      (Let (a "v65") W (RawLoad (LdNarrow Sw) 0) [(t "chk4")]);
      (Let (a "v66") W Sub [(t "v65"); (Const 1)]);
      (Let (a "chk7") A (Renew 0 4 Write 1) [(t "chk4"); (t "v64")]);
      (RawStore Ww 0 (t "v66") (t "chk7"));
      (Let (a "v68") W (Cmp Slt W) [(t "v66"); (Const 4294967294)])] (JGoto (To (a "L62"))));
  (mkBlock (a "L62") [(Phi (a "v70") W [((a "L53"), (Const 0)); ((a "L61"), (t "v68"))])] [] (JBranch (t "v70") (To (a "L71")) (To (a "L72"))));
  (mkBlock (a "L71") [] [(Flight (a "v74") Add [(FAddress (t "v10")); (FValue (Const 16))] (LowerOf (t "v10")));
      (Let (a "chk8") A (HalfCheck Upper 0 8 Read 8) [(t "chk4"); (t "v74")]);
      (Let (a "v75") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk8")]);
      (Let (a "v76") L Ptoi [(t "v75")]);
      (Let (a "v77") L Ptoi [(Const 0)]);
      (Let (a "v78") W (Cmp Ne L) [(t "v76"); (t "v77")])] (JGoto (To (a "L72"))));
  (mkBlock (a "L72") [(Phi (a "v80") W [((a "L62"), (Const 0)); ((a "L71"), (t "v78"))])] [] (JBranch (t "v80") (To (a "L45")) (To (a "L25"))));
  (mkBlock (a "L45") [] [(Flight (a "v82") Add [(FAddress (t "v10")); (FValue (Const 16))] (LowerOf (t "v10")));
      (Let (a "chk9") A (HalfCheck Upper 0 8 Read 8) [(t "chk4"); (t "v82")]);
      (Let (a "v83") P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) [(t "chk9")]);
      (Call (CResult (a "v84") W) (Global (a "__libc_dlclose")) [(Arg P (t "v83"))]);
      (Let (a "chk10") A (Renew 0 8 Write 8) [(t "chk9"); (t "v82")]);
      (RawStorePointer 0 (Const 0) (t "chk10") [AuxEnsure; LowerBarrier; RootedReload; LowerWrite; AddressWrite])] (JGoto (To (a "L25"))));
  (mkBlock (a "L25") [] [] JRetVoid)].
