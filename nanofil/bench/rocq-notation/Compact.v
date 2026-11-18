(** This sample spells the captured directory allocator and locale alias
    comparison using abbreviations for operands and pointer addition. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term Syntax.
Require Import CompactSyntax.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.

Definition hello_image_fn___alloc_dir : func :=
  mkFunc (a "__alloc_dir") (a "export") (RClass P)
    [(W, a "v0"); (W, a "v2"); (W, a "v4"); (P, a "v6")]
    [mkBlock (a "start") []
       [Let (a "v11") W (Ext Ub) [t "v2"];
        Let (a "v12") W (Cmp Eq W) [t "v11"; k 0]]
       (JBranch (t "v12") (to "L13") (to "L14"));
     mkBlock (a "L13") []
       [Call (CResult (a "v16") W) (g "__GI___fcntl64_nocancel") [Arg W (t "v0"); Arg W (k 2); Arg W (k 1)];
        Let (a "v17") W (Cmp Slt W) [t "v16"; k 0]]
       (JGoto (to "L14"));
     mkBlock (a "L14") [Phi (a "v21") W [(a "start", k 0); (a "L13", t "v17")]]
       []
       (JBranch (t "v21") (to "L8") (to "L10"));
     mkBlock (a "L8") []
       []
       (JRet (k 0));
     mkBlock (a "L10") []
       [padd "v31" "v6" (k 56);
        Let (a "chk0") A (Check 0 8 Read 1) [t "v31"];
        Let (a "v32") L (RawLoad LdL 0) [t "chk0"];
        Let (a "v33") W (Cmp Ugt L) [t "v32"; k 32768]]
       (JBranch (t "v33") (to "L27") (to "L29"));
     mkBlock (a "L27") []
       [padd "v35" "v6" (k 56);
        Let (a "v36") L (RawLoad LdL 0) [t "chk0"]]
       (JGoto (to "L29"));
     mkBlock (a "L29") [Phi (a "v37") L [(a "L27", t "v36"); (a "L10", k 32768)]]
       [Let (a "v38") W (Cmp Ult L) [t "v37"; k 1048576]]
       (JBranch (t "v38") (to "L24") (to "L26"));
     mkBlock (a "L24") []
       [padd "v43" "v6" (k 56);
        Let (a "v44") L (RawLoad LdL 0) [t "chk0"];
        Let (a "v45") W (Cmp Ugt L) [t "v44"; k 32768]]
       (JBranch (t "v45") (to "L39") (to "L26"));
     mkBlock (a "L39") []
       [padd "v47" "v6" (k 56);
        Let (a "v48") L (RawLoad LdL 0) [t "chk0"]]
       (JGoto (to "L26"));
     mkBlock (a "L26") [Phi (a "v50") L [(a "L39", t "v48"); (a "L24", k 32768); (a "L29", k 1048576)]]
       [Let (a "v53") L Add [t "v50"; k 48];
        Call (CResult (a "v54") P) (g "malloc") [Arg L (t "v53")];
        Let (a "v59") L Ptoi [t "v54"];
        Let (a "v60") L Ptoi [k 0];
        Let (a "v61") W (Cmp Eq L) [t "v59"; t "v60"]]
       (JBranch (t "v61") (to "L55") (to "L57"));
     mkBlock (a "L55") []
       []
       (JBranch (t "v11") (to "L62") (to "L64"));
     mkBlock (a "L62") []
       [Call CVoid (g "__GI___close_nocancel_nostatus") [Arg W (t "v0")]]
       (JGoto (to "L64"));
     mkBlock (a "L64") []
       []
       (JRet (k 0));
     mkBlock (a "L57") []
       [Let (a "chk4") A (Check 0 4 Write 1) [t "v54"];
        RawStore Ww 0 (t "v0") (t "chk4");
        padd "v71" "v54" (k 4);
        Let (a "chk5") A (HalfCheck Upper 0 4 Write 1) [t "chk4"; t "v71"];
        RawStore Ww 0 (k 0) (t "chk5");
        padd "v73" "v54" (k 8);
        Let (a "chk6") A (HalfCheck Upper 0 8 Write 1) [t "chk4"; t "v73"];
        RawStore Wl 0 (t "v50") (t "chk6");
        padd "v76" "v54" (k 16);
        Let (a "chk7") A (HalfCheck Upper 0 8 Write 1) [t "chk4"; t "v76"];
        RawStore Wl 0 (k 0) (t "chk7");
        padd "v78" "v54" (k 24);
        Let (a "chk8") A (HalfCheck Upper 0 8 Write 1) [t "chk4"; t "v78"];
        RawStore Wl 0 (k 0) (t "chk8");
        padd "v80" "v54" (k 32);
        Let (a "chk9") A (HalfCheck Upper 0 8 Write 1) [t "chk4"; t "v80"];
        RawStore Wl 0 (k 0) (t "chk9");
        padd "v82" "v54" (k 40);
        Let (a "chk10") A (HalfCheck Upper 0 4 Write 1) [t "chk4"; t "v82"];
        RawStore Ww 0 (k 0) (t "chk10")]
       (JRet (t "v54"))].

Definition hello_image_fn_glibc_localealias'23alias_compare : func :=
  mkFunc (a "glibc_localealias#alias_compare") (a "local") (RClass W)
    [(P, a "v0"); (P, a "v2")]
    [mkBlock (a "start") []
       [Let (a "chk0") A (Check 0 8 Read 8) [t "v0"];
        Let (a "v5") P (RawLoadPointer 0 load_effects) [t "chk0"];
        Let (a "chk1") A (Check 0 8 Read 8) [t "v2"];
        Let (a "v7") P (RawLoadPointer 0 load_effects) [t "chk1"];
        Let (a "v8") P Copy [g "_nl_C_locobj"];
        Call (CResult (a "v9") W) (g "__GI___strcasecmp_l") [Arg P (t "v5"); Arg P (t "v7"); Arg P (t "v8")]]
       (JRet (t "v9"))].
