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

Definition hello_image_fn_glibc_libc_start'23init_cpu_features'blocks2 : list block :=
  [ir_blk{ @"L1199" [%"pr.11" : P = phi("L1221" => %"v1233", "L1209" => #0, "L1234" => #0, "L1260" => #0, "L1190" => #0)]:
    %"v1279" : L = Ptoi %"pr.11";
    %"v1280" : L = Ptoi #0;
    %"v1281" : W = (Cmp Eq L) %"v1279", %"v1280"
    => br %"v1281" ? "L1282" : "L1283" };
  ir_blk{ @"L1282":
    %"v1285" = %"v0" +p #20;
    %"v1286" = %"v1285" +p #32;
    %"v1287" = %"v1286" +p #16;
    %"v1288" = %"v1287" +p #4;
    %"chk248" : A = (Renew 0 4 Read 1) %"chk152", %"v1288";
    %"v1289" : W = (RawLoad (LdNarrow Uw) 0) %"chk248";
    %"v1291" : W = And %"v1289", #32;
    %"v1292" : W = (Cmp Ne W) %"v1291", #0
    => goto "L1283" };
  ir_blk{ @"L1283" [%"v1294" : W = phi("L1199" => #0, "L1282" => %"v1292")]:
    => br %"v1294" ? "L1295" : "L1296" };
  ir_blk{ @"L1295":
    %"v1298" = %"v0" +p #20;
    %"v1300" = %"v1298" +p #16;
    %"v1301" = %"v1300" +p #8;
    %"chk249" : A = (Renew 0 4 Read 1) %"chk164", %"v1301";
    %"v1302" : W = (RawLoad (LdNarrow Uw) 0) %"chk249";
    %"v1304" : W = And %"v1302", #4096;
    %"v1305" : W = (Cmp Ne W) %"v1304", #0
    => goto "L1296" };
  ir_blk{ @"L1296" [%"v1307" : W = phi("L1283" => #0, "L1295" => %"v1305")]:
    => br %"v1307" ? "L1308" : "L1309" };
  ir_blk{ @"L1308":
    %"v1311" = %"v0" +p #20;
    %"v1312" = %"v1311" +p #32;
    %"v1313" = %"v1312" +p #16;
    %"v1314" = %"v1313" +p #4;
    %"chk250" : A = (Renew 0 4 Read 1) %"chk152", %"v1314";
    %"v1315" : W = (RawLoad (LdNarrow Uw) 0) %"chk250";
    %"v1317" : W = And %"v1315", #8;
    %"v1318" : W = (Cmp Ne W) %"v1317", #0
    => goto "L1309" };
  ir_blk{ @"L1309" [%"v1320" : W = phi("L1296" => #0, "L1308" => %"v1318")]:
    => br %"v1320" ? "L1321" : "L1322" };
  ir_blk{ @"L1321":
    %"v1324" = %"v0" +p #20;
    %"v1325" = %"v1324" +p #32;
    %"v1326" = %"v1325" +p #16;
    %"v1327" = %"v1326" +p #4;
    %"chk251" : A = (Renew 0 4 Read 1) %"chk152", %"v1327";
    %"v1328" : W = (RawLoad (LdNarrow Uw) 0) %"chk251";
    %"v1330" : W = And %"v1328", #256;
    %"v1331" : W = (Cmp Ne W) %"v1330", #0
    => goto "L1322" };
  ir_blk{ @"L1322" [%"v1333" : W = phi("L1309" => #0, "L1321" => %"v1331")]:
    => br %"v1333" ? "L1334" : "L1335" };
  ir_blk{ @"L1334":
    %"v1337" = %"v0" +p #20;
    %"v1338" = %"v1337" +p #64;
    %"v1339" = %"v1338" +p #16;
    %"v1340" = %"v1339" +p #8;
    %"chk252" : A = (HalfCheck Lower 0 4 Read 1) %"chk3", %"v1340";
    %"v1341" : W = (RawLoad (LdNarrow Uw) 0) %"chk252";
    %"v1343" : W = And %"v1341", #32;
    %"v1344" : W = (Cmp Ne W) %"v1343", #0
    => goto "L1335" };
  ir_blk{ @"L1335" [%"v1346" : W = phi("L1322" => #0, "L1334" => %"v1344")]:
    => br %"v1346" ? "L1347" : "L1348" };
  ir_blk{ @"L1347":
    %"v1350" = %"v0" +p #20;
    %"v1352" = %"v1350" +p #16;
    %"v1353" = %"v1352" +p #8;
    %"chk253" : A = (Renew 0 4 Read 1) %"chk164", %"v1353";
    %"v1354" : W = (RawLoad (LdNarrow Uw) 0) %"chk253";
    %"v1356" : W = And %"v1354", #4194304;
    %"v1357" : W = (Cmp Ne W) %"v1356", #0
    => goto "L1348" };
  ir_blk{ @"L1348" [%"v1359" : W = phi("L1335" => #0, "L1347" => %"v1357")]:
    => br %"v1359" ? "L1360" : "L1361" };
  ir_blk{ @"L1360":
    %"v1363" = %"v0" +p #20;
    %"v1365" = %"v1363" +p #16;
    %"v1366" = %"v1365" +p #8;
    %"chk254" : A = (Renew 0 4 Read 1) %"chk164", %"v1366";
    %"v1367" : W = (RawLoad (LdNarrow Uw) 0) %"chk254";
    %"v1369" : W = And %"v1367", #8388608;
    %"v1370" : W = (Cmp Ne W) %"v1369", #0
    => goto "L1361" };
  ir_blk{ @"L1361" [%"v1372" : W = phi("L1348" => #0, "L1360" => %"v1370")]:
    => br %"v1372" ? "L1275" : "L1277" };
  ir_blk{ @"L1275":
    %"v1373" : P = Copy $"glibc_libc_start#str.327"
    => goto "L1277" };
  ir_blk{ @"L1277" [%"pr.14" : P = phi("L1275" => %"v1373", "L1361" => %"pr.11")]:
    %"v1378" : L = Ptoi %"pr.14";
    %"v1380" : W = (Cmp Ne L) %"v1378", %"v1280"
    => br %"v1380" ? "L1374" : "L1192" };
  ir_blk{ @"L1374":
    %"v1381" : P = Copy $"_dl_platform";
    %"chk255" : A = (Check 0 8 Write 8) %"v1381";
    store.ptr [%"chk255" + 0] <- %"pr.14"
    => goto "L1192" };
  ir_blk{ @"L1192":
    %"v1386" : P = Copy $"glibc_libc_start#_dl_tunable_set_plt_rewrite";
    call void $"__tunable_get_val"(W #1, P %"v1384", P %"v1386");
    %"chk256" : A = (Check 0 8 Read 8) %"v1384";
    %"v1387" : P = (RawLoadPointer 0 load_effects) %"chk256";
    %"iw_6.v1" : P = Copy $"_dl_x86_cpu_features";
    %"iw_6.v4" = %"iw_6.v1" +p #368;
    %"chk257" : A = (Check 0 8 Read 1) %"iw_6.v4";
    %"iw_6.v5" : L = (RawLoad LdL 0) %"chk257";
    %"iw_6.v8" : L = And %"iw_6.v5", #18446744073709551360;
    %"iw_6.v13" : W = (Cmp Sgt L) %"iw_6.v8", #0
    => br %"iw_6.v13" ? "iw_6.L9" : "iw_6.L11" };
  ir_blk{ @"iw_6.L9":
    %"iw_6.v14" : P = Copy $"__x86_data_cache_size_half";
    %"iw_6.v16" : L = Div %"iw_6.v8", #2;
    %"chk258" : A = (Check 0 8 Write 1) %"iw_6.v14";
    store Wl [%"chk258" + 0] <- %"iw_6.v16";
    %"iw_6.v17" : P = Copy $"__x86_data_cache_size";
    %"chk259" : A = (Check 0 8 Write 1) %"iw_6.v17";
    store Wl [%"chk259" + 0] <- %"iw_6.v8"
    => goto "iw_6.L11" };
  ir_blk{ @"iw_6.L11":
    %"iw_6.v21" = %"iw_6.v1" +p #376;
    %"chk260" : A = (HalfCheck Upper 0 8 Read 1) %"chk257", %"iw_6.v21";
    %"iw_6.v22" : L = (RawLoad LdL 0) %"chk260";
    %"iw_6.v25" : L = And %"iw_6.v22", #18446744073709551360;
    %"iw_6.v30" : W = (Cmp Sgt L) %"iw_6.v25", #0
    => br %"iw_6.v30" ? "iw_6.L26" : "iw_6.L28" };
  ir_blk{ @"iw_6.L26":
    %"iw_6.v31" : P = Copy $"__x86_shared_cache_size_half";
    %"iw_6.v33" : L = Div %"iw_6.v25", #2;
    %"chk261" : A = (Check 0 8 Write 1) %"iw_6.v31";
    store Wl [%"chk261" + 0] <- %"iw_6.v33";
    %"iw_6.v34" : P = Copy $"__x86_shared_cache_size";
    %"chk262" : A = (Check 0 8 Write 1) %"iw_6.v34";
    store Wl [%"chk262" + 0] <- %"iw_6.v25"
    => goto "iw_6.L28" };
  ir_blk{ @"iw_6.L28":
    %"iw_6.v36" : P = Copy $"__x86_shared_non_temporal_threshold";
    %"iw_6.v38" = %"iw_6.v1" +p #384;
    %"chk263" : A = (HalfCheck Upper 0 8 Read 1) %"chk257", %"iw_6.v38";
    %"iw_6.v39" : L = (RawLoad LdL 0) %"chk263";
    %"chk264" : A = (Check 0 8 Write 1) %"iw_6.v36";
    store Wl [%"chk264" + 0] <- %"iw_6.v39";
    %"iw_6.v40" : P = Copy $"__x86_memset_non_temporal_threshold";
    %"iw_6.v42" = %"iw_6.v1" +p #392;
    %"chk265" : A = (HalfCheck Upper 0 8 Read 1) %"chk257", %"iw_6.v42";
    %"iw_6.v43" : L = (RawLoad LdL 0) %"chk265";
    %"chk266" : A = (Check 0 8 Write 1) %"iw_6.v40";
    store Wl [%"chk266" + 0] <- %"iw_6.v43";
    %"iw_6.v44" : P = Copy $"__x86_rep_movsb_threshold";
    %"iw_6.v46" = %"iw_6.v1" +p #400;
    %"chk267" : A = (HalfCheck Upper 0 8 Read 1) %"chk257", %"iw_6.v46";
    %"iw_6.v47" : L = (RawLoad LdL 0) %"chk267";
    %"chk268" : A = (Check 0 8 Write 1) %"iw_6.v44";
    store Wl [%"chk268" + 0] <- %"iw_6.v47";
    %"iw_6.v48" : P = Copy $"__x86_rep_stosb_threshold";
    %"iw_6.v50" = %"iw_6.v1" +p #416;
    %"chk269" : A = (HalfCheck Upper 0 8 Read 1) %"chk257", %"iw_6.v50";
    %"iw_6.v51" : L = (RawLoad LdL 0) %"chk269";
    %"chk270" : A = (Check 0 8 Write 1) %"iw_6.v48";
    store Wl [%"chk270" + 0] <- %"iw_6.v51";
    %"iw_6.v52" : P = Copy $"__x86_rep_movsb_stop_threshold";
    %"iw_6.v54" = %"iw_6.v1" +p #408;
    %"chk271" : A = (HalfCheck Upper 0 8 Read 1) %"chk257", %"iw_6.v54";
    %"iw_6.v55" : L = (RawLoad LdL 0) %"chk271";
    %"chk272" : A = (Check 0 8 Write 1) %"iw_6.v52";
    store Wl [%"chk272" + 0] <- %"iw_6.v55";
    %"iw_6.v60" = %"iw_6.v1" +p #340;
    %"chk273" : A = (HalfCheck Lower 0 4 Read 1) %"chk257", %"iw_6.v60";
    %"iw_6.v62" : W = (RawLoad (LdNarrow Uw) 0) %"chk273";
    %"iw_6.v63" : W = And %"iw_6.v62", #65536;
    %"iw_6.v64" : W = (Cmp Ne W) %"iw_6.v63", #0
    => br %"iw_6.v64" ? "iw_6.L56" : "iw_6.join" };
  ir_blk{ @"iw_6.L56":
    %"iw_6.v65" : P = Copy $"__x86_string_control";
    %"chk274" : A = (Check 0 4 Read 1) %"iw_6.v65";
    %"iw_6.v66" : W = (RawLoad (LdNarrow Sw) 0) %"chk274";
    %"iw_6.v68" : W = Or %"iw_6.v66", #1;
    %"chk275" : A = (Renew 0 4 Write 1) %"chk274", %"iw_6.v65";
    store Ww [%"chk275" + 0] <- %"iw_6.v68"
    => goto "iw_6.join" };
  ir_blk{ @"iw_6.join":
    => ret void }].
