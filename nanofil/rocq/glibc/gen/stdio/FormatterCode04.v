(** This file retains complete items or blocks of glibc's checked formatter.
    stdio/code.sh regenerates it from the pinned capture. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Glibc Require Import CodePrelude.
From Nanofil Require Import CaptureNotation.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

(** These blocks retain their order in the linked module. *)
Definition formatter_blocks_04 : list term :=
  [
        cap_blk{ @"L1118" [phi %"v1142" : "l" = ("L1117" => %"v1141", "L1122" => #0)]:
          %"v1143" : "w" = "copy" %"v1142";
          %"v1144" : "l" = op "ext"("sw") %"v1143";
          %"v1145" = #1 +p %"v1144";
          %"v1147" : "l" = "ptoi" %"v1145"
          => goto "L144" };
        cap_blk{ @"L1151":
          call void $"glibc_vfprintf_internal#__printf_buffer_putc"("p" %"v0", "w" #37)
          => goto "L1150" };
        cap_blk{ @"L1155":
          => br %"pr.62" ? "L1173" : "L1174" };
        cap_blk{ @"L1173":
          %"v1178" : "l" = "va_arg" %"v4"
          => goto "L1175" };
        cap_blk{ @"L1174":
          => br %"pr.65" ? "L1179" : "L1180" };
        cap_blk{ @"L1179":
          %"v1184" : "w" = "va_arg" %"v4";
          %"v1185" : "w" = op "ext"("sb") %"v1184";
          %"v1186" : "l" = op "ext"("sw") %"v1185"
          => goto "L1175" };
        cap_blk{ @"L1180":
          %"v1191" : "w" = op "cmp"("eq", "w") %"pr.60", #0
          => br %"v1191" ? "L1187" : "L1188" };
        cap_blk{ @"L1187":
          %"v1193" : "w" = "va_arg" %"v4";
          %"v1194" : "l" = op "ext"("sw") %"v1193"
          => goto "L1175" };
        cap_blk{ @"L1188":
          %"v1196" : "w" = "va_arg" %"v4";
          %"v1197" : "w" = op "ext"("sh") %"v1196";
          %"v1198" : "l" = op "ext"("sw") %"v1197"
          => goto "L1175" };
        cap_blk{ @"L1175" [phi %"pr.103" : "l" = ("L1173" => %"v1178", "L1179" => %"v1186", "L1187" => %"v1194", "L1188" => %"v1198")]:
          %"v1200" : "w" = op "cmp"("slt", "l") %"pr.103", #0
          => br %"v1200" ? "L1201" : "L1209" };
        cap_blk{ @"L1201":
          %"v1206" : "l" = "neg" %"pr.103"
          => goto "L1209" };
        cap_blk{ @"L1211" [phi %"pr.29" : "w" = ("L2195" => #10, "L2198" => #8, "L2200" => #16, "L2226" => #2)]:
          => br %"pr.62" ? "L1258" : "L1259" };
        cap_blk{ @"L1258":
          %"v1263" : "l" = "va_arg" %"v4"
          => goto "L1209" };
        cap_blk{ @"L1259":
          => br %"pr.65" ? "L1264" : "L1265" };
        cap_blk{ @"L1264":
          %"v1269" : "w" = "va_arg" %"v4";
          %"v1270" : "w" = op "ext"("ub") %"v1269";
          %"v1271" : "l" = op "ext"("uw") %"v1270"
          => goto "L1209" };
        cap_blk{ @"L1265":
          %"v1276" : "w" = op "cmp"("eq", "w") %"pr.60", #0
          => br %"v1276" ? "L1272" : "L1273" };
        cap_blk{ @"L1272":
          %"v1278" : "w" = "va_arg" %"v4";
          %"v1279" : "l" = op "ext"("uw") %"v1278"
          => goto "L1209" };
        cap_blk{ @"L1273":
          %"v1281" : "w" = "va_arg" %"v4";
          %"v1282" : "w" = op "ext"("uh") %"v1281";
          %"v1283" : "l" = op "ext"("uw") %"v1282"
          => goto "L1209" };
        cap_blk{ @"L1209" [phi %"pr.95" : "w" = ("L1201" => %"pr.97", "L1175" => %"pr.97", "L1258" => %"pr.97", "L1264" => %"pr.97", "L1272" => %"pr.97", "L1273" => %"pr.97", "L1674" => #120, "L1789" => %"pr.97", "L1778" => %"pr.97"); phi %"pr.53" : "w" = ("L1201" => %"pr.55", "L1175" => %"pr.55", "L1258" => %"pr.55", "L1264" => %"pr.55", "L1272" => %"pr.55", "L1273" => %"pr.55", "L1674" => #0, "L1789" => %"pr.55", "L1778" => %"pr.55"); phi %"pr.50" : "w" = ("L1201" => %"pr.52", "L1175" => %"pr.52", "L1258" => #0, "L1264" => #0, "L1272" => #0, "L1273" => #0, "L1674" => %"pr.52", "L1789" => %"pr.52", "L1778" => %"pr.52"); phi %"pr.44" : "w" = ("L1201" => %"pr.46", "L1175" => %"pr.46", "L1258" => #0, "L1264" => #0, "L1272" => #0, "L1273" => #0, "L1674" => %"pr.46", "L1789" => %"pr.46", "L1778" => %"pr.46"); phi %"pr.40" : "w" = ("L1201" => %"pr.42", "L1175" => %"pr.42", "L1258" => %"pr.42", "L1264" => %"pr.42", "L1272" => %"pr.42", "L1273" => %"pr.42", "L1674" => #1, "L1789" => %"pr.42", "L1778" => %"pr.42"); phi %"pr.28" : "w" = ("L1201" => #10, "L1175" => #10, "L1258" => %"pr.29", "L1264" => %"pr.29", "L1272" => %"pr.29", "L1273" => %"pr.29", "L1674" => #16, "L1789" => #10, "L1778" => #10); phi %"pr.21" : "l" = ("L1201" => %"v1206", "L1175" => %"pr.103", "L1258" => %"v1263", "L1264" => %"v1271", "L1272" => %"v1279", "L1273" => %"v1283", "L1674" => %"v1682", "L1789" => %"v1794", "L1778" => %"v1788"); phi %"pr.18" : "w" = ("L1201" => %"v1200", "L1175" => %"v1200", "L1258" => #0, "L1264" => #0, "L1272" => #0, "L1273" => #0, "L1674" => #0, "L1789" => %"v1786", "L1778" => %"v1786")]:
          %"v1288" : "w" = op "cmp"("slt", "w") %"pr.82", #0
          => br %"v1288" ? "L1286" : "L1285" };
        cap_blk{ @"L1285":
          => goto "L1286" };
        cap_blk{ @"L1286" [phi %"pr.91" : "w" = ("L1285" => #32, "L1209" => %"pr.92"); phi %"pr.81" : "w" = ("L1285" => %"pr.82", "L1209" => #1)]:
          %"v1293" : "w" = op "cmp"("eq", "w") %"pr.81", #0
          => br %"v1293" ? "L1294" : "L1295" };
        cap_blk{ @"L1294":
          %"v1297" : "w" = op "cmp"("eq", "l") %"pr.21", #0
          => goto "L1295" };
        cap_blk{ @"L1295" [phi %"v1299" : "w" = ("L1286" => #0, "L1294" => %"v1297")]:
          => br %"v1299" ? "L1289" : "L1290" };
        cap_blk{ @"L1289":
          %"v1305" : "w" = op "cmp"("eq", "w") %"pr.28", #8
          => br %"v1305" ? "L1306" : "L1307" };
        cap_blk{ @"L1306":
          => goto "L1307" };
        cap_blk{ @"L1307" [phi %"v1310" : "w" = ("L1289" => #0, "L1306" => %"pr.40")]:
          => br %"v1310" ? "L1301" : "L1291" };
        cap_blk{ @"L1301":
          (op "flight"(%"v1312", "sub", [op "address"(%"v102"); #1], op "lower"(%"v102")));
          %"chk144" : "a" = op "check"(int 0, int 1, "write", int 1) %"v1312";
          store "b" [%"chk144" + 0] <- #48
          => goto "L1291" };
        cap_blk{ @"L1290":
          %"v1316" : "w" = op "ext"("sb") %"pr.95";
          %"v1317" : "w" = op "cmp"("eq", "w") %"v1316", #88;
          call %"v1318" : "p" = $"_itoa_word"("l" %"pr.21", "p" %"v102", "w" %"pr.28", "w" %"v1317")
          => goto "L1291" };
        cap_blk{ @"L1291" [phi %"pr.34" : "p" = ("L1290" => %"v1318", "L1301" => %"v1312", "L1307" => %"v102")]:
          => br %"pr.53" ? "L1323" : "L1322" };
        cap_blk{ @"L1322":
          => br %"pr.88" ? "L1325" : "L1323" };
        cap_blk{ @"L1325":
          %"v1328" : "w" = op "cmp"("eq", "w") %"pr.28", #10
          => goto "L1323" };
        cap_blk{ @"L1323" [phi %"v1332" : "w" = ("L1291" => #1, "L1322" => #0, "L1325" => %"v1328")]:
          => br %"pr.53" ? "L1334" : "L1335" };
        cap_blk{ @"L1334":
          %"v1338" : "p" = "copy" $"__libc_tsd_LOCALE";
          %"chk145" : "a" = op "check"(int 0, int 8, "read", int 8) %"v1338";
          %"v1339" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk145";
          %"v1342" : "l" = "ptoi" %"v102";
          %"v1343" : "l" = "ptoi" %"pr.34";
          %"v1344" : "l" = "sub" %"v1342", %"v1343";
          call %"v1345" : "w" = $"__grouping_iterator_init"("p" %"v1319", "w" #1, "p" %"v1339", "w" %"v1344")
          => goto "L1336" };
        cap_blk{ @"L1335":
          => br %"pr.88" ? "L1351" : "L1352" };
        cap_blk{ @"L1351":
          %"v1354" : "w" = op "cmp"("eq", "w") %"pr.28", #10
          => goto "L1352" };
        cap_blk{ @"L1352" [phi %"v1356" : "w" = ("L1335" => #0, "L1351" => %"v1354")]:
          => br %"v1356" ? "L1347" : "L1336" };
        cap_blk{ @"L1347":
          %"v1359" : "l" = "ptoi" %"v102";
          %"v1360" : "l" = "ptoi" %"pr.34";
          %"v1361" : "l" = "sub" %"v1359", %"v1360";
          call %"v1362" : "w" = $"__grouping_iterator_init_none"("p" %"v1319", "w" %"v1361")
          => goto "L1336" };
        cap_blk{ @"L1336":
          => br %"pr.88" ? "L1369" : "L1370" };
        cap_blk{ @"L1369":
          %"v1372" : "w" = op "cmp"("eq", "w") %"pr.28", #10
          => goto "L1370" };
        cap_blk{ @"L1370" [phi %"v1374" : "w" = ("L1336" => #0, "L1369" => %"v1372")]:
          => br %"v1374" ? "L1365" : "L1366" };
        cap_blk{ @"L1365":
          %"v1375" : "p" = "copy" $"__libc_tsd_LOCALE";
          %"chk146" : "a" = op "check"(int 0, int 8, "read", int 8) %"v1375";
          %"v1376" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk146";
          call %"v1379" : "w" = $"__translated_number_width"("p" %"v1376", "p" %"pr.34", "p" %"v102")
          => goto "L1367" };
        cap_blk{ @"L1366":
          %"v1382" : "l" = "ptoi" %"v102";
          %"v1383" : "l" = "ptoi" %"pr.34";
          %"v1384" : "l" = "sub" %"v1382", %"v1383"
          => goto "L1367" };
        cap_blk{ @"L1367" [phi %"pr.106" : "w" = ("L1365" => %"v1379", "L1366" => %"v1384")]:
          => br %"pr.53" ? "L1385" : "L1387" };
        cap_blk{ @"L1385":
          %"v1390" = %"v1319" +p #20;
          %"chk147" : "a" = op "check"(int 0, int 4, "read", int 1) %"v1390";
          %"v1391" : "w" = op "raw_load"("uw", int 0) %"chk147";
          call %"v1393" : "l" = $"__GI_strlen"("p" %"pr.1");
          %"v1394" : "l" = op "ext"("uw") %"v1391";
          %"v1395" : "l" = "mul" %"v1394", %"v1393";
          %"v1396" : "l" = op "ext"("sw") %"pr.106";
          %"v1397" : "l" = "add" %"v1396", %"v1395"
          => goto "L1387" };
        cap_blk{ @"L1387" [phi %"pr.107" : "w" = ("L1385" => %"v1397", "L1367" => %"pr.106")]:
          %"v1401" : "w" = op "cmp"("sle", "w") %"pr.81", %"pr.107"
          => br %"v1401" ? "L1402" : "L1403" };
        cap_blk{ @"L1402":
          %"v1405" : "w" = op "cmp"("ne", "l") %"pr.21", #0
          => goto "L1403" };
        cap_blk{ @"L1403" [phi %"v1407" : "w" = ("L1387" => #0, "L1402" => %"v1405")]:
          => br %"v1407" ? "L1408" : "L1409" };
        cap_blk{ @"L1408":
          => goto "L1409" };
        cap_blk{ @"L1409" [phi %"v1412" : "w" = ("L1403" => #0, "L1408" => %"pr.40")]:
          => br %"v1412" ? "L1413" : "L1414" };
        cap_blk{ @"L1413":
          %"v1416" : "w" = op "cmp"("eq", "w") %"pr.28", #8
          => goto "L1414" };
        cap_blk{ @"L1414" [phi %"v1418" : "w" = ("L1409" => #0, "L1413" => %"v1416")]:
          %"v1427" : "l" = "ptoi" %"v102";
          %"v1428" : "l" = "ptoi" %"pr.34";
          %"v1429" : "l" = "sub" %"v1427", %"v1428";
          %"v1430" : "l" = op "ext"("sw") %"pr.81";
          %"v1431" : "l" = "sub" %"v1430", %"v1429";
          %"v1432" : "w" = op "cmp"("slt", "l") %"v1431", #0
          => br %"v1432" ? "L1423" : "L1422" };
        cap_blk{ @"L1422":
          => goto "L1423" };
        cap_blk{ @"L1423" [phi %"v1441" : "l" = ("L1422" => %"v1431", "L1414" => #0)]:
          %"v1446" : "w" = op "cmp"("eq", "w") %"pr.47", #0
          => br %"v1446" ? "L1442" : "L1443" };
        cap_blk{ @"L1442":
          %"v1449" : "w" = "copy" %"v1441";
          %"v1450" : "w" = "add" %"pr.107", %"v1449";
          %"v1451" : "w" = "sub" %"pr.66", %"v1450";
          %"v1456" : "w" = op "cmp"("ne", "l") %"pr.21", #0
          => br %"v1456" ? "L1457" : "L1458" };
        cap_blk{ @"L1457":
          => goto "L1458" };
        cap_blk{ @"L1458" [phi %"v1461" : "w" = ("L1442" => #0, "L1457" => %"pr.40")]:
          => br %"v1461" ? "L1462" : "L1463" };
        cap_blk{ @"L1462":
          %"v1465" : "w" = op "cmp"("eq", "w") %"pr.28", #16
          => br %"v1465" ? "L1463" : "L1466" };
        cap_blk{ @"L1466":
          %"v1469" : "w" = op "cmp"("eq", "w") %"pr.28", #2
          => goto "L1463" };
        cap_blk{ @"L1463" [phi %"v1473" : "w" = ("L1458" => #0, "L1462" => #1, "L1466" => %"v1469")]:
          => br %"v1473" ? "L1452" : "L1454" };
        cap_blk{ @"L1452":
          %"v1475" : "w" = "sub" %"v1451", #2
          => goto "L1454" };
        cap_blk{ @"L1454" [phi %"pr.67" : "w" = ("L1452" => %"v1475", "L1463" => %"v1451")]:
          => br %"v1418" ? "L1476" : "L1478" };
        cap_blk{ @"L1476":
          %"v1481" : "w" = "sub" %"pr.67", #1
          => goto "L1478" };
        cap_blk{ @"L1478" [phi %"pr.68" : "w" = ("L1476" => %"v1481", "L1454" => %"pr.67")]:
          => br %"pr.18" ? "L1487" : "L1486" };
        cap_blk{ @"L1486":
          => goto "L1487" };
        cap_blk{ @"L1487" [phi %"v1490" : "w" = ("L1478" => #1, "L1486" => %"pr.50")]:
          => br %"v1490" ? "L1492" : "L1491" };
        cap_blk{ @"L1491":
          => goto "L1492" };
        cap_blk{ @"L1492" [phi %"v1495" : "w" = ("L1487" => #1, "L1491" => %"pr.44")]:
          => br %"v1495" ? "L1482" : "L1484" };
        cap_blk{ @"L1482":
          %"v1497" : "w" = "sub" %"pr.68", #1
          => goto "L1484" };
        cap_blk{ @"L1484" [phi %"pr.69" : "w" = ("L1482" => %"v1497", "L1492" => %"pr.68")]:
          %"v1501" : "w" = op "ext"("ub") %"pr.91";
          %"v1502" : "w" = op "cmp"("eq", "w") %"v1501", #32
          => br %"v1502" ? "L1498" : "L1500" };
        cap_blk{ @"L1498":
          %"v1505" : "l" = op "ext"("sw") %"pr.69";
          call void $"glibc_vfprintf_internal#__printf_buffer_pad"("p" %"v0", "w" #32, "l" %"v1505")
          => goto "L1500" };
        cap_blk{ @"L1500" [phi %"pr.70" : "w" = ("L1498" => #0, "L1484" => %"pr.69")]:
          => br %"pr.18" ? "L1506" : "L1507" };
        cap_blk{ @"L1506":
          call void $"glibc_vfprintf_internal#__printf_buffer_putc"("p" %"v0", "w" #45)
          => goto "L1508" };
        cap_blk{ @"L1507":
          => br %"pr.50" ? "L1511" : "L1512" };
        cap_blk{ @"L1511":
          call void $"glibc_vfprintf_internal#__printf_buffer_putc"("p" %"v0", "w" #43)
          => goto "L1508" };
        cap_blk{ @"L1512":
          => br %"pr.44" ? "L1516" : "L1508" };
        cap_blk{ @"L1516":
          call void $"glibc_vfprintf_internal#__printf_buffer_putc"("p" %"v0", "w" #32)
          => goto "L1508" };
        cap_blk{ @"L1508":
          => br %"v1456" ? "L1526" : "L1527" };
        cap_blk{ @"L1526":
          => goto "L1527" };
        cap_blk{ @"L1527" [phi %"v1530" : "w" = ("L1508" => #0, "L1526" => %"pr.40")]:
          => br %"v1530" ? "L1531" : "L1532" };
        cap_blk{ @"L1531":
          %"v1534" : "w" = op "cmp"("eq", "w") %"pr.28", #16
          => br %"v1534" ? "L1532" : "L1535" };
        cap_blk{ @"L1535":
          %"v1538" : "w" = op "cmp"("eq", "w") %"pr.28", #2
          => goto "L1532" };
        cap_blk{ @"L1532" [phi %"v1542" : "w" = ("L1527" => #0, "L1531" => #1, "L1535" => %"v1538")]:
          => br %"v1542" ? "L1521" : "L1523" };
        cap_blk{ @"L1521":
          call void $"glibc_vfprintf_internal#__printf_buffer_putc"("p" %"v0", "w" #48);
          %"v1545" : "w" = op "ext"("sb") %"pr.95";
          call void $"glibc_vfprintf_internal#__printf_buffer_putc"("p" %"v0", "w" %"v1545")
          => goto "L1523" };
        cap_blk{ @"L1523":
          %"v1547" : "w" = "copy" %"v1441";
          %"v1548" : "w" = "add" %"pr.70", %"v1547";
          %"v1551" : "l" = op "ext"("sw") %"v1548";
          call void $"glibc_vfprintf_internal#__printf_buffer_pad"("p" %"v0", "w" #48, "l" %"v1551")
          => br %"v1418" ? "L1552" : "L1554" };
        cap_blk{ @"L1552":
          call void $"glibc_vfprintf_internal#__printf_buffer_putc"("p" %"v0", "w" #48)
          => goto "L1554" };
        cap_blk{ @"L1554":
          => br %"v1332" ? "L1557" : "L1558" };
        cap_blk{ @"L1557":
          => br %"pr.88" ? "L1566" : "L1567" };
        cap_blk{ @"L1566":
          %"v1569" : "w" = op "cmp"("eq", "w") %"pr.28", #10
          => goto "L1567" };
        cap_blk{ @"L1567" [phi %"v1571" : "w" = ("L1557" => #0, "L1566" => %"v1569")]:
          call void $"glibc_vfprintf_internal#group_number"("p" %"v0", "p" %"v1319", "p" %"pr.34", "p" %"v102", "p" %"pr.1", "w" %"v1571")
          => goto "L1150" };
        cap_blk{ @"L1558":
          call void $"__printf_buffer_write"("p" %"v0", "p" %"pr.34", "l" %"v1429")
          => goto "L1150" };
        cap_blk{ @"L1443":
          => br %"pr.18" ? "L1581" : "L1582" };
        cap_blk{ @"L1581":
          call void $"glibc_vfprintf_internal#__printf_buffer_putc"("p" %"v0", "w" #45);
          %"v1587" : "w" = "sub" %"pr.66", #1
          => goto "L1583" };
        cap_blk{ @"L1582":
          => br %"pr.50" ? "L1588" : "L1589" };
        cap_blk{ @"L1588":
          call void $"glibc_vfprintf_internal#__printf_buffer_putc"("p" %"v0", "w" #43);
          %"v1594" : "w" = "sub" %"pr.66", #1
          => goto "L1583" };
        cap_blk{ @"L1589":
          => br %"pr.44" ? "L1595" : "L1583" };
        cap_blk{ @"L1595":
          call void $"glibc_vfprintf_internal#__printf_buffer_putc"("p" %"v0", "w" #32);
          %"v1601" : "w" = "sub" %"pr.66", #1
          => goto "L1583" };
        cap_blk{ @"L1583" [phi %"pr.71" : "w" = ("L1581" => %"v1587", "L1588" => %"v1594", "L1595" => %"v1601", "L1589" => %"pr.66")]:
          %"v1606" : "w" = op "cmp"("ne", "l") %"pr.21", #0
          => br %"v1606" ? "L1607" : "L1608" };
        cap_blk{ @"L1607":
          => goto "L1608" };
        cap_blk{ @"L1608" [phi %"v1611" : "w" = ("L1583" => #0, "L1607" => %"pr.40")]:
          => br %"v1611" ? "L1612" : "L1613" };
        cap_blk{ @"L1612":
          %"v1615" : "w" = op "cmp"("eq", "w") %"pr.28", #16
          => br %"v1615" ? "L1613" : "L1616" };
        cap_blk{ @"L1616":
          %"v1619" : "w" = op "cmp"("eq", "w") %"pr.28", #2
          => goto "L1613" };
        cap_blk{ @"L1613" [phi %"v1623" : "w" = ("L1608" => #0, "L1612" => #1, "L1616" => %"v1619")]:
          => br %"v1623" ? "L1602" : "L1604" };
        cap_blk{ @"L1602":
          call void $"glibc_vfprintf_internal#__printf_buffer_putc"("p" %"v0", "w" #48);
          %"v1626" : "w" = op "ext"("sb") %"pr.95";
          call void $"glibc_vfprintf_internal#__printf_buffer_putc"("p" %"v0", "w" %"v1626");
          %"v1628" : "w" = "sub" %"pr.71", #2
          => goto "L1604" };
        cap_blk{ @"L1604" [phi %"pr.74" : "w" = ("L1602" => %"v1628", "L1613" => %"pr.71")]:
          => br %"v1418" ? "L1629" : "L1631" };
        cap_blk{ @"L1629":
          %"v1634" : "w" = "sub" %"pr.74", #1
          => goto "L1631" };
        cap_blk{ @"L1631" [phi %"pr.75" : "w" = ("L1629" => %"v1634", "L1604" => %"pr.74")]:
          %"v1637" : "w" = "copy" %"v1441";
          %"v1638" : "w" = "add" %"pr.107", %"v1637";
          %"v1639" : "w" = "sub" %"pr.75", %"v1638";
          %"v1641" : "w" = "copy" %"v1441";
          %"v1642" : "l" = op "ext"("uw") %"v1641";
          call void $"glibc_vfprintf_internal#__printf_buffer_pad"("p" %"v0", "w" #48, "l" %"v1642")
          => br %"v1418" ? "L1643" : "L1645" };
        cap_blk{ @"L1643":
          call void $"glibc_vfprintf_internal#__printf_buffer_putc"("p" %"v0", "w" #48)
          => goto "L1645" };
        cap_blk{ @"L1645":
          => br %"v1332" ? "L1648" : "L1649" };
        cap_blk{ @"L1648":
          => br %"pr.88" ? "L1657" : "L1658" };
        cap_blk{ @"L1657":
          %"v1660" : "w" = op "cmp"("eq", "w") %"pr.28", #10
          => goto "L1658" };
        cap_blk{ @"L1658" [phi %"v1662" : "w" = ("L1648" => #0, "L1657" => %"v1660")]:
          call void $"glibc_vfprintf_internal#group_number"("p" %"v0", "p" %"v1319", "p" %"pr.34", "p" %"v102", "p" %"pr.1", "w" %"v1662")
          => goto "L1650" };
        cap_blk{ @"L1649":
          call void $"__printf_buffer_write"("p" %"v0", "p" %"pr.34", "l" %"v1429")
          => goto "L1650" };
        cap_blk{ @"L1650":
          %"v1673" : "l" = op "ext"("sw") %"v1639";
          call void $"glibc_vfprintf_internal#__printf_buffer_pad"("p" %"v0", "w" #32, "l" %"v1673")
          => goto "L1150" };
        cap_blk{ @"L1674":
          %"v1677" : "p" = "va_arg" %"v4";
          %"v1682" : "l" = "ptoi" %"v1677";
          %"v1684" : "w" = op "cmp"("ne", "l") %"v1682", %"v55"
          => br %"v1684" ? poll "L1209" : "L1679" };
        cap_blk{ @"L1679":
          %"v1688" : "p" = "copy" $"glibc_vfprintf_internal#str.284";
          %"v1693" : "w" = op "cmp"("slt", "w") %"pr.82", #5
          => br %"v1693" ? "L1695" : "L1690" };
        cap_blk{ @"L1690":
          => goto "L1695" };
        cap_blk{ @"L1696":
          %"v1701" : "w" = "and" %"v6", #2;
          %"v1702" : "w" = op "cmp"("ne", "w") %"v1701", #0
          => br %"v1702" ? "L1697" : "L1699" };
        cap_blk{ @"L1697":
          %"v1707" : "w" = op "cmp"("eq", "w") %"pr.16", #0
          => br %"v1707" ? "L1703" : "L1705" };
        cap_blk{ @"L1703":
          call %"v1710" : "l" = $"__GI_strlen"("p" %"v2");
          %"v1711" : "l" = "add" %"v1710", #1;
          call %"v1713" : "w" = $"__readonly_area"("p" %"v2", "l" %"v1711")
          => goto "L1705" };
        cap_blk{ @"L1705" [phi %"pr.14" : "w" = ("L1703" => %"v1713", "L1697" => %"pr.16")]:
          %"v1724" : "w" = op "cmp"("eq", "w") %"pr.14", #1
          => br %"v1724" ? "L1717" : "L1725" };
        cap_blk{ @"L1717":
          %"v1718" : "p" = "copy" $"glibc_vfprintf_internal#str.285";
          call void $"__GI___libc_fatal"("p" %"v1718")
          => goto "L1719" };
        cap_blk{ @"L1719":
          %"v1720" : "p" = "copy" $"glibc_vfprintf_internal#str.286";
          call void $"__GI___libc_fatal"("p" %"v1720")
          => goto "L1699" };
        cap_blk{ @"L1725":
          %"v1726" : "w" = op "cmp"("eq", "w") %"pr.14", #3
          => br %"v1726" ? poll "L1719" : "L1727" };
        cap_blk{ @"L1727":
          %"v1728" : "w" = op "cmp"("eq", "w") %"pr.14", #2
          => br %"v1728" ? "L1699" : "L1729" };
        cap_blk{ @"L1729":
          %"v1730" : "w" = op "cmp"("eq", "w") %"pr.14", #0
          => br %"v1730" ? "L1699" : "L1731" };
        cap_blk{ @"L1731":
          => goto "L1699" };
        cap_blk{ @"L1699" [phi %"pr.13" : "w" = ("L1731" => %"pr.14", "L1729" => %"pr.14", "L1719" => %"pr.14", "L1727" => %"pr.14", "L1696" => %"pr.16")]:
          %"v1734" : "p" = "va_arg" %"v4";
          call %"v1737" : "w" = $"__printf_buffer_done"("p" %"v0")
          => br %"pr.62" ? "L1744" : "L1745" };
        cap_blk{ @"L1744":
          %"v1750" : "l" = op "ext"("uw") %"v1737";
          %"chk148" : "a" = op "check"(int 0, int 8, "write", int 1) %"v1734";
          store "l" [%"chk148" + 0] <- %"v1750"
          => goto "L1150" };
        cap_blk{ @"L1745":
          => br %"pr.65" ? "L1751" : "L1752" };
        cap_blk{ @"L1751":
          %"v1757" : "w" = op "ext"("sb") %"v1737";
          %"chk149" : "a" = op "check"(int 0, int 1, "write", int 1) %"v1734";
          store "b" [%"chk149" + 0] <- %"v1757"
          => goto "L1150" };
        cap_blk{ @"L1752":
          %"v1762" : "w" = op "cmp"("eq", "w") %"pr.60", #0
          => br %"v1762" ? "L1758" : "L1759" };
        cap_blk{ @"L1758":
          %"chk150" : "a" = op "check"(int 0, int 4, "write", int 1) %"v1734";
          store "w" [%"chk150" + 0] <- %"v1737"
          => goto "L1150" };
        cap_blk{ @"L1759":
          %"v1767" : "w" = op "ext"("sh") %"v1737";
          %"chk151" : "a" = op "check"(int 0, int 2, "write", int 1) %"v1734";
          store "h" [%"chk151" + 0] <- %"v1767"
          => goto "L1150" };
        cap_blk{ @"L1768":
          => br %"pr.42" ? "L1769" : "L1770" };
        cap_blk{ @"L1769":
          call %"v1774" : "p" = $"__get_errname"("w" %"v19")
          => goto "L1771" };
        cap_blk{ @"L1770":
          call %"v1777" : "p" = $"__GI___strerror_r"("w" %"v19", "p" %"v13", "l" #1000)
          => goto "L1771" };
        cap_blk{ @"L1771" [phi %"pr.37" : "p" = ("L1769" => %"v1774", "L1770" => %"v1777")]:
          %"v1782" : "l" = "ptoi" %"pr.37";
          %"v1784" : "w" = op "cmp"("eq", "l") %"v1782", %"v55"
          => br %"v1784" ? "L1778" : "L1695" };
        cap_blk{ @"L1778":
          %"v1786" : "w" = op "cmp"("slt", "w") %"v19", #0;
          %"v1788" : "l" = op "ext"("sw") %"v19"
          => br %"v1786" ? "L1789" : poll "L1209" };
        cap_blk{ @"L1789":
          %"v1794" : "l" = "neg" %"v1788"
          => goto poll "L1209" };
        cap_blk{ @"L1796":
          => br %"pr.62" ? "L1801" : "L1799" };
        cap_blk{ @"L1799":
          %"v1804" : "w" = "sub" %"pr.66", #1;
          %"v1809" : "w" = op "cmp"("eq", "w") %"pr.47", #0
          => br %"v1809" ? "L1805" : "L1807" };
        cap_blk{ @"L1805":
          %"v1812" : "l" = op "ext"("sw") %"v1804";
          call void $"glibc_vfprintf_internal#__printf_buffer_pad"("p" %"v0", "w" #32, "l" %"v1812")
          => goto "L1807" };
        cap_blk{ @"L1807":
          %"v1815" : "w" = "va_arg" %"v4";
          %"v1816" : "w" = op "ext"("ub") %"v1815";
          %"v1817" : "w" = op "ext"("sb") %"v1816";
          call void $"glibc_vfprintf_internal#__printf_buffer_putc"("p" %"v0", "w" %"v1817")
          => br %"pr.47" ? "L1818" : "L1150" };
        cap_blk{ @"L1818":
          %"v1824" : "l" = op "ext"("sw") %"v1804";
          call void $"glibc_vfprintf_internal#__printf_buffer_pad"("p" %"v0", "w" #32, "l" %"v1824")
          => goto "L1150" };
        cap_blk{ @"L1825":
          %"v1828" : "p" = "va_arg" %"v4"
          => goto "L1695" };
        cap_blk{ @"L1695" [phi %"pr.84" : "w" = ("L1825" => %"pr.82", "L1690" => %"pr.82", "L1679" => #5, "L1771" => %"pr.82"); phi %"pr.63" : "w" = ("L1825" => %"pr.62", "L1690" => #0, "L1679" => #0, "L1771" => #0); phi %"pr.36" : "p" = ("L1825" => %"v1828", "L1690" => %"v1688", "L1679" => %"v1688", "L1771" => %"pr.37")]:
          %"v1833" : "l" = "ptoi" %"pr.36";
          %"v1835" : "w" = op "cmp"("eq", "l") %"v1833", %"v55"
          => br %"v1835" ? "L1829" : "L1830" };
        cap_blk{ @"L1829":
          %"v1841" : "w" = op "cmp"("eq", "w") %"pr.84", #4294967295
          => br %"v1841" ? "L1843" : "L1842" };
        cap_blk{ @"L1842":
          %"v1849" : "w" = op "cmp"("sge", "w") %"pr.84", #6
          => goto "L1843" };
        cap_blk{ @"L1843" [phi %"v1851" : "w" = ("L1829" => #1, "L1842" => %"v1849")]:
          => br %"v1851" ? "L1836" : "L1837" };
        cap_blk{ @"L1836":
          %"v1852" : "p" = "copy" $"glibc_vfprintf_internal#null"
          => goto "L1831" };
        cap_blk{ @"L1837":
          %"v1857" : "p" = "copy" $"glibc_vfprintf_internal#str.289"
          => goto "L1831" };
        cap_blk{ @"L1830":
          %"v1862" : "w" = op "cmp"("eq", "w") %"pr.63", #0
          => br %"v1862" ? "L1863" : "L1864" };
        cap_blk{ @"L1863":
          %"v1865" : "w" = op "ext"("sb") %"pr.97";
          %"v1866" : "w" = op "cmp"("ne", "w") %"v1865", #83
          => goto "L1864" };
        cap_blk{ @"L1864" [phi %"v1868" : "w" = ("L1830" => #0, "L1863" => %"v1866")]:
          => br %"v1868" ? "L1858" : "L1859" }
  ].
