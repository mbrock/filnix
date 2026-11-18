(** This file retains complete items or blocks of glibc's checked formatter.
    stdio/code.sh regenerates it from the pinned capture. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Glibc Require Import CodePrelude.
From Nanofil Require Import CaptureNotation.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

(** These blocks retain their order in the linked module. *)
Definition formatter_blocks_09 : list term :=
  [
        cap_blk{ @"L1450":
          call void $"glibc_vfprintf_internal#__printf_buffer_putc"("p" %"v0", "w" #48);
          %"v1474" : "w" = op "ext"("sb") %"pr.93";
          call void $"glibc_vfprintf_internal#__printf_buffer_putc"("p" %"v0", "w" %"v1474")
          => goto "L1452" };
        cap_blk{ @"L1452":
          %"v1476" : "w" = "copy" %"v1370";
          %"v1477" : "w" = "add" %"pr.75", %"v1476";
          %"v1480" : "l" = op "ext"("sw") %"v1477";
          call void $"glibc_vfprintf_internal#__printf_buffer_pad"("p" %"v0", "w" #48, "l" %"v1480")
          => br %"v1347" ? "L1481" : "L1483" };
        cap_blk{ @"L1481":
          call void $"glibc_vfprintf_internal#__printf_buffer_putc"("p" %"v0", "w" #48)
          => goto "L1483" };
        cap_blk{ @"L1483":
          => br %"v1261" ? "L1486" : "L1487" };
        cap_blk{ @"L1486":
          => br %"v721" ? "L1495" : "L1496" };
        cap_blk{ @"L1495":
          %"v1498" : "w" = op "cmp"("eq", "w") %"pr.47", #10
          => goto "L1496" };
        cap_blk{ @"L1496" [phi %"v1500" : "w" = ("L1486" => #0, "L1495" => %"v1498")]:
          call void $"glibc_vfprintf_internal#group_number"("p" %"v0", "p" %"v1248", "p" %"pr.53", "p" %"v742", "p" %"pr.6", "w" %"v1500")
          => goto "L866" };
        cap_blk{ @"L1487":
          call void $"__printf_buffer_write"("p" %"v0", "p" %"pr.53", "l" %"v1358")
          => goto "L866" };
        cap_blk{ @"L1372":
          => br %"pr.37" ? "L1510" : "L1511" };
        cap_blk{ @"L1510":
          call void $"glibc_vfprintf_internal#__printf_buffer_putc"("p" %"v0", "w" #45);
          %"v1516" : "w" = "sub" %"pr.81", #1
          => goto "L1512" };
        cap_blk{ @"L1511":
          => br %"pr.67" ? "L1517" : "L1518" };
        cap_blk{ @"L1517":
          call void $"glibc_vfprintf_internal#__printf_buffer_putc"("p" %"v0", "w" #43);
          %"v1523" : "w" = "sub" %"pr.81", #1
          => goto "L1512" };
        cap_blk{ @"L1518":
          => br %"pr.62" ? "L1524" : "L1512" };
        cap_blk{ @"L1524":
          call void $"glibc_vfprintf_internal#__printf_buffer_putc"("p" %"v0", "w" #32);
          %"v1530" : "w" = "sub" %"pr.81", #1
          => goto "L1512" };
        cap_blk{ @"L1512" [phi %"pr.76" : "w" = ("L1510" => %"v1516", "L1517" => %"v1523", "L1524" => %"v1530", "L1518" => %"pr.81")]:
          %"v1535" : "w" = op "cmp"("ne", "l") %"pr.40", #0
          => br %"v1535" ? "L1536" : "L1537" };
        cap_blk{ @"L1536":
          %"v1539" : "w" = op "cmp"("ne", "w") %"pr.59", #0
          => goto "L1537" };
        cap_blk{ @"L1537" [phi %"v1540" : "w" = ("L1512" => #0, "L1536" => %"v1539")]:
          => br %"v1540" ? "L1541" : "L1542" };
        cap_blk{ @"L1541":
          %"v1544" : "w" = op "cmp"("eq", "w") %"pr.47", #16
          => br %"v1544" ? "L1542" : "L1545" };
        cap_blk{ @"L1545":
          %"v1548" : "w" = op "cmp"("eq", "w") %"pr.47", #2
          => goto "L1542" };
        cap_blk{ @"L1542" [phi %"v1552" : "w" = ("L1537" => #0, "L1541" => #1, "L1545" => %"v1548")]:
          => br %"v1552" ? "L1531" : "L1533" };
        cap_blk{ @"L1531":
          call void $"glibc_vfprintf_internal#__printf_buffer_putc"("p" %"v0", "w" #48);
          %"v1555" : "w" = op "ext"("sb") %"pr.93";
          call void $"glibc_vfprintf_internal#__printf_buffer_putc"("p" %"v0", "w" %"v1555");
          %"v1557" : "w" = "sub" %"pr.76", #2
          => goto "L1533" };
        cap_blk{ @"L1533" [phi %"pr.79" : "w" = ("L1531" => %"v1557", "L1542" => %"pr.76")]:
          => br %"v1347" ? "L1558" : "L1560" };
        cap_blk{ @"L1558":
          %"v1563" : "w" = "sub" %"pr.79", #1
          => goto "L1560" };
        cap_blk{ @"L1560" [phi %"pr.80" : "w" = ("L1558" => %"v1563", "L1533" => %"pr.79")]:
          %"v1566" : "w" = "copy" %"v1370";
          %"v1567" : "w" = "add" %"pr.99", %"v1566";
          %"v1568" : "w" = "sub" %"pr.80", %"v1567";
          %"v1570" : "w" = "copy" %"v1370";
          %"v1571" : "l" = op "ext"("uw") %"v1570";
          call void $"glibc_vfprintf_internal#__printf_buffer_pad"("p" %"v0", "w" #48, "l" %"v1571")
          => br %"v1347" ? "L1572" : "L1574" };
        cap_blk{ @"L1572":
          call void $"glibc_vfprintf_internal#__printf_buffer_putc"("p" %"v0", "w" #48)
          => goto "L1574" };
        cap_blk{ @"L1574":
          => br %"v1261" ? "L1577" : "L1578" };
        cap_blk{ @"L1577":
          => br %"v721" ? "L1586" : "L1587" };
        cap_blk{ @"L1586":
          %"v1589" : "w" = op "cmp"("eq", "w") %"pr.47", #10
          => goto "L1587" };
        cap_blk{ @"L1587" [phi %"v1591" : "w" = ("L1577" => #0, "L1586" => %"v1589")]:
          call void $"glibc_vfprintf_internal#group_number"("p" %"v0", "p" %"v1248", "p" %"pr.53", "p" %"v742", "p" %"pr.6", "w" %"v1591")
          => goto "L1579" };
        cap_blk{ @"L1578":
          call void $"__printf_buffer_write"("p" %"v0", "p" %"pr.53", "l" %"v1358")
          => goto "L1579" };
        cap_blk{ @"L1579":
          %"v1602" : "l" = op "ext"("sw") %"v1568";
          call void $"glibc_vfprintf_internal#__printf_buffer_pad"("p" %"v0", "w" #32, "l" %"v1602")
          => goto "L866" };
        cap_blk{ @"L1603":
          %"v1611" = %"v612" +p #48;
          %"chk126" : "a" = op "half_check"("upper", int 0, int 4, "read", int 1) %"chk66", %"v1611";
          %"v1612" : "w" = op "raw_load"("sw", int 0) %"chk126";
          %"v1613" : "l" = op "ext"("sw") %"v1612";
          %"v1614" : "l" = "shl" %"v1613", #4;
          %"v1615" = %"pr.16" +p %"v1614";
          %"chk127" : "a" = op "check"(int 0, int 8, "read", int 8) %"v1615";
          %"v1616" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk127";
          %"v1621" : "l" = "ptoi" %"v1616";
          %"v1623" : "w" = op "cmp"("ne", "l") %"v1621", %"v875"
          => br %"v1623" ? poll "L1088" : "L1618" };
        cap_blk{ @"L1618":
          %"v1627" : "p" = "copy" $"glibc_vfprintf_internal#str.284";
          %"v1632" : "w" = op "cmp"("slt", "w") %"pr.89", #5
          => br %"v1632" ? "L1634" : "L1629" };
        cap_blk{ @"L1629":
          => goto "L1634" };
        cap_blk{ @"L1635":
          => br %"v176" ? "L1636" : "L1638" };
        cap_blk{ @"L1636":
          %"v1646" : "w" = op "cmp"("eq", "w") %"pr.3", #0
          => br %"v1646" ? "L1642" : "L1644" };
        cap_blk{ @"L1642":
          call %"v1649" : "l" = $"__GI_strlen"("p" %"v2");
          %"v1650" : "l" = "add" %"v1649", #1;
          call %"v1652" : "w" = $"__readonly_area"("p" %"v2", "l" %"v1650")
          => goto "L1644" };
        cap_blk{ @"L1644" [phi %"pr.2" : "w" = ("L1642" => %"v1652", "L1636" => %"pr.3")]:
          %"v1663" : "w" = op "cmp"("eq", "w") %"pr.2", #1
          => br %"v1663" ? "L1656" : "L1664" };
        cap_blk{ @"L1656":
          %"v1657" : "p" = "copy" $"glibc_vfprintf_internal#str.285";
          call void $"__GI___libc_fatal"("p" %"v1657")
          => goto "L1658" };
        cap_blk{ @"L1658":
          %"v1659" : "p" = "copy" $"glibc_vfprintf_internal#str.286";
          call void $"__GI___libc_fatal"("p" %"v1659")
          => goto "L1638" };
        cap_blk{ @"L1664":
          %"v1665" : "w" = op "cmp"("eq", "w") %"pr.2", #3
          => br %"v1665" ? poll "L1658" : "L1666" };
        cap_blk{ @"L1666":
          %"v1667" : "w" = op "cmp"("eq", "w") %"pr.2", #2
          => br %"v1667" ? "L1638" : "L1668" };
        cap_blk{ @"L1668":
          %"v1669" : "w" = op "cmp"("eq", "w") %"pr.2", #0
          => br %"v1669" ? "L1638" : "L1670" };
        cap_blk{ @"L1670":
          => goto "L1638" };
        cap_blk{ @"L1638" [phi %"pr.1" : "w" = ("L1670" => %"pr.2", "L1668" => %"pr.2", "L1658" => %"pr.2", "L1666" => %"pr.2", "L1635" => %"pr.3")]:
          %"v1678" = %"v612" +p #48;
          %"chk128" : "a" = op "half_check"("upper", int 0, int 4, "read", int 1) %"chk66", %"v1678";
          %"v1679" : "w" = op "raw_load"("sw", int 0) %"chk128";
          %"v1680" : "l" = op "ext"("sw") %"v1679";
          %"v1681" : "l" = "shl" %"v1680", #4;
          %"v1682" = %"pr.16" +p %"v1681";
          %"chk129" : "a" = op "check"(int 0, int 8, "read", int 8) %"v1682";
          %"v1683" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk129";
          call %"v1686" : "w" = $"__printf_buffer_done"("p" %"v0")
          => br %"v696" ? "L1693" : "L1694" };
        cap_blk{ @"L1693":
          %"v1699" : "l" = op "ext"("uw") %"v1686";
          %"chk130" : "a" = op "check"(int 0, int 8, "write", int 1) %"v1683";
          store "l" [%"chk130" + 0] <- %"v1699"
          => goto "L866" };
        cap_blk{ @"L1694":
          => br %"v686" ? "L1700" : "L1701" };
        cap_blk{ @"L1700":
          %"v1706" : "w" = op "ext"("sb") %"v1686";
          %"chk131" : "a" = op "check"(int 0, int 1, "write", int 1) %"v1683";
          store "b" [%"chk131" + 0] <- %"v1706"
          => goto "L866" };
        cap_blk{ @"L1701":
          %"v1711" : "w" = op "cmp"("eq", "w") %"v676", #0
          => br %"v1711" ? "L1707" : "L1708" };
        cap_blk{ @"L1707":
          %"chk132" : "a" = op "check"(int 0, int 4, "write", int 1) %"v1683";
          store "w" [%"chk132" + 0] <- %"v1686"
          => goto "L866" };
        cap_blk{ @"L1708":
          %"v1716" : "w" = op "ext"("sh") %"v1686";
          %"chk133" : "a" = op "check"(int 0, int 2, "write", int 1) %"v1683";
          store "h" [%"chk133" + 0] <- %"v1716"
          => goto "L866" };
        cap_blk{ @"L1717":
          => br %"v616" ? "L1718" : "L1719" };
        cap_blk{ @"L1718":
          call %"v1723" : "p" = $"__get_errname"("w" %"v16")
          => goto "L1720" };
        cap_blk{ @"L1719":
          call %"v1727" : "p" = $"__GI___strerror_r"("w" %"v16", "p" %"v14", "l" #1000)
          => goto "L1720" };
        cap_blk{ @"L1720" [phi %"pr.56" : "p" = ("L1718" => %"v1723", "L1719" => %"v1727")]:
          %"v1732" : "l" = "ptoi" %"pr.56";
          %"v1734" : "w" = op "cmp"("eq", "l") %"v1732", %"v875"
          => br %"v1734" ? "L1728" : "L1634" };
        cap_blk{ @"L1728":
          %"v1736" : "w" = op "cmp"("slt", "w") %"v16", #0;
          %"v1738" : "l" = op "ext"("sw") %"v16"
          => br %"v1736" ? "L1739" : poll "L1088" };
        cap_blk{ @"L1739":
          %"v1744" : "l" = "neg" %"v1738"
          => goto poll "L1088" };
        cap_blk{ @"L1746":
          => br %"v696" ? "L1751" : "L1749" };
        cap_blk{ @"L1749":
          %"v1754" : "w" = "sub" %"pr.81", #1;
          %"v1759" : "w" = op "cmp"("eq", "w") %"pr.64", #0
          => br %"v1759" ? "L1755" : "L1757" };
        cap_blk{ @"L1755":
          %"v1762" : "l" = op "ext"("sw") %"v1754";
          call void $"glibc_vfprintf_internal#__printf_buffer_pad"("p" %"v0", "w" #32, "l" %"v1762")
          => goto "L1757" };
        cap_blk{ @"L1757":
          %"v1770" = %"v612" +p #48;
          %"chk134" : "a" = op "half_check"("upper", int 0, int 4, "read", int 1) %"chk66", %"v1770";
          %"v1771" : "w" = op "raw_load"("sw", int 0) %"chk134";
          %"v1772" : "l" = op "ext"("sw") %"v1771";
          %"v1773" : "l" = "shl" %"v1772", #4;
          %"v1774" = %"pr.16" +p %"v1773";
          %"chk135" : "a" = op "check"(int 0, int 4, "read", int 1) %"v1774";
          %"v1775" : "w" = op "raw_load"("sw", int 0) %"chk135";
          %"v1776" : "w" = op "ext"("ub") %"v1775";
          %"v1777" : "w" = op "ext"("sb") %"v1776";
          call void $"glibc_vfprintf_internal#__printf_buffer_putc"("p" %"v0", "w" %"v1777")
          => br %"pr.64" ? "L1778" : "L866" };
        cap_blk{ @"L1778":
          %"v1784" : "l" = op "ext"("sw") %"v1754";
          call void $"glibc_vfprintf_internal#__printf_buffer_pad"("p" %"v0", "w" #32, "l" %"v1784")
          => goto "L866" };
        cap_blk{ @"L1785":
          %"v1793" = %"v612" +p #48;
          %"chk136" : "a" = op "half_check"("upper", int 0, int 4, "read", int 1) %"chk66", %"v1793";
          %"v1794" : "w" = op "raw_load"("sw", int 0) %"chk136";
          %"v1795" : "l" = op "ext"("sw") %"v1794";
          %"v1796" : "l" = "shl" %"v1795", #4;
          %"v1797" = %"pr.16" +p %"v1796";
          %"chk137" : "a" = op "check"(int 0, int 8, "read", int 8) %"v1797";
          %"v1798" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk137"
          => goto "L1634" };
        cap_blk{ @"L1634" [phi %"pr.88" : "w" = ("L1785" => %"pr.89", "L1629" => %"pr.89", "L1618" => #5, "L1720" => %"pr.89"); phi %"pr.71" : "w" = ("L1785" => %"v696", "L1629" => #0, "L1618" => #0, "L1720" => #0); phi %"pr.55" : "p" = ("L1785" => %"v1798", "L1629" => %"v1627", "L1618" => %"v1627", "L1720" => %"pr.56")]:
          %"v1803" : "l" = "ptoi" %"pr.55";
          %"v1805" : "w" = op "cmp"("eq", "l") %"v1803", %"v875"
          => br %"v1805" ? "L1799" : "L1800" };
        cap_blk{ @"L1799":
          %"v1811" : "w" = op "cmp"("eq", "w") %"pr.88", #4294967295
          => br %"v1811" ? "L1813" : "L1812" };
        cap_blk{ @"L1812":
          %"v1819" : "w" = op "cmp"("sge", "w") %"pr.88", #6
          => goto "L1813" };
        cap_blk{ @"L1813" [phi %"v1821" : "w" = ("L1799" => #1, "L1812" => %"v1819")]:
          => br %"v1821" ? "L1806" : "L1807" };
        cap_blk{ @"L1806":
          %"v1822" : "p" = "copy" $"glibc_vfprintf_internal#null"
          => goto "L1801" };
        cap_blk{ @"L1807":
          %"v1827" : "p" = "copy" $"glibc_vfprintf_internal#str.289"
          => goto "L1801" };
        cap_blk{ @"L1800":
          %"v1832" : "w" = op "cmp"("eq", "w") %"pr.71", #0
          => br %"v1832" ? "L1833" : "L1834" };
        cap_blk{ @"L1833":
          %"v1836" : "w" = op "cmp"("ne", "w") %"v739", #83
          => goto "L1834" };
        cap_blk{ @"L1834" [phi %"v1838" : "w" = ("L1800" => #0, "L1833" => %"v1836")]:
          => br %"v1838" ? "L1828" : "L1829" };
        cap_blk{ @"L1828":
          %"v1844" : "w" = op "cmp"("ne", "w") %"pr.88", #4294967295
          => br %"v1844" ? "L1839" : "L1840" };
        cap_blk{ @"L1839":
          %"v1847" : "l" = op "ext"("sw") %"pr.88";
          call %"v1848" : "l" = $"__GI___strnlen"("p" %"pr.55", "l" %"v1847")
          => goto "L1841" };
        cap_blk{ @"L1840":
          call %"v1850" : "l" = $"__GI_strlen"("p" %"pr.55")
          => goto "L1841" };
        cap_blk{ @"L1841" [phi %"pr.103" : "l" = ("L1839" => %"v1848", "L1840" => %"v1850")]:
          => goto "L1801" };
        cap_blk{ @"L1829":
          %"v1856" : "w" = op "cmp"("ne", "w") %"pr.64", #0;
          call void $"glibc_vfprintf_internal#outstring_converted_wide_string"("p" %"v0", "p" %"pr.55", "w" %"pr.88", "w" %"pr.81", "w" %"v1856")
          => goto "L866" };
        cap_blk{ @"L1801" [phi %"pr.101" : "l" = ("L1806" => #6, "L1807" => #0, "L1841" => %"pr.103"); phi %"pr.57" : "p" = ("L1806" => %"v1822", "L1807" => %"v1827", "L1841" => %"pr.55")]:
          %"v1862" : "l" = op "ext"("sw") %"pr.81";
          %"v1863" : "l" = "sub" %"v1862", %"pr.101";
          %"v1864" : "w" = op "cmp"("slt", "w") %"v1863", #0
          => br %"v1864" ? "L1857" : "L1859" };
        cap_blk{ @"L1857":
          call void $"__printf_buffer_write"("p" %"v0", "p" %"pr.57", "l" %"pr.101")
          => goto "L866" };
        cap_blk{ @"L1859":
          %"v1873" : "w" = op "cmp"("eq", "w") %"pr.64", #0
          => br %"v1873" ? "L1869" : "L1871" };
        cap_blk{ @"L1869":
          %"v1875" : "w" = "copy" %"v1863";
          %"v1876" : "l" = op "ext"("sw") %"v1875";
          call void $"glibc_vfprintf_internal#__printf_buffer_pad"("p" %"v0", "w" #32, "l" %"v1876")
          => goto "L1871" };
        cap_blk{ @"L1871":
          call void $"__printf_buffer_write"("p" %"v0", "p" %"pr.57", "l" %"pr.101")
          => br %"pr.64" ? "L1880" : "L866" };
        cap_blk{ @"L1880":
          %"v1885" : "w" = "copy" %"v1863";
          %"v1886" : "l" = op "ext"("sw") %"v1885";
          call void $"glibc_vfprintf_internal#__printf_buffer_pad"("p" %"v0", "w" #32, "l" %"v1886")
          => goto "L866" };
        cap_blk{ @"L1751":
          call %"v1890" : "p" = $"__GI_memset"("p" %"v1888", "w" #0, "l" #8);
          %"v1897" = %"v612" +p #48;
          %"chk138" : "a" = op "half_check"("upper", int 0, int 4, "read", int 1) %"chk66", %"v1897";
          %"v1898" : "w" = op "raw_load"("sw", int 0) %"chk138";
          %"v1899" : "l" = op "ext"("sw") %"v1898";
          %"v1900" : "l" = "shl" %"v1899", #4;
          %"v1901" = %"pr.16" +p %"v1900";
          %"chk139" : "a" = op "check"(int 0, int 4, "read", int 1) %"v1901";
          %"v1902" : "w" = op "raw_load"("sw", int 0) %"chk139";
          call %"v1903" : "l" = $"__wcrtomb"("p" %"v1887", "w" %"v1902", "p" %"v1888");
          %"v1910" : "w" = op "cmp"("eq", "l") %"v1903", #18446744073709551615
          => br %"v1910" ? "L1904" : "L1906" };
        cap_blk{ @"L1904":
          call void $"glibc_vfprintf_internal#__printf_buffer_mark_failed"("p" %"v0")
          => goto "L101" };
        cap_blk{ @"L1906":
          %"v1915" : "l" = op "ext"("sw") %"pr.81";
          %"v1916" : "l" = "sub" %"v1915", %"v1903";
          %"v1921" : "w" = op "cmp"("eq", "w") %"pr.64", #0
          => br %"v1921" ? "L1917" : "L1919" };
        cap_blk{ @"L1917":
          %"v1923" : "w" = "copy" %"v1916";
          %"v1924" : "l" = op "ext"("sw") %"v1923";
          call void $"glibc_vfprintf_internal#__printf_buffer_pad"("p" %"v0", "w" #32, "l" %"v1924")
          => goto "L1919" };
        cap_blk{ @"L1919":
          call void $"__printf_buffer_write"("p" %"v0", "p" %"v1887", "l" %"v1903")
          => br %"pr.64" ? "L1927" : "L866" };
        cap_blk{ @"L1927":
          %"v1932" : "w" = "copy" %"v1916";
          %"v1933" : "l" = op "ext"("sw") %"v1932";
          call void $"glibc_vfprintf_internal#__printf_buffer_pad"("p" %"v0", "w" #32, "l" %"v1933")
          => goto "L866" };
        cap_blk{ @"L1935":
          %"v1943" = %"v612" +p #48;
          %"chk140" : "a" = op "half_check"("upper", int 0, int 4, "read", int 1) %"chk66", %"v1943";
          %"v1944" : "w" = op "raw_load"("sw", int 0) %"chk140";
          %"v1945" : "l" = op "ext"("sw") %"v1944";
          %"v1946" : "l" = "shl" %"v1945", #4;
          %"v1947" = %"pr.16" +p %"v1946";
          %"chk141" : "a" = op "check"(int 0, int 8, "write", int 8) %"v1936";
          store.ptr [%"chk141" + 0] <- %"v1947";
          %"v1952" : "w" = "and" %"v22", #1
          => br %"v1952" ? "L1948" : "L1974" };
        cap_blk{ @"L1948":
          %"v1961" = %"v612" +p #52;
          %"chk142" : "a" = op "half_check"("upper", int 0, int 4, "write", int 1) %"chk66", %"v1961";
          store "w" [%"chk142" + 0] <- #7;
          %"v1967" = %"v612" +p #12;
          %"chk143" : "a" = op "renew"(int 0, int 4, "read", int 1) %"chk66", %"v1967";
          %"v1968" : "w" = op "raw_load"("uw", int 0) %"chk143";
          %"v1969" : "w" = "and" %"v1968", #4294967294;
          store "w" [%"chk143" + 0] <- %"v1969"
          => goto "L1974" };
        cap_blk{ @"L1974":
          %"v1982" = %"v612" +p #12;
          %"chk145" : "a" = op "renew"(int 0, int 4, "read", int 1) %"chk66", %"v1982";
          %"v1983" : "w" = op "raw_load"("uw", int 0) %"chk145";
          %"v1984" : "w" = "and" %"v1983", #4294963199;
          %"chk146" : "a" = op "renew"(int 0, int 4, "write", int 1) %"chk66", %"v1982";
          store "w" [%"chk146" + 0] <- %"v1984";
          call void $"glibc_vfprintf_internal#__printf_fp_spec"("p" %"v0", "p" %"v612", "p" %"v1936")
          => goto "L866" };
        cap_blk{ @"L1996":
          call void $"glibc_vfprintf_internal#printf_unknown"("p" %"v0", "p" %"v612")
          => goto "L866" };
        cap_blk{ @"L866" [phi %"pr.4" : "w" = ("L1579" => %"pr.3", "L1829" => %"pr.3", "L1857" => %"pr.3", "L1974" => %"pr.3", "L1996" => %"pr.3", "L980" => %"pr.3", "L926" => %"pr.3", "L1496" => %"pr.3", "L1487" => %"pr.3", "L1693" => %"pr.1", "L1700" => %"pr.1", "L1707" => %"pr.1", "L1708" => %"pr.1", "L1778" => %"pr.3", "L1757" => %"pr.3", "L1880" => %"pr.3", "L1871" => %"pr.3", "L1927" => %"pr.3", "L1919" => %"pr.3")]:
          %"v2012" = %"v612" +p #24;
          %"chk147" : "a" = op "half_check"("upper", int 0, int 8, "read", int 8) %"chk66", %"v2012";
          %"v2013" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk147";
          %"v2019" = %"v612" +p #32;
          %"chk148" : "a" = op "half_check"("upper", int 0, int 8, "read", int 8) %"chk66", %"v2019";
          %"v2020" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk148";
          %"v2027" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk147";
          %"v2028" : "l" = "ptoi" %"v2020";
          %"v2029" : "l" = "ptoi" %"v2027";
          %"v2030" : "l" = "sub" %"v2028", %"v2029";
          call void $"__printf_buffer_write"("p" %"v0", "p" %"v2013", "l" %"v2030");
          %"v2032" : "w" = "add" %"pr.5", #1
          => goto poll "L587" };
        cap_blk{ @"L101":
          call void $"glibc_vfprintf_internal#scratch_buffer_free"("p" %"v31");
          call void $"glibc_vfprintf_internal#scratch_buffer_free"("p" %"v24")
          => ret void };
        cap_blk{ @"L2036":
          %"v2038" : "w" = op "cmp"("ult", "l") %"v977", #4
          => br %"v2038" ? "L2039" : "L2040" };
        cap_blk{ @"L2039":
          %"v2041" : "w" = op "cmp"("eq", "l") %"v977", #1
          => br %"v2041" ? poll "L1996" : "L2042" };
        cap_blk{ @"L2042":
          %"v2043" : "w" = op "cmp"("eq", "l") %"v977", #2
          => br %"v2043" ? poll "L980" : "L2044" };
        cap_blk{ @"L2044":
          %"v2045" : "w" = op "cmp"("eq", "l") %"v977", #3
          => br %"v2045" ? poll "L984" : "L2034" };
        cap_blk{ @"L2040":
          %"v2047" : "w" = op "cmp"("eq", "l") %"v977", #4
          => br %"v2047" ? poll "L1090" : "L2048" };
        cap_blk{ @"L2048":
          %"v2049" : "w" = op "cmp"("eq", "l") %"v977", #5
          => br %"v2049" ? poll "L1090" : "L2050" };
        cap_blk{ @"L2050":
          %"v2051" : "w" = op "cmp"("eq", "l") %"v977", #6
          => br %"v2051" ? poll "L1090" : "L2052" };
        cap_blk{ @"L2052":
          %"v2053" : "w" = op "cmp"("eq", "l") %"v977", #7
          => br %"v2053" ? poll "L1935" : "L2034" };
        cap_blk{ @"L2037":
          %"v2055" : "w" = op "cmp"("ult", "l") %"v977", #12
          => br %"v2055" ? "L2056" : "L2057" };
        cap_blk{ @"L2056":
          %"v2058" : "w" = op "cmp"("eq", "l") %"v977", #8
          => br %"v2058" ? poll "L1746" : "L2059" };
        cap_blk{ @"L2059":
          %"v2060" : "w" = op "cmp"("eq", "l") %"v977", #9
          => br %"v2060" ? poll "L1785" : "L2061" };
        cap_blk{ @"L2061":
          %"v2062" : "w" = op "cmp"("eq", "l") %"v977", #10
          => br %"v2062" ? poll "L1603" : "L2063" };
        cap_blk{ @"L2063":
          %"v2064" : "w" = op "cmp"("eq", "l") %"v977", #11
          => br %"v2064" ? poll "L1635" : "L2034" };
        cap_blk{ @"L2057":
          %"v2066" : "w" = op "cmp"("eq", "l") %"v977", #12
          => br %"v2066" ? poll "L1717" : "L2067" };
        cap_blk{ @"L2067":
          %"v2068" : "w" = op "cmp"("eq", "l") %"v977", #13
          => br %"v2068" ? poll "L1751" : "L2069" };
        cap_blk{ @"L2069":
          %"v2070" : "w" = op "cmp"("eq", "l") %"v977", #14
          => br %"v2070" ? poll "L1935" : "L2071" };
        cap_blk{ @"L2071":
          %"v2072" : "w" = op "cmp"("eq", "l") %"v977", #15
          => br %"v2072" ? poll "L1090" : "L2034" };
        cap_blk{ @"L2034":
          => unreachable }
  ].
