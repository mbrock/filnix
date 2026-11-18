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

Definition hello_image_fn_glibc_printf_fp'23__printf_fp_buffer_1'blocks2 : list block :=
  (app (app [ir_blk{ @"L1253" [%"pr.36" : W = phi("L1489" => %"v1455", "L1574" => %"v1455", "L1609" => %"v1455", "L1610" => %"v1455", "L1395" => %"pr.35", "L1246" => %"pr.35")]:
    %"v1667" : W = Sub %"pr.39", #1;
    %"v1669" : P = Copy $"_fpioconst_pow10";
    %"v1670" = %"v1669" +p #24;
    %"v1671" : L = Ptoi %"v1250";
    %"v1672" : L = Ptoi %"v1670";
    %"v1673" : W = (Cmp Ne L) %"v1671", %"v1672"
    => br %"v1673" ? "L1674" : "L1675" };
  ir_blk{ @"L1674":
    %"v1676" = %"v28" +p #8;
    %"chk282" : A = (Renew 0 4 Read 1) %"chk59", %"v1676";
    %"v1677" : W = (RawLoad (LdNarrow Sw) 0) %"chk282";
    %"v1678" : W = (Cmp Sgt W) %"v1677", #0
    => goto "L1675" };
  ir_blk{ @"L1675" [%"v1680" : W = phi("L1253" => #0, "L1674" => %"v1678")]:
    => br %"v1680" ? poll "L1246" : "L1248" };
  ir_blk{ @"L1248":
    %"v1684" = %"v28" +p #8;
    %"chk283" : A = (Renew 0 4 Read 1) %"chk59", %"v1684";
    %"v1685" : W = (RawLoad (LdNarrow Sw) 0) %"chk283";
    %"v1686" : W = (Cmp Sgt W) %"v1685", #0
    => br %"v1686" ? "L1681" : "L1683" };
  ir_blk{ @"L1681":
    %"v1688" = %"v28" +p #48;
    %"chk284" : A = (Renew 0 8 Read 8) %"chk61", %"v1688";
    %"v1689" : P = (RawLoadPointer 0 load_effects) %"chk284";
    %"v1690" = %"v28" +p #16;
    %"v1691" : P = (RawLoadPointer (-32) load_effects) %"chk284";
    %"v1692" = %"v28" +p #24;
    %"v1693" : L = (RawLoad LdL 16) %"chk283";
    call %"v1694" : L = $"__mpn_mul_1"(P %"v1689", P %"v1691", L %"v1693", L #10);
    %"v1695" = %"v28" +p #56;
    %"chk287" : A = (Renew 0 8 Read 1) %"chk192", %"v1692";
    %"v1697" : L = (RawLoad LdL 0) %"chk287";
    %"chk288" : A = (HalfCheck Upper 0 8 Write 1) %"chk2", %"v1695";
    store Wl [%"chk288" + 0] <- %"v1697";
    %"v1702" : W = (Cmp Eq L) %"v1694", #0
    => br %"v1702" ? "L1704" : "L1703" };
  ir_blk{ @"L1703":
    %"v1705" = %"v28" +p #48;
    %"chk289" : A = (Renew 0 8 Read 8) %"chk61", %"v1705";
    %"v1706" : P = (RawLoadPointer 0 load_effects) %"chk289";
    %"v1707" = %"v28" +p #56;
    %"v1708" : L = (RawLoad LdL 0) %"chk288";
    %"v1709" : L = Sub %"v1708", #1;
    %"v1710" : L = Shl %"v1709", #3;
    %"v1711" = %"v1706" +p %"v1710";
    %"chk291" : A = (Check 0 8 Read 1) %"v1711";
    %"v1712" : L = (RawLoad LdL 0) %"chk291";
    %"v1713" : W = (Cmp Ult L) %"v1712", #20
    => goto "L1704" };
  ir_blk{ @"L1704" [%"v1715" : W = phi("L1681" => #1, "L1703" => %"v1713")]:
    => br %"v1715" ? "L1719" : "L1699" };
  ir_blk{ @"L1699":
    %"v1716" : P = Copy $"glibc_printf_fp#str.307";
    %"v1717" : P = Copy $"glibc_printf_fp#str.302";
    %"v1718" : P = Copy $"glibc_printf_fp#str.303";
    call void $"__libc_assert_fail"(P %"v1716", P %"v1717", W #631, P %"v1718")
    => goto "L1719" };
  ir_blk{ @"L1719":
    %"v1723" = %"v28" +p #48;
    %"chk292" : A = (Renew 0 8 Read 8) %"chk61", %"v1723";
    %"v1724" : P = (RawLoadPointer 0 load_effects) %"chk292";
    %"chk293" : A = (Check 0 8 Read 1) %"v1724";
    %"v1726" : L = (RawLoad LdL 0) %"chk293";
    %"iw_20.v6" : W = (Cmp Eq L) %"v1726", #0
    => br %"iw_20.v6" ? "iw_20.L4" : "iw_20.L3" };
  ir_blk{ @"iw_20.L3":
    %"iw_20.v8" : L = Neg %"v1726";
    %"iw_20.v9" : L = And %"v1726", %"iw_20.v8";
    %"iw_20.v10" : L = Sub %"iw_20.v9", #1;
    %"iw_20.v11" : L = Shr %"iw_20.v10", #1;
    %"iw_20.v12" : L = And %"iw_20.v11", #6148914691236517205;
    %"iw_20.v13" : L = Sub %"iw_20.v10", %"iw_20.v12";
    %"iw_20.v14" : L = And %"iw_20.v13", #3689348814741910323;
    %"iw_20.v15" : L = Shr %"iw_20.v13", #2;
    %"iw_20.v16" : L = And %"iw_20.v15", #3689348814741910323;
    %"iw_20.v17" : L = Add %"iw_20.v14", %"iw_20.v16";
    %"iw_20.v18" : L = Shr %"iw_20.v17", #4;
    %"iw_20.v19" : L = Add %"iw_20.v17", %"iw_20.v18";
    %"iw_20.v20" : L = And %"iw_20.v19", #1085102592571150095;
    %"iw_20.v21" : L = Mul %"iw_20.v20", #72340172838076673;
    %"iw_20.v22" : L = Shr %"iw_20.v21", #56
    => goto "iw_20.L4" };
  ir_blk{ @"iw_20.L4" [%"iw_20.v23" : W = phi("iw_20.L3" => %"iw_20.v22", "L1719" => #64)]:
    %"v1763" = %"v28" +p #8;
    %"chk294" : A = (Renew 0 4 Read 1) %"chk59", %"v1763";
    %"v1764" : W = (RawLoad (LdNarrow Sw) 0) %"chk294";
    %"v1765" : W = (Cmp Sgt W) %"v1764", #4
    => br %"v1765" ? "L1762" : "L1761" };
  ir_blk{ @"L1761":
    %"v1766" = %"v28" +p #8;
    %"v1767" : W = (RawLoad (LdNarrow Sw) 0) %"chk294"
    => goto "L1762" };
  ir_blk{ @"L1762" [%"v1768" : W = phi("L1761" => %"v1767", "iw_20.L4" => #4)]:
    %"v1769" : W = (Cmp Slt W) %"iw_20.v23", %"v1768"
    => br %"v1769" ? "L1756" : "L1757" };
  ir_blk{ @"L1756":
    %"v1770" = %"v28" +p #16;
    %"v1771" : P = (RawLoadPointer (-32) load_effects) %"chk292";
    %"v1772" = %"v28" +p #48;
    %"v1773" : P = (RawLoadPointer 0 load_effects) %"chk292";
    %"v1774" = %"v28" +p #56;
    %"chk298" : A = (Renew 0 8 Read 1) %"chk288", %"v1774";
    %"v1775" : L = (RawLoad LdL 0) %"chk298";
    %"v1779" = %"v28" +p #8;
    %"v1780" : W = (RawLoad (LdNarrow Sw) 0) %"chk294";
    %"v1781" : W = (Cmp Sgt W) %"v1780", #4
    => br %"v1781" ? "L1778" : "L1777" };
  ir_blk{ @"L1777":
    %"v1782" = %"v28" +p #8;
    %"v1783" : W = (RawLoad (LdNarrow Sw) 0) %"chk294"
    => goto "L1778" };
  ir_blk{ @"L1778" [%"v1784" : W = phi("L1777" => %"v1783", "L1756" => #4)]:
    %"v1785" : W = Sub #64, %"v1784";
    call %"v1786" : L = $"__mpn_lshift"(P %"v1771", P %"v1773", L %"v1775", W %"v1785");
    %"v1791" : W = (Cmp Ne L) %"v1786", #0
    => br %"v1791" ? "L1787" : "L1758" };
  ir_blk{ @"L1787":
    %"v1792" = %"v28" +p #16;
    %"chk301" : A = (Renew 0 8 Read 8) %"chk60", %"v1792";
    %"v1793" : P = (RawLoadPointer 0 load_effects) %"chk301";
    %"v1794" = %"v28" +p #56;
    %"chk302" : A = (Renew 0 8 Read 1) %"chk288", %"v1794";
    %"v1795" : L = (RawLoad LdL 0) %"chk302";
    %"v1796" : L = Add %"v1795", #1;
    %"chk303" : A = (Renew 0 8 Write 1) %"chk288", %"v1794";
    store Wl [%"chk303" + 0] <- %"v1796";
    %"v1797" : L = Shl %"v1795", #3;
    %"v1798" = %"v1793" +p %"v1797";
    %"chk304" : A = (Check 0 8 Write 1) %"v1798";
    store Wl [%"chk304" + 0] <- %"v1786"
    => goto "L1758" };
  ir_blk{ @"L1757":
    %"v1800" = %"v28" +p #16;
    %"v1801" : P = (RawLoadPointer (-32) load_effects) %"chk292";
    %"v1802" = %"v28" +p #48;
    %"v1803" : P = (RawLoadPointer 0 load_effects) %"chk292";
    %"v1804" = %"v28" +p #56;
    %"chk307" : A = (Renew 0 8 Read 1) %"chk288", %"v1804";
    %"v1805" : L = (RawLoad LdL 0) %"chk307";
    %"v1809" = %"v28" +p #8;
    %"v1810" : W = (RawLoad (LdNarrow Sw) 0) %"chk294";
    %"v1811" : W = (Cmp Sgt W) %"v1810", #4
    => br %"v1811" ? "L1808" : "L1807" };
  ir_blk{ @"L1807":
    %"v1812" = %"v28" +p #8;
    %"v1813" : W = (RawLoad (LdNarrow Sw) 0) %"chk294"
    => goto "L1808" };
  ir_blk{ @"L1808" [%"v1814" : W = phi("L1807" => %"v1813", "L1757" => #4)]:
    call %"v1815" : L = $"__mpn_rshift"(P %"v1801", P %"v1803", L %"v1805", W %"v1814")
    => goto "L1758" };
  ir_blk{ @"L1758":
    %"v1816" = %"v28" +p #24;
    %"v1817" = %"v28" +p #56;
    %"chk310" : A = (Renew 0 8 Read 1) %"chk288", %"v1817";
    %"v1818" : L = (RawLoad LdL 0) %"chk310";
    %"chk311" : A = (Renew 0 8 Write 1) %"chk192", %"v1816";
    store Wl [%"chk311" + 0] <- %"v1818";
    %"v1820" : W = Or %"pr.36", #1;
    %"v1824" = %"v28" +p #16;
    %"chk312" : A = (Renew 0 8 Read 8) %"chk60", %"v1824";
    %"v1825" : P = (RawLoadPointer 0 load_effects) %"chk312";
    %"v1827" : L = (RawLoad LdL 0) %"chk311";
    %"v1828" : L = Sub %"v1827", #1;
    %"v1829" : L = Shl %"v1828", #3;
    %"v1830" = %"v1825" +p %"v1829";
    %"chk314" : A = (Check 0 8 Read 1) %"v1830";
    %"v1831" : L = (RawLoad LdL 0) %"chk314";
    %"v1832" : W = (Cmp Ult L) %"v1831", #10
    => br %"v1832" ? "L1683" : "L1822" };
  ir_blk{ @"L1822":
    %"v1833" : P = Copy $"glibc_printf_fp#str.308";
    %"v1834" : P = Copy $"glibc_printf_fp#str.302";
    %"v1835" : P = Copy $"glibc_printf_fp#str.303";
    call void $"__libc_assert_fail"(P %"v1833", P %"v1834", W #645, P %"v1835")
    => goto "L1683" };
  ir_blk{ @"L1683" [%"pr.38" : W = phi("L1822" => %"v1820", "L1758" => %"v1820", "L1248" => %"pr.36")]:
    %"v1836" = %"v28" +p #8;
    %"chk315" : A = (Renew 0 4 Write 1) %"chk59", %"v1836";
    store Ww [%"chk315" + 0] <- %"pr.38"
    => goto "L333" };
  ir_blk{ @"L1172":
    %"v1841" = %"v28" +p #8;
    %"v1842" : W = (RawLoad (LdNarrow Sw) 0) %"chk64";
    %"v1843" : W = (Cmp Sge W) %"v1842", #0
    => br %"v1843" ? "L1844" : "L1845" };
  ir_blk{ @"L1844":
    %"v1846" = %"v28" +p #8;
    %"v1847" : W = (RawLoad (LdNarrow Sw) 0) %"chk64";
    %"v1848" : W = (Cmp Slt W) %"v1847", #3
    => goto "L1845" };
  ir_blk{ @"L1845" [%"v1850" : W = phi("L1172" => #0, "L1844" => %"v1848")]:
    => br %"v1850" ? "L1851" : "L1852" };
  ir_blk{ @"L1851":
    %"v1853" = %"v28" +p #8;
    %"v1854" : W = (RawLoad (LdNarrow Sw) 0) %"chk64";
    %"v1856" : W = Add %"v1854", %"pr.12";
    %"v1857" : W = (Cmp Slt W) %"v1856", #64
    => goto "L1852" };
  ir_blk{ @"L1852" [%"v1859" : W = phi("L1845" => #0, "L1851" => %"v1857")]:
    => br %"v1859" ? "L1840" : "L1839" };
  ir_blk{ @"L1839":
    %"v1860" : P = Copy $"glibc_printf_fp#str.309";
    %"v1861" : P = Copy $"glibc_printf_fp#str.302";
    %"v1862" : P = Copy $"glibc_printf_fp#str.303";
    call void $"__libc_assert_fail"(P %"v1860", P %"v1861", W #656, P %"v1862")
    => goto "L1840" };
  ir_blk{ @"L1840":
    %"v1863" = %"v28" +p #16;
    %"chk319" : A = (Renew 0 8 Read 8) %"chk60", %"v1863";
    %"v1864" : P = (RawLoadPointer 0 load_effects) %"chk319";
    %"v1865" = %"v28" +p #24;
    %"chk320" : A = (HalfCheck Upper 0 8 Read 1) %"chk2", %"v1865";
    %"v1866" : L = (RawLoad LdL 0) %"chk320";
    %"v1867" = %"v28" +p #8;
    %"chk321" : A = (Renew 0 4 Read 1) %"chk59", %"v1867";
    %"v1868" : W = (RawLoad (LdNarrow Sw) 0) %"chk321";
    %"v1870" : W = Add %"v1868", %"pr.12";
    call %"v1871" : L = $"__mpn_lshift"(P %"v1864", P %"v26", L %"v1866", W %"v1870");
    %"chk322" : A = (Renew 0 8 Read 8) %"chk60", %"v1863";
    %"v1873" : P = (RawLoadPointer 0 load_effects) %"chk322";
    %"chk323" : A = (Renew 0 8 Read 1) %"chk320", %"v1865";
    %"v1875" : L = (RawLoad LdL 0) %"chk323";
    %"v1876" : L = Add %"v1875", #1;
    %"chk324" : A = (Renew 0 8 Write 1) %"chk320", %"v1865";
    store Wl [%"chk324" + 0] <- %"v1876";
    %"v1877" : L = Shl %"v1875", #3;
    %"v1878" = %"v1873" +p %"v1877";
    %"chk325" : A = (Check 0 8 Write 1) %"v1878";
    store Wl [%"chk325" + 0] <- %"v1871";
    %"chk326" : A = (Renew 0 4 Write 1) %"chk59", %"v1867";
    store Ww [%"chk326" + 0] <- #0
    => goto "L333" };
  ir_blk{ @"L333":
    %"v1883" = %"v10" +p #4;
    %"chk327" : A = (HalfCheck Lower 0 4 Read 1) %"chk0", %"v1883";
    %"v1884" : W = (RawLoad (LdNarrow Sw) 0) %"chk327";
    call %"v1896" : P = $"glibc_printf_fp#__ctype_tolower_loc.gnu_inline"();
    %"chk328" : A = (Check 0 8 Read 8) %"v1896";
    %"v1897" : P = (RawLoadPointer 0 load_effects) %"chk328";
    %"v1899" = %"v10" +p #8;
    %"chk329" : A = (HalfCheck Lower 0 4 Read 1) %"chk0", %"v1899";
    %"v1900" : W = (RawLoad (LdNarrow Sw) 0) %"chk329";
    %"v1901" : L = (Ext Sw) %"v1900";
    %"v1902" : L = Shl %"v1901", #2;
    %"v1903" = %"v1897" +p %"v1902";
    %"chk330" : A = (Check 0 4 Read 1) %"v1903";
    %"v1904" : W = (RawLoad (LdNarrow Sw) 0) %"chk330";
    %"v1905" : W = (Ext Sb) %"v1904";
    %"v1910" : W = (Cmp Eq W) %"v1905", #101
    => br %"v1910" ? "L1906" : "L1907" };
  ir_blk{ @"L1906":
    %"v1911" = %"v28" +p #4;
    %"v1913" = %"v10" +p #8;
    %"v1914" : W = (RawLoad (LdNarrow Sw) 0) %"chk329";
    %"chk332" : A = (HalfCheck Upper 0 4 Write 1) %"chk2", %"v1911";
    store Ww [%"chk332" + 0] <- %"v1914";
    %"chk333" : A = (HalfCheck Lower 0 4 Read 1) %"chk0", %"v10";
    %"v1919" : W = (RawLoad (LdNarrow Sw) 0) %"chk333";
    %"v1920" : W = (Cmp Slt W) %"v1919", #0
    => br %"v1920" ? "L1917" : "L1916" };
  ir_blk{ @"L1916":
    %"v1922" : W = (RawLoad (LdNarrow Sw) 0) %"chk333"
    => goto "L1917" };
  ir_blk{ @"L1917" [%"v1923" : W = phi("L1916" => %"v1922", "L1906" => #6)]:
    %"v1926" : L = (Ext Sw) %"v1923";
    %"v1928" : L = Add %"v1926", #2;
    %"v1929" : L = Add %"v1928", #1;
    %"v1930" : L = Add %"v1929", #1;
    %"v1931" : L = Add %"v1930", #4
    => goto "L1908" };
  ir_blk{ @"L1907":
    %"v1936" : W = (Cmp Eq W) %"v1905", #102
    => br %"v1936" ? "L1932" : "L1933" };
  ir_blk{ @"L1932":
    %"v1937" = %"v28" +p #4;
    %"chk335" : A = (HalfCheck Upper 0 4 Write 1) %"chk2", %"v1937";
    store Ww [%"chk335" + 0] <- #102;
    %"chk336" : A = (HalfCheck Lower 0 4 Read 1) %"chk0", %"v10";
    %"v1942" : W = (RawLoad (LdNarrow Sw) 0) %"chk336";
    %"v1943" : W = (Cmp Slt W) %"v1942", #0
    => br %"v1943" ? "L1940" : "L1939" };
  ir_blk{ @"L1939":
    %"v1945" : W = (RawLoad (LdNarrow Sw) 0) %"chk336"
    => goto "L1940" };
  ir_blk{ @"L1940" [%"v1946" : W = phi("L1939" => %"v1945", "L1932" => #6)]:
    %"chk338" : A = (Renew 0 4 Read 1) %"chk2", %"v28";
    %"v1950" : W = (RawLoad (LdNarrow Sw) 0) %"chk338";
    %"v1951" : W = (Cmp Eq W) %"v1950", #0
    => br %"v1951" ? "L1947" : "L1948" };
  ir_blk{ @"L1947":
    %"v1952" = %"v28" +p #8;
    %"chk339" : A = (Renew 0 4 Read 1) %"chk59", %"v1952";
    %"v1953" : W = (RawLoad (LdNarrow Sw) 0) %"chk339";
    %"v1954" : W = Add %"v1953", #1;
    %"v1956" : W = (RawLoad (LdNarrow Sw) 0) %"chk339";
    %"v1957" : L = (Ext Sw) %"v1956";
    %"v1958" : L = Add %"v1957", #1;
    %"v1959" : L = Add %"v1958", #1;
    %"v1961" : L = (Ext Sw) %"v1946";
    %"v1962" : L = Add %"v1959", %"v1961"
    => goto "L1908" };
  ir_blk{ @"L1948":
    %"v1965" : L = (Ext Sw) %"v1946";
    %"v1967" : L = Add %"v1965", #2
    => goto "L1908" };
  ir_blk{ @"L1933":
    %"chk341" : A = (HalfCheck Lower 0 4 Read 1) %"chk0", %"v10";
    %"v1972" : W = (RawLoad (LdNarrow Sw) 0) %"chk341";
    %"v1973" : W = (Cmp Slt W) %"v1972", #0
    => br %"v1973" ? "L1970" : "L1969" };
  ir_blk{ @"L1969":
    %"v1978" : W = (RawLoad (LdNarrow Sw) 0) %"chk341";
    %"v1979" : W = (Cmp Eq W) %"v1978", #0
    => br %"v1979" ? "L1970" : "L1975" };
  ir_blk{ @"L1975":
    %"v1981" : W = (RawLoad (LdNarrow Sw) 0) %"chk341"
    => goto "L1970" };
  ir_blk{ @"L1970" [%"v1983" : W = phi("L1933" => #6, "L1975" => %"v1981", "L1969" => #1)]:
    %"chk344" : A = (Renew 0 4 Read 1) %"chk2", %"v28";
    %"v1987" : W = (RawLoad (LdNarrow Sw) 0) %"chk344";
    %"v1988" : W = (Cmp Eq W) %"v1987", #0
    => br %"v1988" ? "L1989" : "L1990" };
  ir_blk{ @"L1989":
    %"v1991" = %"v28" +p #8;
    %"chk345" : A = (Renew 0 4 Read 1) %"chk59", %"v1991";
    %"v1992" : W = (RawLoad (LdNarrow Sw) 0) %"chk345";
    %"v1994" : W = (Cmp Sge W) %"v1992", %"v1983"
    => goto "L1990" };
  ir_blk{ @"L1990" [%"v1996" : W = phi("L1970" => #0, "L1989" => %"v1994")]:
    => br %"v1996" ? "L1998" : "L1997" };
  ir_blk{ @"L1997":
    %"v1999" : W = (RawLoad (LdNarrow Sw) 0) %"chk344";
    %"v2000" : W = (Cmp Ne W) %"v1999", #0
    => br %"v2000" ? "L2001" : "L1998" };
  ir_blk{ @"L2001":
    %"v2003" = %"v28" +p #8;
    %"chk347" : A = (Renew 0 4 Read 1) %"chk59", %"v2003";
    %"v2004" : W = (RawLoad (LdNarrow Sw) 0) %"chk347";
    %"v2005" : W = (Cmp Sgt W) %"v2004", #4
    => goto "L1998" };
  ir_blk{ @"L1998" [%"v2009" : W = phi("L1990" => #1, "L1997" => #0, "L2001" => %"v2005")]:
    => br %"v2009" ? "L2010" : "L1985" };
  ir_blk{ @"L2010":
    %"v2016" = %"v28" +p #4;
    %"v2018" = %"v10" +p #8;
    %"v2019" : W = (RawLoad (LdNarrow Sw) 0) %"chk329";
    %"v2020" : W = Sub %"v2019", #71;
    %"v2021" : W = Add %"v2020", #69;
    %"chk349" : A = (HalfCheck Upper 0 4 Write 1) %"chk2", %"v2016";
    store Ww [%"chk349" + 0] <- %"v2021";
    %"v2038" : W = Sub %"v1983", #1;
    %"v2041" : L = (Ext Sw) %"v2038";
    %"v2043" : L = Add %"v2041", #2;
    %"v2044" : L = Add %"v2043", #1;
    %"v2045" : L = Add %"v2044", #1;
    %"v2046" : L = Add %"v2045", #4
    => goto "L1986" };
  ir_blk{ @"L1985":
    %"v2047" = %"v28" +p #4;
    %"chk350" : A = (HalfCheck Upper 0 4 Write 1) %"chk2", %"v2047";
    store Ww [%"chk350" + 0] <- #102;
    %"v2051" : W = (RawLoad (LdNarrow Sw) 0) %"chk344";
    %"v2052" : W = (Cmp Eq W) %"v2051", #0
    => br %"v2052" ? "L2048" : "L2050" };
  ir_blk{ @"L2048":
    %"v2053" = %"v28" +p #8;
    %"chk352" : A = (Renew 0 4 Read 1) %"chk59", %"v2053";
    %"v2054" : W = (RawLoad (LdNarrow Sw) 0) %"chk352";
    %"v2055" : W = Add %"v2054", #1
    => goto "L2050" };
  ir_blk{ @"L2050" [%"v2056" : W = phi("L2048" => %"v2055", "L1985" => #0)]:
    %"v2059" : W = Sub %"v1983", %"v2056";
    %"v2061" : L = (Ext Sw) %"v1983";
    %"v2062" : L = Add %"v2061", #1;
    %"v2063" : L = Add %"v2062", #4
    => goto "L1986" };
  ir_blk{ @"L1986" [%"pr.86" : W = phi("L2010" => %"v2038", "L2050" => %"v2059"); %"pr.74" : W = phi("L2010" => #1, "L2050" => %"v2056"); %"pr.68" : L = phi("L2010" => %"v2046", "L2050" => %"v2063")]:
    %"v2068" = %"v10" +p #12;
    %"chk353" : A = (Renew 0 4 Read 1) %"chk0", %"v2068";
    %"v2069" : W = (RawLoad (LdNarrow Uw) 0) %"chk353";
    %"v2070" : W = Shl %"v2069", #28;
    %"v2071" : W = Shr %"v2070", #31
    => br %"v2071" ? "L1908" : "L2065" };
  ir_blk{ @"L2065":
    => goto "L1908" };
  ir_blk{ @"L1908" [%"pr.92" : W = phi("L1917" => #1, "L1947" => #1, "L1948" => #1, "L2065" => #0, "L1986" => #0); %"pr.90" : W = phi("L1917" => #2147483647, "L1947" => #2147483647, "L1948" => #2147483647, "L2065" => %"v1983", "L1986" => %"v1983"); %"pr.84" : W = phi("L1917" => %"v1923", "L1947" => %"v1946", "L1948" => %"v1946", "L2065" => %"pr.86", "L1986" => %"pr.86"); %"pr.82" : W = phi("L1917" => %"v1923", "L1947" => %"v1946", "L1948" => %"v1946", "L2065" => #0, "L1986" => %"pr.86"); %"pr.71" : W = phi("L1917" => #1, "L1947" => %"v1954", "L1948" => #1, "L2065" => %"pr.74", "L1986" => %"pr.74"); %"pr.65" : L = phi("L1917" => %"v1931", "L1947" => %"v1962", "L1948" => %"v1967", "L2065" => %"pr.68", "L1986" => %"pr.68")]:
    %"v2081" : W = (Cmp Uge L) %"pr.65", #18446744073709551613
    => br %"v2081" ? "L2083" : "L2082" }] [ir_blk{ @"L2082":
    %"v2086" : L = (Ext Sw) %"pr.84";
    %"v2087" : W = (Cmp Ult L) %"pr.65", %"v2086"
    => goto "L2083" };
  ir_blk{ @"L2083" [%"v2089" : W = phi("L1908" => #1, "L2082" => %"v2087")]:
    => br %"v2089" ? "L2074" : "L2076" };
  ir_blk{ @"L2074":
    %"v2092" : P = Copy $"__libc_errno";
    %"chk354" : A = (Check 0 4 Write 1) %"v2092";
    store Ww [%"chk354" + 0] <- #34;
    call void $"glibc_printf_fp#__printf_buffer_mark_failed"(P %"v0")
    => ret void };
  ir_blk{ @"L2076":
    %"v2097" : L = Add %"pr.65", #2;
    call %"v2099" : W = $"glibc_printf_fp#__libc_use_alloca.gnu_inline"(L %"v2097");
    %"v2100" : W = (Cmp Eq W) %"v2099", #0
    => br %"v2100" ? "L2101" : "L2102" };
  ir_blk{ @"L2101":
    call %"v2108" : P = $"malloc"(L %"v2097");
    %"v2113" : L = Ptoi %"v2108";
    %"v2114" : L = Ptoi #0;
    %"v2115" : W = (Cmp Eq L) %"v2113", %"v2114"
    => br %"v2115" ? "L2109" : "L2103" };
  ir_blk{ @"L2109":
    call void $"glibc_printf_fp#__printf_buffer_mark_failed"(P %"v0")
    => ret void };
  ir_blk{ @"L2102":
    %"v2119" : P = (Alloc 16) %"v2097"
    => goto "L2103" };
  ir_blk{ @"L2103" [%"pr.16" : P = phi("L2102" => %"v2119", "L2101" => %"v2108")]:
    %"v2121" = %"pr.16" +p #2;
    %"chk355" : A = (Renew 0 4 Read 1) %"chk2", %"v28";
    %"v2125" : W = (RawLoad (LdNarrow Sw) 0) %"chk355";
    %"v2126" : W = (Cmp Eq W) %"v2125", #0
    => br %"v2126" ? "L2128" : "L2127" };
  ir_blk{ @"L2127":
    %"v2129" = %"v28" +p #4;
    %"chk356" : A = (HalfCheck Upper 0 4 Read 1) %"chk2", %"v2129";
    %"v2130" : W = (RawLoad (LdNarrow Sw) 0) %"chk356";
    %"v2131" : W = (Cmp Ne W) %"v2130", #102
    => goto "L2128" };
  ir_blk{ @"L2128" [%"v2133" : W = phi("L2103" => #1, "L2127" => %"v2131")]:
    => br %"v2133" ? "L2122" : "L2123" };
  ir_blk{ @"L2122":
    %"v2137" : W = (RawLoad (LdNarrow Sw) 0) %"chk355";
    %"v2138" : W = (Cmp Eq W) %"v2137", #0
    => br %"v2138" ? "L2140" : "L2139" };
  ir_blk{ @"L2139":
    %"v2142" : W = (Cmp Eq W) %"pr.71", #1
    => goto "L2140" };
  ir_blk{ @"L2140" [%"v2144" : W = phi("L2122" => #1, "L2139" => %"v2142")]:
    => br %"v2144" ? "L2148" : "L2135" };
  ir_blk{ @"L2135":
    %"v2145" : P = Copy $"glibc_printf_fp#str.310";
    %"v2146" : P = Copy $"glibc_printf_fp#str.302";
    %"v2147" : P = Copy $"glibc_printf_fp#str.303";
    call void $"__libc_assert_fail"(P %"v2145", P %"v2146", W #765, P %"v2147")
    => goto "L2148" };
  ir_blk{ @"L2148" [%"pr.76" : W = phi("L2149" => %"v2155", "L2135" => #0, "L2140" => #0); %"pr.51" : P = phi("L2149" => %"v2157", "L2135" => %"v2121", "L2140" => %"v2121")]:
    %"v2153" : W = (Cmp Slt W) %"pr.76", %"pr.71"
    => br %"v2153" ? "L2149" : "L2150" };
  ir_blk{ @"L2149":
    %"v2155" : W = Add %"pr.76", #1;
    %"v2157" = %"pr.51" +p #1;
    call %"v2158" : W = $"glibc_printf_fp#hack_digit"(P %"v28");
    %"v2159" : W = (Ext Sb) %"v2158";
    %"chk358" : A = (Check 0 1 Write 1) %"pr.51";
    store Wb [%"chk358" + 0] <- %"v2159"
    => goto poll "L2148" };
  ir_blk{ @"L2150":
    %"v2164" = %"v10" +p #12;
    %"chk359" : A = (Renew 0 4 Read 1) %"chk0", %"v2164";
    %"v2165" : W = (RawLoad (LdNarrow Uw) 0) %"chk359";
    %"v2166" : W = Shl %"v2165", #28;
    %"v2167" : W = Shr %"v2166", #31
    => br %"v2167" ? "L2169" : "L2168" };
  ir_blk{ @"L2168":
    %"v2171" : W = (Cmp Sgt W) %"pr.82", #0
    => goto "L2169" };
  ir_blk{ @"L2169" [%"v2173" : W = phi("L2150" => #1, "L2168" => %"v2171")]:
    => br %"v2173" ? "L2175" : "L2174" };
  ir_blk{ @"L2174":
    %"v2177" : W = (Cmp Sgt W) %"pr.84", #0
    => br %"v2177" ? "L2178" : "L2175" };
  ir_blk{ @"L2178":
    %"v2180" = %"v28" +p #24;
    %"chk360" : A = (HalfCheck Upper 0 8 Read 1) %"chk2", %"v2180";
    %"v2181" : L = (RawLoad LdL 0) %"chk360";
    %"v2182" : W = (Cmp Sgt L) %"v2181", #1
    => br %"v2182" ? "L2175" : "L2183" };
  ir_blk{ @"L2183":
    %"v2185" = %"v28" +p #16;
    %"chk361" : A = (Renew 0 8 Read 8) %"chk60", %"v2185";
    %"v2186" : P = (RawLoadPointer 0 load_effects) %"chk361";
    %"chk362" : A = (Check 0 8 Read 1) %"v2186";
    %"v2188" : L = (RawLoad LdL 0) %"chk362";
    %"v2189" : W = (Cmp Ne L) %"v2188", #0
    => goto "L2175" };
  ir_blk{ @"L2175" [%"v2195" : W = phi("L2169" => #1, "L2174" => #0, "L2178" => #1, "L2183" => %"v2189")]:
    => br %"v2195" ? "L2160" : "L2124" };
  ir_blk{ @"L2160":
    %"v2197" = %"pr.51" +p #1;
    %"v2198" : W = (Ext Sb) %"v6";
    %"chk363" : A = (Check 0 1 Write 1) %"pr.51";
    store Wb [%"chk363" + 0] <- %"v2198"
    => goto "L2124" };
  ir_blk{ @"L2123":
    %"v2200" = %"v2121" +p #1;
    %"chk364" : A = (Check 0 1 Write 1) %"v2121";
    store Wb [%"chk364" + 0] <- #48;
    %"v2201" = %"v28" +p #8;
    %"chk365" : A = (Renew 0 4 Read 1) %"chk59", %"v2201";
    %"v2202" : W = (RawLoad (LdNarrow Sw) 0) %"chk365";
    %"v2203" : W = Sub %"v2202", #1;
    %"chk366" : A = (Renew 0 4 Write 1) %"chk59", %"v2201";
    store Ww [%"chk366" + 0] <- %"v2203";
    %"v2205" = %"v2200" +p #1;
    %"v2206" : W = (Ext Sb) %"v6";
    %"chk367" : A = (HalfCheck Upper 0 1 Write 1) %"chk364", %"v2200";
    store Wb [%"chk367" + 0] <- %"v2206"
    => goto "L2124" };
  ir_blk{ @"L2124" [%"pr.94" : W = phi("L2123" => %"pr.92", "L2160" => #1, "L2175" => #1); %"pr.75" : W = phi("L2123" => #0, "L2160" => %"pr.76", "L2175" => %"pr.76"); %"pr.50" : P = phi("L2123" => %"v2205", "L2160" => %"v2197", "L2175" => %"pr.51")]:
    => goto "L2209" };
  ir_blk{ @"L2209" [%"pr.106" : W = phi("L2124" => #0, "L2210" => %"pr.106", "L2259" => %"v2265", "L2252" => %"pr.106", "L2246" => %"pr.106"); %"pr.97" : W = phi("L2124" => #0, "L2210" => %"v2241", "L2259" => %"v2241", "L2252" => %"v2241", "L2246" => %"v2241"); %"pr.95" : W = phi("L2124" => %"pr.94", "L2210" => #1, "L2259" => %"pr.95", "L2252" => %"pr.95", "L2246" => %"pr.95"); %"pr.87" : W = phi("L2124" => %"pr.84", "L2210" => %"pr.87", "L2259" => %"v2258", "L2252" => %"v2258", "L2246" => %"pr.87"); %"pr.53" : P = phi("L2124" => %"pr.50", "L2210" => %"v2249", "L2259" => %"v2249", "L2252" => %"v2249", "L2246" => %"v2249")]:
    %"v2215" : W = Add %"pr.82", %"pr.106";
    %"v2216" : W = (Cmp Slt W) %"pr.97", %"v2215"
    => br %"v2216" ? "L2218" : "L2217" };
  ir_blk{ @"L2217":
    %"v2221" : W = (Cmp Slt W) %"pr.97", %"pr.87"
    => br %"v2221" ? "L2222" : "L2218" };
  ir_blk{ @"L2222":
    %"v2224" = %"v28" +p #24;
    %"chk368" : A = (HalfCheck Upper 0 8 Read 1) %"chk2", %"v2224";
    %"v2225" : L = (RawLoad LdL 0) %"chk368";
    %"v2226" : W = (Cmp Sgt L) %"v2225", #1
    => br %"v2226" ? "L2218" : "L2227" };
  ir_blk{ @"L2227":
    %"v2229" = %"v28" +p #16;
    %"chk369" : A = (Renew 0 8 Read 8) %"chk60", %"v2229";
    %"v2230" : P = (RawLoadPointer 0 load_effects) %"chk369";
    %"chk370" : A = (Check 0 8 Read 1) %"v2230";
    %"v2232" : L = (RawLoad LdL 0) %"chk370";
    %"v2233" : W = (Cmp Ne L) %"v2232", #0
    => goto "L2218" };
  ir_blk{ @"L2218" [%"v2239" : W = phi("L2209" => #1, "L2217" => #0, "L2222" => #1, "L2227" => %"v2233")]:
    => br %"v2239" ? "L2210" : "L2211" };
  ir_blk{ @"L2210":
    %"v2241" : W = Add %"pr.97", #1;
    call %"v2243" : W = $"glibc_printf_fp#hack_digit"(P %"v28");
    %"v2244" : W = (Ext Sb) %"v2243";
    %"chk371" : A = (Check 0 1 Write 1) %"pr.53";
    store Wb [%"chk371" + 0] <- %"v2244";
    %"v2249" = %"pr.53" +p #1;
    %"v2250" : W = (RawLoad (LdNarrow Sb) 0) %"chk371";
    %"v2251" : W = (Cmp Ne W) %"v2250", #48
    => br %"v2251" ? poll "L2209" : "L2246" };
  ir_blk{ @"L2246":
    %"v2256" : W = (Cmp Eq W) %"pr.95", #0
    => br %"v2256" ? "L2252" : poll "L2209" };
  ir_blk{ @"L2252":
    %"v2258" : W = Add %"pr.87", #1;
    %"v2263" : W = (Cmp Sgt W) %"pr.82", #0
    => br %"v2263" ? "L2259" : poll "L2209" };
  ir_blk{ @"L2259":
    %"v2265" : W = Add %"pr.106", #1
    => goto poll "L2209" };
  ir_blk{ @"L2211":
    %"v2273" = %"pr.53" +p #18446744073709551615;
    %"chk373" : A = (Check 0 1 Read 1) %"v2273";
    %"v2274" : W = (RawLoad (LdNarrow Sb) 0) %"chk373";
    %"v2275" : W = (Ext Sb) %"v6";
    %"v2276" : W = (Cmp Ne W) %"v2274", %"v2275"
    => br %"v2276" ? "L2267" : "L2268" };
  ir_blk{ @"L2267":
    %"v2280" = %"pr.53" +p #18446744073709551615;
    %"v2281" : W = (RawLoad (LdNarrow Sb) 0) %"chk373"
    => goto "L2269" };
  ir_blk{ @"L2268":
    %"v2285" = %"pr.53" +p #18446744073709551614;
    %"chk375" : A = (HalfCheck Lower 0 1 Read 1) %"chk373", %"v2285";
    %"v2286" : W = (RawLoad (LdNarrow Sb) 0) %"chk375"
    => goto "L2269" };
  ir_blk{ @"L2269" [%"v2287" : W = phi("L2267" => %"v2281", "L2268" => %"v2286")]:
    %"v2288" : W = (Ext Sb) %"v2287";
    call %"v2290" : W = $"glibc_printf_fp#hack_digit"(P %"v28");
    %"v2291" : W = (Ext Sb) %"v2290";
    %"v2297" : W = (Cmp Ne W) %"v2291", #48
    => br %"v2297" ? "L2298" : "L2299" };
  ir_blk{ @"L2298":
    %"v2301" : W = (Cmp Ne W) %"v2291", #53
    => goto "L2299" };
  ir_blk{ @"L2299" [%"v2303" : W = phi("L2269" => #0, "L2298" => %"v2301")]:
    => br %"v2303" ? "L2295" : "L2294" };
  ir_blk{ @"L2294":
    %"v2308" = %"v28" +p #24;
    %"chk376" : A = (HalfCheck Upper 0 8 Read 1) %"chk2", %"v2308";
    %"v2309" : L = (RawLoad LdL 0) %"chk376";
    %"v2310" : W = (Cmp Eq L) %"v2309", #1
    => br %"v2310" ? "L2311" : "L2312" };
  ir_blk{ @"L2311":
    %"v2313" = %"v28" +p #16;
    %"chk377" : A = (Renew 0 8 Read 8) %"chk60", %"v2313";
    %"v2314" : P = (RawLoadPointer 0 load_effects) %"chk377";
    %"chk378" : A = (Check 0 8 Read 1) %"v2314";
    %"v2316" : L = (RawLoad LdL 0) %"chk378";
    %"v2317" : W = (Cmp Eq L) %"v2316", #0
    => goto "L2312" };
  ir_blk{ @"L2312" [%"v2319" : W = phi("L2294" => #0, "L2311" => %"v2317")]:
    => br %"v2319" ? "L2295" : "L2306" };
  ir_blk{ @"L2306":
    %"v2324" = %"v28" +p #40;
    %"chk379" : A = (Renew 0 8 Read 1) %"chk63", %"v2324";
    %"v2325" : L = (RawLoad LdL 0) %"chk379";
    %"v2326" : W = (Cmp Eq L) %"v2325", #0
    => br %"v2326" ? "L2321" : "L2295" };
  ir_blk{ @"L2321":
    %"v2328" = %"v28" +p #24;
    %"v2329" : L = (RawLoad LdL 0) %"chk376"
    => goto "L2330" };
  ir_blk{ @"L2330" [%"pr.118" : L = phi("L2321" => %"v2329", "L2331" => %"v2348")]:
    %"v2334" : W = (Cmp Uge L) %"pr.118", #1
    => br %"v2334" ? "L2335" : "L2336" };
  ir_blk{ @"L2335":
    %"v2337" = %"v28" +p #16;
    %"chk381" : A = (Renew 0 8 Read 8) %"chk60", %"v2337";
    %"v2338" : P = (RawLoadPointer 0 load_effects) %"chk381";
    %"v2340" : L = Sub %"pr.118", #1;
    %"v2341" : L = Shl %"v2340", #3;
    %"v2342" = %"v2338" +p %"v2341";
    %"chk382" : A = (Check 0 8 Read 1) %"v2342";
    %"v2343" : L = (RawLoad LdL 0) %"chk382";
    %"v2344" : W = (Cmp Eq L) %"v2343", #0
    => goto "L2336" };
  ir_blk{ @"L2336" [%"v2346" : W = phi("L2330" => #0, "L2335" => %"v2344")]:
    => br %"v2346" ? "L2331" : "L2332" };
  ir_blk{ @"L2331":
    %"v2348" : L = Sub %"pr.118", #1
    => goto poll "L2330" };
  ir_blk{ @"L2332":
    %"v2350" : W = (Cmp Ugt L) %"pr.118", #0
    => goto "L2295" };
  ir_blk{ @"L2295" [%"pr.115" : W = phi("L2299" => #1, "L2312" => #0, "L2332" => %"v2350", "L2306" => #1)]:
    call %"v2354" : W = $"glibc_printf_fp#get_rounding_mode"();
    %"chk383" : A = (Renew 0 4 Read 1) %"chk1", %"v29";
    %"v2358" : W = (RawLoad (LdNarrow Sw) 0) %"chk383";
    %"v2359" : W = (Cmp Ne W) %"v2358", #0;
    %"v2361" : W = Sub %"v2288", #48;
    %"v2362" : W = And %"v2361", #1;
    %"v2365" : W = (Cmp Sge W) %"v2291", #53;
    call %"v2369" : W = $"glibc_printf_fp#round_away"(W %"v2359", W %"v2362", W %"v2365", W %"pr.115", W %"v2354");
    %"v2370" : W = (Ext Ub) %"v2369"
    => br %"v2370" ? "L2355" : "L2357" };
  ir_blk{ @"L2355":
    %"v2377" : W = (Cmp Sgt W) %"pr.97", #0
    => br %"v2377" ? "L2379" : "L2375" };
  ir_blk{ @"L2379" [%"pr.123" : W = phi("L2380" => %"v2396", "L2355" => #0); %"pr.120" : P = phi("L2380" => %"v2383", "L2355" => %"pr.53")]:
    (Flight (a "v2383") Sub [(FAddress (t "pr.120")); (FValue (Const 1))] (LowerOf (t "pr.120")));
    %"chk384" : A = (Check 0 1 Read 1) %"v2383";
    %"v2384" : W = (RawLoad (LdNarrow Sb) 0) %"chk384";
    %"v2386" : W = (Cmp Ne W) %"v2384", %"v2275"
    => br %"v2386" ? "L2387" : "L2388" };
  ir_blk{ @"L2387":
    %"v2390" : W = (RawLoad (LdNarrow Sb) 0) %"chk384";
    %"v2391" : W = (Cmp Eq W) %"v2390", #57
    => goto "L2388" };
  ir_blk{ @"L2388" [%"v2393" : W = phi("L2379" => #0, "L2387" => %"v2391")]:
    => br %"v2393" ? "L2380" : "L2381" };
  ir_blk{ @"L2380":
    %"chk386" : A = (Renew 0 1 Write 1) %"chk384", %"v2383";
    store Wb [%"chk386" + 0] <- #48;
    %"v2396" : W = Add %"pr.123", #1
    => goto poll "L2379" }]) (app [ir_blk{ @"L2381":
    %"v2402" : W = (Cmp Eq W) %"pr.123", %"pr.82"
    => br %"v2402" ? "L2403" : "L2404" };
  ir_blk{ @"L2403":
    %"v2406" : W = (Cmp Sgt W) %"pr.106", #0
    => goto "L2404" };
  ir_blk{ @"L2404" [%"v2408" : W = phi("L2381" => #0, "L2403" => %"v2406")]:
    => br %"v2408" ? "L2397" : "L2399" };
  ir_blk{ @"L2397":
    %"v2410" : W = Sub %"pr.106", #1
    => goto "L2399" };
  ir_blk{ @"L2399" [%"pr.112" : W = phi("L2397" => %"v2410", "L2404" => %"pr.106")]:
    %"v2415" : W = (RawLoad (LdNarrow Sb) 0) %"chk384";
    %"v2417" : W = (Cmp Ne W) %"v2415", %"v2275"
    => br %"v2417" ? "L2411" : "L2412" };
  ir_blk{ @"L2411":
    %"v2419" : W = (RawLoad (LdNarrow Sb) 0) %"chk384";
    %"v2420" : W = Add %"v2419", #1;
    %"v2421" : W = (Ext Sb) %"v2420";
    %"chk389" : A = (Renew 0 1 Write 1) %"chk384", %"v2383";
    store Wb [%"chk389" + 0] <- %"v2421"
    => goto "L2375" };
  ir_blk{ @"L2412":
    %"v2426" : W = (Cmp Eq W) %"v1905", #103
    => br %"v2426" ? "L2427" : "L2428" };
  ir_blk{ @"L2427":
    %"v2429" = %"v28" +p #4;
    %"chk390" : A = (HalfCheck Upper 0 4 Read 1) %"chk2", %"v2429";
    %"v2430" : W = (RawLoad (LdNarrow Sw) 0) %"chk390";
    %"v2431" : W = (Cmp Eq W) %"v2430", #102
    => goto "L2428" };
  ir_blk{ @"L2428" [%"v2433" : W = phi("L2412" => #0, "L2427" => %"v2431")]:
    => br %"v2433" ? "L2434" : "L2435" };
  ir_blk{ @"L2434":
    %"v2437" = %"v10" +p #12;
    %"chk391" : A = (Renew 0 4 Read 1) %"chk0", %"v2437";
    %"v2438" : W = (RawLoad (LdNarrow Uw) 0) %"chk391";
    %"v2439" : W = Shl %"v2438", #28;
    %"v2440" : W = Shr %"v2439", #31;
    %"v2441" : W = (Cmp Ne W) %"v2440", #0
    => goto "L2435" };
  ir_blk{ @"L2435" [%"v2442" : W = phi("L2428" => #0, "L2434" => %"v2441")]:
    => br %"v2442" ? "L2443" : "L2444" };
  ir_blk{ @"L2443":
    %"v2447" = %"v2121" +p #1;
    %"v2448" : L = Ptoi %"v2383";
    %"v2449" : L = Ptoi %"v2447";
    %"v2450" : W = (Cmp Eq L) %"v2448", %"v2449"
    => goto "L2444" };
  ir_blk{ @"L2444" [%"v2452" : W = phi("L2435" => #0, "L2443" => %"v2450")]:
    => br %"v2452" ? "L2453" : "L2454" };
  ir_blk{ @"L2453":
    %"chk392" : A = (Check 0 1 Read 1) %"v2121";
    %"v2457" : W = (RawLoad (LdNarrow Sb) 0) %"chk392";
    %"v2458" : W = (Cmp Eq W) %"v2457", #48
    => goto "L2454" };
  ir_blk{ @"L2454" [%"v2460" : W = phi("L2444" => #0, "L2453" => %"v2458")]:
    => br %"v2460" ? "L2422" : "L2375" };
  ir_blk{ @"L2422":
    %"v2464" : W = Sub %"pr.112", #1
    => goto "L2375" };
  ir_blk{ @"L2375" [%"pr.119" : P = phi("L2411" => %"v2383", "L2422" => %"v2383", "L2454" => %"v2383", "L2355" => %"pr.53"); %"pr.111" : W = phi("L2411" => %"pr.112", "L2422" => %"v2464", "L2454" => %"pr.112", "L2355" => %"pr.106")]:
    %"v2469" : W = (Cmp Eq W) %"pr.97", #0
    => br %"v2469" ? "L2471" : "L2470" };
  ir_blk{ @"L2470":
    %"chk393" : A = (Check 0 1 Read 1) %"pr.119";
    %"v2473" : W = (RawLoad (LdNarrow Sb) 0) %"chk393";
    %"v2475" : W = (Cmp Eq W) %"v2473", %"v2275"
    => goto "L2471" };
  ir_blk{ @"L2471" [%"v2477" : W = phi("L2375" => #1, "L2470" => %"v2475")]:
    => br %"v2477" ? "L2465" : "L2357" };
  ir_blk{ @"L2465":
    (Flight (a "v2482") Sub [(FAddress (t "pr.119")); (FValue (Const 1))] (LowerOf (t "pr.119")));
    %"chk394" : A = (Check 0 1 Read 1) %"v2482";
    %"v2483" : W = (RawLoad (LdNarrow Sb) 0) %"chk394";
    %"v2485" : W = (Cmp Eq W) %"v2483", %"v2275"
    => br %"v2485" ? "L2478" : "L2488" };
  ir_blk{ @"L2478":
    (Flight (a "v2487") Sub [(FAddress (t "pr.119")); (FValue (Const 1))] (LowerOf (t "pr.119")))
    => goto "L2488" };
  ir_blk{ @"L2488" [%"pr.122" : P = phi("L2489" => %"v2492", "L2478" => %"v2487", "L2465" => %"pr.119")]:
    (Flight (a "v2492") Sub [(FAddress (t "pr.122")); (FValue (Const 1))] (LowerOf (t "pr.122")));
    %"v2494" : L = Ptoi %"v2492";
    %"v2495" : L = Ptoi %"v2121";
    %"v2496" : W = (Cmp Uge L) %"v2494", %"v2495"
    => br %"v2496" ? "L2497" : "L2498" };
  ir_blk{ @"L2497":
    %"chk395" : A = (Check 0 1 Read 1) %"v2492";
    %"v2500" : W = (RawLoad (LdNarrow Sb) 0) %"chk395";
    %"v2501" : W = (Cmp Eq W) %"v2500", #57
    => goto "L2498" };
  ir_blk{ @"L2498" [%"v2503" : W = phi("L2488" => #0, "L2497" => %"v2501")]:
    => br %"v2503" ? "L2489" : "L2490" };
  ir_blk{ @"L2489":
    %"chk396" : A = (Check 0 1 Write 1) %"v2492";
    store Wb [%"chk396" + 0] <- #48
    => goto poll "L2488" };
  ir_blk{ @"L2490":
    => br %"v2496" ? "L2505" : "L2506" };
  ir_blk{ @"L2505":
    %"chk397" : A = (Check 0 1 Read 1) %"v2492";
    %"v2514" : W = (RawLoad (LdNarrow Sb) 0) %"chk397";
    %"v2515" : W = Add %"v2514", #1;
    %"v2516" : W = (Ext Sb) %"v2515";
    %"chk398" : A = (Renew 0 1 Write 1) %"chk397", %"v2492";
    store Wb [%"chk398" + 0] <- %"v2516"
    => goto "L2357" };
  ir_blk{ @"L2506":
    %"v2520" = %"v28" +p #4;
    %"chk399" : A = (HalfCheck Upper 0 4 Read 1) %"chk2", %"v2520";
    %"v2521" : W = (RawLoad (LdNarrow Sw) 0) %"chk399";
    %"v2522" : W = (Cmp Ne W) %"v2521", #102
    => br %"v2522" ? "L2517" : "L2518" };
  ir_blk{ @"L2517":
    %"chk400" : A = (Check 0 1 Write 1) %"v2121";
    store Wb [%"chk400" + 0] <- #49;
    %"v2524" = %"v28" +p #8;
    %"chk401" : A = (Renew 0 4 Read 1) %"chk59", %"v2524";
    %"v2525" : W = (RawLoad (LdNarrow Sw) 0) %"chk401";
    %"chk402" : A = (Renew 0 4 Read 1) %"chk2", %"v28";
    %"v2529" : W = (RawLoad (LdNarrow Sw) 0) %"chk402";
    %"v2530" : W = (Cmp Eq W) %"v2529", #0
    => br %"v2530" ? "L2528" : "L2527" };
  ir_blk{ @"L2527":
    => goto "L2528" };
  ir_blk{ @"L2528" [%"v2532" : W = phi("L2527" => #4294967295, "L2517" => #1)]:
    %"v2533" : W = Add %"v2525", %"v2532";
    %"chk403" : A = (Renew 0 4 Write 1) %"chk59", %"v2524";
    store Ww [%"chk403" + 0] <- %"v2533";
    %"v2537" = %"v28" +p #8;
    %"v2538" : W = (RawLoad (LdNarrow Sw) 0) %"chk403";
    %"v2539" : W = (Cmp Eq W) %"v2538", #0
    => br %"v2539" ? "L2534" : "L2519" };
  ir_blk{ @"L2534":
    store Ww [%"chk402" + 0] <- #0
    => goto "L2519" };
  ir_blk{ @"L2518":
    %"v2545" : W = (Cmp Eq W) %"pr.75", %"pr.90"
    => br %"v2545" ? "L2540" : "L2541" };
  ir_blk{ @"L2540":
    (Flight (a "v2547") Sub [(FAddress (t "v2121")); (FValue (Const 1))] (LowerOf (t "v2121")));
    %"chk406" : A = (Check 0 1 Write 1) %"v2547";
    store Wb [%"chk406" + 0] <- %"v2275";
    (Flight (a "v2550") Sub [(FAddress (t "v2547")); (FValue (Const 1))] (LowerOf (t "v2547")));
    %"chk407" : A = (HalfCheck Lower 0 1 Write 1) %"chk406", %"v2550";
    store Wb [%"chk407" + 0] <- #49;
    %"v2555" = %"v10" +p #12;
    %"chk408" : A = (Renew 0 4 Read 1) %"chk0", %"v2555";
    %"v2556" : W = (RawLoad (LdNarrow Uw) 0) %"chk408";
    %"v2557" : W = Shl %"v2556", #28;
    %"v2558" : W = Shr %"v2557", #31
    => br %"v2558" ? "L2560" : "L2559" };
  ir_blk{ @"L2559":
    => goto "L2560" };
  ir_blk{ @"L2560" [%"v2564" : W = phi("L2540" => #1, "L2559" => %"v2377")]:
    => br %"v2564" ? "L2551" : "L2553" };
  ir_blk{ @"L2551":
    %"v2567" : W = Add %"pr.75", #2;
    %"v2568" : L = (Ext Sw) %"v2567";
    %"v2569" = %"v2550" +p %"v2568";
    %"chk409" : A = (Check 0 1 Write 1) %"v2569";
    store Wb [%"chk409" + 0] <- #48;
    %"v2571" : W = Add %"pr.97", #1
    => goto "L2553" };
  ir_blk{ @"L2553" [%"pr.103" : W = phi("L2551" => %"v2571", "L2560" => %"pr.97")]:
    %"v2574" : W = Add %"pr.103", %"pr.75";
    %"v2578" = %"v28" +p #8;
    %"chk410" : A = (Renew 0 4 Read 1) %"chk59", %"v2578";
    %"v2579" : W = (RawLoad (LdNarrow Sw) 0) %"chk410";
    %"v2580" : W = Add %"v2579", #1;
    %"chk411" : A = (Renew 0 4 Write 1) %"chk59", %"v2578";
    store Ww [%"chk411" + 0] <- %"v2580";
    %"v2581" = %"v28" +p #4;
    call %"v2585" : P = $"glibc_printf_fp#__ctype_b_loc.gnu_inline"();
    %"chk412" : A = (Check 0 8 Read 8) %"v2585";
    %"v2586" : P = (RawLoadPointer 0 load_effects) %"chk412";
    %"v2588" = %"v10" +p #8;
    %"chk413" : A = (Renew 0 4 Read 1) %"chk329", %"v2588";
    %"v2589" : W = (RawLoad (LdNarrow Sw) 0) %"chk413";
    %"v2590" : L = (Ext Sw) %"v2589";
    %"v2591" : L = Shl %"v2590", #1;
    %"v2592" = %"v2586" +p %"v2591";
    %"chk414" : A = (Check 0 2 Read 1) %"v2592";
    %"v2593" : W = (RawLoad (LdNarrow Uh) 0) %"chk414";
    %"v2594" : W = And %"v2593", #256
    => br %"v2594" ? "L2584" : "L2583" };
  ir_blk{ @"L2583":
    => goto "L2584" };
  ir_blk{ @"L2584" [%"v2595" : W = phi("L2583" => #101, "L2553" => #69)]:
    %"chk415" : A = (Renew 0 4 Write 1) %"chk399", %"v2581";
    store Ww [%"chk415" + 0] <- %"v2595"
    => goto "L2519" };
  ir_blk{ @"L2541":
    (Flight (a "v2597") Sub [(FAddress (t "v2121")); (FValue (Const 1))] (LowerOf (t "v2121")));
    %"chk416" : A = (Check 0 1 Write 1) %"v2597";
    store Wb [%"chk416" + 0] <- #49;
    %"v2599" : W = Add %"pr.75", #1
    => goto "L2519" };
  ir_blk{ @"L2519" [%"pr.101" : W = phi("L2534" => %"pr.97", "L2528" => %"pr.97", "L2584" => %"v2574", "L2541" => %"pr.97"); %"pr.80" : W = phi("L2534" => %"pr.75", "L2528" => %"pr.75", "L2584" => #1, "L2541" => %"v2599"); %"pr.48" : P = phi("L2534" => %"v2121", "L2528" => %"v2121", "L2584" => %"v2550", "L2541" => %"v2597")]:
    %"v2605" : W = Add %"pr.80", %"pr.101";
    %"v2607" : W = (Cmp Sgt W) %"v2605", %"pr.90"
    => br %"v2607" ? "L2600" : "L2357" };
  ir_blk{ @"L2600":
    %"v2613" : W = Sub %"v2605", %"pr.90";
    %"v2614" : L = (Ext Sw) %"v2613";
    (Flight (a "v2615") Sub [(FAddress (t "pr.53")); (FValue (t "v2614"))] (LowerOf (t "pr.53")));
    %"v2622" : W = Sub %"pr.101", %"v2613"
    => goto "L2357" };
  ir_blk{ @"L2357" [%"pr.110" : W = phi("L2505" => %"pr.111", "L2600" => %"pr.111", "L2519" => %"pr.111", "L2471" => %"pr.111", "L2295" => %"pr.106"); %"pr.98" : W = phi("L2505" => %"pr.97", "L2600" => %"v2622", "L2519" => %"pr.101", "L2471" => %"pr.97", "L2295" => %"pr.97"); %"pr.77" : W = phi("L2505" => %"pr.75", "L2600" => %"pr.80", "L2519" => %"pr.80", "L2471" => %"pr.75", "L2295" => %"pr.75"); %"pr.54" : P = phi("L2505" => %"pr.53", "L2600" => %"v2615", "L2519" => %"pr.53", "L2471" => %"pr.53", "L2295" => %"pr.53"); %"pr.45" : P = phi("L2505" => %"v2121", "L2600" => %"pr.48", "L2519" => %"pr.48", "L2471" => %"v2121", "L2295" => %"v2121")]:
    => goto "L2623" };
  ir_blk{ @"L2623" [%"pr.105" : W = phi("L2357" => %"pr.98", "L2624" => %"v2642"); %"pr.58" : P = phi("L2357" => %"pr.54", "L2624" => %"v2640")]:
    %"v2629" : W = Add %"pr.82", %"pr.110";
    %"v2630" : W = (Cmp Sgt W) %"pr.105", %"v2629"
    => br %"v2630" ? "L2631" : "L2632" };
  ir_blk{ @"L2631":
    (Flight (a "v2634") Sub [(FAddress (t "pr.58")); (FValue (Const 1))] (LowerOf (t "pr.58")));
    %"chk417" : A = (Check 0 1 Read 1) %"v2634";
    %"v2635" : W = (RawLoad (LdNarrow Sb) 0) %"chk417";
    %"v2636" : W = (Cmp Eq W) %"v2635", #48
    => goto "L2632" };
  ir_blk{ @"L2632" [%"v2638" : W = phi("L2623" => #0, "L2631" => %"v2636")]:
    => br %"v2638" ? "L2624" : "L2625" };
  ir_blk{ @"L2624":
    (Flight (a "v2640") Sub [(FAddress (t "pr.58")); (FValue (Const 1))] (LowerOf (t "pr.58")));
    %"v2642" : W = Sub %"pr.105", #1
    => goto poll "L2623" };
  ir_blk{ @"L2625":
    %"v2647" : W = (Cmp Eq W) %"pr.105", #0
    => br %"v2647" ? "L2648" : "L2649" };
  ir_blk{ @"L2648":
    %"v2651" = %"v10" +p #12;
    %"chk418" : A = (Renew 0 4 Read 1) %"chk0", %"v2651";
    %"v2652" : W = (RawLoad (LdNarrow Uw) 0) %"chk418";
    %"v2653" : W = Shl %"v2652", #28;
    %"v2654" : W = Shr %"v2653", #31;
    %"v2655" : W = (Cmp Eq W) %"v2654", #0
    => goto "L2649" };
  ir_blk{ @"L2649" [%"v2657" : W = phi("L2625" => #0, "L2648" => %"v2655")]:
    => br %"v2657" ? "L2658" : "L2659" };
  ir_blk{ @"L2658":
    (Flight (a "v2661") Sub [(FAddress (t "pr.58")); (FValue (Const 1))] (LowerOf (t "pr.58")));
    %"chk419" : A = (Check 0 1 Read 1) %"v2661";
    %"v2662" : W = (RawLoad (LdNarrow Sb) 0) %"chk419";
    %"v2664" : W = (Cmp Eq W) %"v2662", %"v2275"
    => goto "L2659" };
  ir_blk{ @"L2659" [%"v2666" : W = phi("L2649" => #0, "L2658" => %"v2664")]:
    => br %"v2666" ? "L2643" : "L2645" };
  ir_blk{ @"L2643":
    (Flight (a "v2668") Sub [(FAddress (t "pr.58")); (FValue (Const 1))] (LowerOf (t "pr.58")))
    => goto "L2645" };
  ir_blk{ @"L2645" [%"pr.59" : P = phi("L2643" => %"v2668", "L2659" => %"pr.58")]:
    %"v2672" = %"v28" +p #4;
    %"chk420" : A = (HalfCheck Upper 0 4 Read 1) %"chk2", %"v2672";
    %"v2673" : W = (RawLoad (LdNarrow Sw) 0) %"chk420";
    %"v2674" : W = (Cmp Ne W) %"v2673", #102
    => br %"v2674" ? "L2669" : "L2671" };
  ir_blk{ @"L2669":
    %"chk421" : A = (Renew 0 4 Read 1) %"chk2", %"v28";
    %"v2678" : W = (RawLoad (LdNarrow Sw) 0) %"chk421";
    %"v2679" : W = (Cmp Ne W) %"v2678", #0
    => br %"v2679" ? "L2680" : "L2681" }] [ir_blk{ @"L2680":
    %"v2682" = %"v28" +p #8;
    %"chk422" : A = (Renew 0 4 Read 1) %"chk59", %"v2682";
    %"v2683" : W = (RawLoad (LdNarrow Sw) 0) %"chk422";
    %"v2684" : W = (Cmp Eq W) %"v2683", #4
    => goto "L2681" };
  ir_blk{ @"L2681" [%"v2686" : W = phi("L2669" => #0, "L2680" => %"v2684")]:
    => br %"v2686" ? "L2687" : "L2688" };
  ir_blk{ @"L2687":
    %"v2690" : W = (Cmp Eq W) %"v1905", #103
    => goto "L2688" };
  ir_blk{ @"L2688" [%"v2692" : W = phi("L2681" => #0, "L2687" => %"v2690")]:
    => br %"v2692" ? "L2675" : "L2676" };
  ir_blk{ @"L2675":
    %"v2700" = %"pr.45" +p #1;
    %"v2701" : L = Ptoi %"pr.59";
    %"v2702" : L = Ptoi %"v2700";
    %"v2703" : W = (Cmp Uge L) %"v2701", %"v2702"
    => br %"v2703" ? "L2697" : "L2696" };
  ir_blk{ @"L2696":
    %"v2704" : P = Copy $"glibc_printf_fp#str.311";
    %"v2705" : P = Copy $"glibc_printf_fp#str.302";
    %"v2706" : P = Copy $"glibc_printf_fp#str.303";
    call void $"__libc_assert_fail"(P %"v2704", P %"v2705", W #942, P %"v2706")
    => goto "L2697" };
  ir_blk{ @"L2697":
    %"chk423" : A = (Check 0 1 Read 1) %"pr.45";
    %"v2712" : W = (RawLoad (LdNarrow Sb) 0) %"chk423";
    %"v2713" : W = (Cmp Eq W) %"v2712", #49
    => br %"v2713" ? "L2709" : "L2708" };
  ir_blk{ @"L2708":
    %"v2714" : P = Copy $"glibc_printf_fp#str.312";
    %"v2715" : P = Copy $"glibc_printf_fp#str.302";
    %"v2716" : P = Copy $"glibc_printf_fp#str.303";
    call void $"__libc_assert_fail"(P %"v2714", P %"v2715", W #943, P %"v2716")
    => goto "L2709" };
  ir_blk{ @"L2709":
    %"v2718" : P = Copy $"glibc_printf_fp#str.313";
    call %"v2719" : P = $"__GI_memcpy"(P %"pr.45", P %"v2718", L #6);
    %"v2721" = %"pr.45" +p #1;
    %"chk424" : A = (HalfCheck Upper 0 1 Write 1) %"chk423", %"v2721";
    store Wb [%"chk424" + 0] <- %"v2275";
    %"v2728" = %"pr.45" +p #2;
    %"v2730" : L = Ptoi %"v2728";
    %"v2731" : W = (Cmp Uge L) %"v2701", %"v2730"
    => br %"v2731" ? "L2723" : "L2724" };
  ir_blk{ @"L2723":
    %"v2733" = %"pr.45" +p #6;
    %"v2736" = %"pr.45" +p #2;
    %"v2738" : L = Ptoi %"v2736";
    %"v2739" : L = Sub %"v2701", %"v2738";
    call %"v2740" : P = $"__GI_memset"(P %"v2733", W #48, L %"v2739");
    %"v2742" = %"pr.59" +p #4
    => goto "L2671" };
  ir_blk{ @"L2724":
    %"v2744" = %"pr.59" +p #5
    => goto "L2671" };
  ir_blk{ @"L2676":
    %"v2746" = %"pr.59" +p #1;
    %"v2747" = %"v28" +p #4;
    %"v2748" : W = (RawLoad (LdNarrow Sw) 0) %"chk420";
    %"v2749" : W = (Ext Sb) %"v2748";
    %"chk426" : A = (Check 0 1 Write 1) %"pr.59";
    store Wb [%"chk426" + 0] <- %"v2749";
    %"v2751" = %"v2746" +p #1;
    %"v2755" : W = (RawLoad (LdNarrow Sw) 0) %"chk421"
    => br %"v2755" ? "L2754" : "L2753" };
  ir_blk{ @"L2753":
    => goto "L2754" };
  ir_blk{ @"L2754" [%"v2756" : W = phi("L2753" => #43, "L2676" => #45)]:
    %"v2757" : W = (Ext Sb) %"v2756";
    %"chk428" : A = (HalfCheck Upper 0 1 Write 1) %"chk426", %"v2746";
    store Wb [%"chk428" + 0] <- %"v2757"
    => goto "L2758" };
  ir_blk{ @"L2758" [%"pr.69" : W = phi("L2754" => #10, "L2759" => %"v2766")]:
    %"v2762" = %"v28" +p #8;
    %"chk429" : A = (Renew 0 4 Read 1) %"chk59", %"v2762";
    %"v2763" : W = (RawLoad (LdNarrow Sw) 0) %"chk429";
    %"v2764" : W = (Cmp Sle W) %"pr.69", %"v2763"
    => br %"v2764" ? "L2759" : "L2760" };
  ir_blk{ @"L2759":
    %"v2766" : W = Mul %"pr.69", #10
    => goto poll "L2758" };
  ir_blk{ @"L2760":
    %"v2770" = %"v28" +p #8;
    %"v2771" : W = (RawLoad (LdNarrow Sw) 0) %"chk429";
    %"v2772" : W = (Cmp Slt W) %"v2771", #10
    => br %"v2772" ? "L2767" : "L2775" };
  ir_blk{ @"L2767":
    %"v2774" = %"v2751" +p #1;
    %"chk431" : A = (HalfCheck Upper 0 1 Write 1) %"chk428", %"v2751";
    store Wb [%"chk431" + 0] <- #48
    => goto "L2769" };
  ir_blk{ @"L2775" [%"pr.70" : W = phi("L2775" => %"v2779", "L2760" => %"pr.69"); %"pr.64" : P = phi("L2775" => %"v2781", "L2760" => %"v2751")]:
    %"v2779" : W = Div %"pr.70", #10;
    %"v2781" = %"pr.64" +p #1;
    %"v2782" = %"v28" +p #8;
    %"chk432" : A = (Renew 0 4 Read 1) %"chk59", %"v2782";
    %"v2783" : W = (RawLoad (LdNarrow Sw) 0) %"chk432";
    %"v2785" : W = Div %"v2783", %"v2779";
    %"v2786" : W = Add %"v2785", #48;
    %"v2787" : W = (Ext Sb) %"v2786";
    %"chk433" : A = (Check 0 1 Write 1) %"pr.64";
    store Wb [%"chk433" + 0] <- %"v2787";
    %"v2789" : W = (RawLoad (LdNarrow Sw) 0) %"chk432";
    %"v2791" : W = Rem %"v2789", %"v2779";
    %"chk435" : A = (Renew 0 4 Write 1) %"chk59", %"v2782";
    store Ww [%"chk435" + 0] <- %"v2791";
    %"v2793" : W = (Cmp Sgt W) %"v2779", #10
    => br %"v2793" ? poll "L2775" : "L2769" };
  ir_blk{ @"L2769" [%"pr.63" : P = phi("L2767" => %"v2774", "L2775" => %"v2781")]:
    %"v2795" = %"pr.63" +p #1;
    %"v2796" = %"v28" +p #8;
    %"chk436" : A = (Renew 0 4 Read 1) %"chk59", %"v2796";
    %"v2797" : W = (RawLoad (LdNarrow Sw) 0) %"chk436";
    %"v2798" : W = Add %"v2797", #48;
    %"v2799" : W = (Ext Sb) %"v2798";
    %"chk437" : A = (Check 0 1 Write 1) %"pr.63";
    store Wb [%"chk437" + 0] <- %"v2799"
    => goto "L2671" };
  ir_blk{ @"L2671" [%"pr.60" : P = phi("L2769" => %"v2795", "L2723" => %"v2742", "L2724" => %"v2744", "L2645" => %"pr.59")]:
    %"v2804" : W = (Ext Sb) %"v4";
    %"v2805" : W = (Cmp Ne W) %"v2804", #0
    => br %"v2805" ? "L2806" : "L2807" };
  ir_blk{ @"L2806":
    %"v2809" = %"v10" +p #12;
    %"chk438" : A = (Renew 0 4 Read 1) %"chk0", %"v2809";
    %"v2810" : W = (RawLoad (LdNarrow Uw) 0) %"chk438";
    %"v2811" : W = Shl %"v2810", #24;
    %"v2812" : W = Shr %"v2811", #31;
    %"v2813" : W = (Cmp Ne W) %"v2812", #0
    => goto "L2807" };
  ir_blk{ @"L2807" [%"v2814" : W = phi("L2671" => #0, "L2806" => %"v2813")]:
    => br %"v2814" ? "L2801" : "L2802" };
  ir_blk{ @"L2801":
    call %"v2818" : W = $"__grouping_iterator_init"(P %"v2800", W %"v25", P %"v2", W %"pr.77")
    => goto "L2803" };
  ir_blk{ @"L2802":
    %"v2820" = %"v2800" +p #20;
    %"chk439" : A = (Check 0 4 Write 1) %"v2820";
    store Ww [%"chk439" + 0] <- #0
    => goto "L2803" };
  ir_blk{ @"L2803":
    %"chk440" : A = (Renew 0 4 Read 1) %"chk1", %"v29";
    %"v2824" : W = (RawLoad (LdNarrow Sw) 0) %"chk440"
    => br %"v2824" ? "L2826" : "L2825" };
  ir_blk{ @"L2825":
    %"v2828" = %"v10" +p #12;
    %"chk441" : A = (Renew 0 4 Read 1) %"chk0", %"v2828";
    %"v2829" : W = (RawLoad (LdNarrow Uw) 0) %"chk441";
    %"v2830" : W = Shl %"v2829", #25;
    %"v2831" : W = Shr %"v2830", #31;
    %"v2832" : W = (Cmp Ne W) %"v2831", #0
    => goto "L2826" };
  ir_blk{ @"L2826" [%"v2833" : W = phi("L2803" => #1, "L2825" => %"v2832")]:
    => br %"v2833" ? "L2835" : "L2834" };
  ir_blk{ @"L2834":
    %"v2837" = %"v10" +p #12;
    %"chk442" : A = (Renew 0 4 Read 1) %"chk0", %"v2837";
    %"v2838" : W = (RawLoad (LdNarrow Uw) 0) %"chk442";
    %"v2839" : W = Shl %"v2838", #27;
    %"v2840" : W = Shr %"v2839", #31;
    %"v2841" : W = (Cmp Ne W) %"v2840", #0
    => goto "L2835" };
  ir_blk{ @"L2835" [%"v2842" : W = phi("L2826" => #1, "L2834" => %"v2841")]:
    => br %"v2842" ? "L2821" : "L2823" };
  ir_blk{ @"L2821":
    %"v2844" : W = Sub %"v1884", #1
    => goto "L2823" };
  ir_blk{ @"L2823" [%"pr.44" : W = phi("L2821" => %"v2844", "L2835" => %"v1884")]:
    %"v2848" : L = Ptoi %"pr.60";
    %"v2849" : L = Ptoi %"pr.45";
    %"v2850" : L = Sub %"v2848", %"v2849";
    %"v2851" : L = (Ext Sw) %"pr.44";
    %"v2852" : L = Sub %"v2851", %"v2850";
    %"v2853" : W = Copy %"v2852";
    %"v2854" = %"v2800" +p #20;
    %"chk443" : A = (Check 0 4 Read 1) %"v2854";
    %"v2855" : W = (RawLoad (LdNarrow Uw) 0) %"chk443";
    %"v2856" : W = Sub %"v2853", %"v2855";
    %"v2861" = %"v10" +p #12;
    %"chk444" : A = (Renew 0 4 Read 1) %"chk0", %"v2861";
    %"v2862" : W = (RawLoad (LdNarrow Uw) 0) %"chk444";
    %"v2863" : W = Shl %"v2862", #26;
    %"v2864" : W = Shr %"v2863", #31;
    %"v2865" : W = (Cmp Eq W) %"v2864", #0
    => br %"v2865" ? "L2866" : "L2867" };
  ir_blk{ @"L2866":
    %"v2869" = %"v10" +p #16;
    %"chk445" : A = (HalfCheck Upper 0 4 Read 1) %"chk0", %"v2869";
    %"v2870" : W = (RawLoad (LdNarrow Sw) 0) %"chk445";
    %"v2871" : W = (Cmp Ne W) %"v2870", #48
    => goto "L2867" };
  ir_blk{ @"L2867" [%"v2873" : W = phi("L2823" => #0, "L2866" => %"v2871")]:
    => br %"v2873" ? "L2857" : "L2859" };
  ir_blk{ @"L2857":
    %"v2876" = %"v10" +p #16;
    %"chk446" : A = (HalfCheck Upper 0 4 Read 1) %"chk0", %"v2876";
    %"v2877" : W = (RawLoad (LdNarrow Sw) 0) %"chk446";
    %"v2878" : W = (Ext Sb) %"v2877";
    %"v2880" : L = (Ext Sw) %"v2856";
    call void $"glibc_printf_fp#__printf_buffer_pad"(P %"v0", W %"v2878", L %"v2880")
    => goto "L2859" };
  ir_blk{ @"L2859":
    %"chk447" : A = (Renew 0 4 Read 1) %"chk1", %"v29";
    %"v2884" : W = (RawLoad (LdNarrow Sw) 0) %"chk447"
    => br %"v2884" ? "L2881" : "L2882" };
  ir_blk{ @"L2881":
    call void $"glibc_printf_fp#__printf_buffer_putc"(P %"v0", W #45)
    => goto "L2883" };
  ir_blk{ @"L2882":
    %"v2890" = %"v10" +p #12;
    %"chk448" : A = (Renew 0 4 Read 1) %"chk0", %"v2890";
    %"v2891" : W = (RawLoad (LdNarrow Uw) 0) %"chk448";
    %"v2892" : W = Shl %"v2891", #25;
    %"v2893" : W = Shr %"v2892", #31
    => br %"v2893" ? "L2886" : "L2887" };
  ir_blk{ @"L2886":
    call void $"glibc_printf_fp#__printf_buffer_putc"(P %"v0", W #43)
    => goto "L2883" };
  ir_blk{ @"L2887":
    %"v2899" = %"v10" +p #12;
    %"v2900" : W = (RawLoad (LdNarrow Uw) 0) %"chk448";
    %"v2901" : W = Shl %"v2900", #27;
    %"v2902" : W = Shr %"v2901", #31
    => br %"v2902" ? "L2895" : "L2883" };
  ir_blk{ @"L2895":
    call void $"glibc_printf_fp#__printf_buffer_putc"(P %"v0", W #32)
    => goto "L2883" };
  ir_blk{ @"L2883":
    %"v2908" = %"v10" +p #12;
    %"chk450" : A = (Renew 0 4 Read 1) %"chk0", %"v2908";
    %"v2909" : W = (RawLoad (LdNarrow Uw) 0) %"chk450";
    %"v2910" : W = Shl %"v2909", #26;
    %"v2911" : W = Shr %"v2910", #31;
    %"v2912" : W = (Cmp Eq W) %"v2911", #0
    => br %"v2912" ? "L2913" : "L2914" };
  ir_blk{ @"L2913":
    %"v2916" = %"v10" +p #16;
    %"chk451" : A = (HalfCheck Upper 0 4 Read 1) %"chk0", %"v2916";
    %"v2917" : W = (RawLoad (LdNarrow Sw) 0) %"chk451";
    %"v2918" : W = (Cmp Eq W) %"v2917", #48
    => goto "L2914" };
  ir_blk{ @"L2914" [%"v2920" : W = phi("L2883" => #0, "L2913" => %"v2918")]:
    => br %"v2920" ? "L2904" : "L2906" };
  ir_blk{ @"L2904":
    %"v2923" : L = (Ext Sw) %"v2856";
    call void $"glibc_printf_fp#__printf_buffer_pad"(P %"v0", W #48, L %"v2923")
    => goto "L2906" };
  ir_blk{ @"L2906":
    %"v2927" = %"v2800" +p #20;
    %"chk452" : A = (Renew 0 4 Read 1) %"chk443", %"v2927";
    %"v2928" : W = (RawLoad (LdNarrow Uw) 0) %"chk452";
    %"v2929" : W = (Cmp Ugt W) %"v2928", #0
    => br %"v2929" ? "L2933" : "L2925" };
  ir_blk{ @"L2933" [%"pr.125" : W = phi("L2942" => %"v2953", "L2906" => #0); %"pr.124" : P = phi("L2942" => %"v2951", "L2906" => %"pr.45")]:
    %"v2939" : W = (Cmp Slt W) %"pr.125", %"pr.77"
    => br %"v2939" ? "L2934" : "L2936" };
  ir_blk{ @"L2934":
    call %"v2943" : W = $"__grouping_iterator_next"(P %"v2800");
    %"v2944" : W = (Ext Ub) %"v2943"
    => br %"v2944" ? "L2940" : "L2942" };
  ir_blk{ @"L2940":
    call void $"glibc_printf_fp#__printf_buffer_putc"(P %"v0", W %"v2804")
    => goto "L2942" };
  ir_blk{ @"L2942":
    %"chk453" : A = (Check 0 1 Read 1) %"pr.124";
    %"v2949" : W = (RawLoad (LdNarrow Sb) 0) %"chk453";
    call void $"glibc_printf_fp#__printf_buffer_putc"(P %"v0", W %"v2949");
    %"v2951" = %"pr.124" +p #1;
    %"v2953" : W = Add %"pr.125", #1
    => goto poll "L2933" };
  ir_blk{ @"L2936":
    %"v2959" : L = Ptoi %"pr.124";
    %"v2960" : L = Sub %"v2848", %"v2959";
    call void $"__printf_buffer_write"(P %"v0", P %"pr.124", L %"v2960")
    => goto "L2926" };
  ir_blk{ @"L2925":
    call void $"__printf_buffer_write"(P %"v0", P %"pr.45", L %"v2850")
    => goto "L2926" };
  ir_blk{ @"L2926":
    %"v2972" = %"v10" +p #12;
    %"chk454" : A = (Renew 0 4 Read 1) %"chk0", %"v2972";
    %"v2973" : W = (RawLoad (LdNarrow Uw) 0) %"chk454";
    %"v2974" : W = Shl %"v2973", #26;
    %"v2975" : W = Shr %"v2974", #31
    => br %"v2975" ? "L2968" : "L2970" };
  ir_blk{ @"L2968":
    %"v2978" = %"v10" +p #16;
    %"chk455" : A = (HalfCheck Upper 0 4 Read 1) %"chk0", %"v2978";
    %"v2979" : W = (RawLoad (LdNarrow Sw) 0) %"chk455";
    %"v2980" : W = (Ext Sb) %"v2979";
    %"v2982" : L = (Ext Sw) %"v2856";
    call void $"glibc_printf_fp#__printf_buffer_pad"(P %"v0", W %"v2980", L %"v2982")
    => goto "L2970" };
  ir_blk{ @"L2970":
    => br %"v2100" ? "L2983" : "L2985" };
  ir_blk{ @"L2983":
    call void $"free"(P %"pr.16")
    => goto "L2985" };
  ir_blk{ @"L2985":
    => ret void }])).
