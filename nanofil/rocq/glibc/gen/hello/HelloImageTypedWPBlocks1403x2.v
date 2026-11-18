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

Definition hello_image_fn___wprintf_buffer'blocks2 : list block :=
  [ir_blk{ @"L1876":
    call void $"__wprintf_buffer_write"(P %"v0", P %"pr.38", L %"pr.107")
    => br %"pr.47" ? "L1885" : "L1131" };
  ir_blk{ @"L1885":
    %"v1890" : W = Copy %"v1868";
    %"v1891" : L = (Ext Sw) %"v1890";
    call void $"glibc_vfwprintf_internal#__wprintf_buffer_pad"(P %"v0", W #32, L %"v1891")
    => goto "L1131" };
  ir_blk{ @"L1775":
    %"v1893" : W = Sub %"pr.67", #1;
    %"v1898" : W = (Cmp Eq W) %"pr.47", #0
    => br %"v1898" ? "L1894" : "L1896" };
  ir_blk{ @"L1894":
    %"v1901" : L = (Ext Sw) %"v1893";
    call void $"glibc_vfwprintf_internal#__wprintf_buffer_pad"(P %"v0", W #32, L %"v1901")
    => goto "L1896" };
  ir_blk{ @"L1896":
    %"v1904" : W = VaArg %"v4";
    call void $"glibc_vfwprintf_internal#__wprintf_buffer_putc"(P %"v0", W %"v1904")
    => br %"pr.47" ? "L1905" : "L1131" };
  ir_blk{ @"L1905":
    %"v1911" : L = (Ext Sw) %"v1893";
    call void $"glibc_vfwprintf_internal#__wprintf_buffer_pad"(P %"v0", W #32, L %"v1911")
    => goto "L1131" };
  ir_blk{ @"L1913":
    %"v1918" : W = And %"v6", #1
    => br %"v1918" ? "L1916" : "L1915" };
  ir_blk{ @"L1915":
    => goto "L1916" };
  ir_blk{ @"L1916" [%"pr.58" : W = phi("L1915" => %"pr.57", "L1913" => #0)]:
    code ((app ir[ %"chk158" : A = (Check 0 4 Write 1) %"v1922";
      store Ww [%"chk158" + 0] <- #0;
      %"v1923" = %"v1922" +p #4;
      %"chk159" : A = (HalfCheck Upper 0 4 Write 1) %"chk158", %"v1923";
      store Ww [%"chk159" + 0] <- #0;
      %"v1924" = %"v1922" +p #8;
      %"chk160" : A = (HalfCheck Upper 0 4 Write 1) %"chk158", %"v1924";
      store Ww [%"chk160" + 0] <- #0;
      %"v1925" = %"v1922" +p #12;
      %"chk161" : A = (HalfCheck Upper 0 4 Write 1) %"chk158", %"v1925";
      store Ww [%"chk161" + 0] <- #0;
      %"v1926" = %"v1922" +p #16;
      %"chk162" : A = (HalfCheck Upper 0 4 Write 1) %"chk158", %"v1926";
      store Ww [%"chk162" + 0] <- #0;
      store Ww [%"chk158" + 0] <- %"pr.82";
      store Ww [%"chk159" + 0] <- %"pr.67";
      store Ww [%"chk160" + 0] <- %"pr.97";
      %"v1934" : W = (RawLoad (LdNarrow Uw) 0) %"chk161";
      %"v1935" : W = And %"v1934", #4294967294;
      %"v1936" : W = And %"pr.58", #1;
      %"v1937" : W = Or %"v1935", %"v1936";
      store Ww [%"chk161" + 0] <- %"v1937";
      %"v1942" : W = (RawLoad (LdNarrow Uw) 0) %"chk161";
      %"v1943" : W = And %"v1942", #4294967293;
      %"v1944" : W = Shl %"pr.60", #1;
      %"v1945" : W = And %"v1944", #2;
      %"v1946" : W = Or %"v1943", %"v1945";
      store Ww [%"chk161" + 0] <- %"v1946";
      %"v1951" : W = (RawLoad (LdNarrow Uw) 0) %"chk161";
      %"v1952" : W = And %"v1951", #4294967291;
      %"v1953" : W = Shl %"pr.62", #2;
      %"v1954" : W = And %"v1953", #4;
      %"v1955" : W = Or %"v1952", %"v1954";
      store Ww [%"chk161" + 0] <- %"v1955";
      %"v1960" : W = (RawLoad (LdNarrow Uw) 0) %"chk161";
      %"v1961" : W = And %"v1960", #4294967287;
      %"v1962" : W = Shl %"pr.42", #3;
      %"v1963" : W = And %"v1962", #8;
      %"v1964" : W = Or %"v1961", %"v1963";
      store Ww [%"chk161" + 0] <- %"v1964";
      %"v1969" : W = (RawLoad (LdNarrow Uw) 0) %"chk161";
      %"v1970" : W = And %"v1969", #4294967279] ir[ %"v1971" : W = Shl %"pr.46", #4;
      %"v1972" : W = And %"v1971", #16;
      %"v1973" : W = Or %"v1970", %"v1972";
      store Ww [%"chk161" + 0] <- %"v1973";
      %"v1978" : W = (RawLoad (LdNarrow Uw) 0) %"chk161";
      %"v1979" : W = And %"v1978", #4294967263;
      %"v1980" : W = Shl %"pr.47", #5;
      %"v1981" : W = And %"v1980", #32;
      %"v1982" : W = Or %"v1979", %"v1981";
      store Ww [%"chk161" + 0] <- %"v1982";
      %"v1987" : W = (RawLoad (LdNarrow Uw) 0) %"chk161";
      %"v1988" : W = And %"v1987", #4294967231;
      %"v1989" : W = Shl %"pr.52", #6;
      %"v1990" : W = And %"v1989", #64;
      %"v1991" : W = Or %"v1988", %"v1990";
      store Ww [%"chk161" + 0] <- %"v1991";
      %"v1996" : W = (RawLoad (LdNarrow Uw) 0) %"chk161";
      %"v1997" : W = And %"v1996", #4294967167;
      %"v1998" : W = Shl %"pr.55", #7;
      %"v1999" : W = And %"v1998", #128;
      %"v2000" : W = Or %"v1997", %"v1999";
      store Ww [%"chk161" + 0] <- %"v2000";
      store Ww [%"chk162" + 0] <- %"pr.92";
      %"v2006" : W = (RawLoad (LdNarrow Uw) 0) %"chk161";
      %"v2007" : W = And %"v2006", #4294967039;
      store Ww [%"chk161" + 0] <- %"v2007";
      %"v2015" : W = (RawLoad (LdNarrow Uw) 0) %"chk161";
      %"v2016" : W = And %"v2015", #4294965247;
      %"v2017" : W = Shl %"pr.88", #11;
      %"v2018" : W = And %"v2017", #2048;
      %"v2019" : W = Or %"v2016", %"v2018";
      store Ww [%"chk161" + 0] <- %"v2019";
      %"v2024" : W = (RawLoad (LdNarrow Uw) 0) %"chk161";
      %"v2025" : W = And %"v2024", #4294966271;
      %"v2028" : W = Or %"v2025", #1024;
      store Ww [%"chk161" + 0] <- %"v2028";
      %"v2032" : W = (RawLoad (LdNarrow Uw) 0) %"chk161";
      %"v2033" : W = And %"v2032", #4294963199;
      store Ww [%"chk161" + 0] <- %"v2033";
      %"v2042" = %"v1922" +p #12;
      %"v2043" : W = (RawLoad (LdNarrow Uw) 0) %"chk161";
      %"v2044" : W = And %"v2043", #4294963199;
      store Ww [%"chk161" + 0] <- %"v2044"]))
    => br %"pr.58" ? "L2050" : "L2051" };
  ir_blk{ @"L2050":
    %"v2055" : Extended = VaArg %"v4";
    %"chk193" : A = (Check 0 10 Write 8) %"v86";
    store Wx [%"chk193" + 0] <- %"v2055"
    => goto "L2041" };
  ir_blk{ @"L2051":
    %"v2057" : Double = VaArg %"v4";
    %"chk194" : A = (Check 0 8 Write 1) %"v86";
    store Wd [%"chk194" + 0] <- %"v2057"
    => goto "L2041" };
  ir_blk{ @"L2041":
    %"chk195" : A = (Check 0 8 Write 8) %"v2058";
    store.ptr [%"chk195" + 0] <- %"v86";
    call void $"glibc_vfwprintf_internal#__printf_fp_spec"(P %"v0", P %"v1922", P %"v2058")
    => goto "L1131" };
  ir_blk{ @"L2060":
    %"v2065" : W = (Cmp Eq W) %"pr.97", #0
    => br %"v2065" ? "L2061" : "L78" };
  ir_blk{ @"L2061":
    %"v2066" : P = Copy $"__libc_errno";
    %"chk196" : A = (Check 0 4 Write 1) %"v2066";
    store Ww [%"chk196" + 0] <- #22;
    call void $"glibc_vfwprintf_internal#__wprintf_buffer_mark_failed"(P %"v0")
    => goto "L508" };
  ir_blk{ @"L1131" [%"pr.12" : W = phi("L1132" => %"pr.16", "L1623" => %"pr.16", "L1832" => %"pr.16", "L1862" => %"pr.16", "L2041" => %"pr.16", "L1539" => %"pr.16", "L1530" => %"pr.16", "L1718" => %"pr.13", "L1725" => %"pr.13", "L1732" => %"pr.13", "L1733" => %"pr.13", "L1792" => %"pr.16", "L1781" => %"pr.16", "L1885" => %"pr.16", "L1876" => %"pr.16", "L1905" => %"pr.16", "L1896" => %"pr.16")]:
    %"v2071" : W = Add %"pr.11", #1;
    %"chk197" : A = (Renew 0 8 Read 8) %"chk3", %"v10";
    %"v2072" : P = (RawLoadPointer 0 load_effects) %"chk197";
    %"v2073" = %"v2072" +p #4;
    %"chk198" : A = (Renew 0 8 Write 8) %"chk3", %"v10";
    store.ptr [%"chk198" + 0] <- %"v2073";
    call %"v2074" : P = $"glibc_vfwprintf_internal#__find_specwc.gnu_inline"(P %"v2073");
    %"chk199" : A = (Renew 0 8 Write 8) %"chk3", %"v10";
    store.ptr [%"chk199" + 0] <- %"v2074";
    %"chk200" : A = (Renew 0 8 Read 8) %"chk3", %"v10";
    %"v2077" : P = (RawLoadPointer 0 load_effects) %"chk200";
    %"v2079" : L = Ptoi %"v2077";
    %"v2080" : L = Ptoi %"v2073";
    %"v2081" : L = Sub %"v2079", %"v2080";
    %"v2082" : L = Div %"v2081", #4;
    call void $"__wprintf_buffer_write"(P %"v0", P %"v2073", L %"v2082");
    %"chk201" : A = (Renew 0 8 Read 8) %"chk3", %"v10";
    %"v2083" : P = (RawLoadPointer 0 load_effects) %"chk201";
    %"chk202" : A = (Check 0 4 Read 1) %"v2083";
    %"v2084" : W = (RawLoad (LdNarrow Uw) 0) %"chk202";
    %"v2085" : W = (Cmp Ne W) %"v2084", #0
    => br %"v2085" ? "L2086" : "L2087" };
  ir_blk{ @"L2086":
    call %"v2089" : W = $"glibc_vfwprintf_internal#__wprintf_buffer_has_failed"(P %"v0");
    %"v2090" : W = (Ext Ub) %"v2089";
    %"v2091" : W = (Cmp Eq W) %"v2090", #0
    => goto "L2087" };
  ir_blk{ @"L2087" [%"v2093" : W = phi("L1131" => #0, "L2086" => %"v2091")]:
    => br %"v2093" ? poll "L80" : "L508" };
  ir_blk{ @"L508":
    => ret void };
  ir_blk{ @"L78" [%"pr.15" : W = phi("L68" => #0, "L515" => %"pr.16", "L574" => %"pr.16", "L664" => %"pr.16", "L2060" => %"pr.16"); %"pr.10" : W = phi("L68" => #0, "L515" => %"pr.11", "L574" => %"pr.11", "L664" => %"pr.11", "L2060" => %"pr.11"); %"pr.8" : P = phi("L68" => %"v23", "L515" => %"pr.5", "L574" => %"pr.5", "L664" => %"pr.5", "L2060" => %"pr.5"); %"pr.3" : W = phi("L68" => #0, "L515" => %"pr.1", "L574" => %"pr.1", "L664" => %"pr.1", "L2060" => %"pr.1")]:
    call void $"glibc_vfwprintf_internal#printf_positional"(P %"v0", P %"v2", W %"pr.15", P %"v4", P %"v15", W %"pr.10", P %"v27", P %"v13", W %"v19", P %"pr.8", W %"pr.3", W %"v6")
    => ret void };
  ir_blk{ @"L144" [%"pr.98" : L = phi("L1099" => %"v1128", "L114" => %"v143", "L157" => %"v186", "L198" => %"v227", "L239" => %"v268", "L280" => %"v309", "L326" => %"v355", "L416" => %"v445", "L457" => %"v486", "L540" => %"v569", "L599" => %"v628", "L705" => %"v734", "L746" => %"v775", "L787" => %"v816", "L828" => %"v857", "L869" => %"v898", "L912" => %"v941", "L955" => %"v984", "L998" => %"v1027"); %"pr.97" : W = phi("L1099" => %"v1096", "L114" => %"v111", "L157" => %"v154", "L198" => %"v195", "L239" => %"v236", "L280" => %"v277", "L326" => %"v323", "L416" => %"v413", "L457" => %"v454", "L540" => %"v537", "L599" => %"v596", "L705" => %"v702", "L746" => %"v743", "L787" => %"v784", "L828" => %"v825", "L869" => %"v866", "L912" => %"v909", "L955" => %"v952", "L998" => %"v995"); %"pr.92" : W = phi("L1099" => %"pr.92", "L114" => #32, "L157" => %"pr.92", "L198" => %"pr.92", "L239" => #32, "L280" => %"pr.92", "L326" => %"pr.93", "L416" => %"pr.92", "L457" => %"pr.92", "L540" => %"pr.94", "L599" => %"pr.92", "L705" => %"pr.92", "L746" => %"pr.92", "L787" => %"pr.92", "L828" => %"pr.92", "L869" => %"pr.92", "L912" => %"pr.92", "L955" => %"pr.92", "L998" => %"pr.92"); %"pr.88" : W = phi("L1099" => %"pr.88", "L114" => #0, "L157" => %"pr.88", "L198" => %"pr.88", "L239" => %"pr.88", "L280" => %"pr.88", "L326" => %"pr.88", "L416" => %"pr.88", "L457" => #1, "L540" => %"pr.88", "L599" => %"pr.88", "L705" => %"pr.88", "L746" => %"pr.88", "L787" => %"pr.88", "L828" => %"pr.88", "L869" => %"pr.88", "L912" => %"pr.88", "L955" => %"pr.88", "L998" => %"pr.88"); %"pr.82" : W = phi("L1099" => %"pr.82", "L114" => #4294967295, "L157" => %"pr.82", "L198" => %"pr.82", "L239" => %"pr.82", "L280" => %"pr.82", "L326" => %"pr.82", "L416" => %"pr.82", "L457" => %"pr.82", "L540" => %"pr.82", "L599" => %"pr.82", "L705" => %"pr.85", "L746" => %"pr.82", "L787" => %"pr.82", "L828" => %"pr.82", "L869" => %"pr.82", "L912" => %"pr.82", "L955" => %"pr.82", "L998" => %"pr.82"); %"pr.67" : W = phi("L1099" => %"pr.67", "L114" => #0, "L157" => %"pr.67", "L198" => %"pr.67", "L239" => %"pr.67", "L280" => %"pr.67", "L326" => %"pr.67", "L416" => %"pr.67", "L457" => %"pr.67", "L540" => %"pr.76", "L599" => %"v571", "L705" => %"pr.67", "L746" => %"pr.67", "L787" => %"pr.67", "L828" => %"pr.67", "L869" => %"pr.67", "L912" => %"pr.67", "L955" => %"pr.67", "L998" => %"pr.67"); %"pr.65" : W = phi("L1099" => %"pr.64", "L114" => #0, "L157" => %"pr.65", "L198" => %"pr.65", "L239" => %"pr.65", "L280" => %"pr.65", "L326" => %"pr.65", "L416" => %"pr.65", "L457" => %"pr.65", "L540" => %"pr.65", "L599" => %"pr.65", "L705" => %"pr.65", "L746" => %"pr.65", "L787" => #1, "L828" => %"pr.65", "L869" => %"pr.65", "L912" => %"pr.65", "L955" => %"pr.65", "L998" => %"pr.65"); %"pr.62" : W = phi("L1099" => %"pr.61", "L114" => #0, "L157" => %"pr.62", "L198" => %"pr.62", "L239" => %"pr.62", "L280" => %"pr.62", "L326" => %"pr.62", "L416" => %"pr.62", "L457" => %"pr.62", "L540" => %"pr.62", "L599" => %"pr.62", "L705" => %"pr.62", "L746" => %"pr.62", "L787" => %"pr.62", "L828" => #1, "L869" => #1, "L912" => #1, "L955" => #1, "L998" => #1); %"pr.60" : W = phi("L1099" => %"pr.59", "L114" => #0, "L157" => %"pr.60", "L198" => %"pr.60", "L239" => %"pr.60", "L280" => %"pr.60", "L326" => %"pr.60", "L416" => %"pr.60", "L457" => %"pr.60", "L540" => %"pr.60", "L599" => %"pr.60", "L705" => %"pr.60", "L746" => #1, "L787" => #0, "L828" => %"pr.60", "L869" => %"pr.60", "L912" => %"pr.60", "L955" => %"pr.60", "L998" => %"pr.60"); %"pr.57" : W = phi("L1099" => %"pr.56", "L114" => #0, "L157" => %"pr.57", "L198" => %"pr.57", "L239" => %"pr.57", "L280" => %"pr.57", "L326" => %"pr.57", "L416" => %"pr.57", "L457" => %"pr.57", "L540" => %"pr.57", "L599" => %"pr.57", "L705" => %"pr.57", "L746" => %"pr.57", "L787" => %"pr.57", "L828" => %"pr.57", "L869" => #1, "L912" => #0, "L955" => #0, "L998" => #0); %"pr.55" : W = phi("L1099" => %"pr.55", "L114" => #0, "L157" => %"pr.55", "L198" => %"pr.55", "L239" => %"pr.55", "L280" => %"pr.55", "L326" => %"pr.55", "L416" => #1, "L457" => %"pr.55", "L540" => %"pr.55", "L599" => %"pr.55", "L705" => %"pr.55", "L746" => %"pr.55", "L787" => %"pr.55", "L828" => %"pr.55", "L869" => %"pr.55", "L912" => %"pr.55", "L955" => %"pr.55", "L998" => %"pr.55"); %"pr.52" : W = phi("L1099" => %"pr.52", "L114" => #0, "L157" => %"pr.52", "L198" => #1, "L239" => %"pr.52", "L280" => %"pr.52", "L326" => %"pr.52", "L416" => %"pr.52", "L457" => %"pr.52", "L540" => %"pr.52", "L599" => %"pr.52", "L705" => %"pr.52", "L746" => %"pr.52", "L787" => %"pr.52", "L828" => %"pr.52", "L869" => %"pr.52", "L912" => %"pr.52", "L955" => %"pr.52", "L998" => %"pr.52"); %"pr.47" : W = phi("L1099" => %"pr.47", "L114" => #0, "L157" => %"pr.47", "L198" => %"pr.47", "L239" => #1, "L280" => %"pr.47", "L326" => %"pr.47", "L416" => %"pr.47", "L457" => %"pr.47", "L540" => %"pr.48", "L599" => %"pr.47", "L705" => %"pr.47", "L746" => %"pr.47", "L787" => %"pr.47", "L828" => %"pr.47", "L869" => %"pr.47", "L912" => %"pr.47", "L955" => %"pr.47", "L998" => %"pr.47"); %"pr.46" : W = phi("L1099" => %"pr.46", "L114" => #0, "L157" => #1, "L198" => %"pr.46", "L239" => %"pr.46", "L280" => %"pr.46", "L326" => %"pr.46", "L416" => %"pr.46", "L457" => %"pr.46", "L540" => %"pr.46", "L599" => %"pr.46", "L705" => %"pr.46", "L746" => %"pr.46", "L787" => %"pr.46", "L828" => %"pr.46", "L869" => %"pr.46", "L912" => %"pr.46", "L955" => %"pr.46", "L998" => %"pr.46"); %"pr.42" : W = phi("L1099" => %"pr.42", "L114" => #0, "L157" => %"pr.42", "L198" => %"pr.42", "L239" => %"pr.42", "L280" => #1, "L326" => %"pr.42", "L416" => %"pr.42", "L457" => %"pr.42", "L540" => %"pr.42", "L599" => %"pr.42", "L705" => %"pr.42", "L746" => %"pr.42", "L787" => %"pr.42", "L828" => %"pr.42", "L869" => %"pr.42", "L912" => %"pr.42", "L955" => %"pr.42", "L998" => %"pr.42"); %"pr.5" : P = phi("L1099" => %"pr.5", "L114" => %"pr.9", "L157" => %"pr.5", "L198" => %"pr.5", "L239" => %"pr.5", "L280" => %"pr.5", "L326" => %"pr.5", "L416" => %"pr.6", "L457" => %"pr.5", "L540" => %"pr.5", "L599" => %"pr.5", "L705" => %"pr.5", "L746" => %"pr.5", "L787" => %"pr.5", "L828" => %"pr.5", "L869" => %"pr.5", "L912" => %"pr.5", "L955" => %"pr.5", "L998" => %"pr.5"); %"pr.1" : W = phi("L1099" => %"pr.1", "L114" => %"pr.4", "L157" => %"pr.1", "L198" => %"pr.1", "L239" => %"pr.1", "L280" => %"pr.1", "L326" => %"pr.1", "L416" => %"pr.2", "L457" => %"pr.1", "L540" => %"pr.1", "L599" => %"pr.1", "L705" => %"pr.1", "L746" => %"pr.1", "L787" => %"pr.1", "L828" => %"pr.1", "L869" => %"pr.1", "L912" => %"pr.1", "L955" => %"pr.1", "L998" => %"pr.1")]:
    %"v2106" : W = (Cmp Ult L) %"pr.98", #17
    => br %"v2106" ? "L2107" : "L2108" };
  ir_blk{ @"L2107":
    %"v2109" : W = (Cmp Ult L) %"pr.98", #9
    => br %"v2109" ? "L2110" : "L2111" };
  ir_blk{ @"L2110":
    %"v2112" : W = (Cmp Ult L) %"pr.98", #5
    => br %"v2112" ? "L2113" : "L2114" };
  ir_blk{ @"L2113":
    %"v2115" : W = (Cmp Eq L) %"pr.98", #1
    => br %"v2115" ? poll "L2060" : "L2116" };
  ir_blk{ @"L2116":
    %"v2117" : W = (Cmp Eq L) %"pr.98", #2
    => br %"v2117" ? poll "L147" : "L2118" };
  ir_blk{ @"L2118":
    %"v2119" : W = (Cmp Eq L) %"pr.98", #3
    => br %"v2119" ? poll "L188" : "L2120" };
  ir_blk{ @"L2120":
    %"v2121" : W = (Cmp Eq L) %"pr.98", #4
    => br %"v2121" ? poll "L229" : "L2105" };
  ir_blk{ @"L2114":
    %"v2123" : W = (Cmp Eq L) %"pr.98", #5
    => br %"v2123" ? poll "L270" : "L2124" };
  ir_blk{ @"L2124":
    %"v2125" : W = (Cmp Eq L) %"pr.98", #6
    => br %"v2125" ? poll "L310" : "L2126" };
  ir_blk{ @"L2126":
    %"v2127" : W = (Cmp Eq L) %"pr.98", #7
    => br %"v2127" ? poll "L356" : "L2128" };
  ir_blk{ @"L2128":
    %"v2129" : W = (Cmp Eq L) %"pr.98", #8
    => br %"v2129" ? poll "L487" : "L2105" };
  ir_blk{ @"L2111":
    %"v2131" : W = (Cmp Ult L) %"pr.98", #13
    => br %"v2131" ? "L2132" : "L2133" };
  ir_blk{ @"L2132":
    %"v2134" : W = (Cmp Eq L) %"pr.98", #9
    => br %"v2134" ? poll "L570" : "L2135" };
  ir_blk{ @"L2135":
    %"v2136" : W = (Cmp Eq L) %"pr.98", #10
    => br %"v2136" ? poll "L629" : "L2137" };
  ir_blk{ @"L2137":
    %"v2138" : W = (Cmp Eq L) %"pr.98", #11
    => br %"v2138" ? poll "L736" : "L2139" };
  ir_blk{ @"L2139":
    %"v2140" : W = (Cmp Eq L) %"pr.98", #12
    => br %"v2140" ? poll "L818" : "L2105" };
  ir_blk{ @"L2133":
    %"v2142" : W = (Cmp Eq L) %"pr.98", #13
    => br %"v2142" ? poll "L859" : "L2143" };
  ir_blk{ @"L2143":
    %"v2144" : W = (Cmp Eq L) %"pr.98", #14
    => br %"v2144" ? poll "L902" : "L2145" };
  ir_blk{ @"L2145":
    %"v2146" : W = (Cmp Eq L) %"pr.98", #15
    => br %"v2146" ? poll "L1132" : "L2147" };
  ir_blk{ @"L2147":
    %"v2148" : W = (Cmp Eq L) %"pr.98", #16
    => br %"v2148" ? poll "L1136" : "L2105" };
  ir_blk{ @"L2108":
    %"v2150" : W = (Cmp Ult L) %"pr.98", #25
    => br %"v2150" ? "L2151" : "L2152" };
  ir_blk{ @"L2151":
    %"v2153" : W = (Cmp Ult L) %"pr.98", #21
    => br %"v2153" ? "L2154" : "L2155" };
  ir_blk{ @"L2154":
    %"v2156" : W = (Cmp Eq L) %"pr.98", #17
    => br %"v2156" ? poll "L1192" : "L2157" };
  ir_blk{ @"L2157":
    %"v2158" : W = (Cmp Eq L) %"pr.98", #18
    => br %"v2158" ? poll "L1192" : "L2159" };
  ir_blk{ @"L2159":
    %"v2160" : W = (Cmp Eq L) %"pr.98", #19
    => br %"v2160" ? poll "L1192" : "L2161" };
  ir_blk{ @"L2161":
    %"v2162" : W = (Cmp Eq L) %"pr.98", #20
    => br %"v2162" ? poll "L1913" : "L2105" };
  ir_blk{ @"L2155":
    %"v2164" : W = (Cmp Eq L) %"pr.98", #21
    => br %"v2164" ? poll "L1770" : "L2165" };
  ir_blk{ @"L2165":
    %"v2166" : W = (Cmp Eq L) %"pr.98", #22
    => br %"v2166" ? poll "L1799" : "L2167" };
  ir_blk{ @"L2167":
    %"v2168" : W = (Cmp Eq L) %"pr.98", #23
    => br %"v2168" ? poll "L1648" : "L2169" };
  ir_blk{ @"L2169":
    %"v2170" : W = (Cmp Eq L) %"pr.98", #24
    => br %"v2170" ? poll "L1670" : "L2105" };
  ir_blk{ @"L2152":
    %"v2172" : W = (Cmp Ult L) %"pr.98", #29
    => br %"v2172" ? "L2173" : "L2174" };
  ir_blk{ @"L2173":
    %"v2175" : W = (Cmp Eq L) %"pr.98", #25
    => br %"v2175" ? poll "L1742" : "L2176" };
  ir_blk{ @"L2176":
    %"v2177" : W = (Cmp Eq L) %"pr.98", #26
    => br %"v2177" ? poll "L1775" : "L2178" };
  ir_blk{ @"L2178":
    %"v2179" : W = (Cmp Eq L) %"pr.98", #27
    => br %"v2179" ? poll "L1913" : "L2180" };
  ir_blk{ @"L2180":
    %"v2181" : W = (Cmp Eq L) %"pr.98", #28
    => br %"v2181" ? poll "L945" : "L2105" };
  ir_blk{ @"L2174":
    %"v2183" : W = (Cmp Ult L) %"pr.98", #31
    => br %"v2183" ? "L2184" : "L2185" };
  ir_blk{ @"L2184":
    %"v2186" : W = (Cmp Eq L) %"pr.98", #29
    => br %"v2186" ? poll "L988" : "L2187" };
  ir_blk{ @"L2187":
    %"v2188" : W = (Cmp Eq L) %"pr.98", #30
    => br %"v2188" ? poll "L447" : "L2105" };
  ir_blk{ @"L2185":
    %"v2190" : W = (Cmp Eq L) %"pr.98", #31
    => br %"v2190" ? poll "L1192" : "L2191" };
  ir_blk{ @"L2191":
    %"v2192" : W = (Cmp Eq L) %"pr.98", #32
    => br %"v2192" ? poll "L1028" : "L2193" };
  ir_blk{ @"L2193":
    %"v2194" : W = (Cmp Eq L) %"pr.98", #33
    => br %"v2194" ? poll "L777" : "L2105" };
  ir_blk{ @"L2105":
    => unreachable }].
