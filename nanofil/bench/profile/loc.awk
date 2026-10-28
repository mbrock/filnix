# Explicit line info for a .s of any length: valgrind keeps 20 bits of a
# line number, so line N is line N mod 2^20 of file "BASE+K", K = N >> 20.
BEGIN { M = 1048576 }
{
  k = int(NR / M)
  if (!(k in seen)) { seen[k] = 1; printf "\t.file %d \"%s%s\"\n", k + 1, base, (k ? "+" k : "") }
  if ($0 ~ /^\t[a-z]/) printf "\t.loc %d %d\n", k + 1, NR % M
  print
}
