# The qnode-hosted CLIs must match their Node.js builds byte for byte.
{ pkgs, pkgsFilc }:
pkgs.runCommand "filc-qnode-check" { } ''
  cat > in.bib <<'EOF'
  @article{Smith2020,
    title={A   Title},author = {Smith, J.},
  year=2020}
  @book{a, title="x"}
  @book{a, title="x"}
  EOF
  cp in.bib node.bib
  cp in.bib qjs.bib
  export PRE_COMMIT=1
  ${pkgs.lib.getExe pkgs.bibtex-tidy} --curly --sort --merge -m node.bib
  ${pkgs.lib.getExe pkgsFilc.bibtex-tidy} --curly --sort --merge -m qjs.bib
  cmp node.bib qjs.bib

  printf '+---+\n| A |--->  "x"\n+---+   *\n' > in.txt
  ${pkgs.lib.getExe pkgs.aasvg} < in.txt > node.svg
  ${pkgs.lib.getExe pkgsFilc.aasvg} < in.txt > qjs.svg
  cmp node.svg qjs.svg

  ${pkgsFilc.quickjs}/bin/qjs ${./quickjs-regexp.js}
  touch $out
''
