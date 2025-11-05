{
  base,
  filc2,
  libmojo,
  filc-libcxx ? null,
}:

rec {
  # Third compiler stage uses memory-safe glibc (libmojo)
  # We keep this as a simple wrapper since it just adds libmojo on top of filc2
  filc3 =
    base.runCommand "filc3"
      {
        nativeBuildInputs = [ base.makeWrapper ];
      }
      ''
        mkdir -p $out/bin
        makeWrapper ${filc2}/bin/clang $out/bin/clang \
          --add-flags "-isystem ${libmojo}/include" \
          --add-flags "-L${libmojo}/lib"
        ln -s clang $out/bin/clang++
      '';

  # C++ variant with libcxx support (only if libcxx is available)
  filc3xx =
    if filc-libcxx != null then
      base.runCommand "filc3xx"
        {
          nativeBuildInputs = [ base.makeWrapper ];
        }
        ''
          mkdir -p $out/bin
          makeWrapper ${filc2}/bin/clang $out/bin/clang \
            --add-flags "-isystem ${libmojo}/include" \
            --add-flags "-L${libmojo}/lib"
          makeWrapper ${filc2}/bin/clang++ $out/bin/clang++ \
            --add-flags "-nostdinc++" \
            --add-flags "-I ${filc-libcxx}/include/c++" \
            --add-flags "-isystem ${libmojo}/include" \
            --add-flags "-L${filc-libcxx}/lib" \
            --add-flags "-L${libmojo}/lib"
        ''
    else
      null;

  filc3xx-tranquil =
    if filc-libcxx != null then
      base.runCommand "filc3xx"
        {
          nativeBuildInputs = [ base.makeWrapper ];
        }
        ''
          mkdir -p $out/bin
          makeWrapper ${filc2}/bin/clang $out/bin/clang \
            --add-flags "-isystem ${libmojo}/include" \
            --add-flags "-L${libmojo}/lib"
          makeWrapper ${filc2}/bin/clang++ $out/bin/clang++ \
            --add-flags "-nostdinc++" \
            --add-flags "-isystem ${filc-libcxx}/include/c++" \
            --add-flags "-isystem ${libmojo}/include" \
            --add-flags "-L${filc-libcxx}/lib" \
            --add-flags "-L${libmojo}/lib"
        ''
    else
      null;
}
