{ pkgs, pkgsFilc }:
let
  programs = pkgs.lib.genAttrs [
    "openssh"
    "diffutils"
    "gnugrep"
    "gnused"
    "gnum4"
    "xz"
  ] (name: pkgs.lib.getBin pkgsFilc.${name});
in
pkgsFilc.stdenv.mkDerivation {
  name = "filc-port-version-refresh-check";
  dontUnpack = true;
  nativeBuildInputs = [ pkgs.pkg-config ];
  buildInputs = with pkgsFilc; [
    zlib
    libevent
    libuv
    libxcrypt
    pcre2
    krb5
  ];
  buildPhase = ''
    $CC -O2 ${./port-version-refresh.c} \
      $(pkg-config --cflags --libs zlib libevent libuv libcrypt libpcre2-8 krb5) \
      -o library-check
    ./library-check

    export HOME="$TMPDIR/home"
    mkdir -p "$HOME"
    sshbin=${programs.openssh}/bin
    "$sshbin/ssh" -V 2>&1 | grep -F 'OpenSSH_${pkgsFilc.openssh.version},'
    "$sshbin/sshd" -V 2>&1 | grep -F 'OpenSSH_${pkgsFilc.openssh.version},'
    for algorithm in ed25519 rsa ecdsa; do
      "$sshbin/ssh-keygen" -q -t "$algorithm" -N "" -f "key-$algorithm"
      "$sshbin/ssh-keygen" -l -f "key-$algorithm.pub"
      printf 'Filnix signing regression\n' > message
      "$sshbin/ssh-keygen" -Y sign -f "key-$algorithm" -n filnix message
      printf 'tester %s\n' "$(cat "key-$algorithm.pub")" > allowed-signers
      "$sshbin/ssh-keygen" -Y verify -f allowed-signers -I tester \
        -n filnix -s message.sig < message
      rm message.sig
    done

    printf 'alpha\nbeta\n' > left
    printf 'alpha\ngamma\n' > right
    status=0
    ${programs.diffutils}/bin/diff -u left right > delta || status=$?
    test "$status" -eq 1
    grep -qx '+gamma' delta
    ${programs.diffutils}/bin/cmp left left
    test "$(${programs.gnugrep}/bin/grep -P '^b.ta$' left)" = beta
    test "$(${programs.gnused}/bin/sed 's/beta/gamma/' left)" = "$(cat right)"
    test "$(printf 'eval(6*7)\n' | ${programs.gnum4}/bin/m4)" = 42
    ${programs.xz}/bin/xz -c left > left.xz
    ${programs.xz}/bin/xz -dc left.xz > restored
    ${programs.diffutils}/bin/cmp left restored
    echo 'OpenSSH signing, text utilities and XZ roundtrip passed'
  '';
  installPhase = "touch $out";
}
