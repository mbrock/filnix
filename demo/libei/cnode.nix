{
  lib,
  stdenv,
  libei,
}:

stdenv.mkDerivation {
  pname = "libei-ping-cnode";
  version = libei.version;

  src = ./.;

  strictDeps = true;
  dontConfigure = true;

  buildInputs = [ libei ];

  buildPhase = ''
    runHook preBuild

    $CC \
      -O2 \
      -Wall \
      -Wextra \
      -I${libei}/include \
      ping_cnode.c \
      -L${libei}/lib \
      -Wl,-rpath,${libei}/lib \
      -lei \
      -o libei-ping-cnode

    runHook postBuild
  '';

  installPhase = ''
    runHook preInstall
    install -Dm755 libei-ping-cnode "$out/bin/libei-ping-cnode"
    runHook postInstall
  '';

  meta = with lib; {
    description = "Tiny ei cnode used by the libei ping demo";
    homepage = "https://www.erlang.org/";
    license = licenses.asl20;
    mainProgram = "libei-ping-cnode";
    platforms = [ "x86_64-linux" ];
  };
}
