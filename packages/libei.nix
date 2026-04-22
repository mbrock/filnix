{
  lib,
  stdenv,
  otpSrc,
  otpVersion,
  openssl,
  zlib,
}:

stdenv.mkDerivation {
  pname = "libei";
  version = otpVersion;

  src = otpSrc;
  sourceRoot = "source/lib/erl_interface";

  strictDeps = true;
  enableParallelBuilding = true;

  buildInputs = [
    openssl
    zlib
  ];

  postUnpack = ''
    chmod -R u+w "$NIX_BUILD_TOP/source"
  '';

  configurePhase = ''
    runHook preConfigure

    export ERL_TOP="$NIX_BUILD_TOP/source"
    export OTP_HOST="$("$ERL_TOP/make/autoconf/config.guess")"

    # The standalone erl_interface configure does not generate the OTP
    # verbosity include that its generated Makefile expects.
    substitute "$ERL_TOP/make/output.mk.in" "$ERL_TOP/make/output.mk" \
      --replace-fail "@DEFAULT_VERBOSITY@" "0"

    ./configure \
      --build="$OTP_HOST" \
      --host="$OTP_HOST" \
      --enable-ei-dynamic-lib

    runHook postConfigure
  '';

  buildPhase = ''
    runHook preBuild
    make -C src -f "$OTP_HOST/Makefile" ERL_TOP="$ERL_TOP" opt
    runHook postBuild
  '';

  installPhase = ''
    runHook preInstall

    install -Dm644 include/*.h -t "$out/include"

    install -Dm644 "obj/$OTP_HOST/libei.a" "$out/lib/libei.a"
    install -Dm644 "obj/$OTP_HOST/libei_st.a" "$out/lib/libei_st.a"

    install -Dm755 "lib/$OTP_HOST/libei.so" "$out/lib/libei.so"
    install -Dm755 "lib/$OTP_HOST/libei_st.so" "$out/lib/libei_st.so"

    install -Dm755 "bin/$OTP_HOST/erl_call" "$out/bin/erl_call"

    runHook postInstall
  '';

  meta = with lib; {
    description = "Memory-safe Erlang ei/erl_interface C library built with Fil-C";
    homepage = "https://www.erlang.org/";
    license = licenses.asl20;
    mainProgram = "erl_call";
    platforms = [ "x86_64-linux" ];
  };
}
