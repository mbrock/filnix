{
  lib,
  stdenv,
  erlang ? null,
  otpSrc ? erlang.src,
  otpVersion ? erlang.version,
  openssl,
  zlib,
}:

let
  supportsDynamicLib = lib.versionAtLeast otpVersion "27";
in
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
    configureFlags=(
      --build="$OTP_HOST"
      --host="$OTP_HOST"
    )

    ${lib.optionalString supportsDynamicLib ''
      configureFlags+=(--enable-ei-dynamic-lib)
    ''}

    # The standalone erl_interface configure does not generate the OTP
    # verbosity include that its generated Makefile expects.
    substitute "$ERL_TOP/make/output.mk.in" "$ERL_TOP/make/output.mk" \
      --replace-fail "@DEFAULT_VERBOSITY@" "0"

    ./configure "''${configureFlags[@]}"

    runHook postConfigure
  '';

  buildPhase = ''
    runHook preBuild
    # Force this empty so GNU ld never interprets OTP's "-Wl,-R" runtime-path
    # setting as "--just-symbols=<first-object>" when building shared libei.
    # Older OTP releases that do not build shared libei simply ignore it.
    make -C src -f "$OTP_HOST/Makefile" \
      ERL_TOP="$ERL_TOP" \
      LIB_LD_FLAG_RUNTIME_LIBRARY_PATH= \
      opt
    runHook postBuild
  '';

  installPhase = ''
    runHook preInstall

    install -Dm644 include/*.h -t "$out/include"

    install -Dm644 "obj/$OTP_HOST/libei.a" "$out/lib/libei.a"
    install -Dm644 "obj/$OTP_HOST/libei_st.a" "$out/lib/libei_st.a"

    if [ -f "lib/$OTP_HOST/libei.so" ]; then
      install -Dm755 "lib/$OTP_HOST/libei.so" "$out/lib/libei.so"
      install -Dm755 "lib/$OTP_HOST/libei_st.so" "$out/lib/libei_st.so"
    fi

    install -Dm755 "bin/$OTP_HOST/erl_call" "$out/bin/erl_call"

    runHook postInstall
  '';

  meta = with lib; {
    description = "Erlang ei/erl_interface C library";
    homepage = "https://www.erlang.org/";
    license = licenses.asl20;
    mainProgram = "erl_call";
    platforms = [ "x86_64-linux" ];
  };
}
