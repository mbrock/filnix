# Differential verification of the StealMyBitcoin exploit against the two
# PHP 8.4.25 builds filnix pins: Nixpkgs' unstripped PHP 8.4.25, on which
# the adapted PoC must succeed end to end (heap leak, code leak, forged
# HashTable, zif_system command execution), and pkgsFilc.php84_25, the same
# release under Fil-C, on which every run must die at the first corrupted
# session-id read with a Fil-C panic before a byte leaks (docs/php.md).
{
  pkgs,
  native,
  filc,
}:
let
  # The PoC's address constants are calibrated for these exact builds. A pin
  # that moves off 8.4.25 stops being the vulnerable release this test is
  # about, so say that at evaluation time instead of failing mysteriously.
  pin =
    name: php:
    if php.version != "8.4.25" then
      throw "php-stealmybitcoin: the ${name} PHP is ${php.version}, not the vulnerable 8.4.25 this PoC is calibrated for"
    else
      php;
  nativePhp = pin "native" native;
  filcPhp = pin "Fil-C" filc;
  assets = pkgs.runCommand "php-stealmybitcoin-assets" { } ''
    mkdir -p $out/public $out/bin
    cp ${./php-stealmybitcoin/public/php-version.php} $out/public/php-version.php
    cp ${./php-stealmybitcoin/bin/print-flag} $out/bin/print-flag
    chmod +x $out/bin/print-flag
  '';
in
pkgs.runCommand "filc-php-stealmybitcoin-check"
  {
    # The PoC's proof command resolves print-flag with `which`, so the sandbox
    # PATH the php server inherits needs it.
    nativeBuildInputs = [
      pkgs.python3
      pkgs.which
    ];
    passthru = { inherit native filc; };
  }
  ''
    mkdir -p $out
    python3 ${./php-stealmybitcoin/verify.py} \
      --native ${nativePhp}/bin/php --native-ini ${nativePhp}/lib \
      --filc ${filcPhp}/bin/php --filc-ini ${filcPhp}/lib \
      --nginx ${pkgs.nginx}/bin/nginx \
      --poc ${./php-stealmybitcoin/stealmybitcoin_poc_8425.py} \
      --assets ${assets} \
      --lab "$(mktemp -d)" \
      --out "$out/evidence"
  ''
