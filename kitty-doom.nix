{ stdenv, lib, curl, makeWrapper, fetchgit, fetchurl }:

stdenv.mkDerivation {
  pname = "kitty-doom";
  version = "git";
  
  src = fetchgit {
    url = "https://github.com/mbrock/kitty-doom";
    rev = "ca6c5e40156617489712746bbb594e66293a0aa1";
    hash = "sha256-2DRLohKapV0TiF0ysxITv8yaIprLbV4BU/f6o6IwX40=";
  };

  nativeBuildInputs = [ curl makeWrapper ];

  preBuild = 
    let
      doom1-wad = fetchurl {
        url = "https://distro.ibiblio.org/slitaz/sources/packages/d/doom1.wad";
        hash = "sha256-0wf7r8kaalpn2qc74ng8flqg6fwwwbrviq0mwhkxjrqya2z46z8x";
      };
      puredoom-h = fetchurl {
        url = "https://raw.githubusercontent.com/Daivuk/PureDOOM/master/PureDOOM.h";
        hash = "sha256-0rypvk8m90qvir13jiwxw7jklszawsvz3g7h2g5if4361mqghbbg";
      };
    in ''
    cp ${doom1-wad} DOOM1.WAD
    cp ${puredoom-h} src/PureDOOM.h
    chmod +w src/PureDOOM.h
    
    # Fix Carmack's 1993 allocator to use 8-byte alignment instead of 4-byte
    substituteInPlace src/PureDOOM.h \
      --replace-fail '(size + 3) & ~3' '(size + 7) & ~7'
  '';

  installPhase = ''
    mkdir -p $out/bin $out/share/kitty-doom
    cp build/kitty-doom $out/share/kitty-doom/
    cp DOOM1.WAD $out/share/kitty-doom/
    ln -s DOOM1.WAD $out/share/kitty-doom/doom1.wad
    
    makeWrapper $out/share/kitty-doom/kitty-doom $out/bin/kitty-doom \
      --set DOOMWADDIR $out/share/kitty-doom
  '';

  meta = with lib; {
    homepage = "https://github.com/jserv/kitty-doom";
    description = "Play DOOM in modern terminals with Kitty Graphics Protocol";
  };
}
