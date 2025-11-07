# Simple Fil-C cross-compilation overlay
# Adds patches to nixpkgs packages so they work with Fil-C

{ lib }:

final: prev: {
  zlib = prev.zlib.overrideAttrs (old: {
    patches = (old.patches or [ ]) ++ [
      ./ports/patch/zlib-1.3.patch
    ];
  });

  openssl = prev.openssl.overrideAttrs (old: {
    version = "3.3.1";
    src = final.fetchurl {
      url = "https://www.openssl.org/source/openssl-3.3.1.tar.gz";
      hash = "sha256-d3zVlihMiDN1oqehG/XSeG/FQTJV76sgxQ1v/m0CC34=";
    };
    patches = [
      ./ports/patch/openssl-3.3.1.patch
    ];
  });

  libevent = prev.libevent.overrideAttrs (old: {
    version = "2.1.12";
    src = final.fetchurl {
      url = "https://github.com/libevent/libevent/releases/download/release-2.1.12-stable/libevent-2.1.12-stable.tar.gz";
      hash = "sha256-kubeG+nsF2Qo/SNnZ35hzv/C7hyxGQNQN6J9NGsEA7s=";
    };
    patches = [
      ./ports/patch/libevent-2.1.12.patch
    ];
  });

  libutempter = prev.libutempter.override {
    glib = null;
  };

  tmux = prev.tmux.override {
    withSystemd = false;
  };
}
