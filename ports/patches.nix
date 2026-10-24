# Historical import inventory; not consumed by the active overlay.
# Refreshed imports at Fil-C v0.687; older entries remain where that tree
# has no replacement patch. See docs/filc-0687-port-import.md for gaps.
# Actual versions live in ports.nix and ports/*.nix. Use
# python3 scripts/audit-port-versions.py to inspect evaluated declarations.
{
  attr = {
    version = "2.6.0";
    patches = [ ];
  };
  bash = {
    version = "5.3";
    patches = [ ./patch/bash-5.3.patch ];
  };
  binutils = {
    version = "2.47";
    patches = [ ./patch/binutils-2.47.patch ];
  };
  bison = {
    version = "3.8.2";
    patches = [ ./patch/bison-3.8.2.patch ];
  };
  bzip3 = {
    version = "1.5.1";
    patches = [ ./patch/bzip3.patch ];
  };
  cairo = {
    version = "1.18.0";
    patches = [ ./patch/cairo-1.18.0.patch ];
  };
  cmake = {
    version = "3.30.2";
    patches = [ ./patch/cmake-3.30.2.patch ];
  };
  dash = {
    version = "0.5.13.5";
    patches = [ ./patch/dash-0.5.13.5.patch ];
  };
  dhcpcd = {
    version = "10.0.8";
    patches = [ ./patch/dhcpcd-10.0.8.patch ];
  };
  diffutils = {
    version = "3.10";
    patches = [ ./patch/diffutils-3.10.patch ];
  };
  e2fsprogs = {
    version = "1.47.1";
    patches = [ ./patch/e2fsprogs-1.47.1.patch ];
  };
  elfutils = {
    version = "0.191";
    patches = [ ./patch/elfutils-0.191.patch ];
  };
  emacs = {
    version = "30.1";
    patches = [ ./patch/emacs-30.1.patch ];
  };
  expat = {
    version = "2.7.1";
    patches = [ ./patch/expat-2.7.1.patch ];
  };
  gettext = {
    version = "0.22.5";
    patches = [ ./patch/gettext-0.22.5.patch ];
  };
  git = {
    version = "2.56.0";
    patches = [ ./patch/git-2.56.0.patch ];
  };
  glib = {
    version = "2.80.4";
    patches = [ ./patch/glib-2.80.4.patch ];
  };
  grep = {
    version = "3.11";
    patches = [ ./patch/grep-3.11.patch ];
  };
  gstreamer = {
    version = "1.24.7";
    patches = [ ./patch/gstreamer-1.24.7.patch ];
  };
  icu = {
    version = "79.1";
    patches = [ ./patch/icu.patch ];
  };
  jpeg = {
    version = "6b";
    patches = [ ./patch/jpeg-6b.patch ];
  };
  kbd = {
    version = "2.6.4";
    patches = [ ./patch/kbd-2.6.4.patch ];
  };
  keyutils = {
    version = "1.6.3";
    patches = [ ./patch/keyutils-1.6.3.patch ];
  };
  krb5 = {
    version = "1.21.3";
    patches = [ ./patch/krb5-1.21.3.patch ];
  };
  lfs-bootscripts = {
    version = "20240825";
    patches = [ ./patch/lfs-bootscripts-20240825.patch ];
  };
  libarchive = {
    version = "3.7.4";
    patches = [ ./patch/libarchive-3.7.4.patch ];
  };
  libdrm = {
    version = "2.4.122";
    patches = [ ./patch/libdrm-2.4.122.patch ];
  };
  libedit = {
    version = "20240808-3.1";
    patches = [ ./patch/libedit-20240808-3.1.patch ];
  };
  libevdev = {
    version = "1.11.0";
    patches = [ ./patch/libevdev-1.11.0.patch ];
  };
  libevent = {
    version = "2.1.12";
    patches = [ ./patch/libevent-2.1.12.patch ];
  };
  libffi = {
    version = "3.8.0";
    patches = [ ./patch/libffi-3.8.0.patch ];
  };
  libinput = {
    version = "1.29.1";
    patches = [ ./patch/libinput-1.29.1.patch ];
  };
  libpng = {
    version = "1.6.43";
    patches = [ ./patch/libpng-1.6.43.patch ];
  };
  libuev = {
    version = "2.4.1";
    patches = [ ./patch/libuev-2.4.1.patch ];
  };
  libuv = {
    version = "1.53.0";
    patches = [ ./patch/libuv-1.53.0.patch ];
  };
  libxcrypt = {
    version = "4.4.36";
    patches = [ ./patch/libxcrypt-4.4.36.patch ];
  };
  libxkbcommon = {
    version = "1.11.0";
    patches = [ ./patch/libxkbcommon-xkbcommon-1.11.0.patch ];
  };
  libxml2 = {
    version = "2.14.4";
    patches = [ ./patch/libxml2-2.14.4.patch ];
  };
  linux = {
    version = "6.10.5";
    patches = [ ./patch/linux-6.10.5.patch ];
  };
  linux-pam = {
    version = "1.7.3";
    patches = [ ./patch/Linux-PAM-1.7.3.patch ];
  };
  lua = {
    version = "5.4.7";
    patches = [ ./patch/lua-5.4.7.patch ];
  };
  m4 = {
    version = "1.4.19";
    patches = [ ./patch/m4-1.4.19.patch ];
  };
  make = {
    version = "4.4.1";
    patches = [ ./patch/make-4.4.1.patch ];
  };
  man-db = {
    version = "2.12.1";
    patches = [ ./patch/man-db-2.12.1.patch ];
  };
  openssh = {
    version = "10.6p1";
    patches = [ ./patch/openssh-10.6p1.patch ];
  };
  openssl = {
    version = "3.6.5";
    patches = [ ./patch/openssl-3.6.5.patch ];
  };
  p11-kit = {
    version = "0.25.5";
    patches = [ ./patch/p11-kit-0.25.5.patch ];
  };
  pcre2 = {
    version = "10.49";
    patches = [ ./patch/pcre2-10.49.patch ];
  };
  perl = {
    version = "5.40.0";
    patches = [ ./patch/perl-5.40.0.patch ];
  };
  procps-ng = {
    version = "4.0.4";
    patches = [ ./patch/procps-ng-4.0.4.patch ];
  };
  python = {
    version = "3.12.5";
    patches = [ ./patch/Python-3.12.5.patch ];
  };
  quickjs = {
    version = "2024-02-14";
    patches = [ ./patch/quickjs.patch ];
  };
  seatd = {
    version = "0.9.1";
    patches = [ ./patch/seatd-0.9.1.patch ];
  };
  sed = {
    version = "4.9";
    patches = [ ./patch/sed-4.9.patch ];
  };
  sqlite = {
    version = "3.46.0";
    patches = [ ./patch/sqlite.patch ];
  };
  systemd = {
    version = "256.4";
    patches = [ ./patch/systemd-256.4.patch ];
  };
  tar = {
    version = "1.35";
    patches = [ ./patch/tar-1.35.patch ];
  };
  tcl = {
    version = "8.6.15";
    patches = [ ];
  };
  texinfo = {
    version = "7.1";
    patches = [ ./patch/texinfo-7.1.patch ];
  };
  tmux = {
    version = "3.5a";
    patches = [ ./patch/tmux-3.5a.patch ];
  };
  toybox = {
    version = "8.12";
    patches = [ ./patch/toybox-8.12.patch ];
  };
  vim = {
    version = "9.1.0660";
    patches = [ ./patch/vim-9.1.0660.patch ];
  };
  wayland = {
    version = "1.24.0";
    patches = [ ./patch/wayland-1.24.0.patch ];
  };
  weston = {
    version = "12.0.5";
    patches = [ ./patch/weston-12.0.5.patch ];
  };
  xml-parser = {
    version = "2.47";
    patches = [ ./patch/XML-Parser-2.47.patch ];
  };
  xz = {
    version = "5.8.4";
    patches = [ ./patch/xz-5.8.4.patch ];
  };
  zlib = {
    version = "1.3.2";
    patches = [ ./patch/zlib-1.3.2.patch ];
  };
  zsh = {
    version = "5.9.2";
    patches = [ ./patch/zsh-5.9.2.patch ];
  };
  zstd = {
    version = "1.5.7";
    patches = [ ./patch/zstd-1.5.7.patch ];
  };

  # Additional patches imported from the 0.687 descriptors. These are
  # available inputs, not a declaration that Filnix builds these versions.
  accountsservice = {
    version = "23.13.9";
    patches = [ ./patch/accountsservice-23.13.9.patch ];
  };
  appstream = {
    version = "1.0.3";
    patches = [ ./patch/appstream-1.0.3.patch ];
  };
  colord = {
    version = "1.4.7";
    patches = [ ./patch/colord-1.4.7.patch ];
  };
  coreutils = {
    version = "9.12";
    patches = [ ./patch/coreutils-9.12.patch ];
  };
  curl = {
    version = "8.23.0";
    patches = [ ./patch/curl-8.23.0.patch ];
  };
  dbus = {
    version = "1.16.2";
    patches = [ ./patch/dbus-1.16.2.patch ];
  };
  dconf = {
    version = "0.40.0";
    patches = [ ./patch/dconf-0.40.0.patch ];
  };
  elogind = {
    version = "255.27";
    patches = [ ./patch/elogind-255.27.patch ];
  };
  mozjs = {
    version = "115.10.0";
    patches = [ ./patch/firefox-115.10.0.patch ];
  };
  gcr = {
    version = "4.3.0";
    patches = [ ./patch/gcr-4.3.0.patch ];
  };
  geocode-glib = {
    version = "3.26.4";
    patches = [ ./patch/geocode-glib-3.26.4.patch ];
  };
  gjs = {
    version = "1.80.2";
    patches = [ ./patch/gjs-1.80.2.patch ];
  };
  gnome-desktop = {
    version = "44.5";
    patches = [ ./patch/gnome-desktop-44.5.patch ];
  };
  gnome-font-viewer = {
    version = "46.0";
    patches = [ ./patch/gnome-font-viewer-46.0.patch ];
  };
  gnome-menus = {
    version = "3.36.0";
    patches = [ ./patch/gnome-menus-3.36.0.patch ];
  };
  gnome-session = {
    version = "46.0";
    patches = [ ./patch/gnome-session-46.0.patch ];
  };
  gnome-shell = {
    version = "46.9";
    patches = [ ./patch/gnome-shell-46.9.patch ];
  };
  gnome-text-editor = {
    version = "46.3";
    patches = [ ./patch/gnome-text-editor-46.3.patch ];
  };
  gtksourceview = {
    version = "5.12.1";
    patches = [ ./patch/gtksourceview-5.12.1.patch ];
  };
  gzip = {
    version = "1.15";
    patches = [ ./patch/gzip-1.15.patch ];
  };
  ibus = {
    version = "1.5.30";
    patches = [ ./patch/ibus-1.5.30.patch ];
  };
  json-glib = {
    version = "1.10.6";
    patches = [ ./patch/json-glib-1.10.6.patch ];
  };
  libadwaita = {
    version = "1.5.8";
    patches = [ ./patch/libadwaita-1.5.8.patch ];
  };
  gusb = {
    version = "0.4.2";
    patches = [ ./patch/libgusb-0.4.2.patch ];
  };
  libgweather = {
    version = "4.4.4";
    patches = [ ./patch/libgweather-4.4.4.patch ];
  };
  libxmlb = {
    version = "0.3.21";
    patches = [ ./patch/libxmlb-0.3.21.patch ];
  };
  mg = {
    version = "4.5";
    patches = [ ./patch/mg-4.5.patch ];
  };
  mutter = {
    version = "46.9";
    patches = [ ./patch/mutter-46.9.patch ];
  };
  php = {
    version = "8.4.25";
    patches = [ ./patch/php-8.4.25.patch ];
  };
  polkit = {
    version = "126";
    patches = [ ./patch/polkit-126.patch ];
  };
  postgresql = {
    version = "18.6";
    patches = [ ./patch/postgresql-18.6.patch ];
  };
  pulseaudio = {
    version = "17.0";
    patches = [ ./patch/pulseaudio-17.0.patch ];
  };
  upower = {
    version = "1.90.9";
    patches = [ ./patch/upower-v1.90.9.patch ];
  };
  xxHash = {
    version = "0.8.4";
    patches = [ ./patch/xxHash-0.8.4.patch ];
  };
  zegarmistrz = {
    version = "git";
    patches = [ ./patch/zegarmistrz.patch ];
  };
}
