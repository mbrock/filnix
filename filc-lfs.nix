# Fil-C Linux From Scratch - declarative rootfs construction
{ base, ports }:

let
  lib = base.lib;
  
  # Merge multiple packages into one output
  merge = name: pkgs: base.buildEnv {
    inherit name;
    paths = pkgs;
    pathsToLink = [ "/bin" "/lib" "/share" "/include" ];
  };
  
  # Build a minimal FHS directory structure
  mkFHS = name: contents: base.runCommand name {} ''
    mkdir -p $out/{bin,sbin,lib,lib64,etc,dev,proc,sys,run,tmp,var,home,root,opt,usr}
    
    # Symlink /usr to /
    ln -s ../bin $out/usr/bin
    ln -s ../lib $out/usr/lib
    ln -s ../lib $out/usr/lib64
    ln -s ../include $out/usr/include
    ln -s ../share $out/usr/share
    
    # Copy contents
    ${lib.concatMapStringsSep "\n" (pkg: ''
      [ -d ${pkg}/bin ] && cp -r ${pkg}/bin/* $out/bin/ || true
      [ -d ${pkg}/lib ] && cp -r ${pkg}/lib/* $out/lib/ || true
      [ -d ${pkg}/share ] && cp -r ${pkg}/share/* $out/share/ || true
    '') contents}
    
    chmod -R u+w $out
    chmod 1777 $out/tmp
  '';
  
  # Create essential /etc files
  etcFiles = base.runCommand "etc-files" {} ''
    mkdir -p $out/etc
    
    # /etc/passwd
    cat > $out/etc/passwd <<'EOF'
    root:x:0:0:root:/root:${ports.bash}/bin/bash
    nobody:x:65534:65534:Nobody:/:/bin/false
    EOF
    
    # /etc/group
    cat > $out/etc/group <<'EOF'
    root:x:0:
    nogroup:x:65534:
    EOF
    
    # /etc/shells
    cat > $out/etc/shells <<'EOF'
    ${ports.bash}/bin/bash
    EOF
    
    # /etc/fstab
    cat > $out/etc/fstab <<'EOF'
    proc  /proc  proc   defaults  0 0
    sysfs /sys   sysfs  defaults  0 0
    devpts /dev/pts devpts gid=5,mode=620 0 0
    tmpfs /run   tmpfs  defaults  0 0
    EOF
    
    # /etc/hosts
    cat > $out/etc/hosts <<'EOF'
    127.0.0.1 localhost
    ::1       localhost
    EOF
    
    chmod 644 $out/etc/*
  '';

in rec {
  # Minimal base system - just enough to boot and run bash
  minimal = mkFHS "filc-minimal" [
    ports.bash
    ports.coreutils
    etcFiles
  ];
  
  # Development system - adds common tools
  development = mkFHS "filc-dev" [
    ports.bash
    ports.coreutils
    ports.grep
    ports.sed
    ports.diffutils
    ports.vim
    ports.git
    ports.tmux
    etcFiles
  ];
  
  # Full system - everything we have
  full = mkFHS "filc-full" (
    [etcFiles] ++ (lib.attrValues (lib.filterAttrs (n: v: lib.isDerivation v) ports))
  );
  
  # Bootable disk image (requires kernel)
  diskImage = { rootfs ? full, kernelPackage ? base.linux }: 
    base.runCommand "filc-disk.img" {
      nativeBuildInputs = [ base.e2fsprogs base.util-linux ];
    } ''
      # Create 2GB disk image
      dd if=/dev/zero of=$out bs=1M count=2048
      
      # Create partition table
      parted -s $out mklabel msdos
      parted -s $out mkpart primary ext4 1MiB 100%
      
      # Format and mount
      loopdev=$(losetup -f)
      losetup $loopdev $out
      partprobe $loopdev
      mkfs.ext4 ''${loopdev}p1
      
      mkdir -p mnt
      mount ''${loopdev}p1 mnt
      
      # Copy rootfs
      cp -a ${rootfs}/* mnt/
      
      # Install kernel
      mkdir -p mnt/boot
      cp ${kernelPackage}/bzImage mnt/boot/vmlinuz
      
      # Cleanup
      umount mnt
      losetup -d $loopdev
    '';
  
  # Container tarball
  containerTarball = { rootfs ? minimal }:
    base.runCommand "filc-rootfs.tar.gz" {} ''
      cd ${rootfs}
      tar czf $out .
    '';
  
  # Docker image
  dockerImage = { rootfs ? minimal }:
    base.dockerTools.buildLayeredImage {
      name = "filc-os";
      tag = "latest";
      contents = [ rootfs ];
      config = {
        Cmd = [ "${ports.bash}/bin/bash" ];
        Env = [ "PATH=/bin:/usr/bin" ];
      };
    };
}
