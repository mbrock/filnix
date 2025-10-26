{ base, filenv, packages }:

# Combines all fil-c packages into a single derivation with symlinks
filenv.mkDerivation {
  pname = "fil-c-combined";
  version = "1.0";
  
  buildInputs = base.lib.attrValues packages;
  
  buildPhase = "true";
  
  installPhase = ''
    mkdir -p $out
    
    # Create directory structure
    mkdir -p $out/bin $out/lib $out/include $out/share
    
    # Symlink all binaries
    for pkg in $buildInputs; do
      if [ -d "$pkg/bin" ]; then
        for bin in "$pkg/bin"/*; do
          if [ -f "$bin" ] || [ -L "$bin" ]; then
            ln -sf "$bin" "$out/bin/$(basename "$bin")"
          fi
        done
      fi
    done
    
    # Symlink all libraries
    for pkg in $buildInputs; do
      if [ -d "$pkg/lib" ]; then
        for lib in "$pkg/lib"/*; do
          if [ -f "$lib" ] || [ -L "$lib" ]; then
            ln -sf "$lib" "$out/lib/$(basename "$lib")"
          elif [ -d "$lib" ]; then
            # Handle library subdirectories (like perl5, pkgconfig)
            mkdir -p "$out/lib/$(basename "$lib")"
            cp -rsf "$lib"/* "$out/lib/$(basename "$lib")/"
          fi
        done
      fi
    done
    
    # Symlink includes
    for pkg in $buildInputs; do
      if [ -d "$pkg/include" ]; then
        cp -rsf "$pkg/include"/* "$out/include/" || true
      fi
    done
    
    # Symlink share (man pages, docs, etc)
    for pkg in $buildInputs; do
      if [ -d "$pkg/share" ]; then
        for item in "$pkg/share"/*; do
          if [ -d "$item" ]; then
            mkdir -p "$out/share/$(basename "$item")"
            cp -rsf "$item"/* "$out/share/$(basename "$item")/" || true
          else
            ln -sf "$item" "$out/share/$(basename "$item")" || true
          fi
        done
      fi
    done
  '';
  
  meta = {
    description = "Combined fil-c packages";
  };
}
