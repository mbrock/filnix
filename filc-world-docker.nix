{ base, ports, world-pkgs, dank-bashrc, ghostty-terminfo }:

let
  world-env = base.buildEnv {
    name = "filc-world";
    paths = world-pkgs;
  };
in
base.dockerTools.streamLayeredImage {
  name = "filc-world";
  tag = "latest";
  architecture = "amd64";

  contents = [ world-env ];

  config = {
    Cmd = [ "${ports.bash}/bin/bash" "--rcfile" "/root/.bashrc" "-i" ];
    Env = [
      "PATH=${world-env}/bin"
      "TERMINFO_DIRS=${ghostty-terminfo}/share/terminfo"
      "PS1=\\[\\033[1;32m\\][filc]\\[\\033[0m\\] \\w \\$ "
      "CC=clang"
      "CXX=clang++"
    ];
    WorkingDir = "/root";
  };

  extraCommands = ''
    mkdir -p root
    cat > root/.bashrc <<'EOF'
${builtins.readFile dank-bashrc}
EOF
  '';
}
