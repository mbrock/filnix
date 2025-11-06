{
  pkgs,
  ports,
  builders,
  lighttpd-conf-template,
  cgi-docroot,
}:

builders.bashScript "lighttpd-demo" {
  deps =
    (with pkgs; [
      netcat
      systemd
    ])
    ++ (with ports; [
      coreutils
      ncurses
      gnused
      figlet
      clolcat
      file
    ]);

  excludeShellChecks = [
    "SC2086"
    "SC2064"
    "SC2034"
  ];

  code = ''
        echo '# starting lighttpd-demo...'

        if [ -t 1 ]; then
          BOLD=$(tput bold)
          GREEN=$(tput setaf 2)
          BLUE=$(tput setaf 4)
          CYAN=$(tput setaf 6)
          DIM=$(tput dim)
          RESET=$(tput sgr0)
        else
          BOLD="" GREEN="" BLUE="" CYAN="" DIM="" RESET=""
        fi

        # Find a free port in range 9000-9999
        find_free_port() {
          for port in $(seq 9000 9999); do
            if ! nc -z localhost $port 2>/dev/null; then
              echo $port
              return
            fi
          done
          echo "No free port found in range 9000-9999" >&2
          exit 1
        }

        PORT=$(find_free_port)

        # Create runtime directory
        RUNDIR=''${XDG_RUNTIME_DIR:-/tmp}/filnix-lighttpd
        mkdir -p "$RUNDIR/cache"
        mkdir -p "$RUNDIR/dav"
        chmod 777 "$RUNDIR/dav"

        # Create a welcome file in WebDAV directory
        echo "Welcome to memory-safe WebDAV! Upload files here." > "$RUNDIR/dav/README.txt"
        chmod 644 "$RUNDIR/dav/README.txt"

        # Create htdigest password file for WebDAV
        # Default user: demo / password: demo
        # Format: user:realm:md5(user:realm:password)
        REALM="WebDAV"
        USER="demo"
        PASS="demo"

        # MD5 hash of "demo:WebDAV:demo"
        HASH=$(echo -n "$USER:$REALM:$PASS" | md5sum | cut -d' ' -f1)
        echo "$USER:$REALM:$HASH" > "$RUNDIR/htdigest"

        CONF="$RUNDIR/lighttpd.conf"

        sed -e "s|PORT_PLACEHOLDER|$PORT|g" \
            -e "s|RUNDIR_PLACEHOLDER|$RUNDIR|g" \
            ${lighttpd-conf-template} > "$CONF"

    #    echo
    #    tput bold
    #    figlet -f fender "Fil-C" | head -n-1 | clolcat -f
        # tput dim
        # echo "  Pretty Good CGI Server"
        # tput sgr0
    #    echo
        echo "  ''${BLUE}http://localhost:''${BOLD}$PORT''${RESET}''${DIM}"
    #    echo
        # tput sgr0
        # echo "  ${cgi-docroot}"
        # echo

        # Collect script info into a table
        for script in ${cgi-docroot}/*.cgi; do
          [ -f "$script" ] || continue
          name=$(basename "$script")
          size=$(stat -L -c %s "$script" | numfmt --to=iec-i --suffix=B --padding=7)

          # Determine type - check if binary first to avoid null byte warnings
          if file -b -L "$script" | grep -q "^ELF"; then
            # For binaries, show full file output
            type=$(file -b -L "$script" | cut -d',' -f1-2)
          else
            # For scripts, check shebang
            first_line=$(head -n1 "$script")
            if [[ "$first_line" =~ ^#!.*bash ]]; then
              type="bash script"
            elif [[ "$first_line" =~ ^#! ]]; then
              interp=$(echo "$first_line" | sed 's/^#!//' | awk '{print $1}')
              type="$(basename "$interp") script"
            else
              type=$(file -b -L "$script" | cut -d',' -f1)
            fi
          fi

          printf "    ''${CYAN}%-15s''${RESET} ''${DIM}%s''${RESET}  %s\n" "$name" "$size" "$type"
        done | sort

     #   echo

        tput dim
        echo "  WebDAV credentials: demo / demo"
        tput sgr0
    #    echo

        ${ports.lighttpd}/sbin/lighttpd -D -f "$CONF" 2>&1 | sed 's/^/>>> /'
  '';
}
