{ pkgs, ports }:
let
  # Memory-safe bash script wrapper
  bashScript =
    name:
    {
      deps ? [ ],
      code,
      excludeShellChecks ? [ ],
      bashOptions ? [
        "errexit"
        "nounset"
        "pipefail"
      ],
    }:
    pkgs.writeShellApplication {
      inherit name excludeShellChecks bashOptions;
      runtimeInputs = deps;
      text = code;
      derivationArgs = {
        postBuild = ''
          substituteInPlace $out/bin/${name} \
            --replace-fail '${pkgs.runtimeShell}' '${ports.bash}/bin/bash'
        '';
      };
    };

  # Memory-safe C program builder
  filcProgram =
    name:
    {
      deps ? [ ],
      code,
    }:
    pkgs.stdenv.mkDerivation {
      inherit name;
      src = pkgs.writeText "${name}.c" code;
      nativeBuildInputs = [ ports.filcc ];
      buildInputs = deps;
      unpackPhase = "true";

      CFLAGS = pkgs.lib.concatMapStringsSep " " (dep: "-I${dep}/include") deps;

      LDFLAGS = pkgs.lib.concatMapStringsSep " " (dep: "-L${dep}/lib") deps;

      buildPhase = ''
        clang -o ${name} $src $CFLAGS $LDFLAGS -O2
      '';

      installPhase = ''
        mkdir -p $out/bin
        cp ${name} $out/bin/
      '';
    };

  # Build CGI document root from attrset of scripts
  cgi-bin =
    scripts:
    pkgs.runCommand "cgi-bin" { } ''
      mkdir -p $out
      ${pkgs.lib.concatStringsSep "\n" (
        pkgs.lib.mapAttrsToList (name: drv: ''
          ln -s ${drv}/bin/${name} $out/${name}
        '') scripts
      )}
    '';

  # Build document root with both CGI scripts and static files
  www-root =
    {
      scripts ? { },
      static ? { },
    }:
    pkgs.runCommand "www-root" { } ''
      mkdir -p $out
      ${pkgs.lib.concatStringsSep "\n" (
        pkgs.lib.mapAttrsToList (name: drv: ''
          ln -s ${drv}/bin/${name} $out/${name}
        '') scripts
      )}
      ${pkgs.lib.concatStringsSep "\n" (
        pkgs.lib.mapAttrsToList (name: file: ''
          ln -s ${file} $out/${name}
        '') static
      )}
    '';
in
let
  style-css = pkgs.writeText "style.css" ''
    body { font-family: monospace; background: #1e1e1e; color: #d4d4d4; padding: 20px; }
    .font-gallery { display: flex; flex-wrap: wrap; gap: 15px; margin: 20px 0; }
    .font-sample { 
      flex: 0 0 auto;
      padding: 15px; 
      background: #2d2d2d; 
      border-left: 4px solid #007acc;
      min-width: 200px;
      max-width: 100%;
    }
    .font-name { color: #4ec9b0; font-weight: bold; margin-bottom: 10px; font-size: 0.85em; }
    pre { margin: 0; white-space: pre; overflow-x: auto; color: #ce9178; }
    form { margin: 20px 0; padding: 20px; background: #252526; border: 1px solid #3e3e42; }
    input[type="text"] { 
      padding: 10px; 
      width: 300px; 
      background: #3c3c3c; 
      border: 1px solid #6e6e6e; 
      color: #d4d4d4;
      font-family: monospace;
    }
    input[type="submit"] {
      padding: 10px 20px;
      background: #0e639c;
      border: none;
      color: white;
      cursor: pointer;
      font-family: monospace;
    }
    input[type="submit"]:hover { background: #1177bb; }
    h1 { color: #4ec9b0; }
    .back { color: #569cd6; text-decoration: none; }
    .back:hover { text-decoration: underline; }
  '';
in
let
  html-escape = filcProgram "html-escape" {
    deps = with ports; [ ];
    code = ''
      #include <stdio.h>

      int
      main ()
      {
        int c;
        while ((c = getchar ()) != EOF)
          {
            switch (c)
              {
              case '&':
                printf ("&amp;");
                break;
              case '<':
                printf ("&lt;");
                break;
              case '>':
                printf ("&gt;");
                break;
              case '"':
                printf ("&quot;");
                break;
              case '\''':
                printf ("&#39;");
                break;
              default:
                putchar (c);
              }
          }
        return 0;
      }
    '';
  };

  figlet-cgi = bashScript "figlet.cgi" {
    deps = with ports; [
      coreutils
      figlet
      html-escape
      gnused
      gawk
    ];
    bashOptions = [
      "errexit"
      "nounset"
    ]; # No pipefail - we handle errors manually
    code = ''
      # Parse query string for text parameter
      TEXT="Fil-C"
      if [ -n "$QUERY_STRING" ]; then
        # Simple URL decode and extract text parameter
        TEXT=$(echo "$QUERY_STRING" | sed -n 's/.*text=\([^&]*\).*/\1/p' | sed 's/+/ /g' | sed 's/%20/ /g')
        [ -z "$TEXT" ] && TEXT="Fil-C"
      fi

      # Escape for safe HTML output using Fil-C program
      TEXT_ESCAPED=$(echo "$TEXT" | html-escape)

      cat <<EOF
      Content-Type: text/html; charset=utf-8

      EOF

      cat <<'HEADER'
      <html>
      <head>
      <meta charset="utf-8">
      <title>Figlet Font Gallery</title>
      <link rel="stylesheet" href="style.css">
      </head>
      <body>
      HEADER

      printf '<form method="get">\n'
      printf '  <input type="text" id="text" name="text" value="%s">\n' "$TEXT_ESCAPED"
      printf '  <input type="submit" value="Render">\n'
      printf '</form>\n'
      printf '<div class="font-gallery">\n'

      # Get all fonts and render each one
      figlist | while read -r font; do
        # Try to render font - if it fails, skip to next
        if ! figlet -f "$font" "$TEXT" >/dev/null 2>&1; then
          continue
        fi
        
        echo "<div class='font-sample'>"
        echo "<div class='font-name'>$(echo "$font" | html-escape)</div>"
        echo "<pre>"
        # Render, strip trailing blanks, HTML-escape
        figlet -f "$font" "$TEXT" 2>/dev/null | \
          sed ':a; /^[[:space:]]*$/ { N; s/\n[[:space:]]*$//; ta; }' | \
          html-escape
        echo "</pre>"
        echo "</div>"
      done

      printf '</div>\n'

      cat <<EOF
      <p><a href="hello.cgi" class="back">← Back to main page</a></p>
      </body>
      </html>
      EOF
    '';
  };

  cgi-docroot = www-root {
    scripts = {
      "hello.cgi" = hello-cgi;
      "demo.cgi" = demo-cgi;
      "figlet.cgi" = figlet-cgi;
    };
    static = {
      "style.css" = style-css;
    };
  };

  hello-cgi = bashScript "hello.cgi" {
    deps = with ports; [ coreutils ];
    code = ''
      cat <<EOF
      Content-Type: text/html

      <html>
      <head><title>Fil-C Lighttpd Demo</title></head>
      <body>
      <h1>Hello from Memory-Safe Lighttpd!</h1>
      <p>This web server is built with Fil-C for complete memory safety.</p>
      <h2>Features enabled:</h2>
      <ul>
        <li>Compression: brotli, zstd, bzip2, gzip</li>
        <li>WebDAV support</li>
        <li>Lua scripting (mod_magnet)</li>
        <li>Kerberos authentication</li>
      </ul>
      <h2>CGI Demos:</h2>
      <ul>
        <li><a href="hello.cgi">Bash CGI (this page)</a></li>
        <li><a href="demo.cgi">C CGI with memory safety</a></li>
        <li><a href="figlet.cgi">Figlet Font Gallery (streaming)</a></li>
      </ul>
      <h2>Request info:</h2>
      <pre>
      Server: $(uname -a)
      Time: $(date)
      Query: $QUERY_STRING
      Request Method: $REQUEST_METHOD
      Remote Addr: $REMOTE_ADDR
      </pre>
      </body>
      </html>
      EOF
    '';
  };

  demo-cgi = filcProgram "demo.cgi" {
    deps = with ports; [ ];
    code = ''
      #include <stdio.h>
      #include <stdlib.h>
      #include <string.h>
      #include <time.h>

      int
      main ()
      {
        char *query = getenv ("QUERY_STRING");
        char *method = getenv ("REQUEST_METHOD");
        char *remote = getenv ("REMOTE_ADDR");
        
        /* Array to demonstrate bounds checking.  */
        const char *fruits[] = {
          "apple", "banana", "cherry", "date", "elderberry"
        };
        int num_fruits = 5;
        
        const char *div_style = 
          "border: 2px solid #333; padding: 15px; margin: 20px 0; "
          "background: #f0f0f0;";
        const char *pre_style = "background: #fff; padding: 10px;";
        
        printf ("Content-Type: text/html; charset=utf-8\r\n\r\n");
        printf ("<html>\n");
        printf ("<head>\n");
        printf ("<meta charset=\"utf-8\">\n");
        printf ("<title>%s</title>\n", "Fil-C Memory Safety Demo");
        printf ("</head>\n");
        printf ("<body>\n");
        printf ("<h1>%s</h1>\n", "Memory Safety Interactive Demo");
        printf ("<p>%s</p>\n", 
                "This CGI is written in C with Fil-C memory safety!");
        
        printf ("<h2>%s</h2>\n", "Test Array Bounds Checking");
        printf ("<p>We have an array of %d fruits. ", num_fruits);
        printf ("%s</p>\n", "Try accessing different indices:");
        printf ("<ul>\n");
        for (int i = 0; i < num_fruits; i++)
          printf ("<li><a href=\"?index=%d\">Index %d: %s</a></li>\n",
                  i, i, fruits[i]);
        printf ("</ul>\n");
        
        printf ("<p><strong>%s</strong> ", "Try to break it:");
        printf ("<a href=\"?index=10\">%s</a> | ", 
                "Access index 10 (out of bounds!)");
        printf ("<a href=\"?index=-1\">%s</a> | ",
                "Access index -1 (negative!)");
        printf ("<a href=\"?index=999\">%s</a></p>\n",
                "Access index 999 (way out!)");
        
        /* Parse and handle index parameter.  */
        if (query && strstr (query, "index=") == query)
          {
            int index = atoi (query + 6);
            printf ("<div style='%s'>\n", div_style);
            printf ("<h3>Result for index %d:</h3>\n", index);
            
            if (index >= 0 && index < num_fruits)
              {
                printf ("<p style='color: green;'>");
                printf ("<strong>✓ Safe access:</strong> ");
                printf ("fruits[%d] = \"%s\"</p>\n", index, fruits[index]);
              }
            else
              {
                printf ("<p style='color: orange;'>");
                printf ("<strong>⚠ Out of bounds attempt!</strong></p>\n");
                printf ("<p>Trying to access fruits[%d]...</p>\n", index);
                printf ("<p><em>%s ", 
                        "In unsafe C, this would crash or return garbage.");
                printf ("%s</em></p>\n",
                        "With Fil-C, let's see what happens:");
                printf ("<pre style='%s'>", pre_style);
                
                /* This will trap with Fil-C's memory safety!  */
                const char *result = fruits[index];
                printf ("Value: %s\n", result);
                printf ("</pre>\n");
              }
            printf ("</div>\n");
          }
        
        printf ("<h2>%s</h2>\n", "Request Information:");
        printf ("<pre>\n");
        time_t now = time (NULL);
        printf ("Time: %s", ctime (&now));
        printf ("Query String: %s\n", query ? query : "(none)");
        printf ("Request Method: %s\n", method ? method : "unknown");
        printf ("Remote Address: %s\n", remote ? remote : "unknown");
        printf ("</pre>\n");
        printf ("<p><a href=\"hello.cgi\">← Back to main page</a></p>\n");
        printf ("</body>\n");
        printf ("</html>\n");
        
        return 0;
      }
    '';
  };

  lighttpd-conf-template = pkgs.writeText "lighttpd.conf.template" ''
    server.document-root = "${cgi-docroot}"
    server.port = PORT_PLACEHOLDER
    server.bind = "0.0.0.0"
    server.pid-file = "RUNDIR_PLACEHOLDER/lighttpd.pid"

    server.modules = (
      "mod_access",
      "mod_accesslog",
      "mod_cgi",
      "mod_status",
      "mod_deflate",
    )

    # Enable streaming for CGI responses
    server.stream-response-body = 1

    status.status-url = "/server-status"

    debug.log-request-handling = "enable"

    mimetype.assign = (
      ".html" => "text/html",
      ".css"  => "text/css",
      ".js"   => "application/javascript",
    )

    deflate.cache-dir = "RUNDIR_PLACEHOLDER/cache"
    deflate.mimetypes = ( "text/html", "text/plain", "text/css", "application/javascript" )
    deflate.allowed-encodings = ( "brotli", "gzip", "deflate", "zstd" )

    cgi.assign = ( ".cgi" => "" )

    accesslog.filename = "RUNDIR_PLACEHOLDER/access.log"
    server.errorlog = "RUNDIR_PLACEHOLDER/error.log"
  '';

  lighttpd-demo = bashScript "lighttpd-demo" {
    deps =
      (with pkgs; [
        netcat
        systemd
        ncurses
      ])
      ++ (with ports; [
        coreutils
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
      # Terminal colors (only if stdout is a terminal)
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

      CONF="$RUNDIR/lighttpd.conf"

      sed -e "s|PORT_PLACEHOLDER|$PORT|g" \
          -e "s|RUNDIR_PLACEHOLDER|$RUNDIR|g" \
          ${lighttpd-conf-template} > "$CONF"

      echo
      tput bold
      figlet -f fender "Fil-C" | head -n-1 | clolcat -f
      tput dim
      echo "  Pretty Good CGI Server"
      tput sgr0
      echo
      echo "  ''${BLUE}http://localhost:''${BOLD}$PORT''${RESET}''${DIM}"
      echo
      tput sgr0
      echo "  ${cgi-docroot}"
      echo

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

      echo

      tput dim
      echo "  Press Ctrl-C to stop"
      tput sgr0
      echo

      systemd-run \
        --user \
        --scope \
        --unit=filnix-lighttpd \
        --description="Fil-C Lighttpd Demo" \
        --property=MemoryMax=512M \
        --property=MemoryHigh=384M \
        --property=TasksMax=128 \
        --property=CPUQuota=100% \
        ${ports.lighttpd}/sbin/lighttpd -D -f "$CONF" 2>&1 | sed 's/^/>>> /'
    '';
  };
in
lighttpd-demo
