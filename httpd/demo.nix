{ pkgs, ports }:
let
  # Memory-safe bash script wrapper
  bashScript = name: { deps ? [], code, excludeShellChecks ? [] }: 
    pkgs.writeShellApplication {
      inherit name excludeShellChecks;
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
  filcProgram = name: { deps ? [], code }: 
    pkgs.stdenv.mkDerivation {
      inherit name;
      src = pkgs.writeText "${name}.c" code;
      nativeBuildInputs = [ ports.filcc ];
      buildInputs = deps;
      
      unpackPhase = "true"; # No unpacking needed
      
      buildPhase = ''
        ${ports.filcc}/bin/clang -o ${name} $src ${pkgs.lib.concatMapStringsSep " " (dep: "-I${dep}/include") deps} ${pkgs.lib.concatMapStringsSep " " (dep: "-L${dep}/lib") deps}
      '';
      
      installPhase = ''
        mkdir -p $out/bin
        cp ${name} $out/bin/
      '';
    };
  
  # Build CGI document root from attrset of scripts
  cgi-bin = scripts:
    pkgs.runCommand "cgi-bin" {} ''
      mkdir -p $out
      ${pkgs.lib.concatStringsSep "\n" (pkgs.lib.mapAttrsToList (name: drv: ''
        ln -s ${drv}/bin/${name} $out/${name}
      '') scripts)}
    '';
in
let
  cgi-docroot = cgi-bin {
    "hello.cgi" = hello-cgi;
    "demo.cgi" = demo-cgi;
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
    deps = with ports; [];
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
        netcat systemd
      ]) ++ 
      (with ports; [
        coreutils gnused
      ]);

    excludeShellChecks = [ "SC2086" "SC2064" ];
    code = ''
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
      
      echo "Starting Fil-C Lighttpd demo on http://localhost:$PORT"
      echo "  runtime dir: $RUNDIR"
      echo "  document-root: ${cgi-docroot}"
      echo "  logs: $RUNDIR/access.log, $RUNDIR/error.log"
      echo
      echo "Try these URLs:"
      echo "  curl http://0:$PORT/hello.cgi - Bash CGI"
      echo "  curl http://0:$PORT/demo.cgi  - Memory-safe C CGI"
      echo
      
      exec systemd-run \
        --user \
        --scope \
        --unit=filnix-lighttpd \
        --description="Fil-C Lighttpd Demo" \
        --background="48;5;22" \
        --property=MemoryMax=512M \
        --property=MemoryHigh=384M \
        --property=TasksMax=128 \
        --property=CPUQuota=100% \
        ${ports.lighttpd}/sbin/lighttpd -D -f "$CONF"
    '';
  };
in
  lighttpd-demo
