{ pkgs }:

let
  # Simple HTTP server for ACME challenges using fil-c python3
  challengeServer = pkgs.writeShellApplication {
    name = "uacme-challenge-server";
    runtimeInputs = [ pkgs.python3 ];
    text = ''
      WEBROOT="''${WEBROOT:-$HOME/.uacme/webroot}"
      mkdir -p "$WEBROOT"
      cd "$WEBROOT"
      exec python3 -m http.server 80
    '';
  };

  # Hook script for uacme HTTP-01 validation only
  # Parameters: method type ident token auth
  # Note: WEBROOT must be exported by the calling script
  acmeHook = pkgs.writeShellScript "uacme-hook.sh" ''
    METHOD=$1
    TYPE=$2
    IDENT=$3
    TOKEN=$4
    AUTH=$5
    
    # Only handle HTTP-01 challenges
    if [ "$TYPE" != "http-01" ]; then
      echo "Ignoring $TYPE challenge (only HTTP-01 supported)" >&2
      exit 1
    fi
    
    WEBROOT="''${WEBROOT:-$HOME/.uacme/webroot}"
    CHALLENGE_DIR="$WEBROOT/.well-known/acme-challenge"
    
    case "$METHOD" in
        begin) 
            mkdir -p "$CHALLENGE_DIR"
            echo "Writing HTTP-01 challenge for $IDENT: $CHALLENGE_DIR/$TOKEN" >&2
            printf '%s' "$AUTH" > "$CHALLENGE_DIR/$TOKEN"
            chmod 644 "$CHALLENGE_DIR/$TOKEN"
            ;;
        done|failed) 
            rm -f "$CHALLENGE_DIR/$TOKEN" 2>/dev/null || true
            ;;
        *) 
            echo "Unknown method: $METHOD" >&2
            exit 1
            ;;
    esac
  '';

  # Wrapper script for uacme with proper env vars and HTTP server
  uacmeWrapper = domain: pkgs.writeShellApplication {
    name = "uacme-get-cert";
    runtimeInputs = [ pkgs.uacme pkgs.python3 ];
    text = ''
      DOMAIN="${domain}"
      UACME_DIR="''${UACME_DIR:-$HOME/.uacme}"
      WEBROOT="''${WEBROOT:-$HOME/.uacme/webroot}"
      STAGING="''${STAGING:-}"
      
      export NIX_SSL_CERT_FILE=/etc/ssl/certs/ca-certificates.crt
      export SSL_CERT_FILE=/etc/ssl/certs/ca-certificates.crt
      export WEBROOT
      
      mkdir -p "$UACME_DIR"
      mkdir -p "$WEBROOT/.well-known/acme-challenge"
      
      STAGING_FLAG=""
      if [ -n "$STAGING" ]; then
        STAGING_FLAG="-s"
      fi
      
      # Start HTTP server on port 80
      echo "Starting HTTP server on port 80..."
      cd "$WEBROOT"
      sudo -E python3 -m http.server 80 &
      HTTP_PID=$!
      
      cleanup() {
        echo "Stopping HTTP server..."
        sudo kill $HTTP_PID 2>/dev/null || true
      }
      trap cleanup EXIT
      
      # Wait for server to start
      sleep 2
      
      # Create account if it doesn't exist
      if [ ! -f "$UACME_DIR/private/key.pem" ]; then
        echo "Creating new ACME account..."
        uacme -v -c "$UACME_DIR" $STAGING_FLAG -y new
      fi
      
      # Issue certificate
      echo "Requesting certificate for $DOMAIN..."
      uacme -v -c "$UACME_DIR" $STAGING_FLAG \
        -h ${acmeHook} issue "$DOMAIN"
      
      echo "Certificate saved to: $UACME_DIR/$DOMAIN/cert.pem"
      echo "Private key saved to: $UACME_DIR/private/$DOMAIN/key.pem"
    '';
  };

in {
  inherit challengeServer acmeHook;
  uacme = pkgs.uacme;
  getCert = uacmeWrapper;
  
  # Convenience script for filc.less.rest
  getFilcCert = uacmeWrapper "filc.less.rest";
}
