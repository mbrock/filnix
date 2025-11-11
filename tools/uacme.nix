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

  # Hook script for uacme HTTP-01 validation
  acmeHook = pkgs.writeShellScript "uacme-hook.sh" ''
    WEBROOT="''${WEBROOT:-$HOME/.uacme/webroot}"
    CHALLENGE_DIR="$WEBROOT/.well-known/acme-challenge"
    case "$1" in
        begin) 
            mkdir -p "$CHALLENGE_DIR"
            ;;
        done|failed) 
            rm -f "$CHALLENGE_DIR"/* 2>/dev/null || true
            ;;
        *) 
            printf '%s\n' "$3" > "$CHALLENGE_DIR/$2"
            ;;
    esac
  '';

  # Wrapper script for uacme with proper env vars
  uacmeWrapper = domain: pkgs.writeShellApplication {
    name = "uacme-get-cert";
    runtimeInputs = [ pkgs.uacme ];
    text = ''
      DOMAIN="${domain}"
      UACME_DIR="''${UACME_DIR:-$HOME/.uacme}"
      WEBROOT="''${WEBROOT:-$HOME/.uacme/webroot}"
      STAGING="''${STAGING:-}"
      
      export NIX_SSL_CERT_FILE=/etc/ssl/certs/ca-certificates.crt
      export SSL_CERT_FILE=/etc/ssl/certs/ca-certificates.crt
      
      mkdir -p "$UACME_DIR"
      mkdir -p "$WEBROOT/.well-known/acme-challenge"
      
      STAGING_FLAG=""
      if [ -n "$STAGING" ]; then
        STAGING_FLAG="-s"
      fi
      
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
