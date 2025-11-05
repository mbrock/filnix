{ pkgs, cgi-docroot }:

pkgs.writeText "lighttpd.conf.template" ''
  server.document-root = "${cgi-docroot}"
  server.port = PORT_PLACEHOLDER
  server.bind = "0.0.0.0"
  server.pid-file = "RUNDIR_PLACEHOLDER/lighttpd.pid"

  server.modules = (
    "mod_access",
    "mod_accesslog",
    "mod_alias",
    "mod_authn_file",
    "mod_auth",
    "mod_cgi",
    "mod_status",
    "mod_deflate",
    "mod_webdav",
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

  # WebDAV configuration for /dav directory
  $HTTP["url"] =~ "^/dav($|/)" {
    alias.url = ( "/dav" => "RUNDIR_PLACEHOLDER/dav" )
    webdav.activate = "enable"
    webdav.is-readonly = "disable"
    webdav.sqlite-db-name = "RUNDIR_PLACEHOLDER/cache/webdav_lock.db"
    dir-listing.activate = "enable"

    auth.backend = "htdigest"
    auth.backend.htdigest.userfile = "RUNDIR_PLACEHOLDER/htdigest"
    auth.require = ( "" => (
      "method" => "digest",
      "realm" => "WebDAV",
      "require" => "valid-user"
    ))
  }

  accesslog.filename = "RUNDIR_PLACEHOLDER/access.log"
  server.errorlog = "RUNDIR_PLACEHOLDER/error.log"
''
