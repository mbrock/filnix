# Fil-C Apache under load, prefork and event: the scoreboard (mod_status),
# the shmcb TLS session cache, mod_cache_socache, mod_auth_digest's client
# table, NixOS's posixsem mutex and a graceful restart, each shared by the
# server's processes. A pointer one process stores in shared memory has no
# capability in another; Apache keeps integers, strings and offsets there,
# and the port moves mod_auth_digest's pointers to offsets.
#
# The system refuses apacheHttpd for now, so the nodes take pkgsFilc's,
# the same derivation without the refusal.
{ pkgsFilc }:
{ pkgs, lib, ... }:
let
  cert =
    pkgs.runCommand "apache-test-cert"
      {
        nativeBuildInputs = [ pkgs.buildPackages.openssl ];
      }
      ''
        mkdir $out
        openssl req -x509 -newkey rsa:2048 -nodes -days 3650 -subj /CN=localhost \
          -addext basicConstraints=critical,CA:FALSE \
          -keyout $out/key.pem -out $out/cert.pem
      '';

  docs = pkgs.runCommand "apache-test-docs" { } ''
    mkdir -p $out/secret
    for i in $(seq 400); do echo "line $i of a page big enough to cache"; done > $out/index.html
    echo secret > $out/secret/s.txt
  '';

  # htdigest's format: user:realm:md5(user:realm:password).
  digestUsers = pkgs.runCommand "apache-test-digest" { } ''
    echo "alice:realm:$(printf alice:realm:pw | md5sum | cut -d' ' -f1)" > $out
  '';

  server = mpm: {
    virtualisation.memorySize = 3072;
    virtualisation.cores = 4;
    environment.systemPackages = [
      pkgsFilc.apacheHttpd # ab
      pkgs.curl
      pkgs.openssl
    ];
    services.httpd = {
      enable = true;
      package = pkgsFilc.apacheHttpd;
      inherit mpm;
      adminAddr = "root@localhost";
      maxClients = 64;
      extraModules = [
        "cache"
        "cache_socache"
        "ldap"
      ];
      logPerVirtualHost = false;
      logFormat = "custom";
      customLogFormat = "%P %{SSL_SESSION_RESUMED}x %>s %U";
      virtualHosts.localhost = {
        addSSL = true;
        sslServerCert = "${cert}/cert.pem";
        sslServerKey = "${cert}/key.pem";
        documentRoot = docs;
        extraConfig = ''
          CacheEnable socache /
          CacheDisable /server-status
          CacheDisable /ldap-status
          CacheDisable /secret
          CacheSocache shmcb:/run/httpd/cache(2048000)
          CacheQuickHandler on
          Header set Cache-Control "max-age=600"

          <Location /server-status>
            SetHandler server-status
          </Location>
          <Location /ldap-status>
            SetHandler ldap-status
          </Location>
          <Location /secret>
            AuthType Digest
            AuthName realm
            AuthDigestDomain /secret/
            AuthDigestProvider file
            AuthDigestNcCheck On
            AuthUserFile ${digestUsers}
            Require valid-user
          </Location>
        '';
      };
      extraConfig = ''
        ExtendedStatus On
        # The server-side session cache, not tickets, resumes sessions.
        SSLSessionTickets off
        # The port caches LDAP per process; this is ignored with a warning.
        LDAPSharedCacheSize 500000
        <IfModule mpm_event_module>
          StartServers 4
          ServerLimit 8
          ThreadsPerChild 16
          MaxRequestWorkers 128
        </IfModule>
      '';
    };
  };
in
{
  name = "apache";

  nodes.prefork = server "prefork";
  nodes.event = server "event";

  testScript = ''
    import re

    def status(m, key):
        out = m.succeed("curl -sf 'http://localhost/server-status?auto'")
        return [int(v) for v in re.findall(rf"^{key}: (\d+)$", out, re.M)]

    def ab(m, n, url, background=False):
        cmd = f"ab -q -c 50 -n {n} {url}"
        if background:
            m.succeed(f"{cmd} > /tmp/ab.out 2>&1 &")
            return
        abcheck(m.succeed(cmd), n)

    def abcheck(out, n):
        print(out)
        assert re.search(rf"^Complete requests: +{n}$", out, re.M), out
        assert re.search(r"^Failed requests: +0$", out, re.M), out
        assert "Non-2xx" not in out, out

    def check(m):
        m.wait_for_unit("httpd.service")
        m.wait_for_open_port(80)
        m.wait_for_open_port(443)
        m.succeed("curl -sf http://localhost/index.html >/dev/null")

        with subtest(f"{m.name}: plain and cached load"):
            ab(m, 20000, "http://localhost/index.html")
            # Every process's requests reach the shared scoreboard and cache.
            total = status(m, "Total Accesses")[0]
            assert total >= 20000, total
            # The socache section is the second Cache*Count block.
            hits = status(m, "CacheRetrieveHitCount")
            assert max(hits) >= 19000, hits
            busy = status(m, "BusyWorkers")[0]
            print(f"accesses {total}, cache hits {hits}, busy {busy}")

        with subtest(f"{m.name}: TLS load and session resumption across processes"):
            ab(m, 2000, "https://localhost/index.html")
            # A session one process cached, another resumed. The event MPM
            # has few processes, so allow a few rounds for that to happen.
            for _ in range(5):
                m.succeed("truncate -s0 /var/log/httpd/access.log")
                m.succeed(
                    # HTTP/1.1: over HTTP/2 (event) curl would multiplex on
                    # one connection, so nothing would resume.
                    "curl -sfk --http1.1 -H 'Connection: close' "
                    + " ".join(["-o /dev/null https://localhost/index.html"] * 12)
                )
                lines = [l.split() for l in m.succeed("cat /var/log/httpd/access.log").splitlines()]
                print(lines)
                first = lines[0][0]
                if any(l[1] == "Resumed" and l[0] != first for l in lines):
                    break
            else:
                raise AssertionError("no session resumed in another process")

        with subtest(f"{m.name}: digest clients across processes"):
            m.succeed("truncate -s0 /var/log/httpd/access.log")
            for _ in range(40):
                m.succeed(
                    "curl -sf --digest -u alice:pw -H 'Connection: close' "
                    "http://localhost/secret/s.txt | grep -qx secret"
                )
            pids = {l.split()[0] for l in m.succeed("cat /var/log/httpd/access.log").splitlines()}
            print(f"digest requests served by {len(pids)} processes")
            assert len(pids) > 1, pids

        with subtest(f"{m.name}: graceful restarts under load"):
            gen = status(m, "ParentServerConfigGeneration")[0]
            ab(m, 30000, "http://localhost/index.html", background=True)
            m.sleep(2)
            m.succeed("systemctl reload httpd")
            m.sleep(2)
            m.succeed("systemctl reload httpd")
            m.wait_until_succeeds("! pgrep -x ab", timeout=300)
            abcheck(m.succeed("cat /tmp/ab.out"), 30000)
            assert status(m, "ParentServerConfigGeneration")[0] >= gen + 2
            m.succeed(
                "curl -sf --digest -u alice:pw http://localhost/secret/s.txt | grep -qx secret"
            )

        with subtest(f"{m.name}: mod_ldap caches per process"):
            m.succeed("curl -sf http://localhost/ldap-status >/dev/null")
            m.succeed("grep -q 'LDAPSharedCacheSize 500000 ignored' /var/log/httpd/error.log")

        with subtest(f"{m.name}: no process stopped"):
            log = m.succeed("cat /var/log/httpd/error.log")
            for bad in ["filc safety", "filc panic", "exit signal"]:
                assert bad not in log, log
            m.succeed("systemctl is-active httpd")

    start_all()
    check(prefork)
    check(event)
  '';
}
