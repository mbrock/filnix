"""Native against Fil-C PHP 8.5 on real applications. See README.md.

php-bench setup             build the DokuWiki, MediaWiki and WordPress fixtures
php-bench run               interleaved, repeated counter measurements
php-bench profile           perf record a warm server and break cycles down
php-bench report DIR        summarize a results directory
"""

import argparse
import ctypes
import datetime
import hashlib
import http.client
import json
import os
import re
import shutil
import signal
import statistics
import struct
import subprocess
import sys
import tempfile
import time

ENV = os.environ
STATE = ENV.get("PHP_BENCH_STATE") or os.path.join(
    ENV.get("XDG_CACHE_HOME") or os.path.expanduser("~/.cache"), "php-bench"
)
PORTS = {"dokuwiki": 18301, "mediawiki": 18302, "wordpress": 18303}
FIXTURE_VERSION = "2"

# Production-like settings, the same for every variant. The JIT is off so
# that native and Fil-C both run the interpreter; native-jit turns it on.
INI = {
    "opcache.enable": "1",
    "opcache.enable_cli": "1",
    "opcache.memory_consumption": "256",
    "opcache.interned_strings_buffer": "32",
    "opcache.max_accelerated_files": "20000",
    "opcache.jit": "disable",
    "opcache.jit_buffer_size": "0",
    "memory_limit": "512M",
    "max_execution_time": "0",
    "display_errors": "0",
    "log_errors": "1",
    "zend.assertions": "-1",
    "realpath_cache_size": "4M",
    "date.timezone": "UTC",
}

VARIANTS = {
    "native": ("PHP_BENCH_NATIVE", {}, {}),
    "filc": ("PHP_BENCH_FILC", {}, {}),
    # The staging toolchain (lib/filc-staging.json), which optimization
    # work builds on.
    "filc-staging": ("PHP_BENCH_FILC_STAGING", {}, {}),
    "filc-staging-zendalloc": ("PHP_BENCH_FILC_STAGING", {"USE_ZEND_ALLOC": "1"}, {}),
    "filc-staging-untracked": ("PHP_BENCH_FILC_STAGING", {"USE_TRACKED_ALLOC": "0"}, {}),
    # Levers: what Zend's allocator or an untracked malloc would buy Fil-C
    # (both give up per-value bounds, see docs/php.md), and what native
    # loses without its PCRE JIT or gains with opcache's JIT.
    "filc-zendalloc": ("PHP_BENCH_FILC", {"USE_ZEND_ALLOC": "1"}, {}),
    "filc-untracked": ("PHP_BENCH_FILC", {"USE_TRACKED_ALLOC": "0"}, {}),
    "native-nopcrejit": ("PHP_BENCH_NATIVE", {}, {"pcre.jit": "0"}),
    "native-jit": (
        "PHP_BENCH_NATIVE",
        {},
        {"opcache.jit": "tracing", "opcache.jit_buffer_size": "64M"},
    ),
}


def variant(name):
    """NAME from VARIANTS, or NAME=/path/to/php for another build.
    NAME=/path/to/php,/ini/dir loads the extensions configured in that
    directory, for an unwrapped PHP: php-with-extensions/lib from a build
    with the same PHP release and configuration."""
    if "=" in name:
        name, php = name.split("=", 1)
        php, _, scan = php.partition(",")
        return name, php, {"PHP_INI_SCAN_DIR": scan} if scan else {}, {}
    var, env, ini = VARIANTS[name]
    return name, os.path.join(ENV[var], "bin", "php"), env, ini


# Every PHP process runs on these CPUs; see README.md.
CPUS = ENV.get("PHP_BENCH_CPUS", "0-7,16-23")


def php_args(php, ini, log):
    args = ["taskset", "-c", CPUS, php]
    for k, v in {**INI, **ini, "error_log": log}.items():
        args += ["-d", f"{k}={v}"]
    return args


# ---------------------------------------------------------------- fixtures

LOREM = (
    "lorem ipsum dolor sit amet consectetur adipiscing elit sed do eiusmod "
    "tempor incididunt ut labore et dolore magna aliqua enim ad minim veniam "
    "quis nostrud exercitation ullamco laboris nisi aliquip ex ea commodo "
    "consequat duis aute irure in reprehenderit voluptate velit esse cillum "
    "fugiat nulla pariatur excepteur sint occaecat cupidatat non proident "
    "sunt culpa qui officia deserunt mollit anim id est laborum"
).split()


def words(seed, n):
    return " ".join(LOREM[(seed * 7 + i * 3) % len(LOREM)] for i in range(n))


def article(i, n_pages, style):
    """A deterministic article of a few KB: sections, links, lists, a table."""
    out = []
    link = {
        "doku": lambda j: f"[[wiki:p{j}|page {j}]]",
        "mw": lambda j: f"[[Article {j}|page {j}]]",
        "wp": lambda j: f'<a href="/?p={j}">page {j}</a>',
    }[style]
    for s in range(6):
        title = f"Section {s + 1} {words(i + s, 3)}"
        body = []
        for p in range(3):
            w = words(i * 13 + s * 5 + p, 40)
            j = (i + s + p) % n_pages + 1
            if style == "doku":
                body.append(f"{w} **bold {s}** //it {p}// {link(j)} ''code''.")
            elif style == "mw":
                body.append(f"{w} '''bold {s}''' ''it {p}'' {link(j)} <code>c</code>.")
            else:
                body.append(f"<!-- wp:paragraph --><p>{w} <strong>bold</strong> {link(j)}</p><!-- /wp:paragraph -->")
        items = [words(i + s + k, 6) for k in range(5)]
        if style == "doku":
            out.append(f"===== {title} =====")
            out += [b + "\n" for b in body]
            out += [f"  * {it}" for it in items] + [""]
            out.append("^ key ^ value ^ note ^")
            out += [f"| k{k} | {k * i} | {words(k, 3)} |" for k in range(5)] + [""]
        elif style == "mw":
            out.append(f"== {title} ==")
            out += [b + "\n" for b in body]
            out += [f"* {it}" for it in items] + [""]
            out.append('{| class="wikitable"\n! key !! value !! note')
            out += [f"|-\n| k{k} || {{{{#expr: {k} * {i}}}}} || {words(k, 3)}" for k in range(5)]
            out += ["|}", ""]
        else:
            out.append(f"<!-- wp:heading --><h2>{title}</h2><!-- /wp:heading -->")
            out += body
            out.append("<!-- wp:list --><ul>" + "".join(f"<li>{it}</li>" for it in items) + "</ul><!-- /wp:list -->")
    # A term that only three DokuWiki pages contain, so the search request
    # highlights a few hits instead of backtracking through every page's
    # filler text (every page contains "lorem").
    if style == "doku" and i in (4, 11, 23):
        out.insert(0, f"This page mentions the zephyrine survey from section {i % 6 + 1}.\n")
    if style == "mw":
        out.insert(0, f"{{{{Infobox|name=Article {i}|value={i * 3}}}}}\n")
        out.append(f"[[Category:Group {i % 4}]]")
    return "\n".join(out)


def run(args, **kw):
    print("+", " ".join(map(str, args))[:200], flush=True)
    return subprocess.run(args, check=True, **kw)


def copy_tree(src, dst):
    if os.path.exists(dst):
        shutil.rmtree(dst)
    run(["cp", "-r", "--reflink=auto", src, dst])
    run(["chmod", "-R", "u+w", dst])


def setup_dokuwiki(php):
    root = os.path.join(STATE, "dokuwiki")
    copy_tree(ENV["PHP_BENCH_DOKUWIKI"], root)
    # Nixpkgs' preload points the ACL and users files at its module's env.
    open(f"{root}/inc/preload.php", "w").write("<?php\n")
    open(f"{root}/conf/plugins.local.php", "w").write("<?php\n")
    open(f"{root}/conf/local.php", "w").write(
        "<?php\n$conf['title'] = 'Bench wiki';\n$conf['useacl'] = 0;\n"
        "$conf['userewrite'] = 0;\n$conf['plugin']['popularity']['autosubmit'] = 0;\n"
    )
    n = 30
    pages = f"{root}/data/pages"
    open(f"{pages}/start.txt", "w").write(
        "====== Bench wiki ======\n\n"
        + "\n".join(f"  * [[wiki:p{j}]] {words(j, 8)}" for j in range(1, n + 1))
        + "\n\nSee [[wiki:syntax]].\n"
    )
    for i in range(1, n + 1):
        open(f"{pages}/wiki/p{i}.txt", "w").write(f"====== Page {i} ======\n\n" + article(i, n, "doku"))
    run([php, "bin/indexer.php", "-q"], cwd=root)
    return root


MW_SETTINGS = """<?php
$IP = '{mw}';
require '{state}/mediawiki/LocalSettings.installed.php';
$wgCacheDirectory = '{state}/mediawiki/cache';
$wgJobRunRate = 0;
$wgEnableUploads = false;
$wgShowExceptionDetails = true;
wfLoadExtension( 'ParserFunctions' );
wfLoadExtension( 'Cite' );
"""


def setup_mediawiki(php):
    root = os.path.join(STATE, "mediawiki")
    mw = ENV["PHP_BENCH_MEDIAWIKI"]
    if os.path.exists(root):
        shutil.rmtree(root)
    os.makedirs(f"{root}/cache")
    os.makedirs(f"{root}/data")
    env = {**ENV, "MEDIAWIKI_CONFIG": f"{root}/LocalSettings.installed.php"}
    run(
        [php, f"{mw}/maintenance/run.php", "install", "--dbtype=sqlite", f"--dbpath={root}/data",
         "--dbname=bench", f"--server=http://127.0.0.1:{PORTS['mediawiki']}", "--scriptpath=",
         "--lang=en", "--pass=BenchAdminPassword1", f"--confpath={root}", "--skins=Vector",
         "Bench Wiki", "Admin"],
        env={**env, "MEDIAWIKI_CONFIG": "/nonexistent"},
    )
    os.rename(f"{root}/LocalSettings.php", f"{root}/LocalSettings.installed.php")
    settings = f"{root}/LocalSettings.php"
    open(settings, "w").write(MW_SETTINGS.format(mw=mw, state=STATE))
    env["MEDIAWIKI_CONFIG"] = settings
    n = 30
    pages = {
        "Template:Infobox": '{| class="infobox"\n! {{{name}}}\n|-\n| value: {{#if:{{{value|}}}|{{{value}}}|none}}\n|}',
        "Main Page": "Welcome to the bench wiki.\n\n"
        + "\n".join(f"* [[Article {j}]] {words(j, 8)}" for j in range(1, n + 1)),
    }
    for i in range(1, n + 1):
        pages[f"Article {i}"] = article(i, n, "mw") + f"\n\nCited.<ref>{words(i, 5)}</ref>\n\n<references />"
    for title, text in pages.items():
        run([php, f"{mw}/maintenance/run.php", "edit", "--summary=bench", title], input=text.encode(), env=env)
    # A second revision for histories and recent changes.
    for i in range(1, 6):
        run([php, f"{mw}/maintenance/run.php", "edit", "--summary=update", f"Article {i}"],
            input=(pages[f"Article {i}"] + "\n\nUpdated.").encode(), env=env)
    run([php, f"{mw}/maintenance/run.php", "runJobs"], env=env)
    return mw


WP_CONFIG = """<?php
define( 'DB_NAME', 'bench' );
define( 'DB_USER', '' );
define( 'DB_PASSWORD', '' );
define( 'DB_HOST', '' );
define( 'DB_CHARSET', 'utf8mb4' );
define( 'DB_COLLATE', '' );
define( 'DB_DIR', __DIR__ . '/wp-content/database/' );
define( 'DB_FILE', 'bench.sqlite' );
define( 'WP_HOME', 'http://127.0.0.1:{port}' );
define( 'WP_SITEURL', 'http://127.0.0.1:{port}' );
define( 'DISABLE_WP_CRON', true );
define( 'WP_HTTP_BLOCK_EXTERNAL', true );
define( 'AUTOMATIC_UPDATER_DISABLED', true );
define( 'WP_DEBUG', false );
{salts}
$table_prefix = 'wp_';
if ( ! defined( 'ABSPATH' ) ) define( 'ABSPATH', __DIR__ . '/' );
require_once ABSPATH . 'wp-settings.php';
"""

WP_INSTALL = r"""<?php
define( 'WP_INSTALLING', true );
require __DIR__ . '/wp-load.php';
require ABSPATH . 'wp-admin/includes/upgrade.php';
wp_install( 'Bench Blog', 'admin', 'admin@example.com', true, '', 'BenchAdminPassword1' );
switch_theme( 'twentytwentyfive' );
update_option( 'posts_per_page', 10 );
$cats = array();
foreach ( array( 'News', 'Notes', 'Essays', 'Reviews' ) as $c ) $cats[] = wp_create_category( $c );
$posts = json_decode( file_get_contents( $argv[1] ), true );
$ids = array();
foreach ( $posts as $i => $p ) {
	$ids[] = $id = wp_insert_post( array(
		'post_title' => $p['title'], 'post_content' => $p['content'], 'post_status' => 'publish',
		'post_date' => sprintf( '2026-%02d-%02d 12:00:00', 1 + $i % 9, 1 + $i % 27 ),
		'post_category' => array( $cats[ $i % 4 ] ), 'tags_input' => array( 'tag' . ( $i % 6 ) ),
	) );
	for ( $c = 0; $c < 4; $c++ ) wp_insert_comment( array(
		'comment_post_ID' => $id, 'comment_author' => "Reader $c", 'comment_approved' => 1,
		'comment_content' => "Comment $c on post $i: " . $p['title'],
	) );
}
echo json_encode( array( 'post' => $ids[3], 'cat' => $cats[1] ) );
"""


def setup_wordpress(php):
    root = os.path.join(STATE, "wordpress")
    copy_tree(ENV["PHP_BENCH_WORDPRESS"], root)
    copy_tree(ENV["PHP_BENCH_WP_THEME"], f"{root}/wp-content/themes/twentytwentyfive")
    plugin = f"{root}/wp-content/plugins/sqlite-database-integration"
    copy_tree(ENV["PHP_BENCH_WP_SQLITE"], plugin)
    dropin = open(f"{plugin}/db.copy").read()
    dropin = dropin.replace("{SQLITE_IMPLEMENTATION_FOLDER_PATH}", plugin).replace(
        "{SQLITE_PLUGIN}", "sqlite-database-integration/load.php")
    open(f"{root}/wp-content/db.php", "w").write(dropin)
    os.makedirs(f"{root}/wp-content/database")
    salts = "\n".join(
        f"define( '{k}', '{hashlib.sha256(k.encode()).hexdigest()}' );"
        for k in ["AUTH_KEY", "SECURE_AUTH_KEY", "LOGGED_IN_KEY", "NONCE_KEY",
                  "AUTH_SALT", "SECURE_AUTH_SALT", "LOGGED_IN_SALT", "NONCE_SALT"])
    open(f"{root}/wp-config.php", "w").write(WP_CONFIG.format(port=PORTS["wordpress"], salts=salts))
    open(f"{root}/bench-install.php", "w").write(WP_INSTALL)
    posts = [{"title": f"Post {i} {words(i, 4)}", "content": article(i, 20, "wp")} for i in range(1, 21)]
    with tempfile.NamedTemporaryFile("w", suffix=".json") as f:
        json.dump(posts, f)
        f.flush()
        out = run([php, "bench-install.php", f.name], cwd=root, capture_output=True, text=True).stdout
    os.unlink(f"{root}/bench-install.php")
    json.dump(json.loads(out[out.index("{"):]), open(f"{root}/bench-ids.json", "w"))
    return root


PROBE = """<?php
header('Content-Type: application/json');
$s = function_exists('opcache_get_status') ? opcache_get_status(false) : false;
echo json_encode(['php' => PHP_VERSION, 'sapi' => PHP_SAPI, 'pid' => getmypid(),
  'opcache' => $s ? $s['opcache_enabled'] : false,
  'hits' => $s ? $s['opcache_statistics']['hits'] : 0,
  'misses' => $s ? $s['opcache_statistics']['misses'] : 0,
  'jit' => $s && isset($s['jit']) ? $s['jit']['on'] : false,
  'zend_alloc' => getenv('USE_ZEND_ALLOC'), 'pcre_jit' => ini_get('pcre.jit')]);
"""


def cmd_setup(a):
    php = os.path.join(ENV["PHP_BENCH_NATIVE"], "bin", "php")
    os.makedirs(STATE, exist_ok=True)
    for app in a.apps:
        root = {"dokuwiki": setup_dokuwiki, "mediawiki": setup_mediawiki,
                "wordpress": setup_wordpress}[app](php)
        # The probe goes next to the app (MediaWiki is served from the store).
        probe_dir = os.path.join(STATE, "probe")
        os.makedirs(probe_dir, exist_ok=True)
        open(f"{probe_dir}/probe.php", "w").write(PROBE)
        if app != "mediawiki":
            shutil.copy(f"{probe_dir}/probe.php", f"{root}/__bench_probe.php")
    open(os.path.join(STATE, "VERSION"), "w").write(FIXTURE_VERSION)


# ---------------------------------------------------------------- apps


def app_config(app):
    """(document root, extra env, router script, request mix)."""
    if app == "dokuwiki":
        root = os.path.join(STATE, "dokuwiki")
        urls = [
            "/doku.php?id=start",
            "/doku.php?id=wiki:syntax",
            "/doku.php?id=wiki:p5",
            "/doku.php?id=wiki:p12",
            "/doku.php?id=wiki:syntax&do=export_xhtml",
            "/doku.php?id=start&do=index",
            "/doku.php?id=start&do=search&q=zephyrine",
            "/doku.php?id=wiki:p7&do=edit",
            "/doku.php?id=start&do=recent",
            "/lib/exe/css.php",
            "/lib/exe/js.php",
            "/feed.php",
        ]
        return root, {}, None, urls
    if app == "mediawiki":
        root = ENV["PHP_BENCH_MEDIAWIKI"]
        urls = [
            "/index.php?title=Main_Page",
            "/index.php?title=Article_1",
            "/index.php?title=Article_7",
            "/index.php?title=Article_12",
            "/index.php?title=Article_2&action=history",
            "/index.php?title=Article_3&action=edit",
            "/index.php?title=Special:RecentChanges",
            "/index.php?title=Special:Search&search=lorem+tempor&fulltext=1",
            "/index.php?title=Special:AllPages",
            "/index.php?title=Category:Group_1",
            "/api.php?action=query&prop=revisions&titles=Article_4&rvprop=content&rvslots=main&format=json",
            "/load.php?modules=startup&only=scripts&skin=vector-2022&lang=en",
        ]
        # The router serves the probe, which cannot go in the store.
        env = {"MEDIAWIKI_CONFIG": os.path.join(STATE, "mediawiki", "LocalSettings.php")}
        return root, env, os.path.join(STATE, "probe", "router.php"), urls
    if app == "wordpress":
        root = os.path.join(STATE, "wordpress")
        ids = json.load(open(f"{root}/bench-ids.json"))
        urls = [
            "/",
            f"/?p={ids['post']}",
            f"/?p={ids['post'] + 5}",
            "/?page_id=2",
            f"/?cat={ids['cat']}",
            "/?tag=tag2",
            "/?m=202603",
            "/?s=lorem",
            "/?feed=rss2",
            "/?rest_route=/wp/v2/posts",
            "/wp-login.php",
        ]
        return root, {}, None, urls
    raise KeyError(app)


ROUTER = """<?php
if (parse_url($_SERVER['REQUEST_URI'], PHP_URL_PATH) === '/__bench_probe.php') {
  require __DIR__ . '/probe.php';
  return true;
}
return false;
"""

# ---------------------------------------------------------------- counters

libc = ctypes.CDLL(None, use_errno=True)
# Threads a counted thread starts inherit its counters, and their counts
# fold back into it when they exit: Fil-C starts short-lived threads.
INHERIT, EXCL_USER, EXCL_KERNEL, EXCL_HV = 1 << 1, 1 << 4, 1 << 5, 1 << 6
EVENTS = {
    "cycles_u": (0, 0, EXCL_KERNEL | EXCL_HV),
    "instructions_u": (0, 1, EXCL_KERNEL | EXCL_HV),
    "cycles_k": (0, 0, EXCL_USER | EXCL_HV),
    "task_clock_ns": (1, 1, 0),
}


class Counters:
    """Counters on every thread of a process, read as deltas. Threads that
    start later inherit them from the thread that starts them, and reading
    a counter includes its inheritors, so attach only once. FUGC's marker
    threads count too, so this is the CPU cost of a request."""

    def __init__(self, pid):
        self.pid = pid
        self.fds = {}
        self.attach()

    def attach(self):
        for tid in map(int, os.listdir(f"/proc/{self.pid}/task")):
            if tid in self.fds:
                continue
            fds = {}
            for name, (typ, config, flags) in EVENTS.items():
                attr = ctypes.create_string_buffer(136)
                # type, size, config, sample_period, sample_type, read_format
                # (TOTAL_TIME_ENABLED | TOTAL_TIME_RUNNING), flag bits
                struct.pack_into("IIQQQQQ", attr, 0, typ, 136, config, 0, 0, 3, flags | INHERIT)
                fd = libc.syscall(ctypes.c_long(298), attr, ctypes.c_long(tid),
                                  ctypes.c_long(-1), ctypes.c_long(-1), ctypes.c_long(8))
                if fd < 0 and ctypes.get_errno() == 3:
                    break  # the thread exited
                if fd < 0:
                    raise OSError(ctypes.get_errno(), f"perf_event_open {name} on {tid}")
                fds[name] = fd
            self.fds[tid] = fds

    def read(self):
        out = {}
        for tid, fds in self.fds.items():
            for name, fd in fds.items():
                try:
                    v, en, ru = struct.unpack("QQQ", os.read(fd, 24))
                except OSError:
                    continue
                out[(tid, name)] = (v, en, ru)
        return out

    @staticmethod
    def delta(a, b):
        tot = {n: 0.0 for n in EVENTS}
        mux = False
        for k, (v, en, ru) in b.items():
            v0, en0, ru0 = a.get(k, (0, 0, 0))
            dv, de, dr = v - v0, en - en0, ru - ru0
            if dr and dr < de:
                mux = True
                dv = dv * de / dr
            tot[k[1]] += dv
        tot["threads"] = len({t for t, _ in b})
        tot["multiplexed"] = mux
        return tot


def busy_now(seconds=2.0):
    """Share of the machine's CPUs busy over the next few seconds."""
    t0, i0 = cpu_busy()
    time.sleep(seconds)
    t1, i1 = cpu_busy()
    return 1 - (i1 - i0) / (t1 - t0) if t1 > t0 else 0.0


def wait_quiet(a, what):
    """With --max-busy, hold each measurement until the machine is quiet;
    give up after --wait minutes."""
    if a.max_busy is None:
        return None
    deadline = time.time() + a.wait * 60
    while True:
        b = busy_now()
        if b <= a.max_busy:
            return b
        if time.time() > deadline:
            sys.exit(f"machine {b:.0%} busy (above --max-busy {a.max_busy:.0%}) "
                     f"for {a.wait} min before {what}; stopping")
        print(f"machine {b:.0%} busy, waiting before {what}", flush=True)
        time.sleep(30)


def others_busy(total, idle, own_cpu_s):
    """The machine's busy share less this measurement's own CPU time
    (the server and, under Fil-C, its GC threads)."""
    if not total:
        return None
    return max(0.0, 1 - idle / total - own_cpu_s * os.sysconf("SC_CLK_TCK") / total)


def cpu_busy():
    f = open("/proc/stat").readline().split()[1:]
    vals = list(map(int, f))
    idle = vals[3] + vals[4]
    return sum(vals), idle


# ---------------------------------------------------------------- server


def get(port, url, timeout=600):
    c = http.client.HTTPConnection("127.0.0.1", port, timeout=timeout)
    c.request("GET", url, headers={"Host": f"127.0.0.1:{port}", "Accept-Encoding": "identity"})
    r = c.getresponse()
    body = r.read()
    c.close()
    return r.status, body


class Server:
    def __init__(self, app, var, logdir):
        self.app = app
        self.name, php, env, ini = variant(var)
        root, appenv, router, self.urls = app_config(app)
        os.makedirs(os.path.join(STATE, "probe"), exist_ok=True)
        open(os.path.join(STATE, "probe", "probe.php"), "w").write(PROBE)
        if not router:
            open(os.path.join(root, "__bench_probe.php"), "w").write(PROBE)
        self.port = PORTS[app]
        os.makedirs(logdir, exist_ok=True)
        self.log = os.path.join(logdir, f"{app}-{self.name}.log")
        args = php_args(php, ini, self.log) + ["-S", f"127.0.0.1:{self.port}", "-t", root]
        if router:
            open(router, "w").write(ROUTER)
            args.append(router)
        self.proc = subprocess.Popen(
            args, cwd=root, env={**ENV, **appenv, **env},
            stdout=subprocess.DEVNULL, stderr=open(self.log + ".server", "a"),
            start_new_session=True)
        for _ in range(600):
            try:
                st, body = get(self.port, "/__bench_probe.php", timeout=5)
                if st == 200:
                    self.probe_info = json.loads(body)
                    # The ports are fixed (the fixtures' URLs contain them);
                    # make sure this is our server, not someone else's.
                    if self.probe_info.get("pid") != self.proc.pid:
                        self.stop()
                        raise RuntimeError(f"port {self.port} is served by pid "
                                           f"{self.probe_info.get('pid')}, not ours")
                    break
            except (OSError, http.client.HTTPException):
                pass
            if self.proc.poll() is not None:
                raise RuntimeError(f"{self.name} server for {app} exited; see {self.log}.server")
            time.sleep(0.1)
        else:
            raise RuntimeError(f"{self.name} server for {app} did not start")
        assert self.probe_info["opcache"], self.probe_info

    def request(self, url):
        st, body = get(self.port, url)
        bad = st not in (200, 302) or re.search(rb"Fatal error|Fil-C|filc panic|Uncaught", body[:200000])
        if bad:
            raise RuntimeError(f"{self.name} {self.app} {url}: {st} {body[:500]!r}")
        return st, body

    def stop(self):
        os.killpg(self.proc.pid, signal.SIGTERM)
        try:
            self.proc.wait(10)
        except subprocess.TimeoutExpired:
            os.killpg(self.proc.pid, signal.SIGKILL)
            self.proc.wait()


def session(app, var, a, out):
    """Start a server, warm it, then measure each URL in turn."""
    s = Server(app, var, os.path.join(out, "logs"))
    try:
        for _ in range(a.warmup):
            for u in s.urls:
                s.request(u)
        load0, busy0 = open("/proc/loadavg").read().split()[:3], cpu_busy()
        ctr = Counters(s.proc.pid)
        res = {}
        for u in s.urls:
            walls = []
            c0 = ctr.read()
            for _ in range(a.reps):
                t = time.perf_counter()
                st, body = s.request(u)
                walls.append(time.perf_counter() - t)
            d = Counters.delta(c0, ctr.read())
            res[u] = {k: (v / a.reps if isinstance(v, float) else v) for k, v in d.items()}
            res[u].update(wall_s=statistics.median(walls), status=st, bytes=len(body))
        busy1 = cpu_busy()
        total, idle = busy1[0] - busy0[0], busy1[1] - busy0[1]
        st, body = get(s.port, "/__bench_probe.php")
        return {
            "app": app, "variant": s.name, "urls": res, "probe": json.loads(body),
            "probe_start": s.probe_info, "loadavg_start": load0,
            "loadavg_end": open("/proc/loadavg").read().split()[:3],
            "machine_busy": 1 - idle / total if total else None,
            "others_busy": others_busy(total, idle, sum(x["task_clock_ns"] for x in res.values()) * a.reps / 1e9),
            "time": datetime.datetime.now().isoformat(timespec="seconds"),
        }
    finally:
        s.stop()


def zend_bench(var, out):
    name, php, env, ini = variant(var)
    busy0 = cpu_busy()
    with tempfile.NamedTemporaryFile(suffix=".csv") as f:
        t = time.perf_counter()
        p = run(["perf", "stat", "-x,", "-o", f.name, "-e",
                 "cycles:u,instructions:u,cycles:k,task-clock", "--"]
                + php_args(php, ini, os.path.join(out, "logs", f"bench-{name}.log"))
                + [ENV["PHP_BENCH_ZEND"]], env={**ENV, **env}, capture_output=True, text=True)
        wall = time.perf_counter() - t
        ctr = {}
        for line in open(f.name):
            parts = line.strip().split(",")
            if len(parts) > 2 and parts[0] and parts[0][0].isdigit():
                ctr[parts[2].replace(":", "_").replace("-", "_")] = float(parts[0])
    sections = dict(re.findall(r"^(\S+)\s+([\d.]+)$", p.stdout, re.M))
    busy1 = cpu_busy()
    total, idle = busy1[0] - busy0[0], busy1[1] - busy0[1]
    return {"app": "bench.php", "variant": name, "wall_s": wall, "counters": ctr,
            "machine_busy": 1 - idle / total if total else None,
            "others_busy": others_busy(total, idle, ctr.get("task_clock", 0) / 1e3),
            "sections": {k: float(v) for k, v in sections.items()},
            "loadavg": open("/proc/loadavg").read().split()[:3]}


def lock():
    """One measurement at a time on this machine: runs share the fixtures'
    ports, and concurrent runs would disturb each other's counts."""
    import fcntl
    os.makedirs(STATE, exist_ok=True)
    f = open(os.path.join(STATE, "lock"), "w")
    try:
        fcntl.flock(f, fcntl.LOCK_EX | fcntl.LOCK_NB)
    except BlockingIOError:
        print(f"waiting for another php-bench run ({STATE}/lock)", flush=True)
        fcntl.flock(f, fcntl.LOCK_EX)
    return f


def cmd_run(a):
    _lock = lock()
    if a.cmd == "quiet":
        a.variants = ["native", "filc", "filc-staging"] + a.extra
    out = a.out or os.path.join(STATE, "results", datetime.datetime.now().strftime("%Y%m%d-%H%M%S"))
    os.makedirs(os.path.join(out, "logs"), exist_ok=True)
    meta = {"argv": sys.argv, "variants": {v: variant(v)[1:] for v in a.variants},
            "max_busy": a.max_busy, "rounds": a.rounds, "reps": a.reps,
            "ini": INI, "cpus": CPUS, "host": os.uname().nodename, "nproc": os.cpu_count(),
            "cpu": next(l.split(":", 1)[1].strip() for l in open("/proc/cpuinfo") if l.startswith("model name"))}
    json.dump(meta, open(os.path.join(out, "meta.json"), "w"), indent=1)
    results = open(os.path.join(out, "results.jsonl"), "a")
    for r in range(a.rounds):
        # Alternate the order so drift in machine load hits both variants.
        order = a.variants if r % 2 == 0 else a.variants[::-1]
        for app in a.apps:
            for var in order:
                busy_before = wait_quiet(a, f"round {r} {app} {var}")
                rec = zend_bench(var, out) if app == "bench.php" else session(app, var, a, out)
                rec["round"] = r
                rec["busy_before"] = busy_before
                # Flag a measurement the machine's load disturbed anyway.
                rec["noisy"] = a.max_busy is not None and (rec.get("others_busy") or 0) > a.max_busy
                results.write(json.dumps(rec) + "\n")
                results.flush()
                print(f"round {r} {app} {var}: {summary_line(rec)}", flush=True)
    cmd_report(argparse.Namespace(dir=out))


def summary_line(rec):
    if rec["app"] == "bench.php":
        return f"{rec['counters'].get('cycles_u', 0) / 1e9:.2f} Gcycles:u, {rec['sections'].get('Total', 0):.3f} s"
    u = rec["urls"].values()
    return (f"{sum(x['cycles_u'] for x in u) / 1e9:.3f} Gcycles:u/pass, "
            f"{sum(x['wall_s'] for x in u) * 1000:.0f} ms/pass, others busy {rec['others_busy']:.0%}")


# ---------------------------------------------------------------- report


def cmd_report(a):
    recs = [json.loads(l) for l in open(os.path.join(a.dir, "results.jsonl"))]
    variants = list(dict.fromkeys(r["variant"] for r in recs))
    base = "native" if "native" in variants else variants[0]
    apps = list(dict.fromkeys(r["app"] for r in recs))
    md = [f"# PHP benchmark {os.path.basename(os.path.abspath(a.dir))}", ""]
    md.append(f"Rounds: {1 + max(r['round'] for r in recs)}. Medians across rounds; "
              f"ratios are against {base}. cycles:u and instructions:u count every "
              "thread of the server (Fil-C's GC threads included); wall is the "
              "median request latency.")
    md.append("")
    noisy = sum(1 for r in recs if r.get("noisy"))
    if noisy:
        md.append(f"**{noisy} of {len(recs)} measurements ran while the machine was busier "
                  "than --max-busy; their cycle counts are suspect.**")
        md.append("")
    busy = [r.get("others_busy", r["machine_busy"]) for r in recs if r.get("machine_busy") is not None]
    loads = [float(r.get("loadavg_start", r.get("loadavg", [0]))[0]) for r in recs]
    md.append(f"Machine: other work kept {min(busy):.0%}–{max(busy):.0%} of all CPUs busy during measurement, "
              f"load average {min(loads):.1f}–{max(loads):.1f}." if busy else "")
    md.append("")
    md.append("## Per application (sum over the request mix)")
    md.append("")
    cols = ["cycles_u", "instructions_u", "cycles_k", "task_clock_ns", "wall_s"]
    md.append("| app | variant | Gcycles:u | Ginstr:u | IPC | Gcycles:k | CPU ms | wall ms | ratio cycles:u (min–max) | ratio best cycles:u | ratio instr | ratio wall |")
    md.append("|---|---|---|---|---|---|---|---|---|---|---|---|")
    summary = {}
    for app in apps:
        per = {}
        for v in variants:
            rs = [r for r in recs if r["app"] == app and r["variant"] == v]
            if not rs:
                continue
            if app == "bench.php":
                tot = [{"cycles_u": r["counters"].get("cycles_u", 0),
                        "instructions_u": r["counters"].get("instructions_u", 0),
                        "cycles_k": r["counters"].get("cycles_k", 0),
                        "task_clock_ns": r["counters"].get("task_clock", 0) * 1e6,
                        "wall_s": r["wall_s"]} for r in rs]
            else:
                tot = [{c: sum(u[c] for u in r["urls"].values()) for c in cols} for r in rs]
            per[v] = {c: [t[c] for t in tot] for c in cols}
            per[v]["round"] = [r["round"] for r in rs]
        for v, d in per.items():
            med = {c: statistics.median(d[c]) for c in cols}
            b = per.get(base)
            rat = ""
            if b and v != base:
                bm = {c: statistics.median(b[c]) for c in cols}
                # Ratios within a round, whose variants ran back to back.
                br = dict(zip(b["round"], b["cycles_u"]))
                rs_ = [x / br[r] for r, x in zip(d["round"], d["cycles_u"]) if r in br]
                # Load only adds cycles (SMT siblings, shared L3), so each
                # variant's fewest cycles is its least disturbed measurement.
                rat = (f"{med['cycles_u'] / bm['cycles_u']:.2f} ({min(rs_):.2f}–{max(rs_):.2f}) | "
                       f"{min(d['cycles_u']) / min(b['cycles_u']):.2f} | "
                       f"{med['instructions_u'] / bm['instructions_u']:.2f} | {med['wall_s'] / bm['wall_s']:.2f}")
                summary.setdefault(app, {})[v] = {
                    "cycles_u": med["cycles_u"] / bm["cycles_u"],
                    "best_cycles_u": min(d["cycles_u"]) / min(b["cycles_u"]),
                    "instructions_u": med["instructions_u"] / bm["instructions_u"]}
            else:
                rat = " | | | "
            md.append(f"| {app} | {v} | {med['cycles_u'] / 1e9:.3f} | {med['instructions_u'] / 1e9:.3f} | "
                      f"{med['instructions_u'] / med['cycles_u']:.2f} | {med['cycles_k'] / 1e9:.3f} | "
                      f"{med['task_clock_ns'] / 1e6:.0f} | {med['wall_s'] * 1e3:.0f} | {rat} |")
    md.append("")
    md.append("## Per request (median cycles:u ratio against " + base + ")")
    for app in apps:
        if app == "bench.php":
            continue
        md.append("")
        md.append(f"### {app}")
        md.append("")
        md.append("| request | " + " | ".join(f"{v} Mcycles:u" for v in variants) + " | "
                  + " | ".join(f"{v}/{base}" for v in variants if v != base) + " | bytes |")
        md.append("|---|" + "---|" * (2 * len(variants)))
        urls = list(next(r for r in recs if r["app"] == app)["urls"])
        for u in urls:
            med = {}
            for v in variants:
                xs = [r["urls"][u]["cycles_u"] for r in recs if r["app"] == app and r["variant"] == v]
                if xs:
                    med[v] = statistics.median(xs)
            sizes = {r["urls"][u]["bytes"] for r in recs if r["app"] == app}
            md.append(f"| `{u}` | " + " | ".join(f"{med[v] / 1e6:.1f}" for v in variants if v in med) + " | "
                      + " | ".join(f"{med[v] / med[base]:.2f}" for v in variants if v != base and v in med)
                      + f" | {min(sizes)}–{max(sizes)} |")
    bench = [r for r in recs if r["app"] == "bench.php"]
    if bench:
        md += ["", "## Zend/bench.php sections (median seconds)", ""]
        secs = list(bench[0]["sections"])
        md.append("| section | " + " | ".join(variants) + " | " + " | ".join(f"{v}/{base}" for v in variants if v != base) + " |")
        md.append("|---|" + "---|" * (2 * len(variants) - 1))
        for s in secs:
            med = {v: statistics.median([r["sections"].get(s, 0) for r in bench if r["variant"] == v])
                   for v in variants if any(r["variant"] == v for r in bench)}
            md.append(f"| {s} | " + " | ".join(f"{med[v]:.3f}" for v in med) + " | "
                      + " | ".join(f"{med[v] / med[base]:.1f}" if med[base] else "" for v in med if v != base) + " |")
    open(os.path.join(a.dir, "summary.md"), "w").write("\n".join(md) + "\n")
    json.dump(summary, open(os.path.join(a.dir, "summary.json"), "w"), indent=1)
    print("\n".join(md))


# ---------------------------------------------------------------- profile

STRIP = re.compile(r"^pizlonated(?:FIP?\d*|DA|DO)?_")
CATEGORIES = [
    # (category, dso regex, symbol regex); first match wins.
    # Kernel time spent on memory (faults on fresh pages, zeroing, mmap and
    # munmap, TLB shootdowns) apart from the rest (syscalls and I/O).
    ("kernel memory (faults, zeroing, mmap)", r"^\[kernel\]$",
     r"page|folio|clear_|_pte|pmd|pud|mmap|munmap|madvise|vma|tlb|zap_|lru|memcg|mm_|mmu|rmap|anon|alloc_pages|free_pages|unmap|irqentry|exc_|kernel_init|fault|rmqueue|freelist"),
    ("kernel syscalls & I/O", r"^\[kernel\]$", None),
    ("PCRE", r"pcre", None),
    # Native PCRE's JIT-compiled patterns (perf names their mapping [JIT]).
    ("PCRE", r"^\[JIT\]", None),
    ("PCRE", None, r"^(php_pcre|pcre_get_compiled|pcre2_)"),
    ("SQLite", r"sqlite", None),
    ("FUGC (GC)", r"libpizlo", r"fugc|mark|sweep|scan|verse_heap_.*(sweep|mark|collect)|pas_.*(scaven|decommit)|stop_the_world|soft_handshake|safepoint|pollcheck"),
    ("Fil-C allocator (libpas)", r"libpizlo", r"^(pas_|bmalloc|verse_heap|filc_allocate|filc_free|filc_reallocate|filc_object_|zgc_|filc_.*alloc)"),
    ("Fil-C memcpy/memmove/memset", r"libpizlo|libyolo", r"mem(move|cpy|set)"),
    ("Fil-C runtime (other libpizlo)", r"libpizlo|libyolo|ld-fil", None),
    ("zend_alloc / tracked malloc", None, r"^(_?e(malloc|free|realloc|calloc|strdup|strndup)|_safe_e|zend_mm_|__zend_(malloc|calloc|realloc)|tracked_|zend_alloc|_zend_mm)"),
    ("libc malloc", r"libc", r"^(malloc|free|realloc|calloc|_int_|cfree|tcache|__libc_(malloc|free|realloc|calloc))|malloc_consolidate|unlink_chunk"),
    ("libc mem/str", r"libc", None),
    ("VM handlers & dispatch", None, r"(^ZEND_.*_(HANDLER|HELPER)|^execute_ex$|^zend_vm_|^execute_ex|_helper_SPEC|^zend_execute$|^i_init_|^zend_init_func_execute_data|^init_func_run_time_cache|^zend_fetch_dimension|^zend_fetch_property|^zend_assign_to|^zend_binary_assign|^zend_pre_|^zend_post_|^zend_fetch_var|^zend_check_type|^zend_verify_)"),
    ("Zend GC (cycle collector)", None, r"^(gc_|zend_gc_|zend_get_gc_buffer|zend_std_get_gc)"),
    ("Zend hash tables", None, r"^(_?zend_hash|zend_symtable|_zend_handle_numeric|zend_array_|zend_new_array|_zend_new_array|zend_ht_|zend_hash)"),
    ("Zend strings", None, r"^(zend_string|_?zend_str|zend_interned|zend_new_interned|smart_str|zend_.*_concat|concat_function|zend_strpprintf|zend_vspprintf|zend_print|php_printf|xbuf|zend_inline_hash|zend_hash_func|zend_string_tolower|zend_str_tolower|zend_memnstr|zend_binary_str)"),
    ("Zend values/refcount/dtor", None, r"^(zval_|rc_dtor|zend_objects_store|zend_object_std|zend_objects_|zend_std_|zend_ref|_zval|i_zval|zend_array_destroy|zend_array_dup|zend_list_free|zend_copy_)"),
    ("Zend runtime (other)", None, r"^(zend_|_zend_|ZEND_|compare_function|is_identical|zendi_|increment_function|add_function|sub_function|mul_function|convert_to|_convert_to|zend_operators|instanceof|string_compare|zend_compare)"),
    ("PHP functions & extensions", None, r"^(php_|zif_|ZEND_FUNCTION|_php_|spl_|date_|timelib_|mb|json_|ps_|sapi_|xml|lxb_|dom_|intl|php_stream|_php_stream|plain_wrapper|virtual_|tsrm|uri|ctype|ap_php|sqlite|pdo_|zim_)"),
]


def categorize(dso, sym):
    s = STRIP.sub("", sym)
    for cat, dre, sre in CATEGORIES:
        if dre and not re.search(dre, dso):
            continue
        if sre and not re.search(sre, s):
            continue
        return cat
    if re.search(r"/php$|php-", dso):
        return "PHP functions & extensions"
    return "other libraries"


def cmd_profile(a):
    _lock = lock()
    out = a.out or os.path.join(STATE, "results", "profile-" + datetime.datetime.now().strftime("%Y%m%d-%H%M%S"))
    os.makedirs(os.path.join(out, "logs"), exist_ok=True)
    for app in a.apps:
        for var in a.variants:
            name = variant(var)[0]
            data = os.path.join(out, f"{app}-{name}.perf.data")
            if app == "bench.php":
                _, php, env, ini = variant(var)
                run(["perf", "record", "-e", "cycles", "-c", str(a.period), "-o", data, "--"]
                    + php_args(php, ini, os.devnull) + [ENV["PHP_BENCH_ZEND"]],
                    env={**ENV, **env}, stdout=subprocess.DEVNULL)
            else:
                s = Server(app, var, os.path.join(out, "logs"))
                try:
                    for _ in range(a.warmup):
                        for u in s.urls:
                            s.request(u)
                    # perf record -p sometimes wrote only its header for
                    # Fil-C MediaWiki (threads coming and going while it
                    # attaches); record again when it got no samples.
                    for attempt in range(3):
                        rec = subprocess.Popen(["perf", "record", "-e", "cycles", "-c", str(a.period),
                                                "-p", str(s.proc.pid), "-o", data],
                                               stderr=open(data + ".log", "a"))
                        time.sleep(1)
                        for _ in range(a.passes):
                            for u in s.urls:
                                s.request(u)
                        rec.send_signal(signal.SIGINT)
                        rec.wait()
                        if breakdown(data, out, app, name, a.period, a.passes):
                            break
                        print(f"no samples for {app} {name}, recording again", flush=True)
                finally:
                    s.stop()
                continue
            breakdown(data, out, app, name, a.period, 1)
    cmd_profile_report(argparse.Namespace(dir=out))


def breakdown(data, out, app, name, period, passes):
    rep = subprocess.run(["perf", "report", "-i", data, "--stdio", "--no-children", "-F", "sample,dso,sym",
                          "--sort", "dso,sym", "-g", "none", "--percent-limit", "0", "-t", "\t"],
                         capture_output=True, text=True).stdout
    syms = []
    for line in rep.splitlines():
        if not line.strip() or line.startswith("#"):
            continue
        parts = [p.strip() for p in line.split("\t")]
        if len(parts) < 3:
            continue
        samples, dso, sym = int(parts[0]), parts[1], parts[2]
        kernel = sym.startswith("[k]")
        sym = re.sub(r"^\[[.k]\]\s*", "", sym)
        if kernel:
            dso = "[kernel]"
        syms.append({"samples": samples, "dso": os.path.basename(dso), "sym": STRIP.sub("", sym),
                     "cat": categorize(dso, sym)})
    json.dump({"app": app, "variant": name, "period": period, "passes": passes, "symbols": syms},
              open(os.path.join(out, f"{app}-{name}.profile.json"), "w"))
    return sum(s["samples"] for s in syms)


def cmd_profile_report(a):
    profs = [json.load(open(os.path.join(a.dir, f))) for f in sorted(os.listdir(a.dir)) if f.endswith(".profile.json")]
    profs = [p for p in profs if p["symbols"]]
    md = [f"# PHP profile {os.path.basename(os.path.abspath(a.dir))}", "",
          "Self cycles (user and kernel) by category, from `perf record -e cycles -c PERIOD` on the "
          "warm server over the whole request mix. Gcycles are absolute, so categories compare "
          "directly between variants. Fil-C's inline bounds and capability checks are inside the "
          "functions that execute them and are not a separate category.", ""]
    apps = list(dict.fromkeys(p["app"] for p in profs))
    for app in apps:
        ps = [p for p in profs if p["app"] == app]
        cats = {}
        for p in ps:
            for s in p["symbols"]:
                cats.setdefault(s["cat"], {}).setdefault(p["variant"], 0)
                cats[s["cat"]][p["variant"]] += s["samples"] * p["period"]
        # Gcycles per pass over the request mix, so runs with different
        # pass counts or periods compare.
        tot = {p["variant"]: sum(s["samples"] for s in p["symbols"]) * p["period"] / p.get("passes", 1)
               for p in ps}
        for c in cats:
            for p in ps:
                if p["variant"] in cats[c]:
                    cats[c][p["variant"]] /= p.get("passes", 1)
        vs = sorted((p["variant"] for p in ps), key=lambda v: (v != "native", v))
        ps.sort(key=lambda p: vs.index(p["variant"]))
        base, others = vs[0], vs[1:]
        md += [f"## {app}", "", "Gcycles per pass over the request mix; Δ is against "
               f"{base}, and share is Δ as a part of the whole gap.", "",
               "| category | " + " | ".join(f"{v} Gcyc | {v} %" for v in vs) + " | "
               + " | ".join(f"Δ {v} | share" for v in others) + " |",
               "|---|" + "---|---|" * len(vs) + "---|---|" * len(others)]
        order = sorted(cats, key=lambda c: -max(cats[c].values()))
        for c in order:
            row = f"| {c} | " + " | ".join(
                f"{cats[c].get(v, 0) / 1e9:.3f} | {100 * cats[c].get(v, 0) / tot[v]:.1f}" for v in vs)
            for v in others:
                d = cats[c].get(v, 0) - cats[c].get(base, 0)
                gap = tot[v] - tot[base]
                row += f" | {d / 1e9:+.3f} | {100 * d / gap:.0f}%" if gap else " | |"
            md.append(row + " |")
        md.append("| **total** | " + " | ".join(f"{tot[v] / 1e9:.3f} | 100" for v in vs) + " | "
                  + " | ".join(f"{(tot[v] - tot[base]) / 1e9:+.3f} ({tot[v] / tot[base]:.1f}×) | 100%"
                               for v in others) + " |")
        for p in ps:
            t = sum(s["samples"] for s in p["symbols"])
            md += ["", f"Top symbols, {app} {p['variant']}:", "",
                   "| % | category | symbol | dso |", "|---|---|---|---|"]
            for s in sorted(p["symbols"], key=lambda s: -s["samples"])[:25]:
                md.append(f"| {100 * s['samples'] / t:.1f} | {s['cat']} | `{s['sym'][:70]}` | {s['dso']} |")
        md.append("")
    open(os.path.join(a.dir, "profile.md"), "w").write("\n".join(md) + "\n")
    print("\n".join(md))


def main():
    # Turn SIGTERM into an exception so servers are stopped on the way out.
    signal.signal(signal.SIGTERM, lambda *_: sys.exit(143))
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = p.add_subparsers(dest="cmd", required=True)
    s = sub.add_parser("setup")
    s.add_argument("--apps", nargs="+", default=list(PORTS))
    for name in ("run", "quiet", "profile"):
        s = sub.add_parser(name)
        if name == "quiet":
            s.description = ("Consolidated run for a quiet machine: every application, "
                             "native, filc and filc-staging plus the EXTRA variants, 10 rounds, "
                             "each measurement held until the machine is under --max-busy.")
            s.add_argument("extra", nargs="*", metavar="EXTRA", help="NAME=/path/to/bin/php[,INI_DIR]")
        s.add_argument("--apps", nargs="+", default=list(PORTS) + ["bench.php"])
        if name != "quiet":
            s.add_argument("--variants", nargs="+", default=["native", "filc", "filc-staging"],
                           help=f"from {', '.join(VARIANTS)} or NAME=/path/to/bin/php[,INI_DIR]")
        s.add_argument("--warmup", type=int, default=3, help="passes over the mix before measuring")
        s.add_argument("--out")
        if name in ("run", "quiet"):
            s.add_argument("--max-busy", type=float, default=0.15 if name == "quiet" else None,
                           help="hold each measurement until at most this share of the CPUs is busy, "
                                "and flag measurements that ran busier")
            s.add_argument("--wait", type=float, default=30, help="minutes to wait for a quiet machine")
            s.add_argument("--rounds", type=int, default=10 if name == "quiet" else 5)
            s.add_argument("--reps", type=int, default=5, help="requests per URL per round")
        else:
            s.add_argument("--passes", type=int, default=5)
            s.add_argument("--period", type=int, default=200003)
    s = sub.add_parser("report")
    s.add_argument("dir")
    s = sub.add_parser("profile-report")
    s.add_argument("dir")
    a = p.parse_args()
    if a.cmd in ("run", "quiet", "profile") and any(x != "bench.php" for x in a.apps):
        vf = os.path.join(STATE, "VERSION")
        if not os.path.exists(vf) or open(vf).read().strip() != FIXTURE_VERSION:
            sys.exit(f"no current fixtures in {STATE}; run php-bench setup")
    {"setup": cmd_setup, "run": cmd_run, "quiet": cmd_run, "profile": cmd_profile, "report": cmd_report,
     "profile-report": cmd_profile_report}[a.cmd](a)


if __name__ == "__main__":
    main()
