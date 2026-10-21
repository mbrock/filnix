<?php
// smoke.php for the PHP 7.4 distribution (php74-dist), which has no PECL
// extensions and needs PHP 7 syntax. Prints one line per check and exits
// nonzero if any check fails.

$failed = 0;
function check(string $name, callable $f): void {
    global $failed;
    try {
        $r = $f();
        if ($r === true) {
            echo "ok   $name\n";
            return;
        }
        echo "FAIL $name: ", var_export($r, true), "\n";
    } catch (Throwable $e) {
        echo "FAIL $name: ", get_class($e), ": ", $e->getMessage(), "\n";
    }
    $failed++;
}

$expected = ['bcmath', 'bz2', 'calendar', 'ctype', 'curl', 'date', 'dom',
    'exif', 'fileinfo', 'filter', 'ftp', 'gd', 'gettext', 'gmp', 'hash',
    'iconv', 'imap', 'intl', 'json', 'ldap', 'libxml', 'mbstring', 'mysqli',
    'mysqlnd', 'openssl', 'pcntl', 'pcre', 'PDO', 'pdo_mysql', 'PDO_ODBC',
    'pdo_pgsql', 'pdo_sqlite', 'pgsql', 'Phar', 'posix', 'readline',
    'Reflection', 'session', 'shmop', 'SimpleXML', 'soap', 'sockets', 'sodium',
    'SPL', 'sqlite3', 'standard', 'sysvmsg', 'sysvsem', 'sysvshm', 'tokenizer',
    'xml', 'xmlreader', 'xmlwriter', 'Zend OPcache', 'zip', 'zlib'];
check('extensions loaded', fn() => array_values(array_diff($expected, get_loaded_extensions(), get_loaded_extensions(true))) ?: true);
check('no /nix', fn() => !file_exists('/nix') ?: 'found /nix');
// Zend's allocator counts real usage in 2 MiB chunks; the tracked system
// allocator, which gives Fil-C each value's own bounds, counts bytes.
check('values come from malloc, not Zend chunks', fn() => getenv('USE_ZEND_ALLOC') !== false
    || memory_get_usage(true) % (2 << 20) !== 0 ?: memory_get_usage(true));
check('memory_limit on the tracked allocator', function () {
    $out = shell_exec(escapeshellarg(PHP_BINARY) . ' -d memory_limit=4M -r '
        . escapeshellarg('$a = []; for (;;) $a[] = str_repeat("x", 1000);') . ' 2>&1');
    return strpos($out, 'Allowed memory size of 4194304 bytes exhausted') !== false ?: $out;
});
check('php.ini from etc/', fn() => substr(php_ini_loaded_file(), -12) === '/etc/php.ini' ?: php_ini_loaded_file());

check('typed properties', function () {
    $o = new class { public ?DateTime $d = null; public int $n = 1; };
    $o->d = new DateTime('2020-01-01');
    try { $o->n = 'x'; return 'no TypeError'; } catch (TypeError $e) {}
    return $o->d->format('Y') === '2020';
});
check('weak references', function () {
    $o = new stdClass; $r = WeakReference::create($o);
    $alive = $r->get() === $o; unset($o);
    return $alive && $r->get() === null;
});
check('mbstring', fn() => mb_strtoupper('straße ärger') === 'STRASSE ÄRGER' ?: mb_strtoupper('straße ärger'));
check('intl number', fn() => (new NumberFormatter('de_DE', NumberFormatter::DECIMAL))->format(1234.5) === '1.234,5');
check('iconv latin1 (gconv modules)', fn() => iconv('UTF-8', 'ISO-8859-1', 'Grüße') === "Gr\xfc\xdfe");
check('iconv //IGNORE', fn() => @iconv('UTF-8', 'UTF-8//IGNORE', "a\xC3b") === 'ab');
check('pcre unicode', fn() => preg_replace('/\p{Lu}/u', '_', 'Ärger Über') === '_rger _ber');
check('json', fn() => json_decode(json_encode(['a' => [1, 2.5, 'ü']]), true) === ['a' => [1, 2.5, 'ü']]);
check('dom + xpath', function () {
    $doc = new DOMDocument();
    $doc->loadXML('<r><i n="1">a</i><i n="2">b</i></r>');
    return (new DOMXPath($doc))->evaluate('string(//i[@n=2])') === 'b';
});
check('simplexml', fn() => (string)simplexml_load_string('<a><b>c</b></a>')->b === 'c');
check('openssl sign', function () {
    $k = openssl_pkey_new(['private_key_bits' => 2048]);
    openssl_sign('x', $s, $k, OPENSSL_ALGO_SHA256);
    return openssl_verify('x', $s, openssl_pkey_get_details($k)['key'], OPENSSL_ALGO_SHA256) === 1;
});
check('sodium secretbox', function () {
    $k = sodium_crypto_secretbox_keygen(); $n = random_bytes(24);
    return sodium_crypto_secretbox_open(sodium_crypto_secretbox('hi', $n, $k), $n, $k) === 'hi';
});
check('pdo_sqlite', function () {
    $d = new PDO('sqlite::memory:');
    $d->exec('create table t(x)'); $d->exec("insert into t values ('a')");
    return $d->query('select x from t')->fetchColumn() === 'a';
});
check('gd png', function () {
    $im = imagecreatetruecolor(4, 4); ob_start(); imagepng($im);
    return substr(ob_get_clean(), 1, 3) === 'PNG';
});
check('zip', function () {
    $f = tempnam(sys_get_temp_dir(), 'z'); $z = new ZipArchive;
    $z->open($f, ZipArchive::OVERWRITE); $z->addFromString('a', 'b'); $z->close();
    $z->open($f); $r = $z->getFromName('a'); unlink($f);
    return $r === 'b';
});
check('bz2', fn() => bzdecompress(bzcompress('hello')) === 'hello');
check('pcntl fork', function () {
    $pid = pcntl_fork();
    if ($pid === 0) exit(7);
    pcntl_waitpid($pid, $status);
    return pcntl_wexitstatus($status) === 7;
});
check('sysv shm/sem/msg', function () {
    $key = ftok(__FILE__, 's');
    $sem = sem_get($key); sem_acquire($sem);
    $shm = shm_attach($key, 4096); shm_put_var($shm, 1, ['x' => 1]); $v = shm_get_var($shm, 1); shm_remove($shm);
    sem_release($sem); sem_remove($sem);
    $q = msg_get_queue($key); msg_send($q, 1, 'm'); msg_receive($q, 1, $t, 64, $m); msg_remove_queue($q);
    return $v === ['x' => 1] && $m === 'm';
});
check('curl https setup', fn() => (curl_version()['features'] & CURL_VERSION_SSL) !== 0 && strpos(curl_version()['ssl_version'], 'OpenSSL') !== false);
check('opcache loaded', fn() => function_exists('opcache_get_status'));

echo $failed ? "$failed check(s) failed\n" : "all checks passed\n";
exit($failed ? 1 : 0);
