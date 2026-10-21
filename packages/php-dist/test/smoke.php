<?php
// Exercises the bundled extensions from the CLI. Prints one line per check
// and exits nonzero if any check fails.

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

$tmp = sys_get_temp_dir() . '/php-dist-smoke-' . getmypid();
@mkdir($tmp);

$expected = ['bcmath', 'bz2', 'calendar', 'ctype', 'curl', 'date', 'dom',
    'exif', 'fileinfo', 'filter', 'ftp', 'gd', 'gettext', 'gmp', 'hash',
    'iconv', 'intl', 'json', 'ldap', 'libxml', 'mbstring', 'mysqli', 'mysqlnd',
    'openssl', 'pcntl', 'pcre', 'PDO', 'pdo_mysql', 'PDO_ODBC', 'pdo_pgsql',
    'pdo_sqlite', 'pgsql', 'Phar', 'posix', 'random', 'readline', 'Reflection',
    'session', 'SimpleXML', 'soap', 'sockets', 'sodium', 'SPL',
    'sqlite3', 'standard', 'sysvmsg', 'sysvsem', 'sysvshm', 'tokenizer', 'xml',
    'xmlreader', 'xmlwriter', 'xsl', 'Zend OPcache', 'zip', 'zlib', 'igbinary',
    'redis'];
check('extensions loaded', fn() => array_values(array_diff($expected, get_loaded_extensions(), get_loaded_extensions(true))) ?: true);
check('no /nix', fn() => !file_exists('/nix') ?: 'found /nix');
check('PHP_BINARY is the launcher', fn() => str_ends_with(PHP_BINARY, '/bin/php') && is_executable(PHP_BINARY) ?: PHP_BINARY);
check('PHP_BINARY reruns php', function () {
    $out = shell_exec(escapeshellarg(PHP_BINARY) . ' -r ' . escapeshellarg('echo extension_loaded("intl") ? "yes" : "no";'));
    return $out === 'yes' ?: $out;
});
check('php.ini from etc/', fn() => str_ends_with(php_ini_loaded_file(), '/etc/php.ini') ?: php_ini_loaded_file());

check('mbstring', fn() => mb_strtoupper('straße ärger') === 'STRASSE ÄRGER' ?: mb_strtoupper('straße ärger'));
check('intl number', fn() => (new NumberFormatter('de_DE', NumberFormatter::CURRENCY))->formatCurrency(1234.5, 'EUR') === "1.234,50\u{a0}€");
check('intl collator', function () {
    $a = ['zebra', 'Äpfel', 'apfel', 'Zucker'];
    (new Collator('de_DE'))->sort($a);
    return $a === ['apfel', 'Äpfel', 'zebra', 'Zucker'] ?: $a;
});
check('intl transliterator', fn() => transliterator_transliterate('Any-Latin; Latin-ASCII', 'Привет, мир') === 'Privet, mir');
check('iconv latin1 (gconv modules)', fn() => iconv('UTF-8', 'ISO-8859-1', 'Grüße') === "Gr\xfc\xdfe" ?: bin2hex((string)iconv('UTF-8', 'ISO-8859-1', 'Grüße')));
check('iconv shift_jis', fn() => iconv('SHIFT_JIS', 'UTF-8', iconv('UTF-8', 'SHIFT_JIS', '日本語')) === '日本語');
check('GCONV_PATH, LOCPATH not set for children', fn() => getenv('GCONV_PATH') === false && getenv('LOCPATH') === false);
check('C.UTF-8 locale', fn() => setlocale(LC_ALL, 'C.UTF-8') !== false);
check('date/timezones', function () {
    // Riga moves from EET to EEST at 01:00 UTC on 2026-03-29.
    $d = new DateTime('2026-03-29 02:30:00', new DateTimeZone('Europe/Riga'));
    $d->modify('+1 hour');
    return $d->format('H:i T') === '04:30 EEST' ?: $d->format('H:i T');
});
check('pcre unicode', fn() => preg_replace('/\p{Lu}/u', '_', 'Ärger Über') === '_rger _ber');
check('json', fn() => json_decode(json_encode(['a' => [1, 2.5, 'ü']]), true) === ['a' => [1, 2.5, 'ü']]);

check('dom + xpath', function () {
    $doc = new DOMDocument();
    $doc->loadXML('<r><i n="1">a</i><i n="2">b</i></r>');
    return (new DOMXPath($doc))->evaluate('string(//i[@n=2])') === 'b';
});
check('html5 dom', function () {
    $doc = Dom\HTMLDocument::createFromString('<!doctype html><p class=x>hi<p>there', LIBXML_NOERROR);
    return $doc->querySelectorAll('p')->length === 2 && $doc->querySelector('.x')->textContent === 'hi';
});
check('simplexml', fn() => (string)simplexml_load_string('<a><b>c</b></a>')->b === 'c');
check('xmlwriter/xmlreader', function () {
    $w = new XMLWriter(); $w->openMemory(); $w->startElement('x'); $w->writeAttribute('y', 'z'); $w->endElement();
    $r = XMLReader::XML($w->outputMemory()); $r->read();
    return $r->getAttribute('y') === 'z';
});
check('xsl', function () {
    $xsl = new XSLTProcessor();
    $xsl->importStylesheet(new SimpleXMLElement('<xsl:stylesheet version="1.0" xmlns:xsl="http://www.w3.org/1999/XSL/Transform"><xsl:output method="text"/><xsl:template match="/">n=<xsl:value-of select="count(//i)"/></xsl:template></xsl:stylesheet>'));
    return $xsl->transformToXml(new SimpleXMLElement('<r><i/><i/><i/></r>')) === 'n=3';
});
check('soap classes', fn() => class_exists('SoapClient') && class_exists('SoapServer'));

check('pdo_sqlite', function () {
    $db = new PDO('sqlite::memory:');
    $db->exec('create table t (k text primary key, v integer)');
    $st = $db->prepare('insert into t values (?, ?)');
    foreach (range(1, 100) as $i) $st->execute(["k$i", $i]);
    return (int)$db->query('select sum(v) from t')->fetchColumn() === 5050;
});
check('sqlite3 json', function () use ($tmp) {
    $db = new SQLite3("$tmp/x.db");
    return $db->querySingle("select json_extract('{\"a\":[1,2,3]}', '$.a[2]')") === 3;
});
check('mysqli/pgsql/odbc drivers', function () {
    $d = PDO::getAvailableDrivers();
    sort($d);
    return $d === ['mysql', 'odbc', 'pgsql', 'sqlite'] && class_exists('mysqli') && function_exists('pg_connect') ?: $d;
});

check('gd png/jpeg/webp', function () {
    $im = imagecreatetruecolor(64, 32);
    imagefilledrectangle($im, 0, 0, 63, 31, imagecolorallocate($im, 255, 0, 0));
    imagestring($im, 3, 2, 2, 'Fil-C', imagecolorallocate($im, 255, 255, 255));
    $out = [];
    foreach (['png' => 'imagepng', 'jpeg' => 'imagejpeg', 'webp' => 'imagewebp', 'avif' => 'imageavif'] as $fmt => $fn) {
        ob_start(); $fn($im); $data = ob_get_clean();
        $info = getimagesizefromstring($data);
        $back = imagecreatefromstring($data);
        $out[$fmt] = $info[0] === 64 && $info[1] === 32 && imagesx($back) === 64;
    }
    return !in_array(false, $out, true) ?: $out;
});
check('gd freetype', fn() => function_exists('imagettftext') && gd_info()['FreeType Support'] === true);
check('exif', fn() => exif_imagetype(__FILE__) === false);
check('fileinfo', function () {
    ob_start(); imagepng(imagecreatetruecolor(4, 4)); $png = ob_get_clean();
    $types = [(new finfo(FILEINFO_MIME_TYPE))->buffer($png), mime_content_type(__FILE__)];
    return $types === ['image/png', 'text/x-php'] ?: $types;
});

check('zlib/bz2', function () {
    $s = str_repeat('memory safety ', 1000);
    return gzdecode(gzencode($s, 9)) === $s && bzdecompress(bzcompress($s)) === $s && strlen(gzcompress($s)) < 200;
});
check('zip', function () use ($tmp) {
    $z = new ZipArchive();
    $z->open("$tmp/a.zip", ZipArchive::CREATE);
    $z->addFromString('dir/hello.txt', str_repeat('hello ', 100));
    $z->close();
    $z->open("$tmp/a.zip");
    return $z->getFromName('dir/hello.txt') === str_repeat('hello ', 100);
});
check('phar', function () use ($tmp) {
    // phar.readonly is on in php.ini and can only be turned off at startup.
    shell_exec(escapeshellarg(PHP_BINARY) . ' -d phar.readonly=0 -r ' . escapeshellarg(
        "\$p = new Phar('$tmp/a.phar'); \$p['x.php'] = '<?php return 42;'; \$p->setStub('<?php __HALT_COMPILER();');"));
    return (include "phar://$tmp/a.phar/x.php") === 42;
});

check('openssl rsa + aes', function () {
    $key = openssl_pkey_new(['private_key_bits' => 2048, 'private_key_type' => OPENSSL_KEYTYPE_RSA]);
    openssl_sign('data', $sig, $key, OPENSSL_ALGO_SHA256);
    $pub = openssl_pkey_get_details($key)['key'];
    $iv = random_bytes(12);
    $ct = openssl_encrypt('secret', 'aes-256-gcm', str_repeat('k', 32), 0, $iv, $tag);
    return openssl_verify('data', $sig, $pub, OPENSSL_ALGO_SHA256) === 1
        && openssl_decrypt($ct, 'aes-256-gcm', str_repeat('k', 32), 0, $iv, $tag) === 'secret';
});
check('openssl CA store', function () {
    $loc = openssl_get_cert_locations();
    $file = getenv('SSL_CERT_FILE');
    return $file !== false && is_readable($file) && filesize($file) > 1000 ?: [$file, $loc];
});
check('sodium', function () {
    $alice = sodium_crypto_box_keypair(); $bob = sodium_crypto_box_keypair();
    $nonce = random_bytes(SODIUM_CRYPTO_BOX_NONCEBYTES);
    $ct = sodium_crypto_box('hi bob', $nonce, sodium_crypto_box_keypair_from_secretkey_and_publickey(sodium_crypto_box_secretkey($alice), sodium_crypto_box_publickey($bob)));
    return sodium_crypto_box_open($ct, $nonce, sodium_crypto_box_keypair_from_secretkey_and_publickey(sodium_crypto_box_secretkey($bob), sodium_crypto_box_publickey($alice))) === 'hi bob';
});
check('password_hash argon2id', fn() => password_verify('pw', password_hash('pw', PASSWORD_ARGON2ID)));
check('hash', fn() => hash('sha3-256', 'abc') === '3a985da74fe225b2045c172d6bd390bd855f086e3e9d525b46bfe24511431532');
check('gmp', fn() => gmp_strval(gmp_fact(30)) === '265252859812191058636308480000000');
check('bcmath', fn() => bcdiv('1', '7', 30) === '0.142857142857142857142857142857');
check('calendar', fn() => cal_days_in_month(CAL_GREGORIAN, 2, 2028) === 29);

check('fibers', function () {
    $f = new Fiber(function (int $x) { $y = Fiber::suspend($x * 2); return $y + 1; });
    return $f->start(20) === 40 && $f->resume(41) === null && $f->getReturn() === 42;
});
check('deep recursion is an Error', function () {
    // Calls through array_map recurse in C; plain PHP calls do not and
    // would hit memory_limit instead.
    $f = function ($n) use (&$f) { return array_map($f, [$n + 1]); };
    try { $f(0); } catch (Error $e) { return str_contains($e->getMessage(), 'Maximum call stack size'); }
    return 'no error';
});
check('pcntl fork', function () {
    $pid = pcntl_fork();
    if ($pid === 0) exit(7);
    pcntl_waitpid($pid, $status);
    return pcntl_wexitstatus($status) === 7;
});
check('posix + host NSS', fn() => posix_getpwuid(0)['name'] === 'root' ?: posix_getpwuid(0));
check('sockets pair', function () {
    socket_create_pair(AF_UNIX, SOCK_STREAM, 0, $p);
    socket_write($p[0], 'ping');
    return socket_read($p[1], 4) === 'ping';
});
check('sysv shm/sem/msg', function () {
    $key = ftok(__FILE__, 's');
    $sem = sem_get($key); sem_acquire($sem);
    $shm = shm_attach($key, 4096); shm_put_var($shm, 1, ['x' => 1]); $v = shm_get_var($shm, 1); shm_remove($shm);
    sem_release($sem); sem_remove($sem);
    $q = msg_get_queue($key); msg_send($q, 1, 'm'); msg_receive($q, 1, $t, 64, $m); msg_remove_queue($q);
    return $v === ['x' => 1] && $m === 'm';
});
check('igbinary', fn() => igbinary_unserialize(igbinary_serialize(['a' => new ArrayObject([1])]))['a'][0] === 1);
check('redis class', fn() => (new ReflectionClass('Redis'))->hasMethod('connect'));
check('curl https setup', fn() => (curl_version()['features'] & CURL_VERSION_SSL) !== 0 && str_contains(curl_version()['ssl_version'], 'OpenSSL'));
check('opcache loaded', fn() => function_exists('opcache_get_status'));

shell_exec('rm -rf ' . escapeshellarg($tmp));
echo $failed ? "$failed check(s) failed\n" : "all checks passed\n";
exit($failed ? 1 : 0);
