<?php
// Sends FastCGI requests for $argv[3] to php-fpm at $argv[1]:$argv[2] and
// checks that the workers answer from their opcache.

[, $host, $port, $script] = $argv;

function record(int $type, string $content): string {
    return pack('CCnnCx', 1, $type, 1, strlen($content), 0) . $content;
}

function pair(string $k, string $v): string {
    $len = fn($s) => strlen($s) < 128 ? chr(strlen($s)) : pack('N', strlen($s) | 0x80000000);
    return $len($k) . $len($v) . $k . $v;
}

function fcgi(string $host, int $port, array $params): string {
    $s = stream_socket_client("tcp://$host:$port", $errno, $err, 5);
    if (!$s) throw new RuntimeException("connect: $err");
    $p = '';
    foreach ($params as $k => $v) $p .= pair($k, $v);
    fwrite($s, record(1, pack('nCx5', 1, 0)) . record(4, $p) . record(4, '') . record(5, ''));
    $out = '';
    while (strlen($h = fread($s, 8)) === 8) {
        $r = unpack('Cversion/Ctype/nid/nlen/Cpad', $h);
        $body = $r['len'] ? stream_get_contents($s, $r['len']) : '';
        if ($r['pad']) fread($s, $r['pad']);
        if ($r['type'] === 6) $out .= $body;
        if ($r['type'] === 7) fwrite(STDERR, "fpm stderr: $body\n");
        if ($r['type'] === 3) break;
    }
    fclose($s);
    return $out;
}

for ($i = 0; $i < 100 && !@fsockopen($host, (int)$port); $i++) usleep(100000);

$replies = [];
for ($i = 0; $i < 24; $i++) {
    $raw = fcgi($host, (int)$port, [
        'GATEWAY_INTERFACE' => 'FastCGI/1.0', 'REQUEST_METHOD' => 'GET',
        'SCRIPT_FILENAME' => $script, 'SCRIPT_NAME' => '/index.php',
        'QUERY_STRING' => 'r=opcache', 'REQUEST_URI' => '/index.php?r=opcache',
        'SERVER_NAME' => 'localhost', 'SERVER_PORT' => '80', 'SERVER_PROTOCOL' => 'HTTP/1.1',
        'REMOTE_ADDR' => '127.0.0.1',
    ]);
    [, $body] = explode("\r\n\r\n", $raw, 2) + [1 => ''];
    $replies[] = json_decode($body, true) ?? ['raw' => $raw];
}

$pids = array_unique(array_column($replies, 'pid'));
$failed = 0;
foreach ([
    'all 24 requests answered by fpm-fcgi' => count(array_filter($replies, fn($r) => ($r['sapi'] ?? '') === 'fpm-fcgi')) === 24,
    'opcache enabled in every worker' => !in_array(false, array_column($replies, 'enabled'), true),
    'JIT off' => !in_array(true, array_column($replies, 'jit'), true),
    'script served from opcache' => count(array_filter($replies, fn($r) => $r['cached'] && $r['hits'] > 0)) >= 24 - 2 * count($pids),
    'more than one worker' => count($pids) > 1,
    'intl in fpm' => ($replies[0]['intl'] ?? '') === "1\u{a0}234\u{a0}567,891",
] as $name => $ok) {
    echo $ok ? "ok   " : "FAIL ", $name, "\n";
    $failed += $ok ? 0 : 1;
}
echo 'workers: ', implode(' ', $pids), '; last reply: ', json_encode(end($replies)), "\n";
exit($failed ? 1 : 0);
