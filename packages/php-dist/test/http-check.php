<?php
// Requests www/index.php from the built-in server at $argv[1] (host:port).

$base = "http://$argv[1]";
$failed = 0;
function expect(string $name, bool $ok, $detail = null): void {
    global $failed;
    echo ($ok ? "ok   " : "FAIL "), $name, $ok ? '' : ': ' . var_export($detail, true), "\n";
    $failed += $ok ? 0 : 1;
}

for ($i = 0; $i < 100 && !@fsockopen(...explode(':', $argv[1])); $i++) usleep(100000);

// Sessions over a cookie jar, through the curl extension.
$jar = tempnam(sys_get_temp_dir(), 'jar');
$last = null;
for ($i = 1; $i <= 3; $i++) {
    $c = curl_init("$base/index.php?r=session");
    curl_setopt_array($c, [CURLOPT_RETURNTRANSFER => true, CURLOPT_COOKIEJAR => $jar, CURLOPT_COOKIEFILE => $jar]);
    $last = json_decode(curl_exec($c), true);
    expect("session request $i (curl)", curl_getinfo($c, CURLINFO_HTTP_CODE) === 200 && $last['session'] === $i, $last);
}
expect('cli-server sapi', $last['sapi'] === 'cli-server', $last);

// POST through the http stream wrapper.
$body = file_get_contents("$base/index.php?r=post&s=" . urlencode('ärger'), false, stream_context_create(['http' => [
    'method' => 'POST', 'header' => 'Content-Type: application/json', 'content' => json_encode(['a' => [1, 2]]),
]]));
expect('post json', json_decode($body, true) === ['json' => ['a' => [1, 2]], 'upper' => 'ÄRGER'], $body);

$png = file_get_contents("$base/index.php?r=image");
expect('gd png response', getimagesizefromstring($png)[0] === 120, strlen($png));

$static = file_get_contents("$base/static.txt");
expect('static file', $static === "static file\n", $static);

// Concurrent requests: PHP_CLI_SERVER_WORKERS forks workers.
$mh = curl_multi_init();
$handles = [];
for ($i = 0; $i < 8; $i++) {
    $handles[] = $c = curl_init("$base/index.php?r=session");
    curl_setopt($c, CURLOPT_RETURNTRANSFER, true);
    curl_multi_add_handle($mh, $c);
}
do { curl_multi_exec($mh, $running); curl_multi_select($mh); } while ($running);
$ok = array_filter($handles, fn($c) => curl_getinfo($c, CURLINFO_HTTP_CODE) === 200);
expect('8 concurrent requests', count($ok) === 8, count($ok));

exit($failed ? 1 : 0);
