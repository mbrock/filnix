<?php
// The application that http-check.php and fpm-check.php request, through
// the built-in server and through php-fpm.

switch ($_GET['r'] ?? 'session') {
case 'session':
    session_start();
    $_SESSION['n'] = ($_SESSION['n'] ?? 0) + 1;
    $db = new PDO('sqlite:' . sys_get_temp_dir() . '/php-dist-hits.db');
    $db->exec('create table if not exists hits (at real)');
    $db->prepare('insert into hits values (?)')->execute([microtime(true)]);
    header('Content-Type: application/json');
    echo json_encode([
        'session' => $_SESSION['n'],
        'hits' => (int)$db->query('select count(*) from hits')->fetchColumn(),
        'sapi' => PHP_SAPI,
    ]);
    break;
case 'post':
    header('Content-Type: application/json');
    echo json_encode([
        'json' => json_decode(file_get_contents('php://input'), true),
        'upper' => mb_strtoupper($_GET['s'] ?? ''),
    ]);
    break;
case 'image':
    $im = imagecreatetruecolor(120, 40);
    imagestring($im, 5, 8, 12, 'Fil-C PHP', imagecolorallocate($im, 255, 255, 0));
    header('Content-Type: image/png');
    imagepng($im);
    break;
case 'opcache':
    // Each worker has a private opcache, so report which worker answered.
    $s = opcache_get_status(false);
    header('Content-Type: application/json');
    echo json_encode([
        'pid' => getmypid(),
        'sapi' => PHP_SAPI,
        'enabled' => $s['opcache_enabled'] ?? false,
        'cached' => opcache_is_script_cached(__FILE__),
        'scripts' => $s['opcache_statistics']['num_cached_scripts'] ?? null,
        'hits' => $s['opcache_statistics']['hits'] ?? null,
        'jit' => $s['jit']['on'] ?? false,
        'intl' => (new NumberFormatter('lv_LV', NumberFormatter::DECIMAL))->format(1234567.891),
    ]);
    break;
}
