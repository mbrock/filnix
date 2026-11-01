<?php
// CPU-bound kernels for php-bench, reported like Zend/bench.php: recursive
// calls, integer and float branches, float arithmetic on arrays, sorting,
// and string building (which a JIT barely changes).

function fib($n) { return $n < 2 ? $n : fib($n - 1) + fib($n - 2); }

function branchy($n) {
    $a = 0; $b = 0.0;
    for ($i = 0; $i < $n; $i++) {
        if ($i % 3 == 0) { $a += $i; } elseif ($i % 3 == 1) { $b += $i * 0.5; } else { $a -= 1; }
    }
    return $a + (int)$b;
}

function nbody($steps) {
    $n = 5;
    $x = [0.0, 4.84, 8.34, 12.89, 15.37]; $y = [0.0, -1.16, 4.12, -15.11, -25.91];
    $vx = [0.0, 0.606, -1.01, 1.08, 0.979]; $vy = [0.0, 2.81, 1.82, 0.868, 0.594];
    $m = [39.47, 0.037, 0.011, 0.0017, 0.002];
    for ($s = 0; $s < $steps; $s++) {
        for ($i = 0; $i < $n; $i++) {
            for ($j = $i + 1; $j < $n; $j++) {
                $dx = $x[$i] - $x[$j]; $dy = $y[$i] - $y[$j];
                $d2 = $dx * $dx + $dy * $dy;
                $mag = 0.01 / ($d2 * sqrt($d2));
                $vx[$i] -= $dx * $m[$j] * $mag; $vy[$i] -= $dy * $m[$j] * $mag;
                $vx[$j] += $dx * $m[$i] * $mag; $vy[$j] += $dy * $m[$i] * $mag;
            }
        }
        for ($i = 0; $i < $n; $i++) { $x[$i] += 0.01 * $vx[$i]; $y[$i] += 0.01 * $vy[$i]; }
    }
    return $x[0];
}

function sorting($n) {
    mt_srand(42);
    $a = [];
    for ($i = 0; $i < $n; $i++) { $a[] = mt_rand(); }
    usort($a, fn($p, $q) => $p <=> $q);
    return $a[0];
}

function strings($n) {
    $s = "";
    for ($i = 0; $i < $n; $i++) { $s .= str_pad(dechex($i), 8, "0", STR_PAD_LEFT) . ","; }
    return strlen(implode(";", explode(",", strtoupper($s))));
}

$total = 0;
foreach ([["fib(27)", fn() => fib(27)], ["branchy", fn() => branchy(3000000)],
          ["nbody", fn() => nbody(100000)], ["usort", fn() => sorting(200000)],
          ["strings", fn() => strings(300000)]] as [$name, $f]) {
    $t = hrtime(true);
    $f();
    $d = (hrtime(true) - $t) / 1e9;
    $total += $d;
    printf("%-19s%6.3f\n", $name, $d);
}
printf("%-19s%6.3f\n", "Total", $total);
