# A deterministic jq workload: `bash jq.sh JQ` prints each command's
# stdout, stderr and exit status, so two builds' transcripts can be
# compared byte for byte. It covers jq's parser and compiler, number
# printing and parsing (jv_dtoa: shortest round trips, large and tiny
# exponents, integers beyond 2^53), strings and Unicode escapes, paths,
# sorting, grouping, reduce and foreach, recursion, formats (@base64,
# @csv, @sh, @uri, @html), dates in UTC, --arg/--argjson/--slurp/--raw-
# input/--stream/--seq, oniguruma regular expressions (test, match,
# capture, sub, gsub, splits), error messages and exit codes. Run it in
# an empty directory.
set -u
jq=$1
export LC_ALL=C.UTF-8 TZ=UTC
cat >data.json <<'EOF'
{"users":[{"name":"ada","age":36,"tags":["math","engines"],"score":91.5},
{"name":"brian","age":44,"tags":["c","unix"],"score":88.25},
{"name":"grace","age":85,"tags":["cobol","navy","compilers"],"score":99},
{"name":"Ωmega","age":null,"tags":[],"score":-0.0}],
"nums":[0,1,-1,0.1,1e-7,1.5e300,-2.5e-300,123456789012345678901234567890,9007199254740993,3.141592653589793,1e1000,100,1E2,0.30000000000000004],
"str":"line1\nline2\t\u00e9\ud83d\ude00\"quote\"\\","nested":{"a":{"b":{"c":[1,{"d":2}]}}}}
EOF
printf '1 2 3\n"four" [5] {"six":6}\n' >stream.json
printf 'alpha,1\nbeta,2\ngamma,3\n' >lines.txt

run() {
  echo "### jq $*"
  (exec -a jq "$jq" "$@") 2>&1 && status=0 || status=$?
  echo "### exit $status"
}

run . data.json
run -c '.nums[]' data.json
run -c '.nums | map(. * 3), map(tostring), map(floor? // "x")' data.json
run -c '[.nums[] | (. / 7)]' data.json
run '.nums | add, min, max, length' data.json
run -c '[range(0; 30; 3)], [limit(5; repeat(1))], [range(5) | . * .]' -n
run -c '.users | sort_by(.age) | map(.name)' data.json
run -c '.users | group_by(.tags | length) | map(map(.name))' data.json
run -c '.users | map(select(.score > 90)) | map({name, s: .score})' data.json
run -c '.users[] | "\(.name) is \(.age // "unknown") with \(.tags | join("/"))"' data.json
run -c '[paths]' data.json
run -c '[paths(type == "number")] | length' data.json
run -c 'getpath(["nested","a","b","c",1,"d"]), (setpath(["x","y"]; 1) | .x), delpaths([["users"],["nums"]])' data.json
run -c '[leaf_paths] | map(map(tostring) | join("."))' data.json
run -c '(to_entries | map(.key)), (.nested | [tostream])' data.json
run -c 'reduce .users[] as $u (0; . + ($u.age // 0)), [foreach .nums[] as $n (0; . + 1; [., $n])] | length' data.json
run -c 'def fib: if . < 2 then . else (. - 1 | fib) + (. - 2 | fib) end; [range(20) | fib]' -n
run -c '[recurse(if . < 100 then . * 2 else empty end)]' <<<'3'
run -r '.str, (.str | @json), (.str | explode | length), (.str | @base64), (.str | @base64 | @base64d)' data.json
run -r '.users[] | [.name, .age, .score] | @csv, @tsv' data.json
run -r '.users[0].tags | @sh, @uri "q=\(.[0])&x=\(.[1])"' data.json
run -r '"<a href=\"x\">&</a>" | @html' -n
run -r '.str | ascii_downcase, ltrimstr("line"), (split("\n") | length), test("LINE"; "i")' data.json
run -c '"abc123def456" | [match("[0-9]+"; "g") | .string], sub("[0-9]+"; "#"), gsub("[a-z]"; "")' -n
run -c '[.[] | tojson | fromjson]' stream.json --slurp
run -c 'input_line_number?, .' stream.json
run -c --seq . stream.json
run -c --stream . stream.json
run -R -c 'split(",") | {k: .[0], v: (.[1] | tonumber)}' lines.txt
run -R -s -c 'split("\n") | map(select(length > 0))' lines.txt
run -n -c --arg a 'hello' --argjson b '{"x":[1,2]}' '[$a, $b, $ARGS.named]'
run -c -n '[1700000000, 0, 951782400] | map(todate), map(gmtime | mktime)'
run -c -n '"2015-03-05T23:51:47Z" | fromdate, (strptime("%Y-%m-%dT%H:%M:%SZ") | mktime)'
run -c -n '[1,[2,[3,[4]]]] | flatten, flatten(1), (tostring | length)'
run -c -n '{"b":2,"a":1,"c":{"z":0,"y":[3,1,2]}} | keys, (. | tojson), (.c.y | sort), unique_by(. % 2)?' 
run -S -c . data.json
run -c -n '[1,2,3] | IN(2), any(. > 2), all(. > 0), index(2), (indices(2) | length)'
run -c -n '"x" * 3, ([1,2] - [2]), ({"a":1} * {"a":{"b":2}}), (10 % 3), (-7 % 3), (5 / 2)'
run -c -n '[.[]?], (try error("boom") catch .), (try (1/0) catch .), ([1] | .[1:] )'
run -c '[splits("a+"; "g")], ascii_upcase, (capture("(?<x>a+)(?<y>b)") | .x)' <<<'"baaab"'
run -c -n '"\u00e9" | utf8bytelength, length, ([.] | implode? // "no")'
run -c -n 'input' <<<'[1, 2'
run '.[' data.json
run -n 'error("custom failure")'
run -e '.users[0].missing' data.json
run -n -c '$__loc__, (now | type), ([limit(3; inputs)] | length)'
run -c 'tojson | length' /nonexistent
run --tab '.nested' data.json
run --indent 1 '.users[1]' data.json
run -n -r '[range(1; 6)] | map(pow(.; 10) | tostring) | join(" ")'
run -n -c '[1e17, 1e-5, 123456.789, 2e-308, 4.9e-324, 1.7976931348623157e308] | map(., tostring, (tostring | tonumber))'
run -n -c '[3.0, -0, 1.0e0, 100000000000000000000] | map(tojson)'
run -n -c '[infinite, -infinite, nan] | map(isinfinite, isnan, tostring)'
run --version
