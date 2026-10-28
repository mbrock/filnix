# A deterministic CPython workload: `bash python.sh PYTHON` runs the
# interpreter PYTHON (a build tree's ./python, which finds its own Lib)
# on scripts covering integers and bignums, floats and their repr,
# str, bytes and unicode, dicts and sets, re, json, struct, hashlib,
# sorting, generators, exceptions, threads under the GIL, subprocess
# and gc.collect(), and prints each script's exit status, stderr and
# output, so two builds' transcripts can be compared byte for byte.
# PYTHONHASHSEED is fixed; nothing printed depends on the builder,
# addresses, timings or thread scheduling. Run it in an empty directory.
set -u
py=$1
export PYTHONHASHSEED=0 PYTHONDONTWRITEBYTECODE=1 LC_ALL=C TZ=UTC0
here=$PWD

run() {
  local name=$1; shift
  echo "### $name"
  { "$py" "$@" >out 2>err; } 2>/dev/null && status=0 || status=$?
  sed "s|$here|DIR|g; s|$py|PYTHON|g; s|line [0-9]*, in <module>|line N, in <module>|; s|pid=[0-9]*|pid=N|" err
  sed "s|$here|DIR|g" out
  echo "### exit $status"
}

cat >ints.py <<'EOF'
import math, sys
sys.set_int_max_str_digits(0)
a = 3 ** 200
b = 7 ** 150 - 1
print(a % 1000003, b // 12345678901234567, a * b % (2 ** 61 - 1))
print(divmod(-a, 97), pow(5, 10 ** 6, 2 ** 89 - 1), pow(3, -1, 1000003))
print(math.factorial(300) % 10 ** 30, math.comb(200, 73) % 999983, math.isqrt(10 ** 101))
print(math.gcd(2 ** 120 - 1, 3 ** 80 - 1), math.lcm(*range(1, 60)) % 10 ** 20)
f = 1
for i in range(1, 2000):
    f *= i
s = str(f)
print(len(s), s[:20], s[-30:], int(s[:4000]) % 99991)
print(hex(a)[:40], oct(b)[-20:], bin(12345678901234567890), (a).bit_length(), (-b).bit_count())
print(int("123456789" * 50) // int("987654321" * 20), int("-0x" + "f" * 100, 16) >> 333)
print((a).to_bytes(60, "little").hex()[:50], int.from_bytes(b"\xff" * 33, "big", signed=True))
print(sum(i * i for i in range(10 ** 5)), sum(range(-10 ** 6, 10 ** 6, 7)))
print([x for x in range(2, 200) if all(x % d for d in range(2, math.isqrt(x) + 1))][-10:])
print(sys.maxsize, -sys.maxsize - 1, (sys.maxsize + 1) * 2, ~0, -7 // 2, -7 % 2, 7 // -2)
print(round(123456789, -3), round(-2.5), round(3.5), 10 ** 50 // 3 * 3 + 10 ** 50 % 3 == 10 ** 50)
EOF
run ints ints.py

cat >floats.py <<'EOF'
import math, struct, decimal, fractions, statistics
xs = [0.1, 0.2, 0.1 + 0.2, 1 / 3, 2 / 3, 1e16, 1e-320, 5e-324, 1.7976931348623157e308,
      float("inf"), -float("inf"), float("nan"), -0.0, 123456789.123456789, 2.0 ** 0.5,
      math.pi, math.e, 1e22, 1e23, 9007199254740993.0]
for x in xs:
    print(repr(x), str(x), "%.17g" % x, format(x, ".3e"), format(x, "g"),
          x.hex() if math.isfinite(x) else "-")
print([float(s) for s in ["1e500", "-1e-500", "  12.5  ", "1_000.25", "nan"]][:5])
print(math.fsum([0.1] * 10), sum([0.1] * 10), math.prod([1.5, 2.5, 3.5]))
print(math.sqrt(2), math.exp(1), math.log(10), math.log2(1 << 80), math.sin(1), math.atan2(1, -1))
print(math.frexp(1234.5), math.ldexp(0.75, 11), math.modf(-3.25), math.copysign(1, -0.0))
print(math.floor(-2.5), math.ceil(-2.5), math.trunc(-2.7), (2.5).as_integer_ratio(), (0.1).is_integer())
print(struct.pack("<d", 1 / 3).hex(), struct.unpack(">f", b"\x40\x49\x0f\xdb")[0], struct.pack("e", 1.5).hex())
print(divmod(7.5, -2), 7.5 % -2, -7.5 // 2, 2.0 ** -1074, float.fromhex("0x1.fffffffffffffp+1023"))
decimal.getcontext().prec = 50
print(decimal.Decimal(2).sqrt(), decimal.Decimal(1) / decimal.Decimal(7), decimal.Decimal("1.1") * 3)
print(fractions.Fraction(355, 113) - fractions.Fraction(math.pi), fractions.Fraction("3.1415926535").limit_denominator(1000))
print(statistics.mean([1.5, 2.5, 10]), statistics.median([3, 1, 4, 1, 5]), statistics.pstdev([1, 2, 3, 4]))
print(complex(1, 2) * complex(3, -4), abs(3 + 4j), (1j) ** 2, complex("1.5-2.5j"))
print(f"{1234567.891:,.2f} {0.000123:%} {255:#x} {-42:+08d} {3.14159:>10.3f}|{'x':^7}|")
EOF
run floats floats.py

cat >text.py <<'EOF'
import unicodedata, codecs, string
s = "Grüße, Καλημέρα, こんにちは, 😀 — naïve café"
print(s.upper(), s.lower(), s.casefold(), s.title(), s.swapcase())
print(len(s), [len(s.encode(e)) for e in ("utf-8", "utf-16", "utf-32")], s.encode("utf-8")[:20])
print(s.encode("ascii", "replace"), s.encode("latin-1", "xmlcharrefreplace")[:60], s.encode("ascii", "backslashreplace")[:50])
print([unicodedata.name(c, "?") for c in "é😀Ω"], unicodedata.normalize("NFD", "é") == "e\u0301")
print(unicodedata.category("Ω"), unicodedata.east_asian_width("こ"), unicodedata.numeric("½"), unicodedata.decimal("٣"))
print(s.find("café"), s.split(", "), "-".join(reversed(s.split())), s[::-3], s.isprintable())
print("a,b,,c".split(","), "  x  y ".split(), "x".center(9, "*"), "abc".zfill(8), "tab\tbed".expandtabs(4))
print("%s %r %5.2f %-5d| %c %x %o" % ("str", "rep'r", 3.14159, 42, 65, 255, 8))
print("{0:{1}}|{name!r}".format("hi", 6, name="n"), str.maketrans("abc", "xyz"), "abcabc".translate(str.maketrans("ab", "AB", "c")))
b = bytes(range(256))
print(b[:10], b.hex()[-16:], bytearray(b"hello").replace(b"l", b"L"), b"%d-%s" % (5, b"x"), memoryview(b)[250:].tolist())
print(codecs.encode("hello", "rot13"), codecs.decode(b"68656c6c6f", "hex"))
print("ﬁ".upper(), "İ".lower(), "ß".upper(), "ǅ".istitle(), "١٢٣".isdigit(), int("١٢٣"), "x\u200by".isidentifier())
big = "".join(chr(0x4e00 + (i * 37) % 2000) for i in range(5000))
print(hash(big) == hash(big[:]), big.count(big[17]), big.encode()[-9:], sorted(set(big))[:3])
print(repr("\x00\x7f\u0085\ud800"[:3]), ascii("ü😀"), "abc" < "abd" < "abd\0", min("zay"), max(b"zay"))
print(string.ascii_letters, string.punctuation, "Hello World".partition("o"), "a-b-c".rpartition("-"))
EOF
run text text.py

cat >containers.py <<'EOF'
import collections, heapq, bisect, itertools, functools, operator, array, copy
d = {}
for i in range(20000):
    d[(i * 7919) % 10007] = i
print(len(d), sum(d.values()), list(d.items())[:3], d.get(10006), 123 in d)
for k in list(d)[::3]:
    del d[k]
print(len(d), list(d)[:5], sorted(d)[-3:])
s = set(range(0, 1000, 3)) ^ set(range(0, 1000, 5))
print(len(s), sorted(s)[:10], len(s & set(range(500))), frozenset("abc") | {"d"} == set("abcd"))
c = collections.Counter("the quick brown fox jumps over the lazy dog" * 3)
print(c.most_common(5), sorted(c.elements())[:8])
od = collections.OrderedDict.fromkeys("hello world")
od.move_to_end("h")
print(list(od), collections.deque(range(10), maxlen=4), collections.ChainMap({"a": 1}, {"a": 2, "b": 3})["b"])
P = collections.namedtuple("P", "x y")
print(P(1, 2)._replace(y=5), P._fields, collections.defaultdict(list, a=[1])["b"])
h = [(i * 31) % 97 for i in range(200)]
heapq.heapify(h)
print([heapq.heappop(h) for _ in range(8)], heapq.nlargest(3, range(100), key=lambda v: (v * 7) % 13))
a = sorted((i * 2654435761) % 1000 for i in range(500))
print(bisect.bisect_left(a, 500), bisect.bisect_right(a, 500), a[:5])
print(list(itertools.permutations("abc")), list(itertools.combinations(range(5), 3))[-2:])
print(list(itertools.accumulate(range(10), operator.mul, initial=1)), list(itertools.groupby("aaabbc"))[0][0])
print(functools.reduce(operator.xor, range(1000)), list(itertools.islice(itertools.cycle("xy"), 5)))
@functools.lru_cache(maxsize=None)
def fib(n):
    return n if n < 2 else fib(n - 1) + fib(n - 2)
print(fib(100), fib.cache_info().hits)
arr = array.array("i", range(10))
arr.reverse()
print(arr, arr.tobytes()[:8], array.array("d", [1.5, 2.5]).itemsize)
nested = {"a": [1, {"b": (2, 3)}], "c": {4, 5}}
cp = copy.deepcopy(nested)
print(cp == nested, cp["a"] is nested["a"], sorted(cp["c"]))
words = ("pear apple fig banana cherry date elderberry grape kiwi lemon mango " * 50).split()
print(sorted(words)[:4], sorted(words, key=len)[-1], sorted(set(words), key=lambda w: (-len(w), w))[:3])
recs = [(w[0], len(w), i) for i, w in enumerate(words)]
recs.sort(key=operator.itemgetter(1))
print(recs[:3], recs[-2:], sorted(range(30), key=lambda v: v % 4, reverse=True)[:8])
print(sorted([3.5, -1, 2, float("inf"), 0.0, -0.0]), list(reversed(sorted("hello"))), max(range(10), key=lambda v: -v))
EOF
run containers containers.py

cat >formats.py <<'EOF'
import re, json, struct, hashlib, hmac, base64, binascii
print(re.findall(r"\b(\w)(\w*)\b", "alpha beta gamma")[:2], re.sub(r"(\d+)", lambda m: str(int(m[1]) * 2), "a1b22c333"))
print(re.split(r"[,;]\s*", "a, b;c,  d"), re.match(r"(?P<y>\d{4})-(?P<m>\d\d)", "2024-06-01").groupdict())
print(re.search(r"(?i)straße", "STRASSE straße").span(), re.fullmatch(r"[\w.]+@[\w.]+", "a.b@c.d") is not None)
print(re.findall(r"(?<=\$)\d+(?:\.\d\d)?", "cost $12.50 or $7"), re.compile(r"a{2,3}?").findall("aaaaaaa"))
print(re.sub(r"\s+", " ", "  many   spaces\there \n "), re.escape("a.b*c"), len(re.findall(".", "😀é" * 100)))
text = "\n".join(f"line {i}: key{i % 7}=value{i * 3}" for i in range(2000))
pairs = re.findall(r"key(\d)=value(\d+)", text)
print(len(pairs), pairs[-1], sum(int(v) for _, v in pairs), re.subn(r"value", "v", text)[1])
obj = {"name": "nanofil", "list": [1, 2.5, None, True, "ü\n\"q\""], "nested": {"a": {"b": [{}, []]}},
       "big": 10 ** 30, "float": 1e-7, "uni": "😀"}
js = json.dumps(obj, sort_keys=True)
print(js, json.dumps(obj, indent=2, ensure_ascii=False).count("\n"))
back = json.loads(js)
print(back == obj, json.loads('{"x": [1e400, -0.0, 12345678901234567890]}'), json.loads('"\\ud83d\\ude00"'))
try:
    json.loads('{"a": 1,}')
except json.JSONDecodeError as e:
    print("JSONDecodeError", e.msg, e.pos)
data = [{"id": i, "v": [i * 1.5, str(i)], "t": i % 3 == 0} for i in range(3000)]
s = json.dumps(data)
print(len(s), hashlib.sha1(s.encode()).hexdigest(), json.loads(s)[2999])
packed = struct.pack("<hHiIqQfd?3sx", -2, 65535, -7, 4000000000, -1, 2 ** 64 - 1, 1.5, -2.25, True, b"abc")
print(packed.hex(), struct.calcsize("@ci"), struct.calcsize("=ci"), struct.unpack("<hHiIqQfd?3sx", packed))
print(list(struct.iter_unpack(">HB", bytes(range(9)))), struct.Struct("!I").pack(0xdeadbeef))
for name in ("md5", "sha1", "sha224", "sha256", "sha384", "sha512", "sha3_256", "blake2b", "blake2s"):
    h = hashlib.new(name)
    h.update(b"The quick brown fox " * 1000)
    print(name, h.hexdigest()[:32])
print(hashlib.shake_128(b"x").hexdigest(20), hmac.new(b"key", b"msg", "sha256").hexdigest()[:24])
print(hashlib.blake2b(b"a", digest_size=16, key=b"k").hexdigest())
print(base64.b64encode(bytes(range(40))), base64.b32decode(b"MFRGGZDF"), binascii.crc32(b"hello" * 99), base64.a85encode(b"nanofil"))
EOF
run formats formats.py

cat >control.py <<'EOF'
import sys, traceback, contextlib, gc, weakref, itertools
def gen(n):
    for i in range(n):
        x = yield i * i
        if x:
            yield -x
g = gen(10)
print(next(g), g.send(5), next(g), list(g))
def chain(*its):
    for it in its:
        yield from it
print(list(chain(range(3), "ab", (x for x in [9]))), sum(x for x in range(1000) if x % 7 == 3))
def counter():
    total = 0
    while True:
        try:
            v = yield total
        except ValueError:
            total = -1
        else:
            total += v
c = counter(); next(c)
print(c.send(3), c.send(4), c.throw(ValueError), c.send(10))
c.close()
async def agen():
    for i in range(3):
        yield i
async def amain():
    return [i async for i in agen()]
co = amain()
try:
    co.send(None)
except StopIteration as e:
    print("async", e.value)
class E1(Exception): pass
class E2(E1):
    def __str__(self): return "E2!"
def f(n):
    if n == 0:
        raise E2("deep")
    return f(n - 1)
try:
    f(50)
except E1 as e:
    tb = traceback.extract_tb(e.__traceback__)
    print(type(e).__name__, str(e), len(tb), tb[-1].name)
try:
    try:
        1 / 0
    except ZeroDivisionError as e:
        raise KeyError("k") from e
except KeyError as e:
    print(repr(e), type(e.__cause__).__name__, e.__suppress_context__)
try:
    raise ExceptionGroup("grp", [ValueError(1), TypeError(2), ValueError(3)])
except* ValueError as eg:
    print("star", [str(x) for x in eg.exceptions])
except* TypeError as eg:
    print("star type", len(eg.exceptions))
for bad in ("[][1]", "{}['x']", "int('x')", "None.a", "1 + 'a'", "import nosuchmod", "x = 1 / 0.0", "'%d' % 'a'"):
    try:
        exec(bad, {})
    except Exception as e:
        print(type(e).__name__, e)
def deep(n):
    return deep(n + 1)
sys.setrecursionlimit(400)
try:
    deep(0)
except RecursionError as e:
    print("RecursionError", e)
sys.setrecursionlimit(1000)
@contextlib.contextmanager
def ctx(tag):
    print("enter", tag)
    try:
        yield tag.upper()
    finally:
        print("exit", tag)
with ctx("a") as A, ctx("b") as B:
    print(A + B)
with contextlib.suppress(ZeroDivisionError):
    1 // 0
class Node:
    def __init__(self, n): self.n = n; self.next = None
    def __del__(self): deleted.append(self.n)
deleted = []
gc.collect()
gc.disable()
for i in range(5):
    a, b = Node(2 * i), Node(2 * i + 1)
    a.next, b.next = b, a
del a, b
print("before", sorted(deleted), gc.collect() >= 10, "after", sorted(deleted))
gc.enable()
class K: pass
k = K(); r = weakref.ref(k); d = weakref.WeakValueDictionary(x=k)
print(r() is k, len(d)); del k; gc.collect(); print(r(), len(d))
lst = []
for i in range(100000):
    lst.append([i, str(i), {i: (i,)}])
    if i % 1000 == 0:
        lst = lst[-50:]
print(len(lst), gc.collect() >= 0, lst[-1][1], sys.getrefcount(lst) >= 2)
print(eval(compile("sum(i for i in range(10))", "<s>", "eval")), (lambda *a, **k: (a, sorted(k)))(1, 2, z=3, y=4))
class Meta(type):
    def __new__(m, name, bases, ns): ns["tag"] = name.lower(); return super().__new__(m, name, bases, ns)
class Base(metaclass=Meta):
    __slots__ = ("x",)
    def __init_subclass__(cls, **kw): cls.sub = True
class Derived(Base):
    @property
    def p(self): return self.tag * 2
print(Derived().p, Derived.__mro__[1].__name__, Derived.sub, hasattr(Base(), "__dict__"))
match {"kind": "point", "xy": [3, 4]}:
    case {"kind": "point", "xy": [x, y]} if x < y:
        print("matched", x, y)
EOF
run control control.py

cat >threads.py <<'EOF'
import threading, queue, concurrent.futures, sys
lock = threading.Lock()
count = 0
def work(n):
    global count
    for _ in range(n):
        with lock:
            count += 1
ts = [threading.Thread(target=work, args=(20000,)) for _ in range(6)]
for t in ts: t.start()
for t in ts: t.join()
print("locked count", count)
unlocked = [0]
def bump():
    for _ in range(50000):
        unlocked[0] += 1
ts = [threading.Thread(target=bump) for _ in range(4)]
for t in ts: t.start()
for t in ts: t.join()
print("gil list", len(unlocked))
q = queue.Queue()
out = queue.Queue()
def worker():
    while True:
        item = q.get()
        if item is None:
            break
        out.put(sum(i * item for i in range(1000)))
ws = [threading.Thread(target=worker) for _ in range(4)]
for w in ws: w.start()
for i in range(400): q.put(i)
for _ in ws: q.put(None)
for w in ws: w.join()
res = []
while not out.empty(): res.append(out.get())
print("queue", len(res), sum(res))
cond = threading.Condition()
items = []
def producer():
    for i in range(100):
        with cond:
            items.append(i)
            cond.notify()
def consumer(got):
    while len(got) < 100:
        with cond:
            while not items:
                cond.wait()
            got.append(items.pop(0))
got = []
c = threading.Thread(target=consumer, args=(got,)); p = threading.Thread(target=producer)
c.start(); p.start(); p.join(); c.join()
print("condition", got == list(range(100)))
sem = threading.Semaphore(2); ev = threading.Event(); bar = threading.Barrier(3)
order = []
def staged(i):
    bar.wait()
    with sem:
        order.append(i)
    ev.wait()
ts = [threading.Thread(target=staged, args=(i,)) for i in range(3)]
for t in ts: t.start()
ev.set()
for t in ts: t.join()
print("barrier", sorted(order))
local = threading.local()
def tl(i, r):
    local.v = i
    r[i] = local.v * 10
r = {}
ts = [threading.Thread(target=tl, args=(i, r)) for i in range(5)]
for t in ts: t.start()
for t in ts: t.join()
print("local", sorted(r.items()))
with concurrent.futures.ThreadPoolExecutor(max_workers=4) as ex:
    print("pool", list(ex.map(lambda n: sum(range(n)), range(0, 20000, 2000))))
sys.setswitchinterval(1e-6)
shared = {}
def churn(t):
    for i in range(2000):
        shared[(t, i)] = [i] * 3
        if i % 3 == 0:
            shared.pop((t, i - 3), None)
ts = [threading.Thread(target=churn, args=(t,)) for t in range(4)]
for t in ts: t.start()
for t in ts: t.join()
print("churn", len(shared), threading.active_count())
EOF
run threads threads.py

cat >procs.py <<'EOF'
import subprocess, sys, os, signal
r = subprocess.run([sys.executable, "-c", "import sys; print(sum(range(100))); sys.stderr.write('err\\n'); sys.exit(3)"],
                   capture_output=True, text=True)
print(r.returncode, r.stdout, r.stderr)
r = subprocess.run(["sh", "-c", "echo hi; cat; exit 7"], input=b"from stdin\n", stdout=subprocess.PIPE)
print(r.returncode, r.stdout)
p = subprocess.Popen([sys.executable, "-c", "import sys\nfor l in sys.stdin: print(l.strip()[::-1])"],
                     stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True)
out, _ = p.communicate("abc\nnanofil\n")
print(p.returncode, out.split())
p = subprocess.Popen(["sleep", "30"])
p.send_signal(signal.SIGTERM)
print("killed", p.wait())
print(subprocess.check_output("printf '%s\\n' a b c | wc -l", shell=True).strip())
try:
    subprocess.run(["false"], check=True)
except subprocess.CalledProcessError as e:
    print("CalledProcessError", e.returncode)
rfd, wfd = os.pipe()
pid = os.fork()
if pid == 0:
    os.close(rfd)
    os.write(wfd, b"child %d" % (2 + 2))
    os._exit(5)
os.close(wfd)
print(os.read(rfd, 100), os.waitstatus_to_exitcode(os.waitpid(pid, 0)[1]))
with open("f.txt", "w") as f:
    f.write("x" * 100 + "\n" + "é" * 10)
print(os.path.getsize("f.txt"), open("f.txt", encoding="utf-8").read()[-3:], sorted(os.listdir("."))[:3])
os.rename("f.txt", "g.txt"); os.remove("g.txt"); print(os.path.exists("g.txt"))
EOF
run procs procs.py

run sysexit -c "import sys; print('bye'); sys.exit(42)"
run uncaught -c "def f(): raise ValueError('boom')
f()"
