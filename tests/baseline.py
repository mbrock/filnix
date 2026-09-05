#!/usr/bin/env python3
"""Exercise the installed Fil-C baseline, using its manifest rather than PATH."""
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile

packages = json.loads(Path(sys.argv[1]).read_text())["packages"]


def output(name, kind="out"):
    return Path(packages[name]["outputs"][kind])


def executable(name, command):
    for root in packages[name]["outputs"].values():
        candidate = Path(root) / "bin" / command
        if candidate.exists():
            return str(candidate)
    raise RuntimeError(f"{name} does not provide {command}")


def run(name, command, *args, **kwargs):
    result = subprocess.run([executable(name, command), *args], check=True,
                            text=True, stdout=subprocess.PIPE, **kwargs)
    print(f"{name}: {command} passed", flush=True)
    return result.stdout


with tempfile.TemporaryDirectory() as tmp:
    os.chdir(tmp)
    assert run("bash", "bash", "-c", "x=6; printf '%s' $((x*7))") == "42"
    assert run("sqlite", "sqlite3", ":memory:",
               "create table t(x); insert into t values(20),(22); select sum(x) from t;").strip() == "42"
    assert run("jq", "jq", ".value + 1", input='{"value":41}').strip() == "42"
    assert run("jq", "jq", 'test("^safe[0-9]+$")', input='"safe42"').strip() == "true"
    run("python312", "python3", "-c", '''
import bz2, ctypes, dbm.gnu, hashlib, json, lzma, readline, sqlite3, ssl, zlib
payload = b"Fil-C baseline" * 1000
for module in (bz2, lzma, zlib):
    assert module.decompress(module.compress(payload)) == payload
assert sqlite3.connect(":memory:").execute("select 6*7").fetchone()[0] == 42
assert hashlib.sha256(b"abc").hexdigest() == "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
assert ctypes.CFUNCTYPE(ctypes.c_int, ctypes.c_int)(lambda x: x + 1)(41) == 42
with dbm.gnu.open("baseline.db", "c") as db:
    db[b"key"] = payload
    assert db[b"key"] == payload
assert ssl.SSLContext(ssl.PROTOCOL_TLS_CLIENT)
''')
    assert run("perl", "perl", "-e", "print 6*7") == "42"
    assert run("ruby_3_3", "ruby", "-rjson", "-rfiddle", "-e", 'puts JSON.parse(%q({"v":42}))["v"]') == "42\n"
    assert run("lua", "lua", "-e", "print(6*7)").strip() in ("42", "42.0")
    for name, command in [("openssl", "openssl"), ("openssl-sarcasm", "openssl")]:
        assert "ba7816bf8f01cfea" in run(name, command, "dgst", "-sha256", input="abc")
    Path("payload").write_text("cached and safe\n")
    assert run("curlMinimal", "curl", "--fail", Path("payload").resolve().as_uri()) == "cached and safe\n"
    run("openssh", "ssh-keygen", "-q", "-t", "ed25519", "-N", "", "-f", "key")
    run("openssh", "ssh-keygen", "-l", "-f", "key.pub")
    run("git", "git", "init", "-q", "repo")
    run("git", "git", "-C", "repo", "status", "--porcelain")
    run("gnutar", "tar", "cf", "payload.tar", "payload")
    assert "payload" in run("gnutar", "tar", "tf", "payload.tar")
    source = Path("consumer.c")
    source.write_text('''
#include <assert.h>
#include <sqlite3.h>
#include <ffi.h>
#include <zlib.h>
static int plus_one(int x) { return x + 1; }
int main(void) {
    sqlite3 *db; assert(sqlite3_open(":memory:", &db) == SQLITE_OK);
    assert(sqlite3_exec(db, "select 42", 0, 0, 0) == SQLITE_OK);
    assert(sqlite3_close(db) == SQLITE_OK);
    ffi_cif cif; ffi_type *types[] = { &ffi_type_sint };
    int arg = 41; ffi_arg result = 0; void *values[] = { &arg };
    assert(ffi_prep_cif(&cif, FFI_DEFAULT_ABI, 1, &ffi_type_sint, types) == FFI_OK);
    ffi_call(&cif, FFI_FN(plus_one), &result, values); assert(result == 42);
    assert(zlibVersion()[0] == '1'); return 0;
}
''')
    flags = []
    for name, library in [("sqlite", "sqlite3"), ("libffi", "ffi"), ("zlib", "z")]:
        include = output(name, "dev") / "include"
        libs = output(name, "out") / "lib"
        flags += [f"-I{include}", f"-L{libs}", f"-Wl,-rpath,{libs}", f"-l{library}"]
    run("filcc", "clang", "-O2", str(source), *flags, "-o", "consumer")
    subprocess.run(["./consumer"], check=True)
print("baseline: runtime and development-output checks passed", flush=True)
