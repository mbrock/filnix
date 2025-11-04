# Fil-C Lighttpd Demo

Memory-safe web server demonstration with interactive CGI examples.

## What This Is

A complete web server stack built with Fil-C memory safety:

- **Lighttpd**: Web server compiled with Fil-C (100% memory-safe)
- **Bash CGI**: Shell script running under memory-safe bash
- **C CGI**: Interactive demo showing bounds-checking in action

## Technical Details

### Memory Safety Stack

Every component runs with complete memory safety:

```
┌─────────────────────────────────────┐
│  Lighttpd (Fil-C compiled)          │
│  - HTTP parsing (memory-safe)       │
│  - CGI execution (memory-safe)      │
│  - Compression: brotli, zstd, bzip2 │
└─────────────────────────────────────┘
         │                    │
    ┌────▼────┐         ┌────▼────┐
    │ Bash    │         │  C CGI  │
    │ (Fil-C) │         │ (Fil-C) │
    └─────────┘         └─────────┘
```

### Build Helpers

#### `bashScript name { deps, code }`
Creates memory-safe bash scripts:
- Uses Fil-C compiled bash as interpreter
- Manages dependencies via `runtimeInputs`
- Supports shellcheck exclusions

#### `filcProgram name { deps, code }`
Builds memory-safe C programs inline:
- Compiles with Fil-C toolchain
- Links against memory-safe dependencies
- No escape from memory safety

#### `cgi-bin { "script.cgi" = derivation; ... }`
Assembles CGI document root from attrset

### Interactive Memory Safety Demo

The C CGI (`demo.cgi`) demonstrates bounds-checking:

1. Shows valid array access (indices 0-4)
2. **Invites user to trigger out-of-bounds access**
3. Fil-C traps the violation instead of crashing

Try: `curl http://localhost:9000/demo.cgi?index=999`

### Sandboxing

Runs under systemd-run scope with resource limits:
- `MemoryMax=512M` - Hard memory limit
- `MemoryHigh=384M` - Soft limit (throttles)
- `TasksMax=128` - Process/thread limit
- `CPUQuota=100%` - Single core cap

### Compression Support

All compression algorithms compiled with Fil-C:
- Brotli
- Zstandard
- Bzip2
- Gzip (zlib)

Test: `curl -H 'Accept-Encoding: br' http://localhost:9000/demo.cgi`

## Running

```bash
nix run .#lighttpd-demo
```

Server auto-selects free port in range 9000-9999 and runs in foreground.

## Architecture

```nix
{
  # Memory-safe helpers
  bashScript = ...;     # Bash with Fil-C interpreter
  filcProgram = ...;    # Inline C compilation
  cgi-bin = ...;        # CGI directory builder
  
  # CGI programs
  hello-cgi = bashScript "hello.cgi" { ... };
  demo-cgi = filcProgram "demo.cgi" { ... };
  
  # Assemble
  cgi-docroot = cgi-bin {
    "hello.cgi" = hello-cgi;
    "demo.cgi" = demo-cgi;
  };
}
```

## Why This Matters

1. **No memory safety escapes**: Every layer is Fil-C compiled
2. **Production-ready stack**: Lighttpd + standard libraries
3. **Live demonstration**: Users can try to break memory safety
4. **Real-world complexity**: HTTP parsing, compression, CGI execution

Traditional C servers have exploitable vulnerabilities in HTTP parsing, compression libraries, and CGI handling. Fil-C eliminates entire vulnerability classes while maintaining compatibility and performance.
