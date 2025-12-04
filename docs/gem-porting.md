# Gem Porting Workflow

Fast iterative workflow for porting Ruby gems to Fil-C.

## Setup (once)

```bash
mkdir -p /tmp/gem-port && cd /tmp/gem-port
nix develop .#pkgsFilc.ruby.gems.msgpack --command bash -c '
  source $stdenv/setup
  gem unpack $src
  cd *-*/
  patchPhase
  cd ext/msgpack
  ruby extconf.rb
'
```

## Iterate

```bash
cd /tmp/gem-port/*-*/ext/msgpack
nix develop .#pkgsFilc.ruby.gems.msgpack --command make
```

Fix errors with ast-grep, then re-run make.

## Common ast-grep patterns

```bash
# Fix Qfalse passed where int expected
ast-grep run -p 'rb_attr($A, $B, $C, $D, Qfalse)' \
             -r 'rb_attr($A, $B, $C, $D, 0)' \
             -l c --selector call_expression -U .

# Fix Qtrue passed where int expected
ast-grep run -p 'rb_cstr_to_inum($A, $B, Qtrue)' \
             -r 'rb_cstr_to_inum($A, $B, 1)' \
             -l c --selector call_expression -U .
```

## Generate patch for rubyports.nix

Once working, add fixes to `rubyports.nix` using `astGrep` or `replace` helpers.
