"""Execute source assembly and translations with the same independent caller."""
import json
import os
from pathlib import Path
import resource
import struct
import subprocess


def check_programs(programs, translator, filcc, native_cc, assembler, *, variants):
    resource.setrlimit(resource.RLIMIT_CORE, (0, 0))
    assembly = [".text"]
    for name, label, body in programs:
        assembly += [f"# {label}", f".globl {name}", f".type {name}, @function",
                     f"{name}: #! unsigned long(ptr, unsigned long)", *body, "ret"]
    assembly += ['.section .note.GNU-stack,"",@progbits']
    Path("generated.s").write_text("\n".join(assembly) + "\n")
    Path("generated-cases.json").write_text(json.dumps(programs, indent=2) + "\n")
    declarations = "\n".join(f"uint64_t {name}(const unsigned char *, uint64_t);" for name, _, _ in programs)
    names = ",".join(name for name, _, _ in programs)
    Path("generated.c").write_text("""#include <stdint.h>
    #include <stdio.h>
    """ + declarations + "\ntypedef uint64_t (*fn)(const unsigned char *, uint64_t);\nfn functions[]={" + names + "};\n" + r"""
    int main(void) {
      unsigned char bytes[256];
      uint64_t state=42, values[64]={0,1,2,31,32,63,64,65,255,256,
        UINT64_C(0x7fffffff), UINT64_C(0x80000000), UINT64_C(0xffffffff),
        UINT64_C(0x100000000), UINT64_C(0x7fffffffffffffff),
        UINT64_C(0x8000000000000000), UINT64_MAX};
      for (unsigned i=17;i<64;i++) {
        state=state*UINT64_C(6364136223846793005)+1;
        values[i]=state;
      }
      for (unsigned f=0;f<sizeof functions/sizeof functions[0];f++)
        for (unsigned v=0;v<64;v++) for (unsigned alignment=0;alignment<4;alignment++) {
          for (unsigned i=0;i<sizeof bytes;i++) bytes[i]=(unsigned char)(i*179+31+v);
          uint64_t result=functions[f](bytes+alignment,values[v]);
          if (fwrite(&result,sizeof result,1,stdout)!=1) return 1;
          if (fwrite(bytes,sizeof bytes,1,stdout)!=1) return 1;
        }
    }
    """)


    def run(args, *, output=None, limit=60):
        with open(output, "wb") if output else open(os.devnull, "wb") as stream:
            result = subprocess.run(args, stdout=stream, stderr=subprocess.PIPE, timeout=limit)
        if result.returncode:
            raise AssertionError((args, result.returncode, result.stderr.decode(errors="replace")))


    run([native_cc, "-O2", "generated.c", "generated.s", "-o", "native-reference"])
    run(["./native-reference"], output="native-results.bin", limit=15)
    expected = Path("native-results.bin").read_bytes()
    record_size = 8 + 256  # Return value plus the entire buffer, including guard bytes.
    records = len(programs) * 64 * 4
    assert len(expected) == records * record_size
    for mode, options in variants:
        run([translator, *options, "generated.s"], output=f"generated-{mode}.s", limit=180)
        run([assembler, f"generated-{mode}.s", "-o", f"generated-{mode}.o"])
        run([filcc, "-O2", "generated.c", f"generated-{mode}.o", "-o", f"translated-{mode}"])
        run([f"./translated-{mode}"], output=f"{mode}-results.bin", limit=15)
        actual = Path(f"{mode}-results.bin").read_bytes()
        assert len(actual) == len(expected), (mode, len(actual), len(expected))
        for i in range(records):
            start = i * record_size
            a, b = expected[start:start + record_size], actual[start:start + record_size]
            if a != b:
                p = i // 256
                byte = next(j for j in range(record_size) if a[j] != b[j])
                difference = (("return", struct.unpack_from("<Q", a)[0], struct.unpack_from("<Q", b)[0])
                              if byte < 8 else ("memory byte", byte - 8, a[byte], b[byte]))
                raise AssertionError((mode, programs[p], "value index", (i % 256)//4,
                                      "alignment", i % 4, "native/translated", difference))
    print(f"native differential: {len(programs)} programs, {records} return-and-memory results x {len(variants)} variants")
