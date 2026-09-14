"""Embed CAVA's text resources as C arrays instead of assembler incbin data."""
from pathlib import Path
import re

source = Path("config.c")


def embed(match):
    name, filename = match.groups()
    data = Path(filename).read_bytes()
    chunks = [data[i:i + 24] for i in range(0, len(data), 24)] or [b""]
    literals = "\n".join('    "' + ''.join(f"\\{byte:03o}" for byte in chunk) + '"'
                         for chunk in chunks)
    # INCTXT's size includes the trailing NUL; config.c subtracts it for fwrite.
    return (f"static const char g{name}Data[] =\n{literals};\n"
            f"static const unsigned int g{name}Size = sizeof(g{name}Data);")


text, count = re.subn(r'INCTXT\((\w+), "([^"\n]+)"\);', embed, source.read_text())
if not count:
    raise SystemExit("CAVA no longer declares INCTXT resources")
source.write_text(text)
