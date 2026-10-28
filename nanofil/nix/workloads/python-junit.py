# Per-test results from regrtest's --junit-xml file: one line per test
# case, "NAME RESULT", sorted, RESULT ok, FAIL, ERROR or SKIP. Run it with
# the reference interpreter, so the comparison does not trust the build
# under test.
import sys
import xml.etree.ElementTree as ET

lines = []
for case in ET.parse(sys.argv[1]).iter("testcase"):
    kinds = {child.tag for child in case}
    if "failure" in kinds:
        result = "FAIL"
    elif "error" in kinds:
        result = "ERROR"
    elif "skipped" in kinds:
        result = "SKIP"
    else:
        result = "ok"
    lines.append(f"{case.get('name')} {result}")
print("\n".join(sorted(lines)))
