# CPython's decimal module uses the system libmpdec.
{ pkgsFilc }:
pkgsFilc.runCommand "filc-python-decimal-check" { } ''
  ${pkgsFilc.python3}/bin/python3 -c '
  from decimal import Decimal, getcontext
  getcontext().prec = 50
  assert str(Decimal("1.5")) == "1.5"
  assert str(Decimal(2).sqrt())[:12] == "1.4142135623"
  assert str(Decimal("12345678901234567890") * Decimal("98765432109876543210")) == "1219326311370217952237463801111263526900"
  assert repr(12.3) == "12.3", repr(12.3)
  print("decimal and float repr ok")
  '
  touch $out
''
