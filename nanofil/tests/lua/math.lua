-- libm calls, float/integer results, multiple float results, and the
-- unsigned arithmetic in Lua's deterministic random-number generator.
assert(math.sqrt(2.25) == 1.5)
assert(math.floor(-1.25) == -2 and math.ceil(-1.25) == -1)
assert(math.fmod(-7.5, 2.0) == -1.5)
local i, f = math.modf(-3.25)
assert(i == -3 and f == -0.25)
assert(math.abs(math.sin(math.pi / 2) - 1) < 1e-15)
assert(math.ult(math.maxinteger, math.mininteger))
for _, x in ipairs({0.125, 0.5, 1.0, 1.5, 2.0, 10.0}) do
  print(string.format('%.17g %.17g %.17g %.17g %.17g %.17g',
                      math.sqrt(x), math.log(x), math.exp(x),
                      math.sin(x), math.cos(x), math.atan(x, 0.75)))
end
math.randomseed(0x1234, 0x5678)
for _ = 1, 20 do
  print(string.format('%016x %.17g %d', math.random(0), math.random(),
                      math.random(-100000, 100000)))
end
print('math OK')
