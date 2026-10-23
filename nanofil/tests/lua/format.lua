-- Several doubles in each variadic formatting call, signed zero, and
-- Lua's integer/number formatting paths. The output is compared exactly.
for _, x in ipairs({0.0, -0.0, 0.1, -1.5, 0x1p-1074,
                    0x1.fffffffffffffp1023, 0x1p63,
                    math.huge, -math.huge}) do
  print(string.format('%a | %.17g | %.6e | %.3f', x, x, x, x))
end
print(string.format('%g %g %g %g %g %g %g %g %g %g',
                    1.25, 2.5, 3.75, 4.5, 5.25, 6.5, 7.75, 8.5, 9.25, 10.5))
print(string.format('%d %x %u %q %q', math.mininteger, math.maxinteger,
                    -1, 0x1.23456789abcdep-42, -0.0))
assert(string.format('%.2f', 1.125) == '1.12')
assert(string.format('%.2f', 1.375) == '1.38')
print('format OK')
