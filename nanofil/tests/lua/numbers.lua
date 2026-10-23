-- Exercise Lua's float VM operations and binary64 parsing/conversions.
local function bits(x)
  return string.format('%016x', string.unpack('<I8', string.pack('<d', x)))
end
local tiny = assert(tonumber('0x1p-1074'))
assert(tiny > 0 and tiny / 2 == 0)
assert(bits(tiny * 3 / 2) == '0000000000000002')
assert(bits(-0.0) == '8000000000000000')
assert(1 / -0.0 == -math.huge)
assert(1.0 + 0x1p-53 == 1.0)
assert(tonumber('1.00000000000000011102230246251565404236316680908203125') == 1.0)
assert(tonumber('1.00000000000000011102230246251565404236316680908203126') > 1.0)
local nan = 0.0 / 0.0
assert(nan ~= nan and not (nan < 0) and not (nan >= 0))
assert(math.tointeger(3.0) == 3 and math.tointeger(3.25) == nil)
assert(math.tointeger(math.huge) == nil and math.tointeger(nan) == nil)
assert(math.tointeger(math.maxinteger + 0.0) == nil)
assert(math.tointeger(math.mininteger + 0.0) == math.mininteger)
for _, x in ipairs({0.0, -0.0, tiny, tiny * 3, 0x1p-1022,
                    1.0, 1.0 + 0x1p-52, -1.5,
                    math.mininteger + 0.0, math.maxinteger + 0.0,
                    math.huge, -math.huge}) do
  print(bits(x), bits(x + 0.0), bits(x * -0.5), bits(x / 3.0))
end
-- A loop with float values flowing through table accesses and calls.
local function sum(xs)
  local n = 0.0
  for _, x in ipairs(xs) do n = n + x end
  return n
end
assert(sum({1.5, -0.25, 0.125, 2.0}) == 3.375)
print('numbers OK', bits(sum({1.5, -0.25, 0.125, 2.0})))
