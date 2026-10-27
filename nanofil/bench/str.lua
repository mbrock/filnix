local t={}
for i=1,50000 do t[i]=string.format("k%07d", (i*7919)%50000) end
table.sort(t)
local n=0
for _,v in ipairs(t) do n=n+#v:gsub("%d","") end
print(n, t[1], t[#t])
