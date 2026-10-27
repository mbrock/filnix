local t={}
for i=1,1000 do t[i]=i*3 end
local s=0
for r=1,2000 do for i=1,1000 do s=s+t[i] end end
print(s)
