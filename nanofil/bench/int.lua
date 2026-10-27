local s=0
for i=1,2000000 do s=(s+i*17)%1000000007 end
print(s)
