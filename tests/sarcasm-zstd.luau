local parse = require("./sarcasm/x86_64_parse")
local cg = require("./sarcasm/x86_64_codegen")
local isa = require("./sarcasm/x86_64_isa")
local function instructions(text)
    local result = {}
    for _, node in parse.parseString(text, "att") do
        if node.kind == "insn" then table.insert(result, node) end
    end
    return result
end
local nodes = instructions("movq (%rdi), %rax; addq $1, %rax; ret\n")
assert(#nodes == 3)
for _, node in nodes do assert(node.line == 1) end
nodes = instructions("movq $0, %rax; movq (%rdi), %rax #! load ptr\nret")
assert(#nodes == 3 and not nodes[1].annotation and nodes[2].annotation == "load ptr")
assert(nodes[3].line == 2)
nodes = instructions('movq $1, %rax # comment ; ret ;! load ptr\nret')
assert(#nodes == 2 and not nodes[1].annotation)
local strings = parse.parseString('.asciz "a; b;! c \\"; d"; .byte 1', "att")
assert(strings[1].kind == "directive" and strings[1].name == ".asciz")
assert(strings[2].kind == "directive" and strings[2].name == ".byte")
nodes = instructions("lock; addq $1, (%rdi); ret")
assert(#nodes == 2 and nodes[1].lockPrefix)
nodes = instructions("entry: lock; addq $1, (%rdi); ret")
assert(#nodes == 2 and nodes[1].lockPrefix)
for _, prefix in {"rep", "repe", "repz"} do
    nodes = instructions("entry: " .. prefix .. "; movsq; ret")
    assert(#nodes == 2 and nodes[1].repPrefix == prefix)
    isa.classify(nodes[1])
end
for _, text in {"repne; movsq; ret", "repnz; movsq; ret", "lock; ret"} do
    local ok = pcall(function() isa.classify(instructions(text)[1]) end)
    assert(not ok, "invalid prefix must still be rejected: " .. text)
end
local located = parse.parseString("nop; ret\n", "att", "statements.S")
assert(located[1].line == 1 and located[2].line == 1)
assert(located[1].file == "statements.S" and located[2].file == "statements.S")
local ok, diagnostic = pcall(function()
    parse.parseString("nop; lock;\n", "att", "statements.S")
end)
assert(not ok and string.find(tostring(diagnostic), "statements.S:1", 1, true))
-- Local numeric labels on the same physical line resolve by statement order.
local labels = parse.parseString("1: nop; jmp 1f; 1: ret", "att")
assert(labels[1].name ~= labels[4].name)
assert(labels[3].operands[1].text == labels[4].name)
for _, text in {"movq (%rdi), %rax", "movw %ax, (%rdi)", "movzwl (%rdi), %eax"} do
    local width, align = cg.accessSizeAlign(instructions(text)[1])
    assert(width > 1 and align == 1)
end
local width, align = cg.accessSizeAlign(instructions("lock; addq $1, (%rdi)")[1])
assert(width == 8 and align == 8)
print("semicolon parser and access-width checks passed")
-- `#` comments: full-line, after split statements, hiding `;`, `"` and `#!`
nodes = instructions('# 1 "x.S"\nnop; nop # a; b "c #! load ptr\n\tret; # only a comment')
assert(#nodes == 3 and not nodes[2].annotation and nodes[3].line == 3)
nodes = instructions("nop; movq (%rdi), %rax #! load ptr # not; split")
assert(#nodes == 2 and nodes[2].annotation == "load ptr")
print("comment checks passed")
