local parse = require("./sarcasm/x86_64_parse")
local cg = require("./sarcasm/x86_64_codegen")
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
