// run: $jump_identifiers 0
// run: $jump_identifiers 7
// run: $jump_identifiers -3
// These field names are atoms, not statement-expression AST nodes.
int jump_identifiers(int x) {
    struct {
        int at, label, stmtexpr;
    } fields = {x, x + 1, x + 2};
    return fields.at + fields.label + fields.stmtexpr;
}
