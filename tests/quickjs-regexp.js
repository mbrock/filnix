// Greedy quantifiers take lre_exec_backtrack's no_recurse path, whose
// match position used to lose its Fil-C capability.
function check(got, want) {
  const g = JSON.stringify(got);
  if (g !== JSON.stringify(want)) throw new Error(g + " !== " + JSON.stringify(want));
}
check(/a+/.exec("xaa")[0], "aa");
check(/.*/.exec("abc")[0], "abc");
check("a  b   c".replace(/\s+/g, " "), "a b c");
check(/^(\w+)\s*=\s*(.*?);?$/.exec("key = value;").slice(1), ["key", "value"]);
check("\u00e9t\u00e9 caf\u00e9".match(/\p{L}+/gu), ["\u00e9t\u00e9", "caf\u00e9"]);
check("x".repeat(10000).replace(/x*/, "y"), "y");
console.log("quickjs regexp ok");
