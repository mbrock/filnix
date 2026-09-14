// Exercise stack growth, shrinking and GC through the installed interpreter.
function sum() {
    var result = 0;
    for (var i = 0; i < arguments.length; i++) result += arguments[i];
    return result;
}
for (var round = 0; round < 50; round++) {
    var values = [];
    for (var i = 0; i < 2000; i++) values.push(i);
    if (sum.apply(null, values) !== 1999000) throw new Error('stack values corrupted');
    Duktape.gc();
}
print('Duktape: stack growth, arguments and GC passed');
