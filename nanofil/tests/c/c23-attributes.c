// run: $attributes 0
// run: $attributes 1
// run: $attributes 2

// Unknown attributes and their balanced arguments are ignored, not evaluated.
[[deprecated("test")]] [[maybe_unused]] static int global = 3;
[[]];
struct [[maybe_unused]] Pair {
    [[maybe_unused]] int first [[maybe_unused]];
    int second;
};
enum [[maybe_unused]] Choice { choice [[maybe_unused]] = 2 };
int prototype(int [[vendor::type]], int * [[vendor::pointer]])
    [[vendor::function]];

[[nodiscard]] int attributes([[__maybe_unused__]] int n)
{
    [[maybe_unused]] int sum = global;
    int [[vendor::type]] value [[gnu::unused]] = choice;
    int * [[vendor::pointer]] pointer = &value;
    int array[2] [[vendor::array]] = { 4, 5 };
    struct Pair pair = { 6, 7 };
    [[vendor::ignored((unbound(1, 2)), [3, 4], {5, 6}),]];
    switch (n) {
    case 0:
        sum += array[0];
        [[__fallthrough__]];
    case 1:
        sum += *pointer;
        break;
    default:
        sum += pair.first;
    }
    if (n == 2) [[vendor::statement]] { sum += pair.second; }
    return sum;
}
