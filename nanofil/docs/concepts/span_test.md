# span_test / span test

`span_test(Lo, Hi)` of a pointer P0 is 1 when P0's object contains `[P0+Lo, P0+Hi)`, addresses taken modulo 2^64 and compared unsigned, and 0 otherwise, including for a null, function, external or freed capability. It never traps and reaches no safepoint: it is the [[guard]] that `--checks=guard` puts before a loop.

- A [[renew_if]] of P reads its result G. `ir:guard_covers/5` accepts it when G is a single-definition span test of a single-definition P0 and P's [[guard-chain|guard chain]] puts P's span inside the tested one. Where G is 0 the renew_if runs the full check out of line.
- interp.pl evaluates it in `interp:kind_res/8`; Validate.v transcribes [guard_covers]. Guard.v proves the trust sound: [span_test_ok], [guard_inside], [renew_inside], and along runs [run_guard_checked].

The subtlety: the span test reduces its two addresses modulo 2^64 separately, so their difference is the span's width only because the width is below 2^64, which `ir:valid_op/1` ensures by bounding Lo and Hi as signed 64-bit offsets.

See [rocq.md, Guards and limits](../rocq.md#guards-and-limits) and [m7.md](../m7.md), round 5.
