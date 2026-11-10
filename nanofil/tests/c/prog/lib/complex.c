/* clang's side of complex.c: complex values across the call boundary. */
_Complex double cl_rot(_Complex double z) { return z * 1.0i; }
_Complex float cl_halve(_Complex float z) { return z / 2; }
long double cl_im(_Complex long double z) { return __imag__ z; }
struct holder { char tag; _Complex float f; _Complex double d; };
double cl_sum(struct holder h) { return __real__ h.f + __imag__ h.f + __real__ h.d + __imag__ h.d + h.tag; }
_Complex double nf_conj(_Complex double z);
_Complex float nf_scale(_Complex float z, float k);
long double nf_ldre(_Complex long double z);
double cl_calls(void)
{
    _Complex double a = nf_conj(3.0 + 4.0i);
    _Complex float b = nf_scale(1.0f - 2.0if, 3.0f);
    return __real__ a * 1000 + __imag__ a * 100 + __real__ b * 10 + __imag__ b + nf_ldre(7.0L + 1.0iL);
}
