/* printf's floating conversions and strtod, on values chosen for their
   rounding: halfway cases, subnormals, the extremes, infinities, NaN and
   negative zero, in float, double and long double. */
#include <float.h>
#include <math.h>
#include <stdio.h>
#include <stdlib.h>

int main(void)
{
    double v[] = { 0.0, -0.0, 1.0, 0.1, 0.5, 1.5, 2.5, 1e-5, 123456.789, 1.0 / 3.0, 2.0 / 3.0,
                   1e21, 1e22, 9.999999999999999e22, 5e-324, 2.2250738585072014e-308,
                   DBL_MAX, -DBL_MIN, 0.125, 1234.5, 0.000123456, 1e100, INFINITY, -INFINITY, NAN };
    for (unsigned i = 0; i < sizeof v / sizeof v[0]; i++)
        printf("%f|%.3e|%g|%.17g|%a|%10.4f|%-12.2e|%+.0f|%#g\n", v[i], v[i], v[i], v[i], v[i], v[i], v[i], v[i], v[i]);
    long double l[] = { 1.0L / 3.0L, LDBL_MAX, LDBL_MIN, 1e4000L, -2.5L };
    for (unsigned i = 0; i < sizeof l / sizeof l[0]; i++) printf("%Lg|%.20Le|%La\n", l[i], l[i], l[i]);
    float f = 0.1f;
    printf("%.10f %a %g\n", f, f, (double) FLT_MAX);
    const char *in[] = { "0.1", "1e-320", "1.7976931348623157e308", "1e309", "-0", "0x1.8p1", "nan", "-inf",
                         "2.2250738585072011e-308", "123.456e-2xyz", "4.9406564584124654e-324" };
    for (unsigned i = 0; i < sizeof in / sizeof in[0]; i++) {
        char *end;
        double d = strtod(in[i], &end);
        printf("strtod %s -> %.17g %a rest[%s]\n", in[i], d, d, end);
    }
    printf("strtof %a strtold %La\n", strtof("3.4028235e38", NULL), strtold("1.1", NULL));
    return 0;
}
