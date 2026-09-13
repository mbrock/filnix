#include <QuadProg++/QuadProg++.hh>
#include <cmath>
#include <iostream>

int main() {
    // min 1/2 x' G x + g' x, subject to x0+x1=3 and x0,x1 >= 0.
    // The unique solution is (1,2), with objective value 12.
    quadprogpp::Matrix<double> g(2, 2), ce(2, 1), ci(2, 2);
    quadprogpp::Vector<double> g0(2), ce0(1), ci0(2), x(2);
    g[0][0] = g[1][1] = 4;
    g[0][1] = g[1][0] = -2;
    g0[0] = 6;
    g0[1] = 0;
    ce[0][0] = ce[1][0] = 1;
    ce0[0] = -3;
    ci[0][0] = ci[1][1] = 1;
    ci[0][1] = ci[1][0] = 0;
    ci0[0] = ci0[1] = 0;
    double cost = quadprogpp::solve_quadprog(g, g0, ce, ce0, ci, ci0, x);
    if (!(std::abs(x[0] - 1) < 1e-10 && std::abs(x[1] - 2) < 1e-10 &&
          std::abs(cost - 12) < 1e-10)) {
        std::cerr << "Unexpected solution: " << x[0] << ", " << x[1]
                  << "; cost " << cost << '\n';
        return 1;
    }
    std::cout << "Verified solution (1,2), cost 12\n";
}
