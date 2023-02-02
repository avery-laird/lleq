#include <Sparse>

typedef Eigen::SparseMatrix<double> SpMat;

int main() {
  int n, m;
  SpMat A(n, m);
  Eigen::VectorXd x(m);
  auto y = A*x;
  return y[0];
}