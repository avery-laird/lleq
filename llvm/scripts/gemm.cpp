//
// Created by avery on 10/02/23.
//

extern "C" {

void gemm(int n, int m, double *a, int colsA, double *b,
          double *c) {
  int i, j, k;

  for (i = 0; i < n; ++i) {   /* Loop over the rows of C */
    for (j = 0; j < m; ++j) { /* Loop over the columns of C */
      for (k = 0; k < colsA; ++k) {
        c[i * m + j] += a[i * colsA + k] * b[k * m + j];
      }
    }
  }
}
}