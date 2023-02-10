//
// Created by avery on 10/02/23.
//

extern "C" {

void gemm(int m, int n, int k, double *a, int lda, double *b, int ldb,
          double *c, int ldc) {
  int i, j, p;

  for (i = 0; i < m; ++i) { /* Loop over the rows of C */
    for (j = 0; j < n; ++j) {   /* Loop over the columns of C */
      for (p=0; p<k; ++p){
        c[i*ldc + j] += a[i*lda + p] * b[p*ldb + j];
      }
    }
  }
}

}