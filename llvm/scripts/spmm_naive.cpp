//
// Created by avery on 13/02/23.
//

extern "C" {

void spmm_naive_csr(int N, int M, int *rowptr, double *vals, int *col, double *C, double *B) {
  double sum;
  for (int i=0; i<N; ++i) {
    for (int j=0; j<M; ++j) {
      sum = 0.0;
      for (int e=rowptr[i]; e<rowptr[i+1]; ++e) {
        sum += vals[e] * B[col[e]*M + j];
      }
      C[i*M + j] = sum;
    }
  }
}

void spmm_naive_csr_oneelement(int M, int N, int *rowptr, double *vals, int *col, double *C, double *B) {
  int i, e, j;
  if (M > 0) {
    i=0;
    e=rowptr[i];
    if (N > 0) {
      j = 0;
      C[i*N + j] += C[i*N + j] + vals[e] * B[col[e]*N + j];
    }
  }
}

}