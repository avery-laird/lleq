//
// Created by avery on 13/02/23.
//

extern "C" {

void spmm_naive_csr(int M, int N, int *rowptr, double *vals, int *col, double *C, double *B) {
  for (int i=0; i<M; ++i) {
    for (int e=rowptr[i]; e<rowptr[i+1]; ++e) {
      for (int j=0; j<N; ++j) {
        C[i*N + j] += C[i*N + j] + vals[e] * B[col[e]*N + j];
      }
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