#include <stdlib.h>
#include <stdio.h>

void CSR(int n, int m, double *A, int *rptr, int *cols, double *vals) {
  double *base_vals = vals;
  int *base_cols = cols;
  int nnz = 0;
  rptr[0] = 0;
  for (int i = 0; i < n; ++i) {
    int offset = 0;
    for (int j=0; j < m; ++j) {
      if (A[i*m + j] == 0)
        continue ;
      *base_vals = A[i*m+j]; base_vals++;
      *base_cols = j; base_cols++;
      offset++;
      nnz++;
    }
    rptr[i+1] = rptr[i] + offset;
  }
//  rptr[n] = nnz;
}

int main() {
  int n = 2, m = 2;
  double *A = malloc(sizeof(double)*n*m);
  int *rptr = malloc(sizeof(int)*n*m);
  int *cols = malloc(sizeof(int)*n*m);
  double *vals = malloc(sizeof(double)*n*m);

  A[0] = 0; A[1] = 1;
  A[2] = 1; A[3] = 0;

  CSR(n, m, A, rptr, cols, vals);

  for (int i=0; i < n+1; ++i){
    printf("%d ", rptr[i]);
  }
  printf("\n");

  for (int i=0; i < n; ++i){
    for (int k = rptr[i]; k < rptr[i+1]; ++k)
      printf("%f ", vals[k]);
  }
}