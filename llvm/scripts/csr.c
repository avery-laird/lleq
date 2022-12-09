#include <stdlib.h>
#include <stdio.h>

//typedef struct Compressed {
//  int *rptr;
//  int *cols;
//  double *vals;
//} Compressed;
void CSR(int n, int m, double *A, int *rptr, int *cols, double *vals) {
  int vals_idx = 0, cols_idx = 0;
  int nnz = 0;
  rptr[0] = 0;
  for (int i = 0; i < n; ++i) {
    int offset = 0;
    for (int j=0; j < m; ++j) {
      if (A[i*m + j] == 0)
        continue ;
      vals[vals_idx++] = A[i*m+j];
      cols[cols_idx++] = j;
      offset++;
      nnz++;
    }
    rptr[i+1] = rptr[i] + offset;
  }
  return;
}

int main() {
  int n = 1, m = 1;
  double *A = malloc(sizeof(double)*n*m);
  int *rptr = malloc(sizeof(int)*n*m);
  int *cols = malloc(sizeof(int)*n*m);
  double *vals = malloc(sizeof(double)*n*m);

  A[0] = 1;
//  A[1] = 1;
//  A[2] = 1; A[3] = 0;

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