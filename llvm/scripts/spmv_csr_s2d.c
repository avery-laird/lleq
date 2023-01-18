//
// Created by avery on 16/01/23.
//
#include <stdio.h>
#include <stdlib.h>

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

void spMV_Mul_csr(int n, int* rowPtr, int* col, double* val, double *x, double *y)
{
  int i,k;
  double sum;

  for (i=0; i<n; i++) {
    sum = 0.0;
    for(k=rowPtr[i]; k<rowPtr[i+1]; k++){
      sum += val[k]*x[col[k]];
    }
    y[i] = sum;
  }
}


void gemv(int n, int m, double *y, double *A, double *x)
{
  int i,k;

  for (i=0; i<n; i++) {
    y[i] = 0.0;
    for(k=0; k<m; k++){
      y[i] += A[i*m + k]*x[k];
    }
  }
}


int main() {
  int n = 1, m = 1; // step
  double *A = malloc(sizeof(double)*n*m);
  double *x = malloc(sizeof(double)*m);
  double *y1 = malloc(sizeof(double)*m);
  double *y2 = malloc(sizeof(double)*m);
  int *rptr = malloc(sizeof(int)*n*m);
  int *cols = malloc(sizeof(int)*n*m);
  double *vals = malloc(sizeof(double)*n*m);

  A[0] = 1;

  CSR(n, m, A, rptr, cols, vals);

  y1[0] = 0;
  y2[0] = 0;
  x[0] = 0; // case 1

  spMV_Mul_csr(n, rptr, cols, vals, x, y1);
  gemv(n, m, y2, A, x);

  printf("case 1: %f %f\n", y1[0], y2[0]);

  y1[0] = 0;
  y2[0] = 0;
  x[0] = 1; // case 2
  spMV_Mul_csr(n, rptr, cols, vals, x, y1);
  gemv(n, m, y2, A, x);

  printf("case 2: %f %f\n", y1[0], y2[0]);

  // for case any n.... need symbolic evaluation!

}