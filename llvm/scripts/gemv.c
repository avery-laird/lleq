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

