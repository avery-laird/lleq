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


void gemv_addrow(int n, int m, double *y, double *A, double *x)
{
  int i,k;
  y[n] = 0.0;
  for(k=0; k<m; k++){
    y[n] += A[n*m + k]*x[k];
  }
}

void gemv_addcol(int n, int m, double *y, double *A, double *x)
{
  int i,k;
  for (i=0; i<n; i++) {
    y[i] = 0.0;
    y[i] += A[i*m + m]*x[m];
  }
}

void gemv_addsingle(int n, int m, double *y, double *A, double *x)
{
  y[n+1] = 0.0;
  y[n+1] += A[(n+1)*m + m+1]*x[m+1];
}


void gemv_addsingle_withbranch(int n, int m, double *y, double *A, double *x)
{
  int i,k;
  if (n > 0) {
    i = 0;
    y[i] = 0.0;
    if (m > 0) {
      k = 0;
      y[i] += A[i*m + k]*x[k];
    }
  }
}