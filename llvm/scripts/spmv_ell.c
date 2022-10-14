void spmv_ell(int *indices, double *data, int N, int nc, double *x, double *y)
{
  int i, j;
  for(j = 0; j < nc ; j++){
    for(i = 0; i < N; i++){
      y[i] += data[j * N + i] * x[indices[j * N + i]];
    }
  }
}