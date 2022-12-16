void spMV_Mul_csr(int n, int* rowPtr, int* col, double* val, double *x, double *y)
{
  int i,k;
  double sum;

  for (i=0; i<n; i++) {
    sum = 0.0;
    for(k=rowPtr[i]; k<rowPtr[i+1]; k++){
      sum = sum + val[k]*x[col[k]];
    }
    y[i] = sum;
  }
}

int main() {}

