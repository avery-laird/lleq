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

int main() {}

//int main() {
//
//  int i0, i1, sum0, sum1;
//
//  for (int i0 = 0; i0 < n; ++i0)
//    sum0 += arr[i0];
//
//  for (int i1 = 0; i1 < n; ++i1)
//    if (arr[i1] != 0)
//      sum1 += arr[i1];
//
//  assert(sum0 == sum1);
//}

