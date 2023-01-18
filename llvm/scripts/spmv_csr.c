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


void spMV_Mul_csr_addrow(int n, int* rowPtr, int* col, double* val, double *x, double *y)
{
  int i,k;
  double sum;

  sum = 0.0;
  for(k=rowPtr[n]; k<rowPtr[n+1]; k++){
    sum += val[k]*x[col[k]];
  }
  y[n] = sum;
}

void spMV_Mul_csr_addcol(int n, int* rowPtr, int* col, double* val, double *x, double *y)
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

void spMV_Mul_csr_addsingle(int n, int* rowPtr, int* col, double* val, double *x, double *y)
{
  double sum;

  sum = 0.0;
  sum += val[rowPtr[n+2]]*x[col[rowPtr[n+2]]];
  y[n+1] = sum;
}


void spMV_Mul_csr_addsingle_withbranch(int n, int* rowPtr, int* col, double* val, double *x, double *y)
{
  int i,k;
  double sum;

  if (n > 0) {
    i = 0;
    sum = 0.0;
    if (rowPtr[i] < rowPtr[i+1]) {
      k = rowPtr[i];
      sum += val[k]*x[col[k]];
    }
    y[i] = sum;
    i = i + 1;
  }
}

// how does val relate to A?
// val ~ A
// rptr[n+1] == nnz (fact)
// case (1): A[n+1][0] == 0
//   nnz := nnz + 0
//   val[rptr[n+2]] == 0
//   proof:
//   val[rowPtr[n+2]]*x[col[rowPtr[n+2]]] ?==? A[(n+1)*m + 0]*x[0]
//   0 * x[col[rowPtr[n+2]]] ?==? 0*x[0]
//   0 ?==? 0 --> T
// case (2): A[n+1][0] != 0
//   nnz := nnz + 1
//   val[rptr[n+2]] == A[n+1][0]
//   rowPtr[n+2] == nnz
//   col[nnz] == 0
//   proof:
//   val[rowPtr[n+2]]*x[col[rowPtr[n+2]]] ?==? A[(n+1)*m + 0]*x[0]
//   A[n+1][0]*x[col[rowPtr[n+2]]] ?==? A[n+1][0]*x[0]
//   x[col[rowPtr[n+2]]] ?==? x[0]
//   x[col[nnz]] ?==? x[0]
//   x[0] ?==? x[0] --> T
// case (3): A[0][m+1] == 0
//   nnz := nnz + 0
//   val[rptr[1]-1] == 0
//   proof:
//   val[rptr[1]-1]*x[col[rptr[1]-1]] ?==? A[0][m+1]*x[m+1]
//   0 * x[col[rptr[1]-1]] ?==? 0 * x[m+1]
//   0 ?==? 0 --> T
// case (4): A[0][m+1] != 0
//   nnz := nnz + 1
//   val[rptr[1]-1] == A[0][m+1]
//   col[rptr[1]-1] == m+1
//   proof:
//   val[rptr[1]-1]*x[col[rptr[1]-1]] ?==? A[0][m+1]*x[m+1]
//   A[0][m+1]*x[col[rptr[1]-1]] ?==? A[0][m+1]*x[m+1]
//   x[col[rptr[1]-1]] ?==? x[m+1]
//   x[m+1] ?==? x[m+1] --> T

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

