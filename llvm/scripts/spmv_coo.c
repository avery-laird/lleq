// https://github.com/Sable/fait-maison-spmv/blob/master/src/sequential/c/spmv_coo.c

void spmv_coo(int *rowind, int *colind, double *val, int nz, int N, double *x, double *y)
{
  int i;
  for(i = 0; i < nz ; i++){
    y[rowind[i]] += val[i] * x[colind[i]];
  }  
}

void spmv_coo_addsingle(int *rowind, int *colind, double *val, int nz, int N, double *x, double *y)
{
  int i;
  if (nz > 0) {
    i = 0;
    y[rowind[i]] += val[i] * x[colind[i]];
  }
}

// How does val relate to A?
// case (1): A[n+1][0] == 0 (technically not possible for coo)
//   nnz := nnz + 0
//   rowind[nnz] == n+1
//   colind[nnz] == 0
//   i == nnz
//   val[nnz] == 0
//   proof:
//   y[rowind[nnz]] + val[nnz] * x[colind[nnz]] ?==? y[n+1] + A[(n+1)*m + m+1]*x[m+1]
//   y[n+1] + val[nnz] * x[0] ?==? y[n+1] + A[(n+1)*m + 0]*x[0]
//   val[nnz] * x[0] ?==? A[(n+1)*m + 0]*x[0]
//   0 * x[0] ?==? 0*x[0] --> T
// case (2): A[n+1][0] != 0
//   nnz := nnz + 1
//   val[nnz] == A[n+1][0]
//   proof:
//   val[nnz] * x[0] ?==? A[(n+1)*m + 0]*x[0]
//   val[nnz] ?==? A[(n+1)*m + 0] --> T
// case (3): A[0][m+1] == 0
//   rowind[m+1] == 0
//   colind[m+1] == m+1
//   i == m+1
//   val[m+1] == A[0][m+1]
//   proof:
//   y[rowind[i]] + val[i] * x[colind[i]] ?==? y[0] + A[0][m+1]*x[m+1]
//   y[0] + val[m+1] * x[m+1] ?==? y[0] + A[0][m+1]*x[m+1]
//   val[m+1] * x[m+1] ?==? A[0][m+1]*x[m+1]
//   0 * x[m+1] ?==? 0 * x[m+1] --> T
// case (4): A[0][m+1] != 0
//   val[m+1] == A[0][m+1]
//   proof:
//   val[m+1] * x[m+1] ?==? A[0][m+1]*x[m+1]
//   val[m+1] ?==? A[0][m+1] --> T