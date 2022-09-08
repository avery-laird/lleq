// https://github.com/Sable/fait-maison-spmv/blob/master/src/sequential/c/spmv_coo.c

void spmv_coo(int *rowind, int *colind, double *val, int nz, int N, double *x, double *y)
{
  int i;
  for(i = 0; i < nz ; i++){
    y[rowind[i]] += val[i] * x[colind[i]];
  }  
}