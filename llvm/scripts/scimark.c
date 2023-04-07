void SparseCompRow_matmult( int M, double *y, double *val, int *row,
                           int *col, double *x)
{
  int r;
  int i;
        
  for (r=0; r<M; r++)
  {
    double sum = 0.0;
    int rowR = row[r];
    int rowRp1 = row[r+1];
    for (i=rowR; i<rowRp1; i++)
      sum += x[ col[i] ] * val[i];
    y[r] += sum;
  }
}