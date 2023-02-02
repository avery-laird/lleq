//
// Created by bangtian on 26/08/22.
//
#include "util.h"
#include <cstring>

int csc_to_csr(int nrow, int ncol, int *Ap, int *Ai, double *Ax, int *&rowptr,
               int *&colind, double *&values)
{
    // count row entries to generate row ptr
    int nnz = Ap[ncol];
    int *rowCnt = new int[nrow]();
    for (int i = 0; i < nnz; i++)
        rowCnt[Ai[i]]++;

    rowptr = new int[nrow + 1]();
    int counter = 0;
    for (int i = 0; i < nrow; i++)
    {
        rowptr[i] = counter;
        counter += rowCnt[i];
    }
    rowptr[nrow] = nnz;

    colind = new int[nnz]();
    values = new double[nnz]();

    memset(rowCnt, 0, sizeof(int) * nrow);
    for (int i = 0; i < ncol; i++)
    {
        for (int j = Ap[i]; j < Ap[i + 1]; j++)
        {
            int row = Ai[j];
            int index = rowptr[row] + rowCnt[row];
            colind[index] = i;
            values[index] = Ax[j];
            rowCnt[row]++;
        }
    }
    delete[] rowCnt;

    return 0;
}