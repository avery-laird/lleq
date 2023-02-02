//
// Created by bangtian on 26/08/22.
//

#ifndef RV_TESTS_UTIL_H
#define RV_TESTS_UTIL_H

int csc_to_csr(int nrow, int ncol, int *Ap, int *Ai, double *Ax, int *&rowptr,
               int *&colind, double *&values);
#endif //RV_TESTS_UTIL_H
