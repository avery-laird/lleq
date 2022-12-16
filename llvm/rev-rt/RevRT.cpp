#include "mkl_spblas.h"

enum BACKENDS {
  MKL, TACO
};

#ifndef BACKEND
#define BACKEND MKL
#endif

extern "C" {
  bool SPMV_CSR_D(int n, int *rowPtr, int *col, double *val, double *x,
                  double *y) {
    bool flag = true;
    // checking the monotonicity of rowPtr
  #pragma omp parallel for reduction(&& : flag)
    for (int i = 0; i < n; i++) {
      flag = flag && (rowPtr[i] < rowPtr[i + 1]);
    }
    if (!flag)
      return false;

    bool col_flag = true;
  #pragma omp parallel for reduction(&& : col_flag)
    for (int i = 0; i < n; i++) {
      bool col_f = true;
      for (int j = rowPtr[i]; j < rowPtr[i + 1] - 1; j++) {
        if (col[j] >= col[j + 1]) {
          col_f = false;
          break;
        }
      }

      col_flag = col_flag && col_f;
    }
    if (!col_flag)
      return false;

    if (BACKEND == MKL) {
      sparse_matrix_t A;
      mkl_sparse_d_create_csr(&A, SPARSE_INDEX_BASE_ZERO, rowPtr[n]/n, n, rowPtr, rowPtr,
                              col, val);
      matrix_descr MD = {SPARSE_MATRIX_TYPE_GENERAL};
      mkl_sparse_d_mv(SPARSE_OPERATION_NON_TRANSPOSE, 1.0, A, MD, x, 1.0, y);
      return true;
    } else if (BACKEND == TACO) {
      // unimplemented
    } else {
      // unsupported backend.
    }
    return false;
  }
};