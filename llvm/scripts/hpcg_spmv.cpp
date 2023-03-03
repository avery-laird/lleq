#include <unordered_map>
#include <vector>
/*!
  This defines the type for integers that have local subdomain dimension.
  Define as "long long" when local problem dimension is > 2^31
*/
typedef int local_int_t;
/*!
  This defines the type for integers that have global dimension
  Define as "long long" when global problem dimension is > 2^31
*/
#ifdef HPCG_NO_LONG_LONG
typedef int global_int_t;
#else
typedef long long global_int_t;
#endif
using GlobalToLocalMap = std::unordered_map< global_int_t, local_int_t >;

/*!
  This is a data structure to contain all processor geometry information
*/
struct Geometry_STRUCT {
  int size; //!< Number of MPI processes
  int rank; //!< This process' rank in the range [0 to size - 1]
  int numThreads; //!< This process' number of threads
  local_int_t nx;   //!< Number of x-direction grid points for each local subdomain
  local_int_t ny;   //!< Number of y-direction grid points for each local subdomain
  local_int_t nz;   //!< Number of z-direction grid points for each local subdomain
  int npx;  //!< Number of processors in x-direction
  int npy;  //!< Number of processors in y-direction
  int npz;  //!< Number of processors in z-direction
  int pz; //!< partition ID of z-dimension process that starts the second region of nz values
  int npartz; //!< Number of partitions with varying nz values
  int * partz_ids; //!< Array of partition ids of processor in z-direction where new value of nz starts (valid values are 1 to npz)
  local_int_t * partz_nz; //!< Array of length npartz containing the nz values for each partition
  int ipx;  //!< Current rank's x location in the npx by npy by npz processor grid
  int ipy;  //!< Current rank's y location in the npx by npy by npz processor grid
  int ipz;  //!< Current rank's z location in the npx by npy by npz processor grid
  global_int_t gnx;  //!< Global number of x-direction grid points
  global_int_t gny;  //!< Global number of y-direction grid points
  global_int_t gnz;  //!< Global number of z-direction grid points
  global_int_t gix0;  //!< Base global x index for this rank in the npx by npy by npz processor grid
  global_int_t giy0;  //!< Base global y index for this rank in the npx by npy by npz processor grid
  global_int_t giz0;  //!< Base global z index for this rank in the npx by npy by npz processor grid

};
typedef struct Geometry_STRUCT Geometry;

struct Vector_STRUCT {
  local_int_t localLength;  //!< length of local portion of the vector
  double * values;          //!< array of values
  /*!
   This is for storing optimized data structures created in OptimizeProblem and
   used inside optimized ComputeSPMV().
   */
  void * optimizationData;

};
typedef struct Vector_STRUCT Vector;

struct MGData_STRUCT {
  int numberOfPresmootherSteps; // Call ComputeSYMGS this many times prior to coarsening
  int numberOfPostsmootherSteps; // Call ComputeSYMGS this many times after coarsening
  local_int_t * f2cOperator; //!< 1D array containing the fine operator local IDs that will be injected into coarse space.
  Vector * rc; // coarse grid residual vector
  Vector * xc; // coarse grid solution vector
  Vector * Axf; // fine grid residual vector
  /*!
   This is for storing optimized data structres created in OptimizeProblem and
   used inside optimized ComputeSPMV().
   */
  void * optimizationData;
};
typedef struct MGData_STRUCT MGData;

struct SparseMatrix_STRUCT {
  char  * title; //!< name of the sparse matrix
  Geometry * geom; //!< geometry associated with this matrix
  global_int_t totalNumberOfRows; //!< total number of matrix rows across all processes
  global_int_t totalNumberOfNonzeros; //!< total number of matrix nonzeros across all processes
  local_int_t localNumberOfRows; //!< number of rows local to this process
  local_int_t localNumberOfColumns;  //!< number of columns local to this process
  local_int_t localNumberOfNonzeros;  //!< number of nonzeros local to this process
  char  * nonzerosInRow;  //!< The number of nonzeros in a row will always be 27 or fewer
  global_int_t ** mtxIndG; //!< matrix indices as global values
  local_int_t ** mtxIndL; //!< matrix indices as local values
  double ** matrixValues; //!< values of matrix entries
  double ** matrixDiagonal; //!< values of matrix diagonal entries
  GlobalToLocalMap globalToLocalMap; //!< global-to-local mapping
  std::vector< global_int_t > localToGlobalMap; //!< local-to-global mapping
  mutable bool isDotProductOptimized;
  mutable bool isSpmvOptimized;
  mutable bool isMgOptimized;
  mutable bool isWaxpbyOptimized;
  /*!
   This is for storing optimized data structres created in OptimizeProblem and
   used inside optimized ComputeSPMV().
   */
  mutable struct SparseMatrix_STRUCT * Ac; // Coarse grid matrix
  mutable MGData * mgData; // Pointer to the coarse level data for this fine matrix
  void * optimizationData;  // pointer that can be used to store implementation-specific data

#ifndef HPCG_NO_MPI
  local_int_t numberOfExternalValues; //!< number of entries that are external to this process
  int numberOfSendNeighbors; //!< number of neighboring processes that will be send local data
  local_int_t totalToBeSent; //!< total number of entries to be sent
  local_int_t * elementsToSend; //!< elements to send to neighboring processes
  int * neighbors; //!< neighboring processes
  local_int_t * receiveLength; //!< lenghts of messages received from neighboring processes
  local_int_t * sendLength; //!< lenghts of messages sent to neighboring processes
  double * sendBuffer; //!< send buffer for non-blocking sends
#endif
};
typedef struct SparseMatrix_STRUCT SparseMatrix;

//#ifndef HPCG_NO_MPI
//#include "ExchangeHalo.hpp"
//#endif

#ifndef HPCG_NO_OPENMP
#include <omp.h>
#endif
#include <cassert>


/*!
  Routine to compute matrix vector product y = Ax where:
  Precondition: First call exchange_externals to get off-processor values of x
  This is the reference SPMV implementation.  It CANNOT be modified for the
  purposes of this benchmark.
  @param[in]  A the known system matrix
  @param[in]  x the known vector
  @param[out] y the On exit contains the result: Ax.
  @return returns 0 upon success and non-zero otherwise
  @see ComputeSPMV
*/
extern "C" {
int ComputeSPMV_ref(const SparseMatrix &A, Vector &x, Vector &y) {

  assert(x.localLength >= A.localNumberOfColumns); // Test vector lengths
  assert(y.localLength >= A.localNumberOfRows);

  // #ifndef HPCG_NO_MPI
  //   ExchangeHalo(A,x);
  // #endif
  const double *const xv = x.values;
  double *const yv = y.values;
  const local_int_t nrow = A.localNumberOfRows;
#ifndef HPCG_NO_OPENMP
#pragma omp parallel for
#endif
  for (local_int_t i = 0; i < nrow; i++) {
    double sum = 0.0;
    const double *const cur_vals = A.matrixValues[i];
    const local_int_t *const cur_inds = A.mtxIndL[i];
    const int cur_nnz = A.nonzerosInRow[i];

    for (int j = 0; j < cur_nnz; j++)
      sum += cur_vals[j] * xv[cur_inds[j]];
    yv[i] = sum;
  }
  return 0;
}

int ComputeSPMV_ref_nostruct(
    local_int_t xLocalLength,
    local_int_t yLocalLength,
    local_int_t ALocalNumberOfColumns,
    local_int_t ALocalNumberOfRows,
    const double *const xv,
    double *const yv,
    double **matrixValues,
    local_int_t ** mtxIndL,
    char  * nonzerosInRow) {

//  assert(xLocalLength >= ALocalNumberOfColumns); // Test vector lengths
//  assert(yLocalLength >= ALocalNumberOfRows);

  // #ifndef HPCG_NO_MPI
  //   ExchangeHalo(A,x);
  // #endif
//  const local_int_t nrow = ALocalNumberOfRows;
#ifndef HPCG_NO_OPENMP
#pragma omp parallel for
#endif
  for (local_int_t i = 0; i < ALocalNumberOfRows; i++) {
    double sum = 0.0;
    const double *const cur_vals = matrixValues[i];
    const local_int_t *const cur_inds = mtxIndL[i];
    const int cur_nnz = nonzerosInRow[i];

    for (int j = 0; j < cur_nnz; j++)
      sum += cur_vals[j] * xv[cur_inds[j]];
    yv[i] = sum;
  }
  return 0;
}
}