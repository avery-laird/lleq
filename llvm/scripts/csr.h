//
// Created by bangtian on 25/08/22.
//

#ifndef RV_TESTS_CSR_H
#define RV_TESTS_CSR_H
#include <vector>
#include <string>

using namespace std;
struct CSR{
    double *val;
    int *col_ind;
    int *row_ptr;
    int m, n, nnz;
public:
    CSR(std::string filePath);

    CSR(std::string filePath, bool symmtric);

    void printMatrix();
};

#endif //RV_TESTS_CSR_H
