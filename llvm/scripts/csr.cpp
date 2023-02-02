//
// Created by bangtian on 25/08/22.
//
#include <fstream>
#include <algorithm>
#include <iostream>
#include <cassert>
#include "csr.h"
#include "util.h"

CSR::CSR(std::string filePath) {
    std::ifstream fin(filePath);
    // Ignore headers and comments:
    while (fin.peek() == '%') fin.ignore(2048, '\n');
    // Read defining parameters:
    fin >> m >> n >> nnz;
    vector<int> csc_colptr;
    vector<int> csc_rowIdx;
    vector<double> csc_val;
    int last_col=0;
    csc_colptr.push_back(0);
    for(int l=0; l<nnz; l++)
    {
        int row, col;
        double data;
        fin >> row >> col >> data;
        --row;
        --col;
        csc_rowIdx.push_back(row);
        csc_val.push_back(data);
        if(col>last_col){
            csc_colptr.push_back(csc_rowIdx.size()-1);
            last_col = col;
        }
    }

    csc_colptr.push_back(csc_rowIdx.size());

    csc_to_csr(m, n, csc_colptr.data(), csc_rowIdx.data(), csc_val.data(), row_ptr, col_ind, val);

    fin.close();
}

CSR::CSR(std::string filePath, bool symmtric) {
//    assert(symmtric==true);
//    vector<int> rows, cols;
//    vector<double> data;
//
//    std::ifstream fin(filePath);
//    // Ignore headers and comments:
//    while (fin.peek() == '%') fin.ignore(2048, '\n');
//    // Read defining parameters:
//    fin >> m >> n >> nnz;
//    row_ptr.push_back(0);
//    // read the data in coo format
//    for (int l = 0; l < nnz; l++){
//        int row, col;
//        double d;
//        fin >> row >> col >> d; // (rowIdx, colIdx, val)
//        rows.push_back(row);
//        cols.push_back(col);
//        data.push_back(d);
//    }
//    fin.close();
//    // convert coo to csr
//    for (int l = 1; l <= m; l++){
//        for (int k = 0; k < nnz; k++){
//            if (cols[k] == l){
//                col_ind.push_back(rows[k]);
//                val.push_back(data[k]);
//            }
//            else if (rows[k] == l){
//                col_ind.push_back(cols[k]);
//                val.push_back(data[k]);
//            }
//        }
//        row_ptr.push_back(col_ind.size());
//    }
//
//    row_ptr.push_back(col_ind.size() + 1);
}


void CSR::printMatrix() {
    for(int i=0; i<this->m; i++)
    {
        for(int j=this->row_ptr[i]; j<this->row_ptr[i+1];j++)
        {
            cout<< val[j] << ' ';
        }
        std::cout << std::endl;
    }
}