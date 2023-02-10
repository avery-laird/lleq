LD_LIBRARY_PATH=$LD_LIBRARY_PATH:/usr/local/lib ../build/debug/bin/clang -S -emit-llvm -O0 -Xclang -disable-O0-optnone spmv_ell.c -o spmv_ell.ll
LD_LIBRARY_PATH=$LD_LIBRARY_PATH:/usr/local/lib ../build/debug/bin/clang++ -S -emit-llvm -O0 -Xclang -disable-O0-optnone spmv_csr_nomklheader.cpp -o spmv_csr.ll
LD_LIBRARY_PATH=$LD_LIBRARY_PATH:/usr/local/lib ../build/debug/bin/clang -S -emit-llvm -O0 -Xclang -disable-O0-optnone spmv_coo.c -o spmv_coo.ll
LD_LIBRARY_PATH=$LD_LIBRARY_PATH:/usr/local/lib ../build/debug/bin/clang -S -emit-llvm -O0 -Xclang -disable-O0-optnone simple_loop.c -o simple_loop.ll
LD_LIBRARY_PATH=$LD_LIBRARY_PATH:/usr/local/lib ../build/debug/bin/clang -S -emit-llvm -O0 -Xclang -disable-O0-optnone gemv.c -o gemv.ll
LD_LIBRARY_PATH=$LD_LIBRARY_PATH:/usr/local/lib ../build/debug/bin/clang -S -emit-llvm -O0 -Xclang -disable-O0-optnone ssa_example.c -o ssa_example.ll
LD_LIBRARY_PATH=$LD_LIBRARY_PATH:/usr/local/lib ../build/debug/bin/clang -S -emit-llvm -O0 -Xclang -disable-O0-optnone fma_test.c -o fma_test.ll
LD_LIBRARY_PATH=$LD_LIBRARY_PATH:/usr/local/lib ../build/debug/bin/clang -S -emit-llvm -O0 -Xclang -disable-O0-optnone fib_demo.c -o fib_demo.ll
LD_LIBRARY_PATH=$LD_LIBRARY_PATH:/usr/local/lib ../build/debug/bin/clang -S -emit-llvm -O0 -Xclang -disable-O0-optnone csr.c -o csr.ll
LD_LIBRARY_PATH=$LD_LIBRARY_PATH:/usr/local/lib ../build/debug/bin/clang++ -S -emit-llvm -O0 -Xclang -disable-O0-optnone -Xclang -analyzer-config -Xclang ipa=dynamic-bifurcate -I/files/eigen/Eigen test_eigen.cpp -o eigen_all.ll
LD_LIBRARY_PATH=$LD_LIBRARY_PATH:/usr/local/lib ../build/debug/bin/llvm-extract --func _ZN5Eigen8internal30sparse_time_dense_product_implINS_12SparseMatrixIdLi0EiEENS_6MatrixIdLin1ELi1ELi0ELin1ELi1EEES5_dLi0ELb1EE3runERKS3_RKS5_RS5_RKd eigen_all.ll -o eigen_spmv.ll
LD_LIBRARY_PATH=$LD_LIBRARY_PATH:/usr/local/lib ../build/debug/bin/clang++ -S -emit-llvm -O0 -Xclang -disable-O0-optnone spmm_csr.cpp -o spmm_csr.ll


LD_LIBRARY_PATH=$LD_LIBRARY_PATH:/usr/local/lib ../build/debug/bin/opt -S -mem2reg -loop-rotate -instcombine -simplifycfg -loop-simplify -lcssa -dot-cfg -dot-dom spmv_csr.ll -o spmv_csr_opt.ll
LD_LIBRARY_PATH=$LD_LIBRARY_PATH:/usr/local/lib ../build/debug/bin/opt -S -mem2reg -loop-rotate -instcombine -simplifycfg -loop-simplify -lcssa -dot-cfg -dot-dom spmv_coo.ll -o spmv_coo_opt.ll
LD_LIBRARY_PATH=$LD_LIBRARY_PATH:/usr/local/lib ../build/debug/bin/opt -S -mem2reg -loop-rotate -instcombine -simplifycfg -loop-simplify -lcssa -dot-cfg -dot-dom simple_loop.ll -o simple_loop_opt.ll
LD_LIBRARY_PATH=$LD_LIBRARY_PATH:/usr/local/lib ../build/debug/bin/opt -S -mem2reg -loop-rotate -instcombine -simplifycfg -loop-simplify -lcssa -dot-cfg -dot-dom spmv_ell.ll -o spmv_ell_opt.ll
LD_LIBRARY_PATH=$LD_LIBRARY_PATH:/usr/local/lib ../build/debug/bin/opt -S -mem2reg -loop-rotate -instcombine -simplifycfg -loop-simplify -lcssa -dot-cfg -dot-dom gemv.ll -o gemv_opt.ll
LD_LIBRARY_PATH=$LD_LIBRARY_PATH:/usr/local/lib ../build/debug/bin/opt -S -mem2reg -loop-rotate -instcombine -loop-simplify -lcssa -dot-cfg -dot-dom ssa_example.ll -o ssa_example_opt.ll
LD_LIBRARY_PATH=$LD_LIBRARY_PATH:/usr/local/lib ../build/debug/bin/opt -S -mem2reg -loop-rotate -instcombine -simplifycfg -loop-simplify -lcssa -dot-cfg -dot-dom fma_test.ll -o fma_test_opt.ll
LD_LIBRARY_PATH=$LD_LIBRARY_PATH:/usr/local/lib ../build/debug/bin/opt -S -mem2reg -loop-rotate -instcombine -simplifycfg -loop-simplify -lcssa -dot-cfg -dot-dom fib_demo.ll -o fib_demo_opt.ll
LD_LIBRARY_PATH=$LD_LIBRARY_PATH:/usr/local/lib ../build/debug/bin/opt -S -mem2reg -loop-rotate -instcombine -simplifycfg -loop-simplify -lcssa -dot-cfg -dot-dom csr.ll -o csr_opt.ll
LD_LIBRARY_PATH=$LD_LIBRARY_PATH:/usr/local/lib ../build/debug/bin/opt -S -mem2reg -loop-rotate -instcombine -simplifycfg -loop-simplify -lcssa -inline -dot-cfg -dot-dom eigen_spmv.ll -o eigen_spmv_opt.ll
LD_LIBRARY_PATH=$LD_LIBRARY_PATH:/usr/local/lib ../build/debug/bin/opt -S -mem2reg -loop-rotate -instcombine -simplifycfg -loop-simplify -lcssa -dot-cfg -dot-dom spmm_csr.ll -o spmm_csr_opt.ll

dot -Tpng .spMV_Mul_csr.dot -o spmv_csr.png
dot -Tpng .spmv_coo.dot -o spmv_coo.png
dot -Tpng .simple_loop.dot -o simple_loop.png
dot -Tpng .spmv_ell.dot -o spmv_ell.png
dot -Tpng .gemv.dot -o gemv.png
dot -Tpng .ssa.dot -o ssa.png
dot -Tpng .fma_test.dot -o fma_test.png
dot -Tpng .fma_imp.dot -o fma_imp.png
dot -Tpng .fib_rec.dot -o fib_rec.png
dot -Tpng .fib_iter.dot -o fib_iter.png
dot -Tpng .set1.dot -o set1.png
dot -Tpng .set2.dot -o set2.png
dot -Tpng .CSR.dot -o csr.png
dot -Tpng ._ZN5Eigen8internal30sparse_time_dense_product_implINS_12SparseMatrixIdLi0EiEENS_6MatrixIdLin1ELi1ELi0ELin1ELi1EEES5_dLi0ELb1EE3runERKS3_RKS5_RS5_RKd.dot -o eigen_spmv.png
dot -Tpng .spmm_v2.dot -o spmm_v2.png

dot -Tpng dom.spMV_Mul_csr.dot -o spmv_csr_dom.png
dot -Tpng dom.spmv_coo.dot -o spmv_coo_dom.png
dot -Tpng dom.simple_loop.dot -o simple_loop_dom.png
dot -Tpng dom.spmv_ell.dot -o spmv_ell_dom.png
dot -Tpng dom.gemv.dot -o gemv_dom.png
dot -Tpng dom.ssa.dot -o ssa_dom.png
dot -Tpng dom.fma_test.dot -o fma_test_dom.png
dot -Tpng dom.fma_imp.dot -o fma_imp_dom.png
dot -Tpng dom.fib_rec.dot -o fib_rec_dom.png
dot -Tpng dom.fib_iter.dot -o fib_iter_dom.png
dot -Tpng dom.CSR.dot -o csr_dom.png
dot -Tpng dom.spmm_v2.dot -o spmm_v2_dom.png

#dot -Tpng postdom.spMV_Mul_csr.dot -o spmv_csr_postdom.png
#dot -Tpng postdom.spmv_coo.dot -o spmv_coo_postdom.png
#dot -Tpng postdom.simple_loop.dot -o simple_loop_postdom.png
#dot -Tpng postdom.spmv_ell.dot -o spmv_ell_postdom.png
#dot -Tpng postdom.gemv.dot -o gemv_postdom.png
#dot -Tpng postdom.ssa.dot -o ssa_postdom.png
#dot -Tpng postdom.ssa.dot -o fma_postdom.png


# move everything into the build dir
cp *.ll ../build/debug/bin/
cp *.png ../build/debug/bin/
cp *.ll ../build/release/bin/
cp *.png ../build/release/bin/

rm *.ll
rm *.png
rm .*.dot
rm *.dot