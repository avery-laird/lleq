../build/bin/clang -S -emit-llvm -O0 -Xclang -disable-O0-optnone spmv_csr.c -o spmv_csr.ll
../build/bin/clang -S -emit-llvm -O0 -Xclang -disable-O0-optnone spmv_coo.c -o spmv_coo.ll
../build/bin/clang -S -emit-llvm -O0 -Xclang -disable-O0-optnone simple_loop.c -o simple_loop.ll
../build/bin/clang -S -emit-llvm -O0 -Xclang -disable-O0-optnone spmv_ell.c -o spmv_ell.ll

../build/bin/opt -S --passes="mem2reg,loop-rotate,loop-simplify,lcssa,instcombine,simplifycfg,print<iv-users>,print<scalar-evolution>,dot-cfg" spmv_csr.ll -o spmv_csr_opt.ll
../build/bin/opt -S --passes="mem2reg,loop-rotate,loop-simplify,lcssa,instcombine,simplifycfg,print<iv-users>,print<scalar-evolution>,dot-cfg" spmv_coo.ll -o spmv_coo_opt.ll
../build/bin/opt -S --passes="mem2reg,loop-rotate,loop-simplify,lcssa,instcombine,simplifycfg,print<iv-users>,print<scalar-evolution>,dot-cfg" simple_loop.ll -o simple_loop_opt.ll
../build/bin/opt -S --passes="mem2reg,loop-rotate,loop-simplify,lcssa,instcombine,simplifycfg,print<iv-users>,print<scalar-evolution>,dot-cfg" spmv_ell.ll -o spmv_ell_opt.ll

dot -Tpng .spMV_Mul_csr.dot -o spmv_csr.png
dot -Tpng .spmv_coo.dot -o spmv_coo.png
dot -Tpng .simple_loop.dot -o simple_loop.png
dot -Tpng .spmv_ell.dot -o spmv_ell.png
#
## move everything into the build dir
mv *.ll ../build/bin/
mv *.png ../build/bin/

rm .*.dot