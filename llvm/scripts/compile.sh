../build/bin/clang -S -emit-llvm -O0 -Xclang -disable-O0-optnone spmv.c spmv_coo.c

../build/bin/opt -S --passes="mem2reg,loop-rotate,loop-simplify,lcssa,instcombine,simplifycfg,print<iv-users>,print<scalar-evolution>,dot-cfg" spmv.ll -o spmv_opt.ll
../build/bin/opt -S --passes="mem2reg,loop-rotate,loop-simplify,lcssa,instcombine,simplifycfg,print<iv-users>,print<scalar-evolution>,dot-cfg" spmv_coo.ll -o spmv_coo_opt.ll

dot -Tpng .spMV_Mul_csr.dot -o spmv.png
dot -Tpng .spmv_coo.dot -o spmv_coo.png

# move everything into the build dir
mv *.ll ../build/bin/
mv *.png ../build/bin/

rm .*.dot