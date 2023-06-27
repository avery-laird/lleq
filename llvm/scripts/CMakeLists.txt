set(LD_LIBRARY_PATH "LD_LIBRARY_PATH=${LD_LIBRARY_PATH}:/usr/local/lib")

set(OPT "${PROJECT_BINARY_DIR}/bin/opt")
set(EXTRACT "${PROJECT_BINARY_DIR}/bin/llvm-extract")
set(LLFLAGS -S -emit-llvm -O0 -Xclang -disable-O0-optnone -fno-discard-value-names)
set(OPTFLAGS -S -mem2reg -loop-rotate -instcombine -simplifycfg -loop-simplify -lcssa -dot-cfg -dot-dom)

function(add_function_target filename funcname COMPILER)
    get_filename_component(filename_noext ${filename} NAME_WE)
    message(STATUS "${filename_noext} ${funcname}")
    add_custom_command(
            OUTPUT ${filename_noext}.ll
            COMMAND ${LD_LIBRARY_PATH} ${COMPILER} ${LLFLAGS} ${CMAKE_CURRENT_LIST_DIR}/${filename} -o ${filename_noext}.ll
            DEPENDS ${filename}
            VERBATIM)
    add_custom_target(generate_${filename_noext}_${funcname}_ll DEPENDS ${filename_noext}.ll)

    add_custom_command(
            OUTPUT ${funcname}_extracted.ll
            COMMAND ${LD_LIBRARY_PATH} ${EXTRACT} --func ${funcname} ${filename_noext}.ll -o ${funcname}_extracted.ll
            DEPENDS ${filename_noext}.ll
                    generate_${filename_noext}_${funcname}_ll
            VERBATIM)
    add_custom_target(generate_${funcname}_extracted_ll DEPENDS ${funcname}_extracted.ll)

    add_custom_command(
            OUTPUT ${PROJECT_BINARY_DIR}/bin/${funcname}_opt.ll
            COMMAND ${LD_LIBRARY_PATH} ${OPT} ${OPTFLAGS} ${funcname}_extracted.ll -o ${PROJECT_BINARY_DIR}/bin/${funcname}_opt.ll
            DEPENDS ${funcname}_extracted.ll
                    generate_${funcname}_extracted_ll
            VERBATIM)
    add_custom_target(generate_${funcname}_opt DEPENDS ${PROJECT_BINARY_DIR}/bin/${funcname}_opt.ll)

    add_custom_command(
            OUTPUT ${PROJECT_BINARY_DIR}/bin/${funcname}.png
            COMMAND dot -Tpng .${funcname}.dot -o ${PROJECT_BINARY_DIR}/bin/${funcname}.png
            DEPENDS ${PROJECT_BINARY_DIR}/bin/${funcname}_opt.ll
                    generate_${funcname}_opt
            VERBATIM)
    add_custom_target(generate_${funcname}_png DEPENDS ${PROJECT_BINARY_DIR}/bin/${funcname}.png)

    add_dependencies(opt generate_${funcname}_png)
endfunction()

add_function_target(spmv_ell.c spmv_ell ${PROJECT_BINARY_DIR}/bin/clang)
add_function_target(spmv_csr_nomklheader.cpp spMV_Mul_csr ${PROJECT_BINARY_DIR}/bin/clang++)
add_function_target(spmv_coo.c spmv_coo ${PROJECT_BINARY_DIR}/bin/clang)
add_function_target(spmm_csr.cpp spmm_v2 ${PROJECT_BINARY_DIR}/bin/clang++)
add_function_target(spmm_naive.cpp spmm_naive_csr ${PROJECT_BINARY_DIR}/bin/clang++)
add_function_target(hpcg_spmv.cpp ComputeSPMV_ref_nostruct ${PROJECT_BINARY_DIR}/bin/clang++)
add_function_target(gemm.cpp gemm ${PROJECT_BINARY_DIR}/bin/clang++)
add_function_target(gemv.c gemv ${PROJECT_BINARY_DIR}/bin/clang)
#add_function_target(gemv.c GEMV_ComputeElem ${PROJECT_BINARY_DIR}/bin/clang)
#add_function_target(gemv.c GEMV_AddColElem ${PROJECT_BINARY_DIR}/bin/clang)
#add_function_target(spmv_csr_nomklheader.cpp SpMV_CSR_ComputeElem ${PROJECT_BINARY_DIR}/bin/clang++)
add_function_target(scimark.c SparseCompRow_matmult ${PROJECT_BINARY_DIR}/bin/clang)
add_function_target(npb-cg.cpp spmv ${PROJECT_BINARY_DIR}/bin/clang++)
add_function_target(sparsebench.c random_crs_matprod__ ${PROJECT_BINARY_DIR}/bin/clang)
add_function_target(is_histogram.c histogram_is ${PROJECT_BINARY_DIR}/bin/clang)
add_function_target(ep_histogram.c histogram_ep ${PROJECT_BINARY_DIR}/bin/clang)

set(LLFLAGS -S -emit-llvm -O0 -Xclang -disable-O0-optnone -fno-discard-value-names -Xclang -no-opaque-pointers)
set(OPTFLAGS -S -mem2reg -loop-rotate -instcombine -simplifycfg -loop-simplify -dot-cfg -dot-dom)

#add_function_target(spmv_csr_nomklheader.cpp spMV_Mul_csr ${PROJECT_BINARY_DIR}/bin/clang++)
add_function_target(gemv_inner.c gemv_inner ${PROJECT_BINARY_DIR}/bin/clang)
add_function_target(spmv_inner.c spmv_inner ${PROJECT_BINARY_DIR}/bin/clang)
#add_function_target(gemv.c gemv ${PROJECT_BINARY_DIR}/bin/clang)

set(LLFLAGS -S -emit-llvm -O0 -Xclang -disable-O0-optnone -fno-discard-value-names)
set(OPTFLAGS -S -mem2reg -loop-rotate -instcombine -simplifycfg -loop-simplify -lcssa -dot-cfg -dot-dom)
