set(LD_LIBRARY_PATH "LD_LIBRARY_PATH=${LD_LIBRARY_PATH}:/usr/local/lib")

set(OPT "${PROJECT_BINARY_DIR}/bin/opt")
set(EXTRACT "${PROJECT_BINARY_DIR}/bin/llvm-extract")
set(LLFLAGS -S -emit-llvm -O0 -Xclang -disable-O0-optnone)
set(OPTFLAGS -S -mem2reg -loop-rotate -instcombine -simplifycfg -loop-simplify -lcssa -dot-cfg -dot-dom)

function(add_function_target filename funcname COMPILER)
    get_filename_component(filename_noext ${filename} NAME_WE)
    message(STATUS "${filename_noext} ${funcname}")
    add_custom_command(
            OUTPUT ${filename_noext}.ll
            COMMAND ${LD_LIBRARY_PATH} ${COMPILER} ${LLFLAGS} ${CMAKE_CURRENT_LIST_DIR}/${filename} -o ${filename_noext}.ll
            DEPENDS ${filename}
            VERBATIM)
    add_custom_target(generate_${filename_noext}_ll DEPENDS ${filename_noext}.ll)

    add_custom_command(
            OUTPUT ${funcname}_extracted.ll
            COMMAND ${LD_LIBRARY_PATH} ${EXTRACT} --func ${funcname} ${filename_noext}.ll -o ${funcname}_extracted.ll
            DEPENDS ${filename_noext}.ll
                    generate_${filename_noext}_ll
            VERBATIM)
    add_custom_target(generate_${funcname}_extracted_ll DEPENDS ${funcname}_extracted.ll)

    add_custom_command(
            OUTPUT ${funcname}_opt.ll
            COMMAND ${LD_LIBRARY_PATH} ${OPT} ${OPTFLAGS} ${funcname}_extracted.ll -o ${PROJECT_BINARY_DIR}/bin/${funcname}_opt.ll
            DEPENDS ${funcname}_extracted.ll
                    generate_${funcname}_extracted_ll
            VERBATIM)
    add_custom_target(generate_${funcname}_opt DEPENDS ${funcname}_opt.ll)

    add_custom_command(
            OUTPUT ${funcname}.png
            COMMAND dot -Tpng .${funcname}.dot -o ${PROJECT_BINARY_DIR}/bin/${funcname}.png
            DEPENDS ${funcname}_opt.ll
                    generate_${funcname}_opt
            VERBATIM)
    add_custom_target(generate_${funcname}_png DEPENDS ${funcname}.png)

endfunction()

add_function_target(spmv_ell.c spmv_ell ${PROJECT_BINARY_DIR}/bin/clang)
add_function_target(spmv_csr_nomklheader.cpp spMV_Mul_csr ${PROJECT_BINARY_DIR}/bin/clang++)
add_function_target(spmv_coo.c spmv_coo ${PROJECT_BINARY_DIR}/bin/clang)
add_function_target(spmm_csr.cpp spmm_v2 ${PROJECT_BINARY_DIR}/bin/clang++)

add_dependencies(opt
        generate_spmv_ell_png
        generate_spMV_Mul_csr_png
        generate_spmv_coo_png
        generate_spmm_v2_png)