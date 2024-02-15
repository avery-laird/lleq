set(LLVM_LINK_COMPONENTS
  Analysis
  AsmParser
  Core
  Passes
  Support
  ScalarOpts
  TransformUtils
  )

add_llvm_unittest(REVTests
  REVTest.cpp
  )

target_link_libraries(REVTests PRIVATE LLVMTestingSupport)

set_property(TARGET REVTests PROPERTY FOLDER "Tests/UnitTests/TransformsTests")
