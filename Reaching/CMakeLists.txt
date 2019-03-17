add_llvm_loadable_module( LLVMReaching
  Reaching.cpp

  DEPENDS
  intrinsics_gen
  PLUGIN_TOOL
  opt
  )
