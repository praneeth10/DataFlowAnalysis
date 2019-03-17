add_llvm_loadable_module( LLVMMaypoint
  Maypoint.cpp

  DEPENDS
  intrinsics_gen
  PLUGIN_TOOL
  opt
  )
