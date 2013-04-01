let f oc module_ =
  assert (Llvm_bitwriter.output_bitcode oc module_)
