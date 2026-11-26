module
public import PercLib.CriticalLRP.VolumeMoments.HigherMoments.I420Endpoint.Model

/-! Axiom audit for endpoint reflection and the actual normalized radial kernel. -/
set_option linter.hashCommand false

#print axioms PercLib.CriticalLRP.I420Endpoint.clusterVol_perm
#print axioms PercLib.CriticalLRP.I420Endpoint.mixedPoint_perm
#print axioms PercLib.CriticalLRP.I420Endpoint.mixedPoint_reflect_ba
#print axioms PercLib.CriticalLRP.I420Endpoint.lintegral_mixedPoint_reflect
#print axioms PercLib.CriticalLRP.I420Endpoint.mixedExcl_swap_window
#print axioms PercLib.CriticalLRP.I420Endpoint.mixedExcl_toReal_swap_window
#print axioms PercLib.CriticalLRP.I420Endpoint.radial_reflect_norm
#print axioms PercLib.CriticalLRP.I420Endpoint.cutKernel_reflect_norm
#print axioms PercLib.CriticalLRP.I420Endpoint.mixedExcl_cutKernel_swap
