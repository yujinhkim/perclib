/-
Independently rebuilt from accepted `smwxb4a1l/m2` coefficient artifacts.
Production revision `d9a001b7f0a33cf6395158f7621ad4de1fe3c7c8`.
Only the finite range/cardinality results are integrated; this does not prove
the arbitrary-q weighted fresh evaluation or the further geometric link lemmas
outlined in the artifact narrative.
-/
module
public import PercLib.CriticalLRP.Correlation.I417.Fresh.Depth.Main

/-!
# Audit for the pin--mark depth and coefficient scaffold. -/
set_option linter.hashCommand false
open PercLib.CriticalLRP.I417FreshDepth

#print axioms markDepthK_le
#print axioms markDepth_bounds
#print axioms markDepth_monomial_range
#print axioms depthCount_three
#print axioms depthCount_four
#print axioms depthCount_total
#print axioms genCoeff_five
#print axioms genFreshProfile_eq_freshPoly
