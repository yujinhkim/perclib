/- Integrated from independently rebuilt Ultramath work.
Production base 59c03cea394d5ba573e5d23b06d0f394d065b380.
Scratch source: ../../.ultramath/smwvp122a/m4/Audit.lean.
-/

module

public import PercLib.CriticalLRP.Correlation.SixPoint.RootPairObstruction.Main

/-! The audit prints the axiom footprint of the compiled statements: only the three
standard axioms may occur. -/

@[expose] public section

namespace ChainRefute

#print axioms chainCost_ge_six

#print axioms chainCost_ge_six_perm

#print axioms chainCost

end ChainRefute
