/-
Ultramath swarm `smwziumdb`, member `m5`, direction `d2`.

Independent axiom audit of every theorem exported by `Main.lean`.  The only admissible axioms
are `propext`, `Classical.choice`, `Quot.sound`; `#print axioms` must report exactly that set
(the source-model machinery uses `Classical.choice` and `propext` throughout; no `sorryAx`, no
`Lean.ofReduceBool`, no custom axiom).

Build (from this directory, production worktree read-only):

```
PROD=/workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.scratch/critical-lrp-orchestration
LEAN_PATH=$PWD:$PROD/.lake/build/lib/lean:<production package build dirs>:/opt/lean/lib/lean \
  lean -o Defs.olean -DwarningAsError=true -DautoImplicit=false Defs.lean
LEAN_PATH=... lean -o Main.olean -DwarningAsError=true -DautoImplicit=false Main.lean
LEAN_PATH=... lean -DwarningAsError=true -DautoImplicit=false Audit.lean
```
-/
module

public import PercLib.CriticalLRP.Analysis.SecondMomentCase3.ProductGap.SourceConsumer

/-! # Axiom audit for the Case-3 product route -/

set_option linter.hashCommand false
set_option linter.style.longLine false

open PercLib.CriticalLRP.Orchestration

#print axioms SourceModelData.exclMomentSq_integrand_eq
#print axioms SourceModelData.exclMassQuad_eq_sum_exclMomentSq
#print axioms SourceModelData.meanVol_cutProb
#print axioms SourceModelData.meanVol_cutProb_root
#print axioms SourceModelData.meanVol_cutProb_eq
#print axioms SourceModelData.cutMomentTwoAt_translate
#print axioms SourceModelData.volSq_cutProb_eq
#print axioms SourceModelData.iterPow_three_eq
#print axioms SourceModelData.iterPow_four_eq
#print axioms SourceModelData.T3_eq_iterPow
#print axioms SourceModelData.T4_eq_iterPow
#print axioms SourceModelData.iterPow_cutProb_comm
#print axioms SourceModelData.T3_comm_cutProb
#print axioms SourceModelData.T4_comm_cutProb
#print axioms SourceModelData.case3Numerator_eq_sum_sub_sum
#print axioms SourceModelData.perVertex_case3_eq_p21
#print axioms SourceModelData.tsub_sum_le_sum_tsub
#print axioms SourceModelData.case3Numerator_le_case3DiffWindow
#print axioms SourceModelData.case3DiffWindow_le_polygonWindow
#print axioms SourceModelData.case3Numerator_le_polygonWindow
#print axioms SourceModelData.T3_toReal_eq_polyK
#print axioms SourceModelData.T4_toReal_eq_polyK
#print axioms SourceModelData.T3_ne_top_cutProb
#print axioms SourceModelData.T4_ne_top_cutProb
#print axioms SourceModelData.polygonWindow_toReal_eq
#print axioms SourceModelData.polygonWindow_ne_top
#print axioms SourceModelData.p2ExclError_eq_case3Numerator_toReal
#print axioms SourceModelData.p2ExclError_le_polygonWindow_div
#print axioms SourceModelData.polygonWindow_toReal_le_of_inputs
#print axioms SourceModelData.p2ExclError_le_case3Driver_of_polygonWindow
#print axioms SourceModelData.p2ExclError_tendsto_zero_of_polygonWindow
#print axioms SourceModelData.logIntegrable_p2ExclError_of_polygonWindow
#print axioms SourceModelData.p2ExclError_tendsto_zero_of_polygonBundle
#print axioms SourceModelData.logIntegrable_p2ExclError_of_polygonBundle
#print axioms SourceModelData.secondMoment_asymptotic_case3_p21
#print axioms SourceModelData.p2ExclError_tendsto_zero_of_source_p21
#print axioms SourceModelData.logIntegrable_p2ExclError_of_source_p21
#print axioms SourceModelData.regularlyVarying_two_of_source_p21
#print axioms SourceModelData.secondMoment_asymptotic_case3_of_source_p21
