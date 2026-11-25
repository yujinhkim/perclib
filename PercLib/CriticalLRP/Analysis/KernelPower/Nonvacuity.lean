/- Integrated from independently rebuilt Ultramath work, base revision 4140ac56119d2cd80995f91886669efe004839d5.
Scratch source: ../../.ultramath/smwqozn0q/m1/Nonvacuity.lean ; imports migrated only.
-/

module

/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.
Non-vacuity of the model-level diagonal maximality: the source model class is inhabited.
-/
public import PercLib.CriticalLRP.Analysis.KernelPower.Model
public import PercLib.CriticalLRP.Orchestration.SourceModelNonvacuity

@[expose] public section

noncomputable section

open scoped ENNReal NNReal

attribute [local instance] Classical.propDecidable

open PercLib.CriticalLRP PercLib.CriticalLRP.Orchestration

namespace PercLib.CriticalLRP.KernelPower

/-- The source model class is inhabited (witness `d = 1`, `α = 1`, zero logarithmic error), so
the model-level statements above have satisfiable hypotheses and are not vacuous. -/
theorem sourceModelData_nonempty : Nonempty SourceModelData :=
  PercLib.CriticalLRP.Orchestration.Witness.sourceModelData_nonempty

/-- **Non-vacuity witness** for the source-level `sup_x T^ℓ_{β_c,r}(0,x) = T^ℓ_{β_c,r}(0,0)`:
there is a concrete source model for which the identity holds for every `r > 0` and every `ℓ`. -/
theorem exists_sourceModel_cutKpow_iSup_diag :
    ∃ M : SourceModelData, ∀ (r : ℝ) (n : ℕ),
      (⨆ y : M.V,
          Kpow (fun a b : M.V =>
            twoPointFunction (M.cutKernel r) (M.cutKernel_nonneg r) M.betaCrit a b) n
            (0 : M.V) y)
        = Kpow (fun a b : M.V =>
            twoPointFunction (M.cutKernel r) (M.cutKernel_nonneg r) M.betaCrit a b) n
            (0 : M.V) (0 : M.V) := by
  obtain ⟨M⟩ := PercLib.CriticalLRP.Orchestration.Witness.sourceModelData_nonempty
  exact ⟨M, fun r n => SourceModelData.cutTwoPoint_Kpow_iSup_diag M r n⟩

end PercLib.CriticalLRP.KernelPower
