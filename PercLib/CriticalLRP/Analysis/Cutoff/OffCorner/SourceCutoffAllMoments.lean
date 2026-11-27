module

public import PercLib.CriticalLRP.TreeExpansion.AtlasRealization.Canonical.Ordinary
public import PercLib.CriticalLRP.Analysis.Cutoff.Defect.Triangle

/-! # All positive ordinary cutoff moments from the first

The ordinary atlas bound applies directly to the source cutoff profile: it is
strictly subunit, translation invariant and has first moment equal to its
two-point row sum.  No rescaling of the source norm is required.
-/

@[expose] public section

noncomputable section

open MeasureTheory unitInterval
open scoped ENNReal NNReal BigOperators

set_option linter.hashCommand false

namespace PercLib.CriticalLRP.Orchestration

open PercLib.CriticalLRP

/-- The ordinary tree bound for every positive cutoff moment at an arbitrary
normalized norm.  Strict edge probabilities and translations supply transitivity. -/
theorem cutMoment_le_dfactorial (M : SourceModelData) (r : ℝ)
    {q : ℕ} (hq : 1 ≤ q) :
    M.cutMoment q r ≤ (VolumeMoments.M (q - 1) : ℝ≥0∞) *
      (M.cutMoment 1 r) ^ (2 * q - 1) := by
  let π := M.cutProb r
  have hmean : I417.meanVol π (0 : M.V) = M.cutMoment 1 r := by
    rw [I417.meanVol, I417.tsum_connSet_eq_lintegral, SourceModelData.cutMoment,
      E1Sign.cutLaw_eq]
    simp only [pow_one, π]
  have h := CanonAtlas.Measure.lintegral_cardFun_pow_le_dfactorial_of_transitive π
    (E1Sign.cutProb_lt_one M r) hq (0 : M.V) ?_
  · rw [hmean] at h
    rw [SourceModelData.cutMoment, E1Sign.cutLaw_eq]
    simp_rw [clusterVol, ← Percolation.cardFun_eq_encard]
    simpa only [π] using h
  · intro v
    let g : M.V ≃ M.V := Equiv.addRight v
    refine ⟨g, ?_, ?_⟩
    · intro e
      induction e using Sym2.ind with
      | _ a b =>
          simpa only [Sym2.map_mk, Equiv.coe_addRight, g, π] using
            E1Sign.cutProb_shift_invariant M r v s(a,b)
    · simp [g]

/-- A finite first cutoff moment at a fixed radius gives every higher moment
at that radius.  This does not prove the first-moment/sharpness hypothesis. -/
theorem cutMoment_ne_top_of_one (M : SourceModelData) (r : ℝ)
    (h1 : M.cutMoment 1 r ≠ ⊤) (q : ℕ) : M.cutMoment q r ≠ ⊤ := by
  by_cases hq : 1 ≤ q
  · refine ne_top_of_le_ne_top ?_ (cutMoment_le_dfactorial M r hq)
    exact ENNReal.mul_ne_top (by simp) (ENNReal.pow_ne_top h1)
  · have hq0 : q = 0 := by omega
    subst q
    simp [SourceModelData.cutMoment]

end PercLib.CriticalLRP.Orchestration

#print axioms PercLib.CriticalLRP.Orchestration.cutMoment_le_dfactorial
#print axioms PercLib.CriticalLRP.Orchestration.cutMoment_ne_top_of_one
