/- Coordinator-assembled transitivity instances for the canonical ordinary moment bound.
Production base: `80951640d68930030716cfd90af38fee830518f2`.
The strict candidate was `.scratch/verification/canonical-ordinary/Main.lean`. -/

module

public import PercLib.CriticalLRP.TreeExpansion.AtlasRealization.Canonical.LeafSum
public import PercLib.CriticalLRP.Correlation.I417Example.Trans
public import PercLib.CriticalLRP.PowerLawTreeMoments

/-! Vertex-transitive instances of the canonical ordinary moment bound. -/

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false

open MeasureTheory Measure ProbabilityTheory unitInterval
open scoped ENNReal NNReal

@[expose] public section

namespace CanonAtlas

open PercLib.CriticalLRP (edgeMeasure connSet)

namespace Measure

variable {V : Type*} [DecidableEq V] [Countable V]

/-- Vertex transitivity makes the canonical two-point row sums equal to the
chosen root's mean cluster volume. -/
theorem twoPoint_tsum_eq_meanVol_of_transitive (π : Sym2 V → unitInterval) (x : V)
    (htrans : ∀ v : V, ∃ g : V ≃ V, (∀ e : Sym2 V, π (Sym2.map g e) = π e) ∧ g x = v) :
    ∀ v : V, ∑' y : V, (edgeMeasure π) (connSet v y) =
      PercLib.CriticalLRP.I417.meanVol π x := by
  intro v
  change PercLib.CriticalLRP.I417.meanVol π v = PercLib.CriticalLRP.I417.meanVol π x
  exact PercLib.CriticalLRP.I417Example.meanVol_eq_of_transitive π x htrans v

/-- The ordinary moment bound of Lemma I.4.16, with transitivity supplied by
profile-preserving vertex permutations. -/
theorem lintegral_cardFun_pow_le_dfactorial_of_transitive
    (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1) {q : ℕ} (hq : 1 ≤ q) (x : V)
    (htrans : ∀ v : V, ∃ g : V ≃ V, (∀ e : Sym2 V, π (Sym2.map g e) = π e) ∧ g x = v) :
    ∫⁻ ω, PercLib.CriticalLRP.Percolation.cardFun
        (PercLib.Percolation.Bond.cluster ω x) ^ q ∂(edgeMeasure π) ≤
      (PercLib.CriticalLRP.VolumeMoments.M (q - 1) : ℝ≥0∞) *
        (PercLib.CriticalLRP.I417.meanVol π x) ^ (2 * q - 1) := by
  exact lintegral_cardFun_pow_le_dfactorial π hπ hq x
    (PercLib.CriticalLRP.I417.meanVol π x)
    (twoPoint_tsum_eq_meanVol_of_transitive π x htrans)

end CanonAtlas.Measure

namespace PercLib.CriticalLRP.TreeExpansion

/-- Every positive ordinary moment on the canonical power-law law on `ℤ^d` has the
source's double-factorial tree-moment bound. -/
theorem latticeLongRange_cardFun_pow_le_dfactorial (d : ℕ) (α : ℝ) (β : NNReal)
    {q : ℕ} (hq : 1 ≤ q) :
    ∫⁻ ω, PercLib.CriticalLRP.Percolation.cardFun
        (PercLib.Percolation.Bond.cluster ω (0 : Fin d → ℤ)) ^ q
        ∂(latticeLongRangeMeasure d α β) ≤
      (VolumeMoments.M (q - 1) : ℝ≥0∞) *
        (I417.meanVol (bernoulliEdgeProb (lrKernel d α) (lrKernel_nonneg d α) β)
          (0 : Fin d → ℤ)) ^ (2 * q - 1) := by
  have h : ∫⁻ ω, PercLib.CriticalLRP.Percolation.cardFun
        (PercLib.Percolation.Bond.cluster ω (0 : Fin d → ℤ)) ^ q
        ∂(edgeMeasure (bernoulliEdgeProb (lrKernel d α) (lrKernel_nonneg d α) β)) ≤
      (VolumeMoments.M (q - 1) : ℝ≥0∞) *
        (I417.meanVol (bernoulliEdgeProb (lrKernel d α) (lrKernel_nonneg d α) β)
          (0 : Fin d → ℤ)) ^ (2 * q - 1) := by
    apply CanonAtlas.Measure.lintegral_cardFun_pow_le_dfactorial_of_transitive _
      (fun e => bernoulliEdgeProb_lt_one (lrKernel_nonneg d α) β e) hq (0 : Fin d → ℤ)
    intro v
    let g : (Fin d → ℤ) ≃ (Fin d → ℤ) := Equiv.addRight v
    refine ⟨g, ?_, ?_⟩
    · intro e
      induction e using Sym2.ind with
      | _ a b =>
          simpa only [Sym2.map_mk, Equiv.coe_addRight, g] using
            lrKernel_unitInterval_translation_of_pair d α β a b v
    · simp [g]
  simpa only [latticeLongRangeMeasure, longRangeMeasure] using h

end PercLib.CriticalLRP.TreeExpansion

set_option linter.hashCommand false

#print axioms CanonAtlas.Measure.twoPoint_tsum_eq_meanVol_of_transitive
#print axioms CanonAtlas.Measure.lintegral_cardFun_pow_le_dfactorial_of_transitive
#print axioms PercLib.CriticalLRP.TreeExpansion.latticeLongRange_cardFun_pow_le_dfactorial
