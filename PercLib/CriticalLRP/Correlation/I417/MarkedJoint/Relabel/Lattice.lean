/- Coordinator-assembled vertex-transitivity and canonical power-law instantiations.
Production base: `6839e6c10d3409bc64145d313d7e4438c3c7f41f`.
The strict candidate was `.scratch/verification/q-one-lattice/Main.lean`. -/

module

public import PercLib.CriticalLRP.Correlation.I417.MarkedJoint.Relabel.QOne
public import PercLib.CriticalLRP.Correlation.I417Example.Trans
public import PercLib.CriticalLRP.PowerLawTreeMoments

/-! The positive-`p`, `q = 1` moment-gap bound on vertex-transitive models. -/

open MeasureTheory Measure ProbabilityTheory unitInterval
open scoped ENNReal NNReal

@[expose] public section

namespace PercLib.CriticalLRP.I417MarkedRelabel

/-- The positive-`p`, `q = 1` polygon bound, with transitivity discharged by
profile-preserving vertex permutations. -/
theorem moment_gap_q_one_le_of_transitive_pos {V : Type*} [Countable V] [DecidableEq V]
    (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1) (x y : V)
    (htrans : ∀ v : V, ∃ g : V ≃ V, (∀ e : Sym2 V, π (Sym2.map g e) = π e) ∧ g x = v)
    {p : ℕ} (hp : 1 ≤ p) :
    I417A.momentProd π x y p 1 - I417A.rawDiff π x y p 1 ≤
      ∑ ℓ ∈ Finset.Icc 2 (p + 1), (I417Marked.markedCount p ℓ : ℝ≥0∞) *
        ((I417.meanVol π x) ^ (2 * p + 2 - ℓ) *
          I417Base.iterPow (fun a b => (edgeMeasure π) (connSet a b)) (ℓ + 1) x y) :=
  moment_gap_q_one_le_of_pos π hπ x y (I417Example.meanVol_eq_of_transitive π x htrans) hp

end PercLib.CriticalLRP.I417MarkedRelabel

namespace PercLib.CriticalLRP.TreeExpansion

/-- The positive-`p`, `q = 1` instance of Lemma I.4.17 for the canonical power-law
law on `ℤ^d`. No subcriticality or finite-moment premise is added. -/
theorem latticeLongRange_moment_gap_q_one_le_of_pos (d : ℕ) (α : ℝ) (β : NNReal)
    (x y : Fin d → ℤ) {p : ℕ} (hp : 1 ≤ p) :
    I417A.momentProd (bernoulliEdgeProb (lrKernel d α) (lrKernel_nonneg d α) β) x y p 1 -
      I417A.rawDiff (bernoulliEdgeProb (lrKernel d α) (lrKernel_nonneg d α) β) x y p 1 ≤
      ∑ ℓ ∈ Finset.Icc 2 (p + 1), (I417Marked.markedCount p ℓ : ℝ≥0∞) *
        ((I417.meanVol (bernoulliEdgeProb (lrKernel d α) (lrKernel_nonneg d α) β) x) ^
          (2 * p + 2 - ℓ) *
          I417Base.iterPow (fun a b =>
            (edgeMeasure (bernoulliEdgeProb (lrKernel d α) (lrKernel_nonneg d α) β))
              (connSet a b)) (ℓ + 1) x y) := by
  apply I417MarkedRelabel.moment_gap_q_one_le_of_transitive_pos _
    (fun e => bernoulliEdgeProb_lt_one (lrKernel_nonneg d α) β e) x y _ hp
  intro v
  let g : (Fin d → ℤ) ≃ (Fin d → ℤ) := Equiv.addRight (v - x)
  refine ⟨g, ?_, ?_⟩
  · intro e
    induction e using Sym2.ind with
    | _ a b =>
        simpa only [Sym2.map_mk, Equiv.coe_addRight, g] using
          lrKernel_unitInterval_translation_of_pair d α β a b (v - x)
  · simp [g]

end PercLib.CriticalLRP.TreeExpansion

set_option linter.hashCommand false

#print axioms PercLib.CriticalLRP.I417MarkedRelabel.moment_gap_q_one_le_of_transitive_pos
#print axioms PercLib.CriticalLRP.TreeExpansion.latticeLongRange_moment_gap_q_one_le_of_pos
