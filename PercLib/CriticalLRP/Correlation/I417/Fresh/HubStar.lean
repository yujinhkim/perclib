/- The canonical marked-terminal interpretation of `hubStar`.
Independently assembled by the coordinator at production base
`7de248af57491ca9436e22580350c7e954cb9474`.
The strict candidate was `.scratch/verification/fresh-hubstar/Main.lean`. -/

module
public import PercLib.CriticalLRP.Correlation.I417.Fresh.Main
public import PercLib.CriticalLRP.Correlation.I417.MarkedJoint.Transversal.Depth

/-! The hub star is exactly a canonical marked terminal event. -/

open MeasureTheory Measure ProbabilityTheory unitInterval
open scoped ENNReal NNReal

@[expose] public section

namespace PercLib.CriticalLRP.I417Fresh

variable {V : Type*} [Countable V]

/-- The ordinary terminal event is the arm star. -/
theorem labelEvent_eq_armStar (w : V) {q : ℕ} (g : Fin q → V) :
    I417A.labelEvent w g = armStar w g := by
  ext ω
  simp [armStar, I417A.labelEvent_eq_iInter, connSet]

/-- The hub star is the terminal event with root `w`, arms `g` and marked leaf `y`. -/
theorem hubStar_eq_labelEvent_markedExtend (y w : V) {q : ℕ} (g : Fin q → V) :
    hubStar y w g = I417A.labelEvent w (I417Marked.markedExtend y g) := by
  rw [I417Marked.labelEvent_markedExtend, hubStar, ← labelEvent_eq_armStar,
    connSet_swap y w]
  exact Set.inter_comm _ _

/-- The hub-star arm sum is the base marked joint moment with the roles of the root and mark
chosen at the fresh side. No restored-cluster identity or finite approximation is used. -/
theorem tsum_hubStar_eq_jointPow (π : Sym2 V → unitInterval) (y w : V) (q : ℕ) :
    (∑' g : Fin q → V, (edgeMeasure π) (hubStar y w g)) = I417Gen.jointPow π w q y := by
  rw [← I417Gen.tsum_labelEvent_inter π w q y]
  exact tsum_congr fun g => by
    rw [← I417Marked.labelEvent_markedExtend, ← hubStar_eq_labelEvent_markedExtend]

variable [DecidableEq V]

/-- The ordinary marked non-plane depth bound lifts to the fresh hub star through the exact
terminal-event identity. This is an upper bound on the larger hub-star event, not a claim that
its chain-cover decomposition follows. -/
theorem tsum_hubStar_le_nonplane_markedDepth (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1)
    (χ : ℝ≥0∞) (hχ : ∀ v, ∑' y : V, (edgeMeasure π) (connSet v y) = χ)
    (y w : V) {q : ℕ} (hq : 1 ≤ q) :
    (∑' g : Fin q → V, (edgeMeasure π) (hubStar y w g)) ≤
      ∑ ℓ ∈ Finset.Icc 2 (q + 1), (I417MarkedTransversal.nonplaneMarkedCount q ℓ : ℝ≥0∞) *
        (χ ^ (2 * q + 1 - ℓ) *
          I417Base.iterPow (fun a b => (edgeMeasure π) (connSet a b)) ℓ w y) := by
  rw [tsum_hubStar_eq_jointPow]
  exact I417MarkedTransversal.jointPow_le_nonplane_markedDepth π hπ χ hχ w hq y

/-- The same upper bound applies to the genuine fresh factor by its already proved containment
in the larger hub-star event. -/
theorem tsum_freshMark_le_nonplane_markedDepth (π : Sym2 V → unitInterval)
    (hπ : ∀ e, π e < 1) (χ : ℝ≥0∞) (hχ : ∀ v, ∑' y : V, (edgeMeasure π) (connSet v y) = χ)
    (y w : V) {q : ℕ} (hq : 1 ≤ q) (j : Fin q) :
    (∑' g : Fin q → V, (edgeMeasure π) (I417Gen.freshMark y g j w)) ≤
      ∑ ℓ ∈ Finset.Icc 2 (q + 1), (I417MarkedTransversal.nonplaneMarkedCount q ℓ : ℝ≥0∞) *
        (χ ^ (2 * q + 1 - ℓ) *
          I417Base.iterPow (fun a b => (edgeMeasure π) (connSet a b)) ℓ w y) := by
  refine (ENNReal.tsum_le_tsum fun g => ?_).trans
    (tsum_hubStar_le_nonplane_markedDepth π hπ χ hχ y w hq)
  exact measure_mono (freshMark_subset_hubStar y w g j)

end PercLib.CriticalLRP.I417Fresh

set_option linter.hashCommand false

#print axioms PercLib.CriticalLRP.I417Fresh.hubStar_eq_labelEvent_markedExtend
#print axioms PercLib.CriticalLRP.I417Fresh.tsum_hubStar_eq_jointPow
#print axioms PercLib.CriticalLRP.I417Fresh.tsum_freshMark_le_nonplane_markedDepth
