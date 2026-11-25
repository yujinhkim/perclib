/- Integrated from independently rebuilt Ultramath work.
Production base 70b027b0634874e65ce4bf8ec8fc8a7835e658e7.
Scratch source: repository-root .ultramath/smwwnvyp3/m3/.
-/

/- Consistency of the Case 1 quantities with the existing Lemma I.4.11 formulation.
-/
module

public import PercLib.CriticalLRP.VolumeMoments.HigherMoments.I420Case1.Main
public import PercLib.CriticalLRP.Correlation.I411.Basic

/-!
# Consistency checks for the Case 1 quantities

`I411.exclMoment` is the paper's `E_{β,r}[|K| ∑_{y∈B} 1(y∉K)|K_y|]`, the case
`ℓ = 1`, `p = 2` of the excluded mixed marked expectation.  `mixedExcl_one_one`
records that `mixedExcl π o 1 1 B` is *the same object*; the Case 1 theorem is thus a
genuine generalisation in `(ℓ+1, p-ℓ)` of the quantity already used in Lemma I.4.11,
not a new quantity with the paper's name.

The degenerate cases (`B = ∅`) evaluate to `0` on both sides of the discrepancy,
which is a check that the definitions do not silently add a positive `|K_o|` factor
when the window is empty.
-/

@[expose] public section

noncomputable section

open MeasureTheory Measure ProbabilityTheory unitInterval
open scoped ENNReal

set_option linter.unusedSectionVars false

namespace PercLib.CriticalLRP

namespace I420Case1

variable {V : Type*} [Countable V]

/-- The Case 1 excluded mixed marked expectation at `(a, b) = (1, 1)` is exactly the
Lemma I.4.11 excluded expectation. -/
theorem mixedExcl_one_one (π : Sym2 V → unitInterval) (o : V) (B : Finset V) :
    mixedExcl π o 1 1 B = I411.exclMoment π o B := by
  rw [mixedExcl, I411.exclMoment]
  simp only [pow_one]

/-- The excluded mixed marked expectation vanishes on the empty window. -/
theorem mixedExcl_empty (π : Sym2 V → unitInterval) (o : V) (a b : ℕ) :
    mixedExcl π o a b ∅ = 0 := by
  rw [mixedExcl]
  simp

/-- The product factor vanishes on the empty window. -/
theorem prodFactor_empty (π : Sym2 V → unitInterval) (o : V) (a b : ℕ) :
    prodFactor π o a b ∅ = 0 := by
  rw [prodFactor]
  simp

/-- The mixed cluster-window moment vanishes on the empty window. -/
theorem windowMoment_empty (π : Sym2 V → unitInterval) (o : V) (k : ℕ) :
    windowMoment π o k ∅ = 0 := by
  rw [windowMoment]
  have hzero : ∀ ω : Config V, clusterVolIn ω o ((∅ : Finset V) : Set V) = 0 := by
    intro ω
    rw [clusterVolIn_coe_finset]
    simp
  simp only [hzero, mul_zero]
  simp

end I420Case1

end PercLib.CriticalLRP
