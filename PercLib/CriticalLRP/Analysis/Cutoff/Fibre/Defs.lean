/-
Swarm `smwtzmkep`, member `m4`, direction (3).  Definitions only; the reindexing statements live
in `Fibre.Full`.
-/
module

public import PercLib.CriticalLRP.Analysis.Cutoff.ExcludedFlux

/-!
# Untruncated ordered-pair and edge excluded increments

`ExcludedFlux.pairIncr` / `ExcludedFlux.edgeIncr` carry the cluster volume truncated to a finite
vertex set `A` (that is what makes the model's finite-moment arguments work).  The paper's own
double sum `PivotFlux.paperSum` uses the *full* cluster volume `|K_c|` instead.  This file
introduces the untruncated counterparts `pairIncrFull` and `edgeIncrFull`, so that the finite-fibre
reindexing can be stated at the paper's level and then compared with `PivotFlux.paperSum`.
-/

set_option autoImplicit false

open scoped ENNReal NNReal

@[expose] public section

namespace PercLib.CriticalLRP.Orchestration

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Countable V]

/-- The untruncated ordered-pair (`p = 1`, standardized) excluded increment: the paper's
`pivotWeight r ω 0 b c` with the full cluster volume `|K_c|`, before summing.  `d` is the
two-point distance predicate (`d c b` is `M.S.dist c b ≤ r`). -/
noncomputable def pairIncrFull (d : V → V → Prop) [DecidableRel d] (ω : Config V) (o b c : V) :
    ℝ≥0∞ :=
  (if Connects ω o b then (1 : ℝ≥0∞) else 0) * (if d c b then 1 else 0) *
    (if ¬ Connects ω b c then 1 else 0) * clusterVol ω c

/-- The untruncated edge increment: `pairIncrFull` read as a function of the unordered edge,
i.e. the sum of its two ordered-pair increments. -/
noncomputable def edgeIncrFull (d : V → V → Prop) [DecidableRel d]
    (hd : ∀ a b, (d a b ↔ d b a)) (ω : Config V) (o : V) (e : Sym2 V) : ℝ≥0∞ :=
  Sym2.lift ⟨fun x y => (if d x y then 1 else 0) *
      ((if Connects ω o x then (1 : ℝ≥0∞) else 0) * (if ¬ Connects ω x y then 1 else 0) *
          clusterVol ω y
        + (if Connects ω o y then (1 : ℝ≥0∞) else 0) * (if ¬ Connects ω y x then 1 else 0) *
          clusterVol ω x), by
    intro a b
    dsimp only
    by_cases hab : d a b
    · have hba : d b a := (hd b a).mpr hab
      simp only [hab, hba, ite_true]
      ring
    · have hba : ¬ d b a := fun h => hab ((hd b a).mp h)
      simp only [hab, hba, ite_false]
      ring⟩ e

/-- The two-point distance predicate of a source model at radius `r`, in the ordered-pair
orientation used by `pairIncrFull` (`d c b` is `dist c b ≤ r`). -/
def cutDist (M : SourceModelData) (r : ℝ) : M.V → M.V → Prop := fun c b => M.S.dist c b ≤ r

/-- The distance predicate is symmetric, so the edge version of the source weight is available. -/
theorem cutDist_symm (M : SourceModelData) (r : ℝ) :
    ∀ a b : M.V, (cutDist M r a b ↔ cutDist M r b a) := by
  intro a b
  simp only [cutDist, SourceNormData.dist_comm M.S b a]

end PercLib.CriticalLRP.Orchestration
