/-
Swarm `smwtzmkep`, member `m4`, direction (3).
-/
module

public import PercLib.CriticalLRP.Analysis.Cutoff.ExcludedFlux
public import PercLib.CriticalLRP.Analysis.Cutoff.Fibre.Defs

/-!
# Finite truncations increase to the untruncated excluded increment

The model's excluded increments `pairIncr d ω o A` carry the cluster volume truncated to a finite
vertex set `A`; the paper's weight `pairIncrFull` uses the full `|K_c|`.  This file proves the
pointwise comparison:

* `sMomentTruncENN_one_le_clusterVol`: the truncated cardinality is at most `|K_c|`;
* `iSup_sMomentTruncENN_one`: truncations increase to `|K_c|` over all finite `A`;
* `pairIncr_le_pairIncrFull`: `pairIncr … A ≤ pairIncrFull …` pointwise;
* `iSup_pairIncr_eq_pairIncrFull`: `⨆ A, pairIncr … A = pairIncrFull …` pointwise;
* `tsum_pairIncr_le_tsum_pairIncrFull`: the corresponding `tsum` comparison.

Only pointwise statements about the integrand are proved.  Nothing here says that the truncations
increase to the paper weight *under a measure* (that would be a monotone-convergence step) or that
a derivative may be passed through any of these sums.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped ENNReal NNReal

@[expose] public section

namespace PercLib.CriticalLRP.Orchestration

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Countable V]

/-- The truncated cardinality of a cluster is at most the full cluster volume. -/
theorem sMomentTruncENN_one_le_clusterVol (ω : Config V) (c : V) (A : Finset V) :
    sMomentTruncENN (fun _ => (1 : ℝ)) c A ω ≤ clusterVol ω c := by
  rw [clusterVol_eq_tsum]
  simp only [sMomentTruncENN, ENNReal.ofReal_one]
  exact ENNReal.sum_le_tsum A

/-- The truncations of the cardinality of a cluster increase to its full volume. -/
theorem iSup_sMomentTruncENN_one (ω : Config V) (c : V) :
    (⨆ A : Finset V, sMomentTruncENN (fun _ => (1 : ℝ)) c A ω) = clusterVol ω c := by
  rw [clusterVol_eq_tsum, ENNReal.tsum_eq_iSup_sum]
  exact iSup_congr fun A => by simp only [sMomentTruncENN, ENNReal.ofReal_one]

/-- The truncated excluded increment is at most the untruncated one. -/
theorem pairIncr_le_pairIncrFull (d : V → V → Prop) [DecidableRel d] (ω : Config V) (o b c : V)
    (A : Finset V) :
    pairIncr d ω o A b c ≤ pairIncrFull d ω o b c := by
  simp only [pairIncr, pairIncrFull]
  exact mul_le_mul_of_nonneg_left (sMomentTruncENN_one_le_clusterVol ω c A) zero_le

/-- **Truncations increase to the paper's ordered-pair increment.** -/
theorem iSup_pairIncr_eq_pairIncrFull (d : V → V → Prop) [DecidableRel d] (ω : Config V)
    (o b c : V) :
    (⨆ A : Finset V, pairIncr d ω o A b c) = pairIncrFull d ω o b c := by
  simp only [pairIncr, pairIncrFull]
  rw [← iSup_sMomentTruncENN_one ω c]
  rw [ENNReal.mul_iSup]

/-- The `tsum` of the truncated increments is bounded by the `tsum` of the untruncated ones. -/
theorem tsum_pairIncr_le_tsum_pairIncrFull (d : V → V → Prop) [DecidableRel d] (ω : Config V)
    (o : V) (A : Finset V) :
    (∑' p : V × V, pairIncr d ω o A p.1 p.2) ≤ ∑' p : V × V, pairIncrFull d ω o p.1 p.2 :=
  ENNReal.tsum_le_tsum fun p => pairIncr_le_pairIncrFull d ω o p.1 p.2 A

end PercLib.CriticalLRP.Orchestration

/-! ## Axiom audit -/

set_option linter.hashCommand false
set_option linter.style.longLine false

namespace PercLib.CriticalLRP.Orchestration

#print axioms PercLib.CriticalLRP.Orchestration.sMomentTruncENN_one_le_clusterVol
#print axioms PercLib.CriticalLRP.Orchestration.iSup_sMomentTruncENN_one
#print axioms PercLib.CriticalLRP.Orchestration.pairIncr_le_pairIncrFull
#print axioms PercLib.CriticalLRP.Orchestration.iSup_pairIncr_eq_pairIncrFull
#print axioms PercLib.CriticalLRP.Orchestration.tsum_pairIncr_le_tsum_pairIncrFull

end PercLib.CriticalLRP.Orchestration
