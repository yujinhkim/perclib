/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

# Measurability of `encard` along a measurable set-valued map

Independent submission `smwp81k72`: useful for a proposed first-hit partition,
without asserting that partition or any higher-moment theorem.
-/

/-
Swarm `smwp81k72`, member `m2`, direction d2.  Proof-only module.

A reusable measurability lemma that any *branch decomposition* of the cluster needs, and
that the repository only has for `cluster` itself (`PercLib.Percolation.Bond.measurable_encard_cluster`):
the `ℝ≥0∞`-cardinality of a measurable set-valued map is measurable.  This applies to
set differences and priority-selected pieces of a branch decomposition.
Measurability alone does not assert that such pieces cover the
cluster or are independent of the root-incident edges.

No new axioms, no `sorry`, no `admit`, no `native_decide`, no heartbeat changes.
-/
module

public import PercLib.CriticalLRP.CountableProduct.MomentRecursion

set_option autoImplicit false
set_option linter.deprecated false
set_option linter.unusedSectionVars false

attribute [local instance] Classical.propDecidable

@[expose] public section

open MeasureTheory Set
open PercLib.Percolation.Bond
open scoped ENNReal

namespace PercLib.CriticalLRP.MomentRecursion.SetEncCard

open PercLib.CriticalLRP.Renewal

variable {V : Type*} [Countable V] {W : Type*} [Countable W]

/-- **`encard` of a measurable set-valued map.**  For a countable `W` and a measurable
`S : Config V → Set W`, the function `ω ↦ ((S ω).encard : ℝ≥0∞)` is measurable.  Proved
by writing the cardinality as the sum of the indicators of the coordinates `z ∈ S ω`, via
the accepted `setVol_eq_encard`. -/
theorem measurable_encard_of_measurable {S : Config V → Set W} (hS : Measurable S) :
    Measurable fun ω => ((S ω).encard : ℝ≥0∞) := by
  classical
  have hfun : (fun ω => ((S ω).encard : ℝ≥0∞))
      = fun ω => ∑' z : W, (S ω).indicator (fun _ => (1 : ℝ≥0∞)) z := by
    funext ω
    exact (setVol_eq_encard (S ω)).symm
  rw [hfun]
  refine Measurable.ennreal_tsum fun z => ?_
  have hset : MeasurableSet {ω : Config V | z ∈ S ω} :=
    measurableSet_setOfPred.mpr (hS.mem z)
  have hind : (fun ω : Config V => (S ω).indicator (fun _ => (1 : ℝ≥0∞)) z)
      = fun ω => if z ∈ S ω then (1 : ℝ≥0∞) else 0 := by
    funext ω
    exact Set.indicator_apply (S ω) (fun _ => (1 : ℝ≥0∞)) z
  rw [hind]
  exact Measurable.ite hset measurable_const measurable_const

/-- Specialisation to the pruned cluster, recovering
`measurable_prunedVol` as an instance of the general lemma. -/
example (o y : V) : Measurable fun ω : Config V =>
    ((cluster (ω ∩ blockT o) y).encard : ℝ≥0∞) :=
  measurable_encard_of_measurable (measurable_cluster y |>.comp (measurable_inter_const (blockT o)))

#print axioms PercLib.CriticalLRP.MomentRecursion.SetEncCard.measurable_encard_of_measurable
