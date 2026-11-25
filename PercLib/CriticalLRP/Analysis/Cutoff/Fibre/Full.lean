/-
Swarm `smwtzmkep`, member `m4`, direction (3).
-/
module

public import PercLib.CriticalLRP.Analysis.Cutoff.ExcludedFlux
public import PercLib.CriticalLRP.Analysis.Cutoff.Fibre.Defs
public import PercLib.CriticalLRP.Analysis.Cutoff.Fibre.Reindex

/-!
# Finite-fibre reindexing at the untruncated (paper) level

The statements of `Fibre.Reindex` transferred to the untruncated increments `pairIncrFull` /
`edgeIncrFull` of `Fibre.Defs`:

* `pairIncrFull_self`, `edgeIncrFull_mk`, `edgeIncrFull_loop`: the pointwise inputs;
* `sum_pairIncrFull_eq_sum_edgeIncrFull`: the finite-window identity;
* `tsum_pairIncrFull_eq_tsum_edgeIncrFull`: the `tsum` identity.

Nothing here refers to a measure, a derivative or a moment: these are pointwise summation
identities.
-/

set_option autoImplicit false

open scoped ENNReal NNReal

@[expose] public section

namespace PercLib.CriticalLRP.Orchestration

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Countable V]

/-! ## Pointwise inputs -/

omit [Countable V] in
/-- A vertex contributes nothing paired with itself, at the untruncated level. -/
theorem pairIncrFull_self (d : V → V → Prop) [DecidableRel d] (ω : Config V) (o b : V) :
    pairIncrFull d ω o b b = 0 := by
  simp only [pairIncrFull]
  by_cases h : Connects ω o b <;> simp [h]

omit [Countable V] in
/-- The untruncated edge increment is the sum of its two ordered-pair increments. -/
theorem edgeIncrFull_mk (d : V → V → Prop) [DecidableRel d] (hd : ∀ a b, (d a b ↔ d b a))
    (ω : Config V) (o x y : V) :
    edgeIncrFull d hd ω o s(x, y) = pairIncrFull d ω o x y + pairIncrFull d ω o y x := by
  simp only [edgeIncrFull, pairIncrFull, Sym2.lift_mk]
  by_cases h : d x y
  · have h' : d y x := (hd y x).mpr h
    simp only [h, h', ite_true]
    ring
  · have h' : ¬ d y x := fun hh => h ((hd y x).mp hh)
    simp only [h, h', ite_false, zero_mul]
    ring

omit [Countable V] in
/-- A loop contributes nothing, at the untruncated level. -/
theorem edgeIncrFull_loop (d : V → V → Prop) [DecidableRel d] (hd : ∀ a b, (d a b ↔ d b a))
    (ω : Config V) (o x : V) : edgeIncrFull d hd ω o s(x, x) = 0 := by
  rw [edgeIncrFull_mk]
  simp only [pairIncrFull]
  by_cases h : Connects ω o x <;> simp [h]

/-! ## The window and `tsum` identities -/

omit [Countable V] in
/-- **The finite-window identity at the untruncated level.** -/
theorem sum_pairIncrFull_eq_sum_edgeIncrFull (d : V → V → Prop) [DecidableRel d]
    (hd : ∀ a b, (d a b ↔ d b a)) (ω : Config V) (o : V) (X : Finset V) :
    ∑ x ∈ X, ∑ y ∈ X, pairIncrFull d ω o x y
      = ∑ e ∈ X.sym2, edgeIncrFull d hd ω o e :=
  sum_pairs_eq_sum_sym2 (pairIncrFull_self d ω o) (fun x y => edgeIncrFull_mk d hd ω o x y) X

omit [Countable V] in
/-- **The ordered-pair and edge `tsum`s agree at the untruncated level.** -/
theorem tsum_pairIncrFull_eq_tsum_edgeIncrFull (d : V → V → Prop) [DecidableRel d]
    (hd : ∀ a b, (d a b ↔ d b a)) (ω : Config V) (o : V) :
    (∑' p : V × V, pairIncrFull d ω o p.1 p.2) = ∑' e : Sym2 V, edgeIncrFull d hd ω o e :=
  tsum_pairs_eq_tsum_sym2 (pairIncrFull_self d ω o) (fun x y => edgeIncrFull_mk d hd ω o x y)

end PercLib.CriticalLRP.Orchestration

/-! ## Axiom audit -/

set_option linter.hashCommand false
set_option linter.style.longLine false

namespace PercLib.CriticalLRP.Orchestration

#print axioms PercLib.CriticalLRP.Orchestration.pairIncrFull
#print axioms PercLib.CriticalLRP.Orchestration.edgeIncrFull
#print axioms PercLib.CriticalLRP.Orchestration.pairIncrFull_self
#print axioms PercLib.CriticalLRP.Orchestration.edgeIncrFull_mk
#print axioms PercLib.CriticalLRP.Orchestration.edgeIncrFull_loop
#print axioms PercLib.CriticalLRP.Orchestration.sum_pairIncrFull_eq_sum_edgeIncrFull
#print axioms PercLib.CriticalLRP.Orchestration.tsum_pairIncrFull_eq_tsum_edgeIncrFull

end PercLib.CriticalLRP.Orchestration
