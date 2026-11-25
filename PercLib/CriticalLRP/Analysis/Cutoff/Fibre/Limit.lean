/-
Swarm `smwtzmkep`, member `m4`, direction (3).
-/
module

public import PercLib.CriticalLRP.Analysis.Cutoff.ExcludedFlux
public import PercLib.CriticalLRP.Analysis.Cutoff.Fibre.Defs
public import PercLib.CriticalLRP.Analysis.Cutoff.Fibre.Full
public import PercLib.CriticalLRP.Analysis.Cutoff.Fibre.Reindex
public import PercLib.CriticalLRP.Analysis.Cutoff.Fibre.Truncation

/-!
# The truncation limit of the summed excluded increment

The model's summed excluded increment over a finite truncation `A`,
`A ↦ Σ'_p pairIncr d ω o A p.1 p.2`, is monotone in `A`, and its supremum over all finite `A` is
the paper's summed weight `Σ'_p pairIncrFull d ω o p.1 p.2`.  The same holds on the closed-edge
side:

* `iSup_tsum_pairIncr_eq_tsum_pairIncrFull`;
* `iSup_tsum_edgeIncr_eq_tsum_edgeIncrFull`.

The proof is a finite-sum/sup interchange: for a finite `P`, `Σ_{p∈P} ⨆_A g A p = ⨆_A Σ_{p∈P} g A p`
(`sum_iSup_eq_iSup_sum`), because the index `Finset V` is directed by union and every summand is
monotone in `A` (`iSup_add_iSup_of_monotone`), and then two `iSup` interchanges.

This is a *pointwise* statement about the integrand.  No measure, no monotone-convergence theorem
under a law, no derivative and no infinite-moment claim is made here.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped ENNReal NNReal

@[expose] public section

namespace PercLib.CriticalLRP.Orchestration

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Countable V]

/-- Truncating the cluster volume to a larger finite vertex set does not decrease the
excluded increment. -/
theorem monotone_pairIncr_trunc (d : V → V → Prop) [DecidableRel d] (ω : Config V) (o b c : V) :
    Monotone (fun A : Finset V => pairIncr d ω o A b c) := by
  intro A B hAB
  simp only [pairIncr]
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum_of_subset_of_nonneg hAB ?_) zero_le
  intro x _ _
  exact zero_le

/-- The sum of the suprema of two monotone families over the directed set of finite vertex sets
is the supremum of the sums: enlarging the truncation handles both families at once. -/
theorem iSup_add_iSup_of_monotone {f g : Finset V → ℝ≥0∞} (hf : Monotone f) (hg : Monotone g) :
    (⨆ A, f A) + (⨆ A, g A) = ⨆ A, (f A + g A) := by
  refine le_antisymm ?_ (iSup_le fun A => add_le_add (le_iSup f A) (le_iSup g A))
  rw [ENNReal.iSup_add]
  refine iSup_le fun A => ?_
  rw [ENNReal.add_iSup]
  refine iSup_le fun B => ?_
  exact le_trans (add_le_add (hf (Finset.subset_union_left : A ⊆ A ∪ B))
    (hg (Finset.subset_union_right : B ⊆ A ∪ B))) (le_iSup (fun C => f C + g C) (A ∪ B))

/-- A finite sum of suprema of monotone families over finite vertex sets is the supremum of the
finite sums. -/
theorem sum_iSup_eq_iSup_sum (P : Finset (V × V)) (g : Finset V → V × V → ℝ≥0∞)
    (hg : ∀ p, Monotone (fun A => g A p)) :
    ∑ p ∈ P, (⨆ A, g A p) = ⨆ A, ∑ p ∈ P, g A p := by
  induction P using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih =>
    have hmono : Monotone (fun A : Finset V => ∑ p ∈ s, g A p) :=
      fun A B hAB => Finset.sum_le_sum fun p _ => hg p hAB
    calc ∑ p ∈ Finset.cons a s ha, (⨆ A, g A p)
        = (⨆ A, g A a) + (∑ p ∈ s, ⨆ A, g A p) := Finset.sum_cons ha
      _ = (⨆ A, g A a) + (⨆ A, ∑ p ∈ s, g A p) := by rw [ih]
      _ = ⨆ A, (g A a + ∑ p ∈ s, g A p) := iSup_add_iSup_of_monotone (hg a) hmono
      _ = ⨆ A, ∑ p ∈ Finset.cons a s ha, g A p :=
        iSup_congr fun A => (Finset.sum_cons ha).symm

/-- **The truncations of the summed ordered-pair excluded increment increase to the paper's
summed weight.** -/
theorem iSup_tsum_pairIncr_eq_tsum_pairIncrFull (d : V → V → Prop) [DecidableRel d]
    (ω : Config V) (o : V) :
    (⨆ A : Finset V, ∑' p : V × V, pairIncr d ω o A p.1 p.2)
      = ∑' p : V × V, pairIncrFull d ω o p.1 p.2 := by
  calc (⨆ A : Finset V, ∑' p : V × V, pairIncr d ω o A p.1 p.2)
      = ⨆ A : Finset V, ⨆ P : Finset (V × V), ∑ p ∈ P, pairIncr d ω o A p.1 p.2 :=
        iSup_congr fun A => ENNReal.tsum_eq_iSup_sum
    _ = ⨆ P : Finset (V × V), ⨆ A : Finset V, ∑ p ∈ P, pairIncr d ω o A p.1 p.2 := iSup_comm
    _ = ⨆ P : Finset (V × V), ∑ p ∈ P, ⨆ A : Finset V, pairIncr d ω o A p.1 p.2 :=
        iSup_congr fun P =>
          (sum_iSup_eq_iSup_sum P (fun A p => pairIncr d ω o A p.1 p.2)
            (fun p => monotone_pairIncr_trunc d ω o p.1 p.2)).symm
    _ = ⨆ P : Finset (V × V), ∑ p ∈ P, pairIncrFull d ω o p.1 p.2 :=
        iSup_congr fun P => Finset.sum_congr rfl fun p _ =>
          iSup_pairIncr_eq_pairIncrFull d ω o p.1 p.2
    _ = ∑' p : V × V, pairIncrFull d ω o p.1 p.2 := ENNReal.tsum_eq_iSup_sum.symm

/-- **The truncations of the summed edge excluded increment increase to the paper's summed
weight, read over unordered edges.** -/
theorem iSup_tsum_edgeIncr_eq_tsum_edgeIncrFull (d : V → V → Prop) [DecidableRel d]
    (hd : ∀ a b, (d a b ↔ d b a)) (ω : Config V) (o : V) :
    (⨆ A : Finset V, ∑' e : Sym2 V, edgeIncr d hd ω o A e)
      = ∑' e : Sym2 V, edgeIncrFull d hd ω o e := by
  calc (⨆ A : Finset V, ∑' e : Sym2 V, edgeIncr d hd ω o A e)
      = ⨆ A : Finset V, ∑' p : V × V, pairIncr d ω o A p.1 p.2 :=
        iSup_congr fun A => (tsum_pairIncr_eq_tsum_edgeIncr d hd ω o A).symm
    _ = ∑' p : V × V, pairIncrFull d ω o p.1 p.2 :=
        iSup_tsum_pairIncr_eq_tsum_pairIncrFull d ω o
    _ = ∑' e : Sym2 V, edgeIncrFull d hd ω o e :=
        tsum_pairIncrFull_eq_tsum_edgeIncrFull d hd ω o

end PercLib.CriticalLRP.Orchestration

/-! ## Axiom audit -/

set_option linter.hashCommand false
set_option linter.style.longLine false

namespace PercLib.CriticalLRP.Orchestration

#print axioms PercLib.CriticalLRP.Orchestration.monotone_pairIncr_trunc
#print axioms PercLib.CriticalLRP.Orchestration.iSup_add_iSup_of_monotone
#print axioms PercLib.CriticalLRP.Orchestration.sum_iSup_eq_iSup_sum
#print axioms PercLib.CriticalLRP.Orchestration.iSup_tsum_pairIncr_eq_tsum_pairIncrFull
#print axioms PercLib.CriticalLRP.Orchestration.iSup_tsum_edgeIncr_eq_tsum_edgeIncrFull

end PercLib.CriticalLRP.Orchestration
