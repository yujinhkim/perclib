/- Integrated from independently rebuilt Ultramath work, base revision 75f8858d8e30ea17b20f9ff1d216bc1508c01ce2.
Scratch source: ../../.ultramath/smwpxw774/m1/S474A/BK.lean ; module path rewritten only.
-/

/-
# Iterated BK in `ℝ≥0∞` form, and the value of a five-edge tree diagram

The repository's `Percolation.bk_fin` (`PercLib.CriticalLRP.BK.Finite`) is the iterated
van den Berg--Kesten inequality for the `ℝ`-valued law `edgeLaw p`.  Everything in this
development is `ℝ≥0∞`-valued, so we restate the induction in `ℝ≥0∞` using the two-fold
`bk_ennreal` of `PercLib.CriticalLRP.Correlation.TreeGraphCanonical`; no `toReal` transport is
needed and no finiteness hypothesis is introduced.

Consequence: the measure of a five-edge tree diagram is at most the product of its five
two-point functions (`tree5_le`), which is the numerical value the printed diagram carries
once the summed vertices are evaluated by transitivity.
-/
module

public import PercLib.CriticalLRP.Correlation.I417Example.Defs

open MeasureTheory Measure ProbabilityTheory unitInterval
open scoped ENNReal NNReal

@[expose] public section

namespace PercLib.CriticalLRP.I417Example

variable {V : Type*} [Countable V]

attribute [local instance] Classical.propDecidable

/-- **Iterated BK for a `Fin`-indexed family, `ℝ≥0∞` form.**  For increasing finitely witnessed
events `A i`, the `k`-fold disjoint occurrence has measure at most the product of the measures. -/
theorem bk_fin_ennreal (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1) {k : ℕ}
    (A : Fin k → Set (Config V)) (hA : ∀ i, IsUpperSet (A i))
    (hf : ∀ i, Percolation.FiniteWitness (A i)) :
    (edgeMeasure π) (Percolation.DisjointOccurrenceFin A) ≤ ∏ i, (edgeMeasure π) (A i) := by
  induction k with
  | zero =>
      have huniv : Percolation.DisjointOccurrenceFin A = Set.univ := by
        ext ω
        refine ⟨fun _ => trivial, fun _ => ?_⟩
        exact ⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩
      rw [huniv, measure_univ]
      simp
  | succ k ih =>
      rw [Percolation.disjointOccurrenceFin_succ_eq]
      have hbound := bk_ennreal π hπ (A 0)
        (Percolation.DisjointOccurrenceFin fun i : Fin k => A i.succ)
        (hA 0) (Percolation.disjointOccurrenceFin_upper _) (hf 0)
        (Percolation.disjointOccurrenceFin_finiteWitness _)
      have htail := ih (fun i : Fin k => A i.succ) (fun i => hA i.succ) (fun i => hf i.succ)
      rw [Fin.prod_univ_succ]
      exact hbound.trans (mul_le_mul' le_rfl htail)

/-- **BK for the five-edge tree diagrams**: `P(Tree5 A B C D E) ≤ P(A)P(B)P(C)P(D)P(E)` for
increasing finitely witnessed events. -/
theorem tree5_le (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1)
    (A B C D E : Set (Config V)) (hA : IsUpperSet A) (hB : IsUpperSet B) (hC : IsUpperSet C)
    (hD : IsUpperSet D) (hE : IsUpperSet E)
    (fA : Percolation.FiniteWitness A) (fB : Percolation.FiniteWitness B)
    (fC : Percolation.FiniteWitness C) (fD : Percolation.FiniteWitness D)
    (fE : Percolation.FiniteWitness E) :
    (edgeMeasure π) (Tree5 A B C D E) ≤
      (edgeMeasure π) A * (edgeMeasure π) B * (edgeMeasure π) C * (edgeMeasure π) D *
        (edgeMeasure π) E := by
  have hU : ∀ i : Fin 5, IsUpperSet (![A, B, C, D, E] i) := by
    intro i
    fin_cases i <;> simpa using ‹_›
  have hF : ∀ i : Fin 5, Percolation.FiniteWitness (![A, B, C, D, E] i) := by
    intro i
    fin_cases i <;> simpa using ‹_›
  have h := bk_fin_ennreal π hπ (fun i : Fin 5 => ![A, B, C, D, E] i) hU hF
  have hprod : (∏ i : Fin 5, (edgeMeasure π) (![A, B, C, D, E] i)) =
      (edgeMeasure π) A * (edgeMeasure π) B * (edgeMeasure π) C * (edgeMeasure π) D *
        (edgeMeasure π) E := by
    simp [Fin.prod_univ_five]
  rw [hprod] at h
  exact h

end PercLib.CriticalLRP.I417Example
