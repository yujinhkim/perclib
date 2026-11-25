/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

module

public import PercLib.CriticalLRP.BK.Lift

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

set_option autoImplicit true

/-!
# Iterated BK for a `Fin`-indexed family of events

`bk_list` gives the iterated BK inequality for a list of increasing finitely witnessed events.  The
tree-graph development of member m1 (`LRPTree.BKIncreasing`) uses a `Fin k`-indexed family, so this
file provides that form.  It also provides the bridge between my `Set E`-based model and the
`Finset E`-based finite Bernoulli law of the root project, which is how `BKIncreasing` is
discharged in `BKBridge.lean`.
-/

set_option maxHeartbeats 1000000

@[expose] public section

namespace PercLib.CriticalLRP

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section Fin
attribute [local instance] Classical.propDecidable

/-- `k`-fold disjoint occurrence: pairwise disjoint finite witnesses, each contained in `ω` and
already forcing its event. -/
def DisjointOccurrenceFin {k : ℕ} (A : Fin k → Set (Set E)) : Set (Set E) :=
  {ω | ∃ W : Fin k → Finset E, (∀ i, (W i : Set E) ⊆ ω) ∧ (∀ i, (W i : Set E) ∈ A i) ∧
    ∀ i j, i ≠ j → Disjoint (W i) (W j)}

theorem disjointOccurrenceFin_upper {k : ℕ} (A : Fin k → Set (Set E)) :
    IsUpperSet (DisjointOccurrenceFin A) := by
  rintro ω η h ⟨W, hsub, hmem, hdisj⟩
  exact ⟨W, fun i => (hsub i).trans h, hmem, hdisj⟩

theorem disjointOccurrenceFin_finiteWitness {k : ℕ} (A : Fin k → Set (Set E)) :
    FiniteWitness (DisjointOccurrenceFin A) := by
  rintro ω ⟨W, hsub, hmem, hdisj⟩
  refine ⟨Finset.univ.sup W, ?_, W, ?_, hmem, hdisj⟩
  · intro e he
    obtain ⟨i, -, hi⟩ := Finset.mem_sup.mp he
    exact hsub i hi
  · intro i
    exact Finset.le_sup (f := W) (Finset.mem_univ i)

/-- Splitting off the first coordinate of a `Fin (k+1)`-indexed disjoint occurrence. -/
theorem disjointOccurrenceFin_succ_eq {k : ℕ} (A : Fin (k + 1) → Set (Set E)) :
    DisjointOccurrenceFin A =
      DisjointOccurrence (A 0) (DisjointOccurrenceFin fun i : Fin k => A i.succ) := by
  have hsup : ∀ (W : Fin k → Finset E) (i : Fin k), W i ⊆ Finset.univ.sup W :=
    fun W i => Finset.le_sup (f := W) (Finset.mem_univ i)
  ext ω
  constructor
  · rintro ⟨W, hsub, hmem, hdisj⟩
    refine ⟨W 0, Finset.univ.sup (fun i : Fin k => W i.succ), hsub 0, ?_, ?_, hmem 0, ?_⟩
    · intro e he
      obtain ⟨i, -, hi⟩ := Finset.mem_sup.mp he
      exact hsub i.succ hi
    · rw [Finset.disjoint_left]
      intro e he hf
      obtain ⟨i, -, hi⟩ := Finset.mem_sup.mp hf
      exact Finset.disjoint_left.mp (hdisj 0 i.succ (Ne.symm (Fin.succ_ne_zero i))) he hi
    · exact ⟨fun i => W i.succ, fun i => hsup (fun j => W j.succ) i, fun i => hmem i.succ,
        fun i j hij => hdisj i.succ j.succ (fun h => hij (Fin.succ_injective k h))⟩
  · rintro ⟨s, t, hs, ht, hdisj, hmem, hmemt⟩
    obtain ⟨W, hsub, hmemW, hdisjW⟩ := hmemt
    refine ⟨fun i => Fin.cases s W i, ?_, ?_, ?_⟩
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa using hs
      · exact (hsub j).trans ht
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa using hmem
      · simpa using hmemW j
    · intro i j hij
      match i, j with
      | ⟨0, _⟩, ⟨0, _⟩ => exact (hij rfl).elim
      | ⟨0, _⟩, ⟨j' + 1, hj'⟩ =>
          have hj : j' < k := Nat.lt_of_succ_lt_succ hj'
          show Disjoint s (W ⟨j', hj⟩)
          exact Finset.disjoint_left.mpr fun e he hf =>
            Finset.disjoint_left.mp hdisj he (hsub ⟨j', hj⟩ hf)
      | ⟨i' + 1, hi'⟩, ⟨0, _⟩ =>
          have hi : i' < k := Nat.lt_of_succ_lt_succ hi'
          show Disjoint (W ⟨i', hi⟩) s
          exact Finset.disjoint_left.mpr fun e he hf =>
            Finset.disjoint_left.mp hdisj hf (hsub ⟨i', hi⟩ he)
      | ⟨i' + 1, hi'⟩, ⟨j' + 1, hj'⟩ =>
          have hi : i' < k := Nat.lt_of_succ_lt_succ hi'
          have hj : j' < k := Nat.lt_of_succ_lt_succ hj'
          show Disjoint (W ⟨i', hi⟩) (W ⟨j', hj⟩)
          refine hdisjW ⟨i', hi⟩ ⟨j', hj⟩ (fun h => hij ?_)
          have hv : i' = j' := congrArg Fin.val h
          exact Fin.ext (by simp [hv])

/-- **Iterated BK for a `Fin`-indexed family**, edge-dependent parameters. -/
theorem bk_fin [Countable E] (p : E → unitInterval) (hp : ∀ e, p e < 1) {k : ℕ}
    (A : Fin k → Set (Set E)) (hA : ∀ i, IsUpperSet (A i)) (hf : ∀ i, FiniteWitness (A i)) :
    (edgeLaw p).real (DisjointOccurrenceFin A) ≤ ∏ i, (edgeLaw p).real (A i) := by
  induction k with
  | zero =>
    have huniv : DisjointOccurrenceFin A = Set.univ := by
      ext ω
      refine ⟨fun _ => trivial, fun _ => ?_⟩
      exact ⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩
    rw [huniv]
    simp
  | succ k ih =>
    rw [disjointOccurrenceFin_succ_eq]
    have hbound := bkEdge p hp (A 0) (DisjointOccurrenceFin fun i : Fin k => A i.succ)
      (hA 0) (disjointOccurrenceFin_upper _) (hf 0) (disjointOccurrenceFin_finiteWitness _)
    have htail := ih (fun i : Fin k => A i.succ) (fun i => hA i.succ) (fun i => hf i.succ)
    have hprod : (∏ i, (edgeLaw p).real (A i)) =
        (edgeLaw p).real (A 0) * ∏ i : Fin k, (edgeLaw p).real (A i.succ) :=
      Fin.prod_univ_succ _
    rw [hprod]
    exact hbound.trans (mul_le_mul_of_nonneg_left htail measureReal_nonneg)

end Fin

end Percolation

end PercLib.CriticalLRP
