/-
Independently built finite-index BK bridge.  Swarm smwwtd5t5, member m2 (direction B).
Production read only, at HEAD 4c53bb5a8e76a4358a426adf71169b916b90f51f.
-/

/-
# Finite-index BK: the `List` form and the family form are the same event

Production's iterated BK `Percolation.bk_list` is stated for `List (Set (Set E))` with the
*nested* disjoint occurrence `A₀ ∘ (A₁ ∘ (⋯ ∘ Aₙ₋₁))`.  The atlas of Lemma I.4.16 supplies one
witness per atlas edge and needs all of them pairwise disjoint, which is `DisjFam`
(`Defs.lean`).  This file proves that the two formulations agree exactly:

* `disjFam_eq_disjointOccurrenceList_ofFn` :
  `DisjFam A = DisjointOccurrenceList (List.ofFn A)` for `A : Fin n → Set (Set E)`.

The interesting direction is `DisjointOccurrenceList … ⊆ DisjFam A`.  In the nesting at level
`i` the witness `sᵢ ⊆ tᵢ₋₁` is disjoint from `tᵢ`, and every deeper witness `sⱼ` (`j > i`) sits
inside `tᵢ`; hence `sᵢ ⊥ sⱼ` for `i ≠ j`.  So the nesting really does select a pairwise-disjoint
family, and iterated BK applies to the family event without loss.

Nothing here uses finiteness of the edge type `E`: only the *index* `Fin n` is finite.  This is
what lets BK be applied at the atlas edges of one shape in the canonical countable model
`Config V = Set (Sym2 V)`, where `Sym2 V` is infinite; see `Canonical.lean`.
-/

module

public import PercLib.CriticalLRP.BK.FiniteIndex.Defs

/-!
# Finite-index BK
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

open MeasureTheory Measure ProbabilityTheory
open scoped ENNReal

namespace PercLib.CriticalLRP

namespace Percolation

variable {E : Type*}

/-! ## The family form and the `List` form agree -/

/-- Splitting off the first index: a pairwise-disjoint family for `Fin (n+1)` is a witness for
the first event together with the union of the remaining witnesses, which is a witness for the
family of the remaining events. -/
theorem disjFam_succ_subset {n : ℕ} (A : Fin (n + 1) → Set (Set E)) :
    DisjFam A ⊆ DisjointOccurrence (A 0) (DisjFam fun i : Fin n => A i.succ) := by
  classical
  rintro ω ⟨W, hsub, hmem, hdisj⟩
  refine ⟨W 0, Finset.univ.biUnion fun i : Fin n => W i.succ, ?_, ?_, ?_, hmem 0, ?_⟩
  · simpa using hsub 0
  · intro e he
    obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.mp he
    exact hsub i.succ hi
  · rw [Finset.disjoint_biUnion_right]
    intro i _
    exact hdisj 0 i.succ (fun h => Fin.succ_ne_zero i h.symm)
  · refine ⟨fun i => W i.succ, ?_, fun i => hmem i.succ, fun i j hij => ?_⟩
    · intro i e he
      exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, he⟩
    · exact hdisj i.succ j.succ (by simpa using hij)

/-- **The family form implies the `List` form.** -/
theorem disjFam_subset_disjointOccurrenceList_ofFn {n : ℕ} :
    ∀ A : Fin n → Set (Set E),
      DisjFam A ⊆ DisjointOccurrenceList (List.ofFn A) := by
  intro A
  induction n with
  | zero => intro ω _; exact Set.mem_univ ω
  | succ n ih =>
    intro ω hω
    rw [List.ofFn_succ]
    obtain ⟨s, t, hs, ht, hst, hsa, hta⟩ := disjFam_succ_subset A hω
    exact ⟨s, t, hs, ht, hst, hsa, ih (fun i : Fin n => A i.succ) hta⟩

/-- **The `List` form implies the family form.**  The nesting of `DisjointOccurrenceList` selects,
at every level, a witness disjoint from everything below it, so the selected witnesses are
pairwise disjoint. -/
theorem disjointOccurrenceList_subset_disjFam_ofFn {n : ℕ} :
    ∀ A : Fin n → Set (Set E),
      DisjointOccurrenceList (List.ofFn A) ⊆ DisjFam A := by
  intro A
  induction n with
  | zero =>
    intro ω _
    exact ⟨fun i => Fin.elim0 i, fun i => Fin.elim0 i, fun i => Fin.elim0 i,
      fun i => Fin.elim0 i⟩
  | succ n ih =>
    intro ω hω
    rw [List.ofFn_succ] at hω
    obtain ⟨s, t, hs, ht, hst, hsa, hta⟩ := hω
    obtain ⟨W, hWsub, hWmem, hWdisj⟩ := ih (fun i : Fin n => A i.succ) hta
    refine ⟨Fin.cons s W, ?_, ?_, ?_⟩
    · intro i
      induction i using Fin.cases with
      | zero => simpa using hs
      | succ j => simpa using (hWsub j).trans ht
    · intro i
      induction i using Fin.cases with
      | zero => simpa using hsa
      | succ j => simpa using hWmem j
    · intro i j hij
      induction i using Fin.cases with
      | zero =>
        induction j using Fin.cases with
        | zero => exact absurd rfl hij
        | succ l => exact hst.mono_right (Finset.coe_subset.mp (hWsub l))
      | succ k =>
        induction j using Fin.cases with
        | zero => exact (hst.mono_right (Finset.coe_subset.mp (hWsub k))).symm
        | succ l => exact hWdisj k l (fun h => hij (by rw [h]))

/-- **Equality of the family form and the `List` form** (finite index `Fin n`). -/
theorem disjFam_eq_disjointOccurrenceList_ofFn {n : ℕ} (A : Fin n → Set (Set E)) :
    DisjFam A = DisjointOccurrenceList (List.ofFn A) :=
  Set.Subset.antisymm (disjFam_subset_disjointOccurrenceList_ofFn A)
    (disjointOccurrenceList_subset_disjFam_ofFn A)

/-- **Equality of the family form and the `List` form** for an arbitrary finite index type,
along an explicit identification with `Fin n`. -/
theorem disjFam_eq_disjointOccurrenceList_equiv {ι : Type*} {n : ℕ} (e : ι ≃ Fin n)
    (A : ι → Set (Set E)) :
    DisjFam A = DisjointOccurrenceList (List.ofFn fun j : Fin n => A (e.symm j)) := by
  classical
  rw [disjFam_congr e A (fun j : Fin n => A (e.symm j)) (fun i => by simp)]
  exact disjFam_eq_disjointOccurrenceList_ofFn _

/-- **Equality of the family form and the `List` form** for an arbitrary finite index type. -/
theorem disjFam_eq_disjointOccurrenceList {ι : Type*} [Fintype ι] (A : ι → Set (Set E)) :
    DisjFam A = DisjointOccurrenceList
      (List.ofFn fun j : Fin (Fintype.card ι) => A ((Fintype.equivFin ι).symm j)) :=
  disjFam_eq_disjointOccurrenceList_equiv (Fintype.equivFin ι) A

/-! ## BK for the family form on the canonical model -/

variable {V : Type*} [Countable V]

/-- **Iterated BK for a finite-indexed family of events, `Fin n` form, real form.**

The bound is the product of the individual probabilities, over the same finite index.  Only the
index is finite: the edge type `Sym2 V` stays countable and infinite. -/
theorem bk_disjFam_real_fin (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1) {n : ℕ}
    {A : Fin n → Set (Config V)} (hA : ∀ i, IsUpperSet (A i))
    (hf : ∀ i, FiniteWitness (A i)) :
    (edgeMeasure π).real (DisjFam A) ≤ ∏ i, (edgeMeasure π).real (A i) := by
  classical
  have hupper : ∀ B ∈ List.ofFn A, IsUpperSet B := by
    intro B hB
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hB
    exact hA i
  have hfw : ∀ B ∈ List.ofFn A, FiniteWitness B := by
    intro B hB
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hB
    exact hf i
  have h := edgeMeasure_bk_list π hπ (List.ofFn A) hupper hfw
  simp only [List.map_ofFn, List.prod_ofFn] at h
  rwa [disjFam_eq_disjointOccurrenceList_ofFn]

/-- **Iterated BK for a finite-indexed family of events, arbitrary finite index, real form.** -/
theorem bk_disjFam_real (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1) {ι : Type*}
    [Fintype ι] {A : ι → Set (Config V)} (hA : ∀ i, IsUpperSet (A i))
    (hf : ∀ i, FiniteWitness (A i)) :
    (edgeMeasure π).real (DisjFam A) ≤ ∏ i, (edgeMeasure π).real (A i) := by
  classical
  set e := Fintype.equivFin ι
  set B : Fin (Fintype.card ι) → Set (Config V) := fun j => A (e.symm j) with hB
  have hcongr : DisjFam A = DisjFam B :=
    disjFam_congr e A B (fun i => by simp [hB])
  rw [hcongr]
  refine (bk_disjFam_real_fin π hπ (A := B) (fun j => hA _) (fun j => hf _)).trans (le_of_eq ?_)
  exact (Fintype.prod_equiv (M := ℝ) e (fun i => (edgeMeasure π).real (A i))
    (fun j => (edgeMeasure π).real (B j)) (fun i => by simp [hB])).symm

/-- **Iterated BK for a finite-indexed family of events, arbitrary finite index, `ℝ≥0∞` form.**

This is the form used for union bounds: the measure of the disjoint-occurrence event is bounded
by the product of the measures of the single edges, one factor per atlas edge. -/
theorem bk_disjFam (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1) {ι : Type*} [Fintype ι]
    {A : ι → Set (Config V)} (hA : ∀ i, IsUpperSet (A i))
    (hf : ∀ i, FiniteWitness (A i)) :
    edgeMeasure π (DisjFam A) ≤ ∏ i, edgeMeasure π (A i) := by
  classical
  have hreal := bk_disjFam_real π hπ hA hf
  have htop : edgeMeasure π (DisjFam A) ≠ ⊤ := measure_ne_top _ _
  calc edgeMeasure π (DisjFam A)
      = ENNReal.ofReal ((edgeMeasure π).real (DisjFam A)) := by
        rw [measureReal_def, ENNReal.ofReal_toReal htop]
    _ ≤ ENNReal.ofReal (∏ i, (edgeMeasure π).real (A i)) := ENNReal.ofReal_le_ofReal hreal
    _ = ∏ i, ENNReal.ofReal ((edgeMeasure π).real (A i)) := by
        simpa using ENNReal.ofReal_prod_of_nonneg (s := Finset.univ)
          (f := fun i => (edgeMeasure π).real (A i)) (fun i _ => measureReal_nonneg)
    _ = ∏ i, edgeMeasure π (A i) := by
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]

/-- Passing a list product of real measurable values to `ℝ≥0∞` commutes with the product. -/
theorem ofReal_prod_map_real (π : Sym2 V → unitInterval) (As : List (Set (Config V))) :
    ENNReal.ofReal (As.map (fun A => (edgeMeasure π).real A)).prod
      = (As.map fun A => edgeMeasure π A).prod := by
  induction As with
  | nil => simp
  | cons A As ih =>
    simp only [List.map_cons, List.prod_cons]
    have h1 : ENNReal.ofReal ((edgeMeasure π).real A) = edgeMeasure π A := by
      rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]
    rw [ENNReal.ofReal_mul measureReal_nonneg, h1, ih]

/-- **Iterated BK in `ℝ≥0∞` form for the nested (`List`) expression.**  Production's
`edgeMeasure_bk_list` gives the real-valued bound; this is the same bound on the measures
themselves, with the product over the list and no finiteness of the edge type. -/
theorem edgeMeasure_bk_list_ennreal (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1)
    (As : List (Set (Config V))) (hA : ∀ A ∈ As, IsUpperSet A)
    (hf : ∀ A ∈ As, FiniteWitness A) :
    edgeMeasure π (DisjointOccurrenceList As) ≤ (As.map fun A => edgeMeasure π A).prod := by
  have hreal := edgeMeasure_bk_list π hπ As hA hf
  have htop : edgeMeasure π (DisjointOccurrenceList As) ≠ ⊤ := measure_ne_top _ _
  calc edgeMeasure π (DisjointOccurrenceList As)
      = ENNReal.ofReal ((edgeMeasure π).real (DisjointOccurrenceList As)) := by
        rw [measureReal_def, ENNReal.ofReal_toReal htop]
    _ ≤ ENNReal.ofReal ((As.map fun A => (edgeMeasure π).real A).prod) :=
        ENNReal.ofReal_le_ofReal hreal
    _ = (As.map fun A => edgeMeasure π A).prod := ofReal_prod_map_real π As

end Percolation

end PercLib.CriticalLRP
