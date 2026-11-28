/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

The deterministic amalgamation lemma for an arbitrary fixed revealed set, as an instance of
the decision-tree theorem: a tree that queries the revealed set in some order and stops.
-/
module

public import PercLib.CriticalLRP.Correlation.Gladkov.DecisionTree.Main

/-!
# The deterministic case as a decision tree

`listTree L` queries the entries of `L` in order, each with decision `"S"`, and stops. The
entries of a list without repetitions are distinct, so the tree is consistent and
`prodBernoulli_treeFirst_second_indep` applies; its revealed set is `{i | i ∈ L}`. This
recovers `PercLib.GladkovAmalgam.amalgam_indep` for every fixed revealed set, so the
decision-tree theorem is a strict generalisation of the deterministic lemma.
-/

set_option autoImplicit false

@[expose] public section

open MeasureTheory
open PercLib.Probability
open scoped ENNReal

namespace PercLib.GladkovAmalgam

variable {ι : Type*}

/-- The record of a query of the edge `i` with decision `"S"` against the configuration
`ν`. -/
noncomputable def recOf (ν : Set (ι × Bool)) (i : ι) : Rec ι :=
  ⟨i, true, bit ν (i, false), bit ν (i, true)⟩

/-- The tree that queries the entries of `L` in order, all with decision `"S"`, and stops. -/
noncomputable def listTree (L : List ι) : Tree ι :=
  fun τ => (L[τ.length]?).map fun i => (i, true)

theorem listTree_of_getElem? {L : List ι} {τ : List (Rec ι)} {i : ι}
    (h : L[τ.length]? = some i) : listTree L τ = some (i, true) := by
  simp [listTree, h]

theorem listTree_of_le {L : List ι} {τ : List (Rec ι)} (h : L.length ≤ τ.length) :
    listTree L τ = none := by
  simp [listTree, h]

/-- Along its run the tree records exactly the entries of `L` in order. -/
theorem runN_listTree {L : List ι} (ν : Set (ι × Bool)) (n : ℕ) :
    runN (listTree L) ν n = (L.take n).map (recOf ν) := by
  induction n with
  | zero => simp [runN]
  | succ n ih =>
      have hlen : ((L.take n).map (recOf ν)).length = min n L.length := by
        rw [List.length_map, List.length_take]
      rw [runN_succ, ih]
      by_cases hlt : n < L.length
      · have hσ : listTree L ((L.take n).map (recOf ν)) = some (L[n], true) := by
          simp only [listTree, hlen, Nat.min_eq_left (le_of_lt hlt),
            List.getElem?_eq_getElem hlt]
          rfl
        rw [step_of_some hσ]
        have h2 : (L.take (n + 1)).map (recOf ν) =
            (L.take n).map (recOf ν) ++ [recOf ν L[n]] := by
          rw [List.take_add_one, List.getElem?_eq_getElem hlt, List.map_append]
          simp
        rw [h2]
        rfl
      · have hge : L.length ≤ n := Nat.not_lt.1 hlt
        have hσ : listTree L ((L.take n).map (recOf ν)) = none := by
          apply listTree_of_le
          rw [hlen, Nat.min_eq_right hge]
        rw [step_of_none hσ, List.take_of_length_le hge, List.take_of_length_le (by omega)]

theorem trace_listTree [Fintype ι] {L : List ι} (hL : L.Nodup) (ν : Set (ι × Bool)) :
    trace (listTree L) ν = L.map (recOf ν) := by
  have hcard : L.length ≤ Fintype.card ι := List.Nodup.length_le_card hL
  rw [show trace (listTree L) ν = runN (listTree L) ν (Fintype.card ι) from rfl,
    runN_listTree ν, List.take_of_length_le hcard]

theorem treeSet_listTree [Fintype ι] {L : List ι} (hL : L.Nodup) (ν : Set (ι × Bool)) :
    treeSet (listTree L) ν = {i : ι | i ∈ L} := by
  ext i
  rw [treeSet, trace, runN_listTree ν, List.take_of_length_le (List.Nodup.length_le_card hL)]
  simp only [Set.mem_ofPred_eq, List.mem_map]
  constructor
  · rintro ⟨r, ⟨a, ha, rfl⟩, he, -⟩
    exact he ▸ ha
  · intro hi
    exact ⟨recOf ν i, ⟨i, hi, rfl⟩, rfl, rfl⟩

/-- An entry of a list without repetitions is not among the earlier entries. -/
theorem getElem_not_mem_take {L : List ι} (hL : L.Nodup) {n : ℕ} (hn : n < L.length) :
    L[n] ∉ L.take n := by
  intro hmem
  obtain ⟨m, hm, hme⟩ := List.mem_iff_getElem.1 hmem
  have hm' : m < L.length := by
    rw [List.length_take] at hm
    omega
  have h1 : (L.take n)[m] = L[m] := List.getElem_take
  have heq : L[m] = L[n] := by rw [← h1, hme]
  have hmn : m = n := (List.Nodup.getElem_inj hL (i := m) (j := n)).1 heq
  have hmn' : m < n := by
    rw [List.length_take] at hm
    omega
  omega

theorem consistent_listTree {L : List ι} (hL : L.Nodup) : Consistent (listTree L) := by
  intro ν n i c hc r hr
  have hlenq : (runN (listTree L) ν n).length = min n L.length := by
    rw [runN_listTree, List.length_map, List.length_take]
  have hlt' : (runN (listTree L) ν n).length < L.length := by
    by_contra hcon
    rw [listTree_of_le (Nat.not_lt.1 hcon)] at hc
    exact absurd hc (by simp)
  have hlt : n < L.length := by
    rw [hlenq] at hlt'
    omega
  have hinv : runN (listTree L) ν n = (L.take n).map (recOf ν) := runN_listTree ν n
  have hσ : listTree L (runN (listTree L) ν n) = some (L[n], true) := by
    simp only [listTree, hinv, List.length_map, List.length_take,
      Nat.min_eq_left (le_of_lt hlt), List.getElem?_eq_getElem hlt]
    rfl
  rw [hσ] at hc
  simp only [Option.some.injEq, Prod.mk.injEq] at hc
  obtain ⟨rfl, -⟩ := hc
  rw [hinv] at hr
  obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hr
  exact fun he => getElem_not_mem_take hL hlt (he ▸ ha)

theorem treeFirst_listTree [Fintype ι] {L : List ι} (hL : L.Nodup) (ν : Set (ι × Bool)) :
    treeFirst (listTree L) ν = amalFirst {i : ι | i ∈ L} ν := by
  rw [treeFirst, treeSet_listTree hL ν]

theorem treeSecond_listTree [Fintype ι] {L : List ι} (hL : L.Nodup) (ν : Set (ι × Bool)) :
    treeSecond (listTree L) ν = amalSecond {i : ι | i ∈ L} ν := by
  rw [treeSecond, treeSet_listTree hL ν]

set_option linter.unusedFintypeInType false in
/-- The deterministic amalgamation lemma for `{i | i ∈ L}`, as an instance of the
decision-tree theorem. The finiteness hypothesis is used by the proof. -/
theorem prodBernoulli_listTree [Fintype ι] {L : List ι} (hL : L.Nodup)
    (q : ι → unitInterval) (A B : Set (Set ι)) :
    prodBernoulli (twoProfile q) {ω | amalFirst {i : ι | i ∈ L} ω ∈ A ∧
        amalSecond {i : ι | i ∈ L} ω ∈ B} =
      prodBernoulli q A * prodBernoulli q B := by
  have h := prodBernoulli_treeFirst_second_indep q (consistent_listTree hL) A B
  simpa only [treeFirst_listTree hL, treeSecond_listTree hL] using h

set_option linter.unusedFintypeInType false in
/-- **The deterministic amalgamation lemma for an arbitrary fixed revealed set.** This is
`PercLib.GladkovAmalgam.amalgam_indep`, obtained here as an instance of the decision-tree
theorem. The finiteness hypothesis is used by the proof. -/
theorem prodBernoulli_fixedSet [Fintype ι] (q : ι → unitInterval) (T : Set ι)
    (A B : Set (Set ι)) :
    prodBernoulli (twoProfile q) {ω | amalFirst T ω ∈ A ∧ amalSecond T ω ∈ B} =
      prodBernoulli q A * prodBernoulli q B := by
  classical
  have hL : ∀ i : ι, i ∈ T.toFinset.toList ↔ i ∈ T := by
    intro i
    simp
  have h := prodBernoulli_listTree (L := T.toFinset.toList)
    (Finset.nodup_toList T.toFinset) q A B
  have hset : {i : ι | i ∈ T.toFinset.toList} = T := Set.ext hL
  rwa [hset] at h

end PercLib.GladkovAmalgam
