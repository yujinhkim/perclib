/-
Ultramath swarm `smwxenel0`, member `m1`, direction d2 (`TWO-JOINT-MIDDLE-EVALUATION`).

End-to-end: every labelled pattern at the middle split, all free vertices summed, costs
`(E|K|²)²(E|K|)³`.

`pat k` sends comb slots to the five labels, so the five terminal sums appear in the order
fixed by `pat k`.  Each identity below is the event-to-slot bridge composed with the slot
evaluation of `Five.lean`, the only work being the reindexing of the five terminal sums
supplied by `midSlotK2_tsum_root_joint_of_perm` / `midSlotK2_tsum_root_chain_of_perm`.

The label variables are `y, z, w, q, r` in the order of the production `evalFslotU`, and
the terminal vector is `![0, y, z, w, q, r]`, so the root is `T 0 = 0`; `pat_root_slot`
says that every pattern puts the root in comb slot `0` or comb slot `2`, and the two
evaluation theorems correspond to these two cases.
-/
module

public import PercLib.CriticalLRP.Correlation.SixPoint.TwoJointEval.Five

/-!
# All fifteen evaluated middle-split patterns

Only the middle split is evaluated; other splits and the moment assembly remain open.
-/


open Set MeasureTheory
open scoped ENNReal BigOperators
open PercLib.Percolation.Bond
open PercLib.Probability
open PercLib.CriticalLRP.TreeExpansion.FivePoint
open PercLib.CriticalLRP.TreeExpansion.SixPoint

@[expose] public section

namespace PercLib.CriticalLRP.SixPoint.TwoJointEval

variable {V : Type*}

/-- `pat 6` is the identity labelling. -/
theorem pat_six : PercLib.CriticalLRP.TreeExpansion.FivePoint.pat 6 =
    ![0, 1, 2, 3, 4] := by
  rw [← patF_eq]
  rfl

/-- **One fully evaluated middle split.**  For the identity-labelled six-terminal comb
(`k = 6`), split at comb arm `2`: the probability, with the four free vertices
`c, u, v, w` summed and the five non-root terminals `y, z, w, q, r` summed, is at most

$$(\mathbb{E}|K|^2)^2(\mathbb{E}|K|)^3 .$$

No constant, no moment finiteness and no independence assumption is used. -/
theorem sixShape_mid_tsum_le_id [Countable V] [AddCommGroup V]
    (π : Sym2 V → unitInterval)
    (hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y)) :
    (∑' y : V, ∑' z : V, ∑' w : V, ∑' q : V, ∑' r : V,
        law π (⋃ c : V, ⋃ u : V, ⋃ v : V, ⋃ w' : V,
          {ω : PercLib.CriticalLRP.Config V |
            SixShape (openGraph ω) 6 2 c u v w' ![0, y, z, w, q, r]})) ≤
      (secondMoment π 0) ^ 2 * (∑' x, tau π 0 x) ^ 3 := by
  refine (ENNReal.tsum_le_tsum fun y => ENNReal.tsum_le_tsum fun z =>
    ENNReal.tsum_le_tsum fun w => ENNReal.tsum_le_tsum fun q =>
    ENNReal.tsum_le_tsum fun r => sixShape_union_le (V := V) π 6 _).trans_eq ?_
  rw [← patF_eq]
  simp only [patF, lift5, Fin.isValue, Matrix.cons_val]
  exact midSlotK2_tsum_root_joint π hq 0

/-- Pattern `k = 0` (`pat 0 = ![['1', '2', '0', '3', '4']]`) at the middle split
`j = 2`, root on the residual chain (comb slot 2), all free vertices summed. -/
theorem sixShape_mid_tsum_le_pat0 [Countable V] [AddCommGroup V]
    (π : Sym2 V → unitInterval)
    (hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y)) :
    (∑' y : V, ∑' z : V, ∑' w : V, ∑' q : V, ∑' r : V,
        law π (⋃ c : V, ⋃ u : V, ⋃ v : V, ⋃ w' : V,
          {ω : PercLib.CriticalLRP.Config V |
            SixShape (openGraph ω) 0 2 c u v w' ![0, y, z, w, q, r]})) ≤
      (secondMoment π 0) ^ 2 * (∑' x, tau π 0 x) ^ 3 := by
  refine (ENNReal.tsum_le_tsum fun y => ENNReal.tsum_le_tsum fun z =>
    ENNReal.tsum_le_tsum fun w => ENNReal.tsum_le_tsum fun q =>
    ENNReal.tsum_le_tsum fun r => sixShape_union_le (V := V) π 0 _).trans_eq ?_
  rw [← patF_eq]
  simp only [patF, lift5, Fin.isValue, Matrix.cons_val]
  have hperm : (∑' u : Fin 5 → V,
      midSlotK2 π (u 0) (u 1) 0 (u 2) (u 3) (u 4)) =
      (secondMoment π 0) ^ 2 * (∑' x, tau π 0 x) ^ 3 := by
    have h := midSlotK2_tsum_root_chain_of_perm π hq (0 : V)
      (Equiv.ofBijective (![0, 1, 2, 3, 4] : Fin 5 → Fin 5) (by decide) : Equiv.Perm (Fin 5))
    simpa only [Equiv.ofBijective_apply, Fin.isValue, Matrix.cons_val] using h
  rw [tsum_fin5
    (G := fun u : Fin 5 → V => midSlotK2 π (u 0) (u 1) 0 (u 2) (u 3) (u 4))] at hperm
  exact hperm

/-- Pattern `k = 1` (`pat 1 = ![['1', '3', '0', '2', '4']]`) at the middle split
`j = 2`, root on the residual chain (comb slot 2), all free vertices summed. -/
theorem sixShape_mid_tsum_le_pat1 [Countable V] [AddCommGroup V]
    (π : Sym2 V → unitInterval)
    (hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y)) :
    (∑' y : V, ∑' z : V, ∑' w : V, ∑' q : V, ∑' r : V,
        law π (⋃ c : V, ⋃ u : V, ⋃ v : V, ⋃ w' : V,
          {ω : PercLib.CriticalLRP.Config V |
            SixShape (openGraph ω) 1 2 c u v w' ![0, y, z, w, q, r]})) ≤
      (secondMoment π 0) ^ 2 * (∑' x, tau π 0 x) ^ 3 := by
  refine (ENNReal.tsum_le_tsum fun y => ENNReal.tsum_le_tsum fun z =>
    ENNReal.tsum_le_tsum fun w => ENNReal.tsum_le_tsum fun q =>
    ENNReal.tsum_le_tsum fun r => sixShape_union_le (V := V) π 1 _).trans_eq ?_
  rw [← patF_eq]
  simp only [patF, lift5, Fin.isValue, Matrix.cons_val]
  have hperm : (∑' u : Fin 5 → V,
      midSlotK2 π (u 0) (u 2) 0 (u 1) (u 3) (u 4)) =
      (secondMoment π 0) ^ 2 * (∑' x, tau π 0 x) ^ 3 := by
    have h := midSlotK2_tsum_root_chain_of_perm π hq (0 : V)
      (Equiv.ofBijective (![0, 2, 1, 3, 4] : Fin 5 → Fin 5) (by decide) : Equiv.Perm (Fin 5))
    simpa only [Equiv.ofBijective_apply, Fin.isValue, Matrix.cons_val] using h
  rw [tsum_fin5
    (G := fun u : Fin 5 → V => midSlotK2 π (u 0) (u 2) 0 (u 1) (u 3) (u 4))] at hperm
  exact hperm

/-- Pattern `k = 2` (`pat 2 = ![['1', '4', '0', '2', '3']]`) at the middle split
`j = 2`, root on the residual chain (comb slot 2), all free vertices summed. -/
theorem sixShape_mid_tsum_le_pat2 [Countable V] [AddCommGroup V]
    (π : Sym2 V → unitInterval)
    (hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y)) :
    (∑' y : V, ∑' z : V, ∑' w : V, ∑' q : V, ∑' r : V,
        law π (⋃ c : V, ⋃ u : V, ⋃ v : V, ⋃ w' : V,
          {ω : PercLib.CriticalLRP.Config V |
            SixShape (openGraph ω) 2 2 c u v w' ![0, y, z, w, q, r]})) ≤
      (secondMoment π 0) ^ 2 * (∑' x, tau π 0 x) ^ 3 := by
  refine (ENNReal.tsum_le_tsum fun y => ENNReal.tsum_le_tsum fun z =>
    ENNReal.tsum_le_tsum fun w => ENNReal.tsum_le_tsum fun q =>
    ENNReal.tsum_le_tsum fun r => sixShape_union_le (V := V) π 2 _).trans_eq ?_
  rw [← patF_eq]
  simp only [patF, lift5, Fin.isValue, Matrix.cons_val]
  have hperm : (∑' u : Fin 5 → V,
      midSlotK2 π (u 0) (u 3) 0 (u 1) (u 2) (u 4)) =
      (secondMoment π 0) ^ 2 * (∑' x, tau π 0 x) ^ 3 := by
    have h := midSlotK2_tsum_root_chain_of_perm π hq (0 : V)
      (Equiv.ofBijective (![0, 3, 1, 2, 4] : Fin 5 → Fin 5) (by decide) : Equiv.Perm (Fin 5))
    simpa only [Equiv.ofBijective_apply, Fin.isValue, Matrix.cons_val] using h
  rw [tsum_fin5
    (G := fun u : Fin 5 → V => midSlotK2 π (u 0) (u 3) 0 (u 1) (u 2) (u 4))] at hperm
  exact hperm

/-- Pattern `k = 3` (`pat 3 = ![['0', '2', '1', '3', '4']]`) at the middle split
`j = 2`, root on an ear of the first joint pair, all free vertices summed. -/
theorem sixShape_mid_tsum_le_pat3 [Countable V] [AddCommGroup V]
    (π : Sym2 V → unitInterval)
    (hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y)) :
    (∑' y : V, ∑' z : V, ∑' w : V, ∑' q : V, ∑' r : V,
        law π (⋃ c : V, ⋃ u : V, ⋃ v : V, ⋃ w' : V,
          {ω : PercLib.CriticalLRP.Config V |
            SixShape (openGraph ω) 3 2 c u v w' ![0, y, z, w, q, r]})) ≤
      (secondMoment π 0) ^ 2 * (∑' x, tau π 0 x) ^ 3 := by
  refine (ENNReal.tsum_le_tsum fun y => ENNReal.tsum_le_tsum fun z =>
    ENNReal.tsum_le_tsum fun w => ENNReal.tsum_le_tsum fun q =>
    ENNReal.tsum_le_tsum fun r => sixShape_union_le (V := V) π 3 _).trans_eq ?_
  rw [← patF_eq]
  simp only [patF, lift5, Fin.isValue, Matrix.cons_val]
  have hperm : (∑' u : Fin 5 → V,
      midSlotK2 π 0 (u 1) (u 0) (u 2) (u 3) (u 4)) =
      (secondMoment π 0) ^ 2 * (∑' x, tau π 0 x) ^ 3 := by
    have h := midSlotK2_tsum_root_joint_of_perm π hq (0 : V)
      (Equiv.ofBijective (![1, 0, 2, 3, 4] : Fin 5 → Fin 5) (by decide) : Equiv.Perm (Fin 5))
    simpa only [Equiv.ofBijective_apply, Fin.isValue, Matrix.cons_val] using h
  rw [tsum_fin5
    (G := fun u : Fin 5 → V => midSlotK2 π 0 (u 1) (u 0) (u 2) (u 3) (u 4))] at hperm
  exact hperm

/-- Pattern `k = 4` (`pat 4 = ![['0', '3', '1', '2', '4']]`) at the middle split
`j = 2`, root on an ear of the first joint pair, all free vertices summed. -/
theorem sixShape_mid_tsum_le_pat4 [Countable V] [AddCommGroup V]
    (π : Sym2 V → unitInterval)
    (hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y)) :
    (∑' y : V, ∑' z : V, ∑' w : V, ∑' q : V, ∑' r : V,
        law π (⋃ c : V, ⋃ u : V, ⋃ v : V, ⋃ w' : V,
          {ω : PercLib.CriticalLRP.Config V |
            SixShape (openGraph ω) 4 2 c u v w' ![0, y, z, w, q, r]})) ≤
      (secondMoment π 0) ^ 2 * (∑' x, tau π 0 x) ^ 3 := by
  refine (ENNReal.tsum_le_tsum fun y => ENNReal.tsum_le_tsum fun z =>
    ENNReal.tsum_le_tsum fun w => ENNReal.tsum_le_tsum fun q =>
    ENNReal.tsum_le_tsum fun r => sixShape_union_le (V := V) π 4 _).trans_eq ?_
  rw [← patF_eq]
  simp only [patF, lift5, Fin.isValue, Matrix.cons_val]
  have hperm : (∑' u : Fin 5 → V,
      midSlotK2 π 0 (u 2) (u 0) (u 1) (u 3) (u 4)) =
      (secondMoment π 0) ^ 2 * (∑' x, tau π 0 x) ^ 3 := by
    have h := midSlotK2_tsum_root_joint_of_perm π hq (0 : V)
      (Equiv.ofBijective (![2, 0, 1, 3, 4] : Fin 5 → Fin 5) (by decide) : Equiv.Perm (Fin 5))
    simpa only [Equiv.ofBijective_apply, Fin.isValue, Matrix.cons_val] using h
  rw [tsum_fin5
    (G := fun u : Fin 5 → V => midSlotK2 π 0 (u 2) (u 0) (u 1) (u 3) (u 4))] at hperm
  exact hperm

/-- Pattern `k = 5` (`pat 5 = ![['0', '4', '1', '2', '3']]`) at the middle split
`j = 2`, root on an ear of the first joint pair, all free vertices summed. -/
theorem sixShape_mid_tsum_le_pat5 [Countable V] [AddCommGroup V]
    (π : Sym2 V → unitInterval)
    (hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y)) :
    (∑' y : V, ∑' z : V, ∑' w : V, ∑' q : V, ∑' r : V,
        law π (⋃ c : V, ⋃ u : V, ⋃ v : V, ⋃ w' : V,
          {ω : PercLib.CriticalLRP.Config V |
            SixShape (openGraph ω) 5 2 c u v w' ![0, y, z, w, q, r]})) ≤
      (secondMoment π 0) ^ 2 * (∑' x, tau π 0 x) ^ 3 := by
  refine (ENNReal.tsum_le_tsum fun y => ENNReal.tsum_le_tsum fun z =>
    ENNReal.tsum_le_tsum fun w => ENNReal.tsum_le_tsum fun q =>
    ENNReal.tsum_le_tsum fun r => sixShape_union_le (V := V) π 5 _).trans_eq ?_
  rw [← patF_eq]
  simp only [patF, lift5, Fin.isValue, Matrix.cons_val]
  have hperm : (∑' u : Fin 5 → V,
      midSlotK2 π 0 (u 3) (u 0) (u 1) (u 2) (u 4)) =
      (secondMoment π 0) ^ 2 * (∑' x, tau π 0 x) ^ 3 := by
    have h := midSlotK2_tsum_root_joint_of_perm π hq (0 : V)
      (Equiv.ofBijective (![3, 0, 1, 2, 4] : Fin 5 → Fin 5) (by decide) : Equiv.Perm (Fin 5))
    simpa only [Equiv.ofBijective_apply, Fin.isValue, Matrix.cons_val] using h
  rw [tsum_fin5
    (G := fun u : Fin 5 → V => midSlotK2 π 0 (u 3) (u 0) (u 1) (u 2) (u 4))] at hperm
  exact hperm

/-- Pattern `k = 7` (`pat 7 = ![['0', '3', '2', '1', '4']]`) at the middle split
`j = 2`, root on an ear of the first joint pair, all free vertices summed. -/
theorem sixShape_mid_tsum_le_pat7 [Countable V] [AddCommGroup V]
    (π : Sym2 V → unitInterval)
    (hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y)) :
    (∑' y : V, ∑' z : V, ∑' w : V, ∑' q : V, ∑' r : V,
        law π (⋃ c : V, ⋃ u : V, ⋃ v : V, ⋃ w' : V,
          {ω : PercLib.CriticalLRP.Config V |
            SixShape (openGraph ω) 7 2 c u v w' ![0, y, z, w, q, r]})) ≤
      (secondMoment π 0) ^ 2 * (∑' x, tau π 0 x) ^ 3 := by
  refine (ENNReal.tsum_le_tsum fun y => ENNReal.tsum_le_tsum fun z =>
    ENNReal.tsum_le_tsum fun w => ENNReal.tsum_le_tsum fun q =>
    ENNReal.tsum_le_tsum fun r => sixShape_union_le (V := V) π 7 _).trans_eq ?_
  rw [← patF_eq]
  simp only [patF, lift5, Fin.isValue, Matrix.cons_val]
  have hperm : (∑' u : Fin 5 → V,
      midSlotK2 π 0 (u 2) (u 1) (u 0) (u 3) (u 4)) =
      (secondMoment π 0) ^ 2 * (∑' x, tau π 0 x) ^ 3 := by
    have h := midSlotK2_tsum_root_joint_of_perm π hq (0 : V)
      (Equiv.ofBijective (![2, 1, 0, 3, 4] : Fin 5 → Fin 5) (by decide) : Equiv.Perm (Fin 5))
    simpa only [Equiv.ofBijective_apply, Fin.isValue, Matrix.cons_val] using h
  rw [tsum_fin5
    (G := fun u : Fin 5 → V => midSlotK2 π 0 (u 2) (u 1) (u 0) (u 3) (u 4))] at hperm
  exact hperm

/-- Pattern `k = 8` (`pat 8 = ![['0', '4', '2', '1', '3']]`) at the middle split
`j = 2`, root on an ear of the first joint pair, all free vertices summed. -/
theorem sixShape_mid_tsum_le_pat8 [Countable V] [AddCommGroup V]
    (π : Sym2 V → unitInterval)
    (hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y)) :
    (∑' y : V, ∑' z : V, ∑' w : V, ∑' q : V, ∑' r : V,
        law π (⋃ c : V, ⋃ u : V, ⋃ v : V, ⋃ w' : V,
          {ω : PercLib.CriticalLRP.Config V |
            SixShape (openGraph ω) 8 2 c u v w' ![0, y, z, w, q, r]})) ≤
      (secondMoment π 0) ^ 2 * (∑' x, tau π 0 x) ^ 3 := by
  refine (ENNReal.tsum_le_tsum fun y => ENNReal.tsum_le_tsum fun z =>
    ENNReal.tsum_le_tsum fun w => ENNReal.tsum_le_tsum fun q =>
    ENNReal.tsum_le_tsum fun r => sixShape_union_le (V := V) π 8 _).trans_eq ?_
  rw [← patF_eq]
  simp only [patF, lift5, Fin.isValue, Matrix.cons_val]
  have hperm : (∑' u : Fin 5 → V,
      midSlotK2 π 0 (u 3) (u 1) (u 0) (u 2) (u 4)) =
      (secondMoment π 0) ^ 2 * (∑' x, tau π 0 x) ^ 3 := by
    have h := midSlotK2_tsum_root_joint_of_perm π hq (0 : V)
      (Equiv.ofBijective (![3, 1, 0, 2, 4] : Fin 5 → Fin 5) (by decide) : Equiv.Perm (Fin 5))
    simpa only [Equiv.ofBijective_apply, Fin.isValue, Matrix.cons_val] using h
  rw [tsum_fin5
    (G := fun u : Fin 5 → V => midSlotK2 π 0 (u 3) (u 1) (u 0) (u 2) (u 4))] at hperm
  exact hperm

/-- Pattern `k = 9` (`pat 9 = ![['0', '1', '3', '2', '4']]`) at the middle split
`j = 2`, root on an ear of the first joint pair, all free vertices summed. -/
theorem sixShape_mid_tsum_le_pat9 [Countable V] [AddCommGroup V]
    (π : Sym2 V → unitInterval)
    (hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y)) :
    (∑' y : V, ∑' z : V, ∑' w : V, ∑' q : V, ∑' r : V,
        law π (⋃ c : V, ⋃ u : V, ⋃ v : V, ⋃ w' : V,
          {ω : PercLib.CriticalLRP.Config V |
            SixShape (openGraph ω) 9 2 c u v w' ![0, y, z, w, q, r]})) ≤
      (secondMoment π 0) ^ 2 * (∑' x, tau π 0 x) ^ 3 := by
  refine (ENNReal.tsum_le_tsum fun y => ENNReal.tsum_le_tsum fun z =>
    ENNReal.tsum_le_tsum fun w => ENNReal.tsum_le_tsum fun q =>
    ENNReal.tsum_le_tsum fun r => sixShape_union_le (V := V) π 9 _).trans_eq ?_
  rw [← patF_eq]
  simp only [patF, lift5, Fin.isValue, Matrix.cons_val]
  have hperm : (∑' u : Fin 5 → V,
      midSlotK2 π 0 (u 0) (u 2) (u 1) (u 3) (u 4)) =
      (secondMoment π 0) ^ 2 * (∑' x, tau π 0 x) ^ 3 := by
    have h := midSlotK2_tsum_root_joint_of_perm π hq (0 : V)
      (Equiv.ofBijective (![0, 2, 1, 3, 4] : Fin 5 → Fin 5) (by decide) : Equiv.Perm (Fin 5))
    simpa only [Equiv.ofBijective_apply, Fin.isValue, Matrix.cons_val] using h
  rw [tsum_fin5
    (G := fun u : Fin 5 → V => midSlotK2 π 0 (u 0) (u 2) (u 1) (u 3) (u 4))] at hperm
  exact hperm

/-- Pattern `k = 10` (`pat 10 = ![['0', '2', '3', '1', '4']]`) at the middle split
`j = 2`, root on an ear of the first joint pair, all free vertices summed. -/
theorem sixShape_mid_tsum_le_pat10 [Countable V] [AddCommGroup V]
    (π : Sym2 V → unitInterval)
    (hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y)) :
    (∑' y : V, ∑' z : V, ∑' w : V, ∑' q : V, ∑' r : V,
        law π (⋃ c : V, ⋃ u : V, ⋃ v : V, ⋃ w' : V,
          {ω : PercLib.CriticalLRP.Config V |
            SixShape (openGraph ω) 10 2 c u v w' ![0, y, z, w, q, r]})) ≤
      (secondMoment π 0) ^ 2 * (∑' x, tau π 0 x) ^ 3 := by
  refine (ENNReal.tsum_le_tsum fun y => ENNReal.tsum_le_tsum fun z =>
    ENNReal.tsum_le_tsum fun w => ENNReal.tsum_le_tsum fun q =>
    ENNReal.tsum_le_tsum fun r => sixShape_union_le (V := V) π 10 _).trans_eq ?_
  rw [← patF_eq]
  simp only [patF, lift5, Fin.isValue, Matrix.cons_val]
  have hperm : (∑' u : Fin 5 → V,
      midSlotK2 π 0 (u 1) (u 2) (u 0) (u 3) (u 4)) =
      (secondMoment π 0) ^ 2 * (∑' x, tau π 0 x) ^ 3 := by
    have h := midSlotK2_tsum_root_joint_of_perm π hq (0 : V)
      (Equiv.ofBijective (![1, 2, 0, 3, 4] : Fin 5 → Fin 5) (by decide) : Equiv.Perm (Fin 5))
    simpa only [Equiv.ofBijective_apply, Fin.isValue, Matrix.cons_val] using h
  rw [tsum_fin5
    (G := fun u : Fin 5 → V => midSlotK2 π 0 (u 1) (u 2) (u 0) (u 3) (u 4))] at hperm
  exact hperm

/-- Pattern `k = 11` (`pat 11 = ![['0', '4', '3', '1', '2']]`) at the middle split
`j = 2`, root on an ear of the first joint pair, all free vertices summed. -/
theorem sixShape_mid_tsum_le_pat11 [Countable V] [AddCommGroup V]
    (π : Sym2 V → unitInterval)
    (hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y)) :
    (∑' y : V, ∑' z : V, ∑' w : V, ∑' q : V, ∑' r : V,
        law π (⋃ c : V, ⋃ u : V, ⋃ v : V, ⋃ w' : V,
          {ω : PercLib.CriticalLRP.Config V |
            SixShape (openGraph ω) 11 2 c u v w' ![0, y, z, w, q, r]})) ≤
      (secondMoment π 0) ^ 2 * (∑' x, tau π 0 x) ^ 3 := by
  refine (ENNReal.tsum_le_tsum fun y => ENNReal.tsum_le_tsum fun z =>
    ENNReal.tsum_le_tsum fun w => ENNReal.tsum_le_tsum fun q =>
    ENNReal.tsum_le_tsum fun r => sixShape_union_le (V := V) π 11 _).trans_eq ?_
  rw [← patF_eq]
  simp only [patF, lift5, Fin.isValue, Matrix.cons_val]
  have hperm : (∑' u : Fin 5 → V,
      midSlotK2 π 0 (u 3) (u 2) (u 0) (u 1) (u 4)) =
      (secondMoment π 0) ^ 2 * (∑' x, tau π 0 x) ^ 3 := by
    have h := midSlotK2_tsum_root_joint_of_perm π hq (0 : V)
      (Equiv.ofBijective (![3, 2, 0, 1, 4] : Fin 5 → Fin 5) (by decide) : Equiv.Perm (Fin 5))
    simpa only [Equiv.ofBijective_apply, Fin.isValue, Matrix.cons_val] using h
  rw [tsum_fin5
    (G := fun u : Fin 5 → V => midSlotK2 π 0 (u 3) (u 2) (u 0) (u 1) (u 4))] at hperm
  exact hperm

/-- Pattern `k = 12` (`pat 12 = ![['0', '1', '4', '2', '3']]`) at the middle split
`j = 2`, root on an ear of the first joint pair, all free vertices summed. -/
theorem sixShape_mid_tsum_le_pat12 [Countable V] [AddCommGroup V]
    (π : Sym2 V → unitInterval)
    (hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y)) :
    (∑' y : V, ∑' z : V, ∑' w : V, ∑' q : V, ∑' r : V,
        law π (⋃ c : V, ⋃ u : V, ⋃ v : V, ⋃ w' : V,
          {ω : PercLib.CriticalLRP.Config V |
            SixShape (openGraph ω) 12 2 c u v w' ![0, y, z, w, q, r]})) ≤
      (secondMoment π 0) ^ 2 * (∑' x, tau π 0 x) ^ 3 := by
  refine (ENNReal.tsum_le_tsum fun y => ENNReal.tsum_le_tsum fun z =>
    ENNReal.tsum_le_tsum fun w => ENNReal.tsum_le_tsum fun q =>
    ENNReal.tsum_le_tsum fun r => sixShape_union_le (V := V) π 12 _).trans_eq ?_
  rw [← patF_eq]
  simp only [patF, lift5, Fin.isValue, Matrix.cons_val]
  have hperm : (∑' u : Fin 5 → V,
      midSlotK2 π 0 (u 0) (u 3) (u 1) (u 2) (u 4)) =
      (secondMoment π 0) ^ 2 * (∑' x, tau π 0 x) ^ 3 := by
    have h := midSlotK2_tsum_root_joint_of_perm π hq (0 : V)
      (Equiv.ofBijective (![0, 3, 1, 2, 4] : Fin 5 → Fin 5) (by decide) : Equiv.Perm (Fin 5))
    simpa only [Equiv.ofBijective_apply, Fin.isValue, Matrix.cons_val] using h
  rw [tsum_fin5
    (G := fun u : Fin 5 → V => midSlotK2 π 0 (u 0) (u 3) (u 1) (u 2) (u 4))] at hperm
  exact hperm

/-- Pattern `k = 13` (`pat 13 = ![['0', '2', '4', '1', '3']]`) at the middle split
`j = 2`, root on an ear of the first joint pair, all free vertices summed. -/
theorem sixShape_mid_tsum_le_pat13 [Countable V] [AddCommGroup V]
    (π : Sym2 V → unitInterval)
    (hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y)) :
    (∑' y : V, ∑' z : V, ∑' w : V, ∑' q : V, ∑' r : V,
        law π (⋃ c : V, ⋃ u : V, ⋃ v : V, ⋃ w' : V,
          {ω : PercLib.CriticalLRP.Config V |
            SixShape (openGraph ω) 13 2 c u v w' ![0, y, z, w, q, r]})) ≤
      (secondMoment π 0) ^ 2 * (∑' x, tau π 0 x) ^ 3 := by
  refine (ENNReal.tsum_le_tsum fun y => ENNReal.tsum_le_tsum fun z =>
    ENNReal.tsum_le_tsum fun w => ENNReal.tsum_le_tsum fun q =>
    ENNReal.tsum_le_tsum fun r => sixShape_union_le (V := V) π 13 _).trans_eq ?_
  rw [← patF_eq]
  simp only [patF, lift5, Fin.isValue, Matrix.cons_val]
  have hperm : (∑' u : Fin 5 → V,
      midSlotK2 π 0 (u 1) (u 3) (u 0) (u 2) (u 4)) =
      (secondMoment π 0) ^ 2 * (∑' x, tau π 0 x) ^ 3 := by
    have h := midSlotK2_tsum_root_joint_of_perm π hq (0 : V)
      (Equiv.ofBijective (![1, 3, 0, 2, 4] : Fin 5 → Fin 5) (by decide) : Equiv.Perm (Fin 5))
    simpa only [Equiv.ofBijective_apply, Fin.isValue, Matrix.cons_val] using h
  rw [tsum_fin5
    (G := fun u : Fin 5 → V => midSlotK2 π 0 (u 1) (u 3) (u 0) (u 2) (u 4))] at hperm
  exact hperm

/-- Pattern `k = 14` (`pat 14 = ![['0', '3', '4', '1', '2']]`) at the middle split
`j = 2`, root on an ear of the first joint pair, all free vertices summed. -/
theorem sixShape_mid_tsum_le_pat14 [Countable V] [AddCommGroup V]
    (π : Sym2 V → unitInterval)
    (hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y)) :
    (∑' y : V, ∑' z : V, ∑' w : V, ∑' q : V, ∑' r : V,
        law π (⋃ c : V, ⋃ u : V, ⋃ v : V, ⋃ w' : V,
          {ω : PercLib.CriticalLRP.Config V |
            SixShape (openGraph ω) 14 2 c u v w' ![0, y, z, w, q, r]})) ≤
      (secondMoment π 0) ^ 2 * (∑' x, tau π 0 x) ^ 3 := by
  refine (ENNReal.tsum_le_tsum fun y => ENNReal.tsum_le_tsum fun z =>
    ENNReal.tsum_le_tsum fun w => ENNReal.tsum_le_tsum fun q =>
    ENNReal.tsum_le_tsum fun r => sixShape_union_le (V := V) π 14 _).trans_eq ?_
  rw [← patF_eq]
  simp only [patF, lift5, Fin.isValue, Matrix.cons_val]
  have hperm : (∑' u : Fin 5 → V,
      midSlotK2 π 0 (u 2) (u 3) (u 0) (u 1) (u 4)) =
      (secondMoment π 0) ^ 2 * (∑' x, tau π 0 x) ^ 3 := by
    have h := midSlotK2_tsum_root_joint_of_perm π hq (0 : V)
      (Equiv.ofBijective (![2, 3, 0, 1, 4] : Fin 5 → Fin 5) (by decide) : Equiv.Perm (Fin 5))
    simpa only [Equiv.ofBijective_apply, Fin.isValue, Matrix.cons_val] using h
  rw [tsum_fin5
    (G := fun u : Fin 5 → V => midSlotK2 π 0 (u 2) (u 3) (u 0) (u 1) (u 4))] at hperm
  exact hperm

end PercLib.CriticalLRP.SixPoint.TwoJointEval
