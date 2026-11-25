/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

module

public import PercLib.CriticalLRP.TreeExpansion.SpatialTreeGraph
public import PercLib.CriticalLRP.TreeExpansion.TreeSumRecursionFull

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

set_option autoImplicit true

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section

namespace PercLib.CriticalLRP.TreeExpansion

open Finset
open PercLib.CriticalLRP.TreeGraph PercLib.CriticalLRP

variable {V : Type*} [AddCommGroup V] [Fintype V] [DecidableEq V]
variable {E : Type*} [Fintype E] [DecidableEq E]

/-! ## 0. The vacuity lemma -/

/-- Every additive functional from a finite abelian group to the reals is zero. -/
theorem addMonoidHom_eq_zero_of_finite (φ : V →+ ℝ) : φ = 0 := by
  ext v
  have hV : IsAddTorsion V := isAddTorsion_of_finite
  obtain ⟨n, hn0, hnv⟩ := (hV v).exists_nsmul_eq_zero
  have h1 : n • φ v = 0 := by rw [← map_nsmul, hnv, map_zero]
  have h2 : (n : ℝ) * φ v = 0 := by simpa [nsmul_eq_mul] using h1
  exact (mul_eq_zero.mp h2).resolve_left (by exact_mod_cast hn0.ne')

theorem abs_apply_rpow_eq_zero (φ : V →+ ℝ) {p : ℝ} (hp : 0 < p) (y : V) :
    |φ y| ^ p = 0 := by
  rw [addMonoidHom_eq_zero_of_finite φ]
  simp [Real.zero_rpow hp.ne']

theorem abs_apply_rpow_zero (φ : V →+ ℝ) (y : V) : |φ y| ^ (0 : ℝ) = 1 := by
  simp

/-! ## 1. The unmarked tree-sum evaluation (`p = 0`) -/

/-- **The unmarked tree-sum evaluation**, in the form needed at `p = 0`:
`∑_x treeSum k n o x ≤ (2n-3)!! (E|K|)^{2n-1}`.  Every rooted tree with `n` labelled leaves
contributes exactly `S^{2n-1}` (`RTree.sum_wt_labelled`), and the number of non-plane trees
is at most `(2n-3)!!` (`RTree.card_LT_fin_le`). -/
theorem sum_treeSum_le (pr : E → ℝ) (hp : ∀ e, 0 ≤ pr e) (hp1 : ∀ e, pr e ≤ 1)
    (ends : E → Sym2 V) (o : V)
    (hinv : ∀ a b : V, twoPoint pr ends a b = twoPoint pr ends o (b - a)) {n : ℕ} (hn : 1 ≤ n) :
    (∑ x : Fin n → V, treeSum (twoPoint pr ends) n o x)
      ≤ (VolumeMoments.M (n - 1) : ℝ) * (clusterVolume pr ends o) ^ (2 * n - 1) := by
  classical
  set S : ℝ := clusterVolume pr ends o with hSdef
  have hS0 : 0 ≤ S := by
    rw [hSdef, clusterVolume]
    exact Finset.sum_nonneg fun y _ => twoPoint_nonneg hp hp1 ends o y
  have hS : ∀ v : V, ∑ y : V, twoPoint pr ends v y = S :=
    fun v => twoPoint_total_eq pr ends o hinv v
  have ht : ∀ t : RTree.LT (Fin n),
      (∑ x : Fin n → V, RTree.wt (twoPoint pr ends) t.val
        (fun r => x (RTree.leafOfPos t.val r)) o) = S ^ (2 * n - 1) :=
    fun t => RTree.sum_wt_labelled (twoPoint pr ends) S hS t.2 o
  have hmain : (∑ x : Fin n → V, treeSum (twoPoint pr ends) n o x)
      = (1 / 2 ^ (n - 1)) * ((Fintype.card (RTree.LT (Fin n)) : ℝ) * S ^ (2 * n - 1)) := by
    simp only [treeSum]
    calc ∑ x : Fin n → V, (1 / 2 ^ (n - 1)) *
          ∑ t : RTree.LT (Fin n),
            RTree.wt (twoPoint pr ends) t.val (fun q => x (RTree.leafOfPos t.val q)) o
        = (1 / 2 ^ (n - 1)) * ∑ x : Fin n → V, ∑ t : RTree.LT (Fin n),
            RTree.wt (twoPoint pr ends) t.val (fun q => x (RTree.leafOfPos t.val q)) o :=
          (Finset.mul_sum _ _ _).symm
      _ = (1 / 2 ^ (n - 1)) * ∑ t : RTree.LT (Fin n), ∑ x : Fin n → V,
            RTree.wt (twoPoint pr ends) t.val (fun q => x (RTree.leafOfPos t.val q)) o := by
          rw [Finset.sum_comm]
      _ = (1 / 2 ^ (n - 1)) * ∑ _t : RTree.LT (Fin n), S ^ (2 * n - 1) := by
          rw [Finset.sum_congr rfl fun t _ => ht t]
      _ = (1 / 2 ^ (n - 1)) * ((Fintype.card (RTree.LT (Fin n)) : ℝ) * S ^ (2 * n - 1)) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [hmain]
  have hcard : (Fintype.card (RTree.LT (Fin n)) : ℝ)
      ≤ (2 : ℝ) ^ (n - 1) * (VolumeMoments.M (n - 1) : ℝ) := by
    have h := RTree.card_LT_fin_le n
    have h' : ((Fintype.card (RTree.LT (Fin n)) : ℝ)
        ≤ ((2 ^ (n - 1) * VolumeMoments.M (n - 1) : ℕ) : ℝ)) := by exact_mod_cast h
    rwa [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] at h'
  have hpow : (0 : ℝ) ≤ S ^ (2 * n - 1) := pow_nonneg hS0 _
  have hc : (0 : ℝ) ≤ 1 / 2 ^ (n - 1) := by positivity
  calc (1 / 2 ^ (n - 1)) * ((Fintype.card (RTree.LT (Fin n)) : ℝ) * S ^ (2 * n - 1))
      ≤ (1 / 2 ^ (n - 1)) *
          (((2 : ℝ) ^ (n - 1) * (VolumeMoments.M (n - 1) : ℝ)) * S ^ (2 * n - 1)) := by
        refine mul_le_mul_of_nonneg_left ?_ hc
        exact mul_le_mul_of_nonneg_right hcard hpow
    _ = (VolumeMoments.M (n - 1) : ℝ) * S ^ (2 * n - 1) := by
        field_simp

/-! ## 2. `WeightedTreeSum` is true for `0 ≤ pr ≤ 1` — but vacuously so for `p > 0` -/

/-- **`WeightedTreeSum` holds unconditionally (for probabilities in `[0,1]`).**

For `p > 0` both sides vanish, because `φ ≡ 0` on a finite abelian group
(`addMonoidHom_eq_zero_of_finite`); for `p = 0` the weight is `|φ|^0 = 1` and the claim is
exactly the unmarked tree-sum evaluation `sum_treeSum_le`, with the constant `n^{max(0,1)} = n`
providing the factor `S^{2n-2}·S = S^{2n-1}`.

`0 ≤ pr`, `pr ≤ 1` are needed only in the `p = 0` case (they give `clusterVolume ≥ 0`); without
them the statement is false, see `docs`/report. -/
theorem weightedTreeSum_of_finite (pr : E → ℝ) (hpr0 : ∀ e, 0 ≤ pr e) (hpr1 : ∀ e, pr e ≤ 1)
    (ends : E → Sym2 V) (o : V) : WeightedTreeSum pr ends o := by
  intro n hn i₀ φ p hp hinv
  rcases eq_or_lt_of_le hp with hp0 | hppos
  · rw [← hp0]
    simp only [abs_apply_rpow_zero, one_mul]
    have hmax : max (0 : ℝ) 1 = 1 := max_eq_right zero_le_one
    rw [hmax, Real.rpow_one]
    have hS0 : 0 ≤ clusterVolume pr ends o :=
      Finset.sum_nonneg fun y _ => twoPoint_nonneg hpr0 hpr1 ends o y
    have hSpow : (clusterVolume pr ends o) ^ (2 * n - 2) * (∑ y : V, twoPoint pr ends o y)
        = (clusterVolume pr ends o) ^ (2 * n - 1) := by
      have hS' : (∑ y : V, twoPoint pr ends o y) = clusterVolume pr ends o := rfl
      rw [hS', ← pow_succ]
      congr 1
      omega
    rw [mul_assoc, hSpow]
    have h1 := sum_treeSum_le pr hpr0 hpr1 ends o hinv hn
    refine h1.trans ?_
    have hstep : (VolumeMoments.M (n - 1) : ℝ) ≤ (VolumeMoments.M (n - 1) : ℝ) * (n : ℝ) := by
      have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      have hM0 : (0 : ℝ) ≤ (VolumeMoments.M (n - 1) : ℝ) := Nat.cast_nonneg _
      nlinarith
    exact mul_le_mul_of_nonneg_right hstep (pow_nonneg hS0 _)
  · have hzero : ∀ y : V, |φ y| ^ p = 0 := fun y => abs_apply_rpow_eq_zero φ hppos y
    have hL : (∑ x : Fin n → V, |φ (x i₀)| ^ p * treeSum (twoPoint pr ends) n o x) = 0 := by
      simp [hzero]
    have hR : (∑ y : V, |φ y| ^ p * twoPoint pr ends o y) = 0 := by simp [hzero]
    rw [hL, hR, mul_zero]

/-- **The spatially weighted tree-graph inequality (Lemma I.5.9, finite model) with the
tree-sum input discharged.**  Same statement as `spatial_tree_graph_of_inputs`, but with no
`hW` hypothesis.  Note that this statement is only non-trivial through its additive
functionals `Φ i`: on a *finite* abelian `V` every `Φ i` is zero, so the left-hand side
vanishes whenever `∑ q > 0`.  See the report for the honest repair. -/
theorem spatial_tree_graph_of_finite (pr : E → ℝ) (hp : ∀ e, 0 ≤ pr e) (hp1 : ∀ e, pr e ≤ 1)
    (ends : E → Sym2 V) (o : V) (hTG : TreeGraphBound pr ends (twoPoint pr ends))
    (hinv : ∀ a b : V, twoPoint pr ends a b = twoPoint pr ends o (b - a))
    {n : ℕ} (hn : 1 ≤ n) (q : Fin n → ℝ) (Φ : Fin n → V →+ ℝ) (M : ℝ)
    (hq : ∀ i, 0 ≤ q i) (hP : 0 < ∑ i, q i)
    (hM : ∀ i, ∑ y : V, |Φ i y| ^ (∑ j, q j) * twoPoint pr ends o y ≤ M) :
    expectReal pr (fun s => tupleSum (clusterF ends s o) n (fun x => ∏ i, |Φ i (x i)| ^ q i))
      ≤ (VolumeMoments.M (n - 1) : ℝ) * (n : ℝ) ^ (max (∑ i, q i) 1) *
          (clusterVolume pr ends o) ^ (2 * n - 2) * M :=
  spatial_tree_graph_of_inputs pr hp hp1 ends o hTG
    (weightedTreeSum_of_finite pr hp hp1 ends o) hinv hn q Φ M hq hP hM

/-- The same in the source's printed shape. -/
theorem spatial_tree_graph_printed_of_finite (pr : E → ℝ) (hp : ∀ e, 0 ≤ pr e)
    (hp1 : ∀ e, pr e ≤ 1) (ends : E → Sym2 V) (o : V)
    (hTG : TreeGraphBound pr ends (twoPoint pr ends))
    (hinv : ∀ a b : V, twoPoint pr ends a b = twoPoint pr ends o (b - a))
    {n : ℕ} (hn : 1 ≤ n) (q : Fin n → ℝ) (Φ : Fin n → V →+ ℝ) (M : ℝ)
    (hq : ∀ i, 0 ≤ q i) (hP : 0 < ∑ i, q i)
    (hM : ∀ i, expectReal pr (fun s => ((clusterF ends s o).card : ℝ) ^ (n - 1) *
            ∑ y ∈ clusterF ends s o, |Φ i y| ^ (∑ j, q j)) ≤ M) :
    expectReal pr (fun s => tupleSum (clusterF ends s o) n (fun x => ∏ i, |Φ i (x i)| ^ q i))
      ≤ (VolumeMoments.M (n - 1) : ℝ) * (n : ℝ) ^ (max (∑ i, q i) 1) *
          (clusterVolume pr ends o) ^ (2 * n - 2) * M :=
  spatial_tree_graph_printed pr hp hp1 ends o hTG
    (weightedTreeSum_of_finite pr hp hp1 ends o) hinv hn q Φ M hq hP hM

/-- **Lemma I.5.9 (finite model) from the BK inequality alone**: both remaining inputs,
`TreeGraphBound` (via `treeGraphBound_of_bk'`) and `WeightedTreeSum` (via
`weightedTreeSum_of_finite`), are discharged. -/
theorem spatial_tree_graph_of_bk (pr : E → ℝ) (hp : ∀ e, 0 ≤ pr e) (hp1 : ∀ e, pr e ≤ 1)
    (ends : E → Sym2 V) (o : V) (hBK : BKIncreasing pr)
    (hinv : ∀ a b : V, twoPoint pr ends a b = twoPoint pr ends o (b - a))
    {n : ℕ} (hn : 1 ≤ n) (q : Fin n → ℝ) (Φ : Fin n → V →+ ℝ) (M : ℝ)
    (hq : ∀ i, 0 ≤ q i) (hP : 0 < ∑ i, q i)
    (hM : ∀ i, ∑ y : V, |Φ i y| ^ (∑ j, q j) * twoPoint pr ends o y ≤ M) :
    expectReal pr (fun s => tupleSum (clusterF ends s o) n (fun x => ∏ i, |Φ i (x i)| ^ q i))
      ≤ (VolumeMoments.M (n - 1) : ℝ) * (n : ℝ) ^ (max (∑ i, q i) 1) *
          (clusterVolume pr ends o) ^ (2 * n - 2) * M :=
  spatial_tree_graph_of_finite pr hp hp1 ends o
    (PercLib.CriticalLRP.TreeGraph.treeGraphBound_of_bk' pr hp hp1 hBK) hinv hn q Φ M hq hP hM

#print axioms PercLib.CriticalLRP.TreeExpansion.addMonoidHom_eq_zero_of_finite
#print axioms PercLib.CriticalLRP.TreeExpansion.abs_apply_rpow_eq_zero
#print axioms PercLib.CriticalLRP.TreeExpansion.sum_treeSum_le
#print axioms PercLib.CriticalLRP.TreeExpansion.weightedTreeSum_of_finite
#print axioms PercLib.CriticalLRP.TreeExpansion.spatial_tree_graph_of_finite
#print axioms PercLib.CriticalLRP.TreeExpansion.spatial_tree_graph_printed_of_finite
#print axioms PercLib.CriticalLRP.TreeExpansion.spatial_tree_graph_of_bk

end PercLib.CriticalLRP.TreeExpansion
