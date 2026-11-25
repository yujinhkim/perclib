/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
New proofs using pinned mathlib's simple paths, cylinder probabilities and
ENNReal sums. No upstream proof is copied; reuse findings are on issue #39.
-/
module

public import PercLib.Probability.Cylinder
public import PercLib.Percolation.Bond.Susceptibility
public import PercLib.Percolation.Bond.WalkSum
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
public import Mathlib.Data.List.OfFn

/-! # Subcritical off-diagonal row sums
Probability products are computed only for simple paths, whose edges are distinct.
The subsequent enlargement to arbitrary sequences is a deterministic inequality.
-/
@[expose] public section
noncomputable section
open MeasureTheory Set PercLib.Probability
open scoped ENNReal NNReal
open Classical
namespace PercLib.Percolation.Bond
variable {V : Type*}

/-- Every connection has a deterministic simple-path certificate in the complete graph. -/
theorem conn_subset_iUnion_path (x y : V) :
    conn x y ⊆ ⋃ p : (⊤ : SimpleGraph V).Path x y,
      {ω : Config V | (p.1.edges.toFinset : Set (Sym2 V)) ⊆ ω} := by
  intro ω hω
  obtain ⟨p, hp⟩ := hω.exists_isPath
  refine mem_iUnion.mpr ⟨⟨p.mapLe le_top, hp.mapLe le_top⟩, ?_⟩
  intro e he
  have he' : e ∈ (openGraph ω).edgeSet := p.edges_subset_edgeSet (by simpa using he)
  exact (show e ∈ ω \ Sym2.diagSet by simpa [openGraph, SimpleGraph.edgeSet_fromEdgeSet] using he').1

/-- The probability bound sums only simple paths, including the empty path when x=y. -/
@[tag "5C44"]
theorem tau_le_tsum_paths [Countable V] (q : Sym2 V → unitInterval) (x y : V) :
    tau q x y ≤ ∑' p : (⊤ : SimpleGraph V).Path x y,
      ∏ e ∈ p.1.edges.toFinset, (unitInterval.toNNReal (q e) : ℝ≥0∞) := by
  let : Countable ((⊤ : SimpleGraph V).Walk x y) :=
    Function.Injective.countable SimpleGraph.Walk.support_injective
  calc
    tau q x y ≤ law q (⋃ p : (⊤ : SimpleGraph V).Path x y,
        {ω : Config V | (p.1.edges.toFinset : Set (Sym2 V)) ⊆ ω}) :=
      measure_mono (conn_subset_iUnion_path x y)
    _ ≤ ∑' p : (⊤ : SimpleGraph V).Path x y,
        law q {ω : Config V | (p.1.edges.toFinset : Set (Sym2 V)) ⊆ ω} := measure_iUnion_le _
    _ = _ := by simp only [law, prodBernoulli_subset]

/-- Appending the first vertex to a list agrees with the explicit walk-weight recursion. -/
theorem walkWeight_list_cons (a : V → V → ℝ≥0∞) (x y : V) (l : List V) :
    walkWeight a x (y :: l).get = a x y * walkWeight a y l.get := by
  have h : (y :: l).get = Fin.cons y l.get := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  rw [h, walkWeight_cons]

/-- The ordered edge product of any walk is its deterministic masked sequence weight.
This is an algebraic identity, not a claim about the probability of repeated edges. -/
theorem walk_edges_prod_eq_weight (q : Sym2 V → unitInterval) {G : SimpleGraph V}
    {x y : V} (p : G.Walk x y) :
    (p.edges.map (fun e => (unitInterval.toNNReal (q e) : ℝ≥0∞))).prod =
      walkWeight (offDiagonal (fun v w => (unitInterval.toNNReal (q s(v,w)) : ℝ≥0∞)))
        x p.support.tail.get := by
  induction p with
  | nil => simp
  | @cons x z y h p ih =>
    simp only [SimpleGraph.Walk.edges_cons, List.map_cons, List.prod_cons,
      SimpleGraph.Walk.support_cons, List.tail_cons]
    rw [← p.cons_tail_support, walkWeight_list_cons, ← ih]
    simp [offDiagonal, h.ne.symm]

/-- A simple path's distinct-coordinate cylinder product equals its sequence weight. -/
theorem path_prod_eq_weight (q : Sym2 V → unitInterval) {x y : V}
    (p : (⊤ : SimpleGraph V).Path x y) :
    (∏ e ∈ p.1.edges.toFinset, (unitInterval.toNNReal (q e) : ℝ≥0∞)) =
      walkWeight (offDiagonal (fun v w => (unitInterval.toNNReal (q s(v,w)) : ℝ≥0∞)))
        x p.1.support.tail.get := by
  rw [List.prod_toFinset _ p.2.isTrail.edges_nodup, walk_edges_prod_eq_weight]

/-- A path, including its endpoint, is determined by its continuation list. -/
theorem path_tail_injective (x : V) :
    Function.Injective (fun p : Σ y, (⊤ : SimpleGraph V).Path x y => p.2.1.support.tail) := by
  rintro ⟨y, p, hp⟩ ⟨z, r, hr⟩ heq
  change p.support.tail = r.support.tail at heq
  have hs : p.support = r.support := by
    rw [← p.cons_tail_support, ← r.cons_tail_support, heq]
  have hyz : y = z := by
    rw [← p.getLast_support, ← r.getLast_support]
    simp only [hs]
  subst z
  have hpr : p = r := SimpleGraph.Walk.support_injective hs
  subst r
  rfl

/-- Expected cluster volume is bounded by the sum of masked walk weights. -/
theorem chi_le_tsum_walkSum [Countable V] (q : Sym2 V → unitInterval) (x : V) :
    chi q x ≤ ∑' n, walkSum
      (offDiagonal (fun v w => (unitInterval.toNNReal (q s(v,w)) : ℝ≥0∞))) n x := by
  let a := offDiagonal (fun v w : V => (unitInterval.toNNReal (q s(v,w)) : ℝ≥0∞))
  calc
    chi q x = ∑' y, tau q x y := chi_eq_tsum_tau q x
    _ ≤ ∑' y, ∑' p : (⊤ : SimpleGraph V).Path x y,
        ∏ e ∈ p.1.edges.toFinset, (unitInterval.toNNReal (q e) : ℝ≥0∞) :=
      ENNReal.tsum_le_tsum (tau_le_tsum_paths q x)
    _ = ∑' p : Σ y, (⊤ : SimpleGraph V).Path x y,
        walkWeight a x p.2.1.support.tail.get := by
      simp_rw [path_prod_eq_weight]
      exact (ENNReal.tsum_sigma' (fun p : Σ y, (⊤ : SimpleGraph V).Path x y =>
        walkWeight a x p.2.1.support.tail.get)).symm
    _ ≤ ∑' l : List V, walkWeight a x l.get :=
      ENNReal.tsum_comp_le_tsum_of_injective (path_tail_injective x)
        (fun l => walkWeight a x l.get)
    _ = ∑' t : Σ n, Fin n → V, walkWeight a x t.2 :=
      (List.equivSigmaTuple.tsum_eq (fun t => walkWeight a x t.2))
    _ = ∑' n, walkSum a n x := by
      rw [ENNReal.tsum_sigma']
      simp_rw [walkSum_eq_tsum_walkWeight]

/-- The uniform off-diagonal row bound controls susceptibility. No diagonal
condition, host graph, transitivity or finite-degree assumption is needed. -/
theorem chi_le_inv_one_sub_of_rowSum [Countable V] (q : Sym2 V → unitInterval)
    (m : ℝ≥0∞)
    (hrow : ∀ v, (∑' w, if w = v then 0 else
      (unitInterval.toNNReal (q s(v,w)) : ℝ≥0∞)) ≤ m)
    (hm : m < 1) (x : V) : chi q x ≤ (1 - m)⁻¹ :=
  (chi_le_tsum_walkSum q x).trans
    (walkSum_masked_total_le _ m hrow hm x)

/-- Subunit off-diagonal rows imply finite susceptibility at every vertex. -/
theorem chi_lt_top_of_rowSum [Countable V] (q : Sym2 V → unitInterval)
    (m : ℝ≥0∞)
    (hrow : ∀ v, (∑' w, if w = v then 0 else
      (unitInterval.toNNReal (q s(v,w)) : ℝ≥0∞)) ≤ m)
    (hm : m < 1) (x : V) : chi q x < ⊤ :=
  lt_of_le_of_lt (chi_le_tsum_walkSum q x)
    (walkSum_total_lt_top _ m hrow hm x)

/-- With probability one all clusters are finite simultaneously for the fixed profile. -/
theorem ae_all_clusters_finite_of_rowSum [Countable V] (q : Sym2 V → unitInterval)
    (m : ℝ≥0∞)
    (hrow : ∀ v, (∑' w, if w = v then 0 else
      (unitInterval.toNNReal (q s(v,w)) : ℝ≥0∞)) ≤ m)
    (hm : m < 1) : ∀ᵐ ω ∂law q, ∀ x, (cluster ω x).Finite := by
  rw [ae_all_iff]
  intro x
  have hmeas : Measurable (fun ω : Config V => ((cluster ω x).encard : ℝ≥0∞)) :=
    (measurable_of_countable (fun n : ℕ∞ => (n : ℝ≥0∞))).comp (measurable_encard_cluster x)
  have h := ae_lt_top hmeas (chi_lt_top_of_rowSum q m hrow hm x).ne
  filter_upwards [h] with ω hω
  exact Set.encard_lt_top_iff.mp (ENat.toENNReal_lt_top.mp hω)

/-- The length-zero contribution gives a lower bound of one. -/
theorem one_le_chi [Countable V] (q : Sym2 V → unitInterval) (x : V) :
    1 ≤ chi q x := by
  rw [chi_eq_tsum_tau, ← tau_self q x]
  exact ENNReal.le_tsum x

/-- Vanishing off-diagonal rates give susceptibility exactly one, regardless of loops. -/
theorem chi_eq_one_of_offDiagonal_zero [Countable V] (q : Sym2 V → unitInterval)
    (hq : ∀ v w, w ≠ v → q s(v,w) = 0) (x : V) : chi q x = 1 := by
  apply le_antisymm _ (one_le_chi q x)
  have hrow : ∀ v, (∑' w, if w = v then 0 else
      (unitInterval.toNNReal (q s(v,w)) : ℝ≥0∞)) ≤ 0 := by
    intro v
    apply le_of_eq
    calc
      _ = ∑' _ : V, (0 : ℝ≥0∞) := by
        apply tsum_congr
        intro w
        split_ifs with h
        · rfl
        · simp [hq v w h]
      _ = 0 := tsum_zero
  simpa using chi_le_inv_one_sub_of_rowSum q 0 hrow (by simp) x

-- Arbitrary diagonal rates are allowed, including probability one.
example [Countable V] (x : V) :
    chi (fun e : Sym2 V => if e.IsDiag then 1 else 0) x = 1 := by
  apply chi_eq_one_of_offDiagonal_zero
  intro v w h
  simp [Sym2.mk_isDiag_iff, Ne.symm h]

-- A nonzero two-vertex profile satisfies the subcritical hypothesis.
example : chi (fun _ : Sym2 Bool => (⟨1/2, by norm_num⟩ : unitInterval)) false ≤ 2 := by
  classical
  have hp : (unitInterval.toNNReal (⟨1/2, by norm_num⟩ : unitInterval) : ℝ≥0∞) = 1/2 := by
    change ((1/2 : ℝ≥0) : ℝ≥0∞) = _
    simp
  have hbound := chi_le_inv_one_sub_of_rowSum
    (fun _ : Sym2 Bool => (⟨1/2, by norm_num⟩ : unitInterval)) (1/2)
    (by intro v; cases v <;> norm_num [tsum_fintype, hp]) (by norm_num) false
  convert hbound using 1; norm_num

-- A backtracking walk uses one unordered coordinate twice. Its open event has
-- probability 1/2, whereas its deterministic length-two weight is 1/4.
example : prodBernoulli (fun _ : Sym2 Bool => (⟨1/2, by norm_num⟩ : unitInterval))
    {ω | ({s(false,true), s(true,false)} : Set (Sym2 Bool)) ⊆ ω} = 1/2 := by
  have hp : (unitInterval.toNNReal (⟨1/2, by norm_num⟩ : unitInterval) : ℝ≥0∞) = 1/2 := by
    change ((1/2 : ℝ≥0) : ℝ≥0∞) = _
    simp
  have h : s(true,false) = s(false,true) := Sym2.eq_swap
  have hevent : {ω : Set (Sym2 Bool) | ({s(false,true), s(true,false)} : Set (Sym2 Bool)) ⊆ ω} =
      {ω | s(false,true) ∈ ω} := by ext ω; simp [h]
  rw [hevent, prodBernoulli_setOf_mem]
  exact hp

example : walkWeight (offDiagonal (fun _ _ : Bool => (1/2 : ℝ≥0∞))) false
    (Fin.cons true (Fin.cons false (fun i : Fin 0 => i.elim0))) = 1/4 := by
  norm_num [walkWeight_cons, offDiagonal, ← ENNReal.mul_inv]

example (q : Sym2 Unit → unitInterval) : chi q () = 1 := by
  apply chi_eq_one_of_offDiagonal_zero
  intro v w h
  exact (h (Subsingleton.elim _ _)).elim

example (q : Sym2 Empty → unitInterval) : ∀ᵐ ω ∂law q, ∀ x, (cluster ω x).Finite := by
  exact Filter.Eventually.of_forall (fun _ x => x.elim)

end PercLib.Percolation.Bond
