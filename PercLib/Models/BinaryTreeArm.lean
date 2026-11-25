/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.
Q-73: the critical arm recursion on the rooted binary tree and the exact two-point function
on rooted trees. New for this project; no upstream proof is copied, and no new definition
is introduced.
-/
module

public import PercLib.Models.TreeRecursion
public import PercLib.Percolation.Bond.Forest
public import PercLib.Percolation.Bond.PathLowerBounds
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.Metric
public import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

/-!
# The rooted binary tree: the critical arm and the two-point function

The rooted `k`-ary tree is the graph
`SimpleGraph.fromRel fun u w : List (Fin k) => ∃ b, w = b :: u` of `Models/Tree.lean`.

* `isAcyclic_kTree`, `reachable_kTree`: it is a tree.
* `tau_kTree_eq_pow` (NDIC, item 2): with open probability `p` on tree edges and `0` on
  other pairs (any value on the diagonal), `tau q x y = p ^ dist(x,y)` for every `p ∈ [0,1]`.
* `binaryArm_zero`, `binaryArm_succ`, `tendsto_mul_binaryArm` (NDIC, item 1): at `p = 1/2`
  on the binary tree the probability `r_n` that the root is joined by open edges to some
  word of length `n` satisfies `r_0 = 1`, `r_(n+1) = r_n − r_n²/4` and `n · r_n → 4`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology PercLib.Probability PercLib.Percolation.Bond
open scoped ENNReal

namespace PercLib.Models

variable {k : ℕ}

/-! ### The rooted tree is a tree -/

/-- The rooted `k`-ary tree is acyclic: every edge is a bridge, because the descendants of
the lower endpoint are closed under the remaining adjacencies. -/
theorem isAcyclic_kTree :
    (SimpleGraph.fromRel fun u w : List (Fin k) => ∃ b, w = b :: u).IsAcyclic := by
  set G := SimpleGraph.fromRel fun u w : List (Fin k) => ∃ b, w = b :: u
  -- the edge from `v` to its child `b :: v` is a bridge
  have hchild : ∀ (v : List (Fin k)) (b : Fin k), G.IsBridge s(v, b :: v) := by
    intro v b
    rw [SimpleGraph.isBridge_iff]
    intro hr
    set S : Set (List (Fin k)) := {z | (b :: v) <:+ z}
    have hS : ∀ a c, (G.deleteEdges {s(v, b :: v)}).Adj a c → a ∈ S → c ∈ S := by
      intro a c hac ha
      rw [SimpleGraph.deleteEdges_adj] at hac
      obtain ⟨hG, hne⟩ := hac
      rcases (kTree_adj_iff a c).mp hG with ⟨d, rfl⟩ | ⟨d, rfl⟩
      · exact ha.trans (List.suffix_cons d a)
      · rcases List.suffix_cons_iff.mp ha with h | h
        · exfalso
          apply hne
          have hd : d = b ∧ c = v := by simpa using h.symm
          rw [hd.1, hd.2]
          simp [Sym2.eq_swap]
        · exact h
    have hmem := mem_of_reachable_of_closed hS hr.symm (List.suffix_refl _)
    have := hmem.length_le
    simp at this
  rw [SimpleGraph.isAcyclic_iff_forall_adj_isBridge]
  intro v w hvw
  rcases (kTree_adj_iff v w).mp hvw with ⟨b, rfl⟩ | ⟨b, rfl⟩
  · exact hchild v b
  · rw [Sym2.eq_swap]
    exact hchild w b

/-- Every word is joined to the root. -/
theorem reachable_kTree (w : List (Fin k)) :
    (SimpleGraph.fromRel fun u w : List (Fin k) => ∃ b, w = b :: u).Reachable [] w := by
  induction w with
  | nil => exact SimpleGraph.Reachable.refl _
  | cons b u ih =>
    exact ih.trans ((kTree_adj_iff u (b :: u)).mpr (Or.inl ⟨b, rfl⟩)).reachable

/-! ### The two-point function -/

/-- **NDIC, item 2.** On the rooted `k`-ary tree with open probability `p` on tree edges and
`0` on all other pairs (any value on the diagonal), `tau q x y = p ^ dist(x,y)` for every
`p ∈ [0,1]` and all vertices, with `p ^ 0 = 1`. -/
theorem tau_kTree_eq_pow (p : unitInterval) (q : Sym2 (List (Fin k)) → unitInterval)
    (hq : ∀ u w, u ≠ w → q s(u, w) =
      if s(u, w) ∈ (SimpleGraph.fromRel fun u w : List (Fin k) => ∃ b, w = b :: u).edgeSet
        then p else 0)
    (x y : List (Fin k)) :
    tau q x y = (unitInterval.toNNReal p : ℝ≥0∞) ^
      (SimpleGraph.fromRel fun u w : List (Fin k) => ∃ b, w = b :: u).dist x y := by
  classical
  set G := SimpleGraph.fromRel fun u w : List (Fin k) => ∃ b, w = b :: u with hG
  have hhost : ∀ᵐ ω ∂law q, openGraph ω ≤ G := by
    filter_upwards [ae_config_subset_positive q] with ω hω
    intro a c hac
    obtain ⟨he, hne⟩ := (openGraph_adj_iff ω a c).mp hac
    have hpos : 0 < q s(a, c) := hω he
    rw [hq a c hne] at hpos
    by_contra hnot
    have : s(a, c) ∉ G.edgeSet := hnot
    rw [ite_eq_right this] at hpos
    exact lt_irrefl _ hpos
  have hreach : G.Reachable x y := (reachable_kTree x).symm.trans (reachable_kTree y)
  obtain ⟨w, hpath, hlen⟩ := hreach.exists_path_of_dist
  rw [tau_eq_prod_of_ae_le_acyclic q isAcyclic_kTree hhost ⟨w, hpath⟩]
  have hprob : ∀ e ∈ w.edges, q e = p := by
    intro e he
    have heG := w.edges_subset_edgeSet he
    induction e using Sym2.ind with
    | _ a c =>
      have hne : a ≠ c := G.ne_of_adj heG
      rw [hq a c hne, ite_eq_left heG]
  refine (Finset.prod_congr rfl (g := fun _ => (unitInterval.toNNReal p : ℝ≥0∞))
      fun e he => ?_).trans ?_
  · rw [hprob e (List.mem_toFinset.mp (by convert he))]
  rw [Finset.prod_const, ← hlen, ← SimpleGraph.Walk.length_edges]
  congr 1
  convert List.toFinset_card_of_nodup hpath.isTrail.edges_nodup

/-! ### The critical arm of the binary tree -/

/-- The recursion `x_(n+1) = x_n − x_n²/4` started from `1` satisfies `n x_n → 4`. -/
theorem tendsto_mul_of_arm_recursion (x : ℕ → ℝ) (h0 : x 0 = 1)
    (hs : ∀ n, x (n + 1) = x n - x n ^ 2 / 4) :
    Tendsto (fun n : ℕ => (n : ℝ) * x n) atTop (𝓝 4) := by
  have hbd : ∀ n, 0 < x n ∧ x n ≤ 1 := by
    intro n
    induction n with
    | zero => rw [h0]; norm_num
    | succ n ih =>
      rw [hs n]
      obtain ⟨h1, h2⟩ := ih
      constructor <;> nlinarith
  have hinv : ∀ n, (x (n + 1))⁻¹ = (x n)⁻¹ + (4 - x n)⁻¹ := by
    intro n
    obtain ⟨h1, h2⟩ := hbd n
    have h3 : (4 : ℝ) - x n ≠ 0 := by linarith
    have h4 : x n - x n ^ 2 / 4 ≠ 0 := by nlinarith
    rw [hs n]
    field_simp
    ring
  have hsum : ∀ n, (x n)⁻¹ = 1 + ∑ j ∈ Finset.range n, (4 - x j)⁻¹ := by
    intro n
    induction n with
    | zero => simp [h0]
    | succ n ih => rw [hinv n, ih, Finset.sum_range_succ]; ring
  -- `x n → 0`
  have hlow : ∀ n : ℕ, 1 + (n : ℝ) / 4 ≤ (x n)⁻¹ := by
    intro n
    rw [hsum n]
    have : ∀ j ∈ Finset.range n, (1 / 4 : ℝ) ≤ (4 - x j)⁻¹ := by
      intro j _
      obtain ⟨h1, h2⟩ := hbd j
      rw [one_div]
      exact inv_anti₀ (by linarith) (by linarith)
    have := Finset.sum_le_sum this
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at this
    linarith
  have hx0 : Tendsto x atTop (𝓝 0) := by
    have hup : ∀ n : ℕ, x n ≤ (1 + (n : ℝ) / 4)⁻¹ := by
      intro n
      have h1 := (hbd n).1
      calc x n = ((x n)⁻¹)⁻¹ := (inv_inv _).symm
        _ ≤ (1 + (n : ℝ) / 4)⁻¹ := inv_anti₀ (by positivity) (hlow n)
    have hlim : Tendsto (fun n : ℕ => (1 + (n : ℝ) / 4)⁻¹) atTop (𝓝 0) := by
      apply Tendsto.inv_tendsto_atTop
      apply tendsto_atTop_add_const_left
      exact (tendsto_natCast_atTop_atTop).atTop_div_const (by norm_num)
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
      (fun n => (hbd n).1.le) hup
  have hu : Tendsto (fun j => (4 - x j)⁻¹) atTop (𝓝 (1 / 4)) := by
    have := (tendsto_const_nhds (x := (4 : ℝ))).sub hx0
    rw [sub_zero] at this
    simpa [one_div] using this.inv₀ (by norm_num)
  have hces := hu.cesaro
  have havg : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * (x n)⁻¹) atTop (𝓝 (1 / 4)) := by
    have h1 : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
    have := h1.add hces
    rw [zero_add] at this
    refine this.congr fun n => ?_
    rw [hsum n]
    ring
  have := havg.inv₀ (by norm_num)
  rw [one_div, inv_inv] at this
  refine this.congr fun n => ?_
  rw [mul_inv, inv_inv, inv_inv]

/-- The half-probability tree profile of the binary tree. -/
private theorem toReal_half :
    ((unitInterval.toNNReal (⟨1 / 2, by norm_num, by norm_num⟩ : unitInterval) : ℝ≥0∞)).toReal =
      1 / 2 := by
  rw [ENNReal.coe_toReal]
  rfl

/-- **NDIC, item 1**, start: `r_0 = 1`. -/
theorem binaryArm_zero :
    (law (fun e : Sym2 (List (Fin 2)) =>
        if e ∈ (SimpleGraph.fromRel fun u w : List (Fin 2) => ∃ b, w = b :: u).edgeSet then
          (⟨1 / 2, by norm_num, by norm_num⟩ : unitInterval) else 0)
      {ω | ∃ w : List (Fin 2), w.length = 0 ∧
        ∀ m < 0, s(w.drop (m + 1), w.drop m) ∈ ω}).toReal = 1 := by
  have : {ω : Config (List (Fin 2)) | ∃ w : List (Fin 2), w.length = 0 ∧
      ∀ m < 0, s(w.drop (m + 1), w.drop m) ∈ ω} = Set.univ :=
    Set.eq_univ_of_forall fun ω => ⟨[], rfl, fun m hm => absurd hm (Nat.not_lt_zero m)⟩
  rw [this, measure_univ, ENNReal.toReal_one]

/-- **NDIC, item 1**, recursion: `r_(n+1) = r_n − r_n²/4` at `p = 1/2`. -/
theorem binaryArm_succ (n : ℕ) :
    (law (fun e : Sym2 (List (Fin 2)) =>
        if e ∈ (SimpleGraph.fromRel fun u w : List (Fin 2) => ∃ b, w = b :: u).edgeSet then
          (⟨1 / 2, by norm_num, by norm_num⟩ : unitInterval) else 0)
      {ω | ∃ w : List (Fin 2), w.length = n + 1 ∧
        ∀ m < n + 1, s(w.drop (m + 1), w.drop m) ∈ ω}).toReal =
    (law (fun e : Sym2 (List (Fin 2)) =>
        if e ∈ (SimpleGraph.fromRel fun u w : List (Fin 2) => ∃ b, w = b :: u).edgeSet then
          (⟨1 / 2, by norm_num, by norm_num⟩ : unitInterval) else 0)
      {ω | ∃ w : List (Fin 2), w.length = n ∧
        ∀ m < n, s(w.drop (m + 1), w.drop m) ∈ ω}).toReal -
    (law (fun e : Sym2 (List (Fin 2)) =>
        if e ∈ (SimpleGraph.fromRel fun u w : List (Fin 2) => ∃ b, w = b :: u).edgeSet then
          (⟨1 / 2, by norm_num, by norm_num⟩ : unitInterval) else 0)
      {ω | ∃ w : List (Fin 2), w.length = n ∧
        ∀ m < n, s(w.drop (m + 1), w.drop m) ∈ ω}).toReal ^ 2 / 4 := by
  rw [law_depth_succ (k := 2)]
  set L := law (fun e : Sym2 (List (Fin 2)) =>
        if e ∈ (SimpleGraph.fromRel fun u w : List (Fin 2) => ∃ b, w = b :: u).edgeSet then
          (⟨1 / 2, by norm_num, by norm_num⟩ : unitInterval) else 0)
      {ω | ∃ w : List (Fin 2), w.length = n ∧ ∀ m < n, s(w.drop (m + 1), w.drop m) ∈ ω}
  set c : ℝ≥0∞ := (unitInterval.toNNReal (⟨1 / 2, by norm_num, by norm_num⟩ : unitInterval) : ℝ≥0∞)
  have hL : L ≤ 1 := prob_le_one
  have hc : c ≤ 1 := by
    have : c.toReal ≤ 1 := by rw [toReal_half]; norm_num
    exact (ENNReal.toReal_le_toReal (by simp [c]) ENNReal.one_ne_top).mp (by simpa using this)
  have hcL : c * L ≤ 1 := mul_le_one' hc hL
  have hsq : (1 - c * L) ^ 2 ≤ 1 := pow_le_one₀ (zero_le) tsub_le_self
  rw [ENNReal.toReal_sub_of_le hsq ENNReal.one_ne_top, ENNReal.toReal_pow,
    ENNReal.toReal_sub_of_le hcL ENNReal.one_ne_top, ENNReal.toReal_mul, toReal_half,
    ENNReal.toReal_one]
  ring

/-- **NDIC, item 1**, asymptotics: `n · r_n → 4` at `p = 1/2`. -/
theorem tendsto_mul_binaryArm :
    Tendsto (fun n : ℕ => (n : ℝ) *
      (law (fun e : Sym2 (List (Fin 2)) =>
        if e ∈ (SimpleGraph.fromRel fun u w : List (Fin 2) => ∃ b, w = b :: u).edgeSet then
          (⟨1 / 2, by norm_num, by norm_num⟩ : unitInterval) else 0)
      {ω | ∃ w : List (Fin 2), w.length = n ∧
        ∀ m < n, s(w.drop (m + 1), w.drop m) ∈ ω}).toReal) atTop (𝓝 4) :=
  tendsto_mul_of_arm_recursion _ binaryArm_zero binaryArm_succ

/-! ### Non-vacuity witnesses (D-5) -/

/-- `r_1 = 3/4`. -/
example :
    (law (fun e : Sym2 (List (Fin 2)) =>
        if e ∈ (SimpleGraph.fromRel fun u w : List (Fin 2) => ∃ b, w = b :: u).edgeSet then
          (⟨1 / 2, by norm_num, by norm_num⟩ : unitInterval) else 0)
      {ω | ∃ w : List (Fin 2), w.length = 0 + 1 ∧
        ∀ m < 0 + 1, s(w.drop (m + 1), w.drop m) ∈ ω}).toReal = 3 / 4 := by
  rw [binaryArm_succ, binaryArm_zero]
  norm_num

/-- `r_2 = 39/64`. -/
example :
    (law (fun e : Sym2 (List (Fin 2)) =>
        if e ∈ (SimpleGraph.fromRel fun u w : List (Fin 2) => ∃ b, w = b :: u).edgeSet then
          (⟨1 / 2, by norm_num, by norm_num⟩ : unitInterval) else 0)
      {ω | ∃ w : List (Fin 2), w.length = 0 + 1 + 1 ∧
        ∀ m < 0 + 1 + 1, s(w.drop (m + 1), w.drop m) ∈ ω}).toReal = 39 / 64 := by
  rw [binaryArm_succ, binaryArm_succ, binaryArm_zero]
  norm_num

/-- Item 2 at adjacent vertices: `tau q [] [0] = p`. -/
example (p : unitInterval) :
    tau (fun e : Sym2 (List (Fin 2)) =>
        if e ∈ (SimpleGraph.fromRel fun u w : List (Fin 2) => ∃ b, w = b :: u).edgeSet then p
          else 0) [] [0] = (unitInterval.toNNReal p : ℝ≥0∞) := by
  rw [tau_kTree_eq_pow p _ (fun u w _ => rfl)]
  have hadj : (SimpleGraph.fromRel fun u w : List (Fin 2) => ∃ b, w = b :: u).Adj [] [0] :=
    (kTree_adj_iff [] [0]).mpr (Or.inl ⟨0, rfl⟩)
  rw [SimpleGraph.dist_eq_one_iff_adj.mpr hadj, pow_one]

end PercLib.Models
