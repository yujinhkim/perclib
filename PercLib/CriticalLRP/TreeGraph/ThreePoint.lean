/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
The first tree-graph inequality of Aizenman--Newman, equation (I.2.1) of

  T. Hutchcroft, *Critical long-range percolation I: High effective dimension*,
  arXiv:2508.18807v1, Section I.2, p. 22:

    `P_β(x ↔ y ↔ z) ≤ ∑_w P_β(x ↔ w) P_β(w ↔ y) P_β(w ↔ z)`

for Bernoulli bond percolation on a weighted graph, together with the interface through
which the BK inequality enters.

The BK inequality itself is *not* proved here; it enters as the explicit hypothesis
`BKIncreasing p`, the increasing-event, arbitrary-arity form of van den Berg--Kesten /
Reimer ("if A and B are increasing events ... P(A ∘ B) ≤ P(A)P(B)", p. 21). Two equivalent
encodings of the disjoint occurrence `∘` are provided and proved equivalent for increasing
events: the paper's witness form (`DisjOccW`, p. 21) and the "disjoint witness sets inside
the configuration" form (`DisjOccK`) used for the assembly.

Everything else in the proof of (I.2.1) is proved here: monotonicity of the percolation
probability, the finite union bound, and the three-arm decomposition of `Conn.lean`.
-/
module

public import PercLib.CriticalLRP.TreeGraph.Connectivity
public import PercLib.CriticalLRP.FiniteBernoulli

set_option autoImplicit true

set_option linter.unusedSectionVars false

@[expose] public section

namespace PercLib.CriticalLRP.TreeGraph

open Finset

variable {V : Type*} [DecidableEq V]
variable {E : Type*} [Fintype E] [DecidableEq E]

noncomputable section

/-! ### The finite Bernoulli law -/

/-- Probability of an event under the finite independent edge law of
`CriticalPercLib.CriticalLRP.FiniteBernoulli`. -/
def prob (p : E → ℝ) (A : Set (Finset E)) : ℝ := PercLib.CriticalLRP.probability p A

theorem prob_nonneg {p : E → ℝ} (hp : ∀ e, 0 ≤ p e) (hp1 : ∀ e, p e ≤ 1)
    (A : Set (Finset E)) : 0 ≤ prob p A := by
  simp only [prob, PercLib.CriticalLRP.probability, PercLib.CriticalLRP.expectation]
  refine Finset.sum_nonneg fun s _ => mul_nonneg
    (PercLib.CriticalLRP.configurationLaw_nonneg p hp hp1 s) ?_
  by_cases hs : s ∈ A <;> simp [hs]

theorem prob_mono {p : E → ℝ} (hp : ∀ e, 0 ≤ p e) (hp1 : ∀ e, p e ≤ 1)
    {A B : Set (Finset E)} (h : A ⊆ B) : prob p A ≤ prob p B := by
  simp only [prob, PercLib.CriticalLRP.probability, PercLib.CriticalLRP.expectation]
  refine Finset.sum_le_sum fun s _ => ?_
  refine mul_le_mul_of_nonneg_left ?_ (PercLib.CriticalLRP.configurationLaw_nonneg p hp hp1 s)
  by_cases hs : s ∈ A
  · have hsB : s ∈ B := h hs
    simp [hs, hsB]
  · by_cases hsB : s ∈ B <;> simp [hs, hsB]

/-- Finite union bound for the percolation probability. -/
theorem prob_biUnion_le_sum {p : E → ℝ} (hp : ∀ e, 0 ≤ p e) (hp1 : ∀ e, p e ≤ 1)
    {ι : Type*} (W : Finset ι) (A : ι → Set (Finset E)) :
    prob p (⋃ i ∈ W, A i) ≤ ∑ i ∈ W, prob p (A i) := by
  classical
  have key : ∀ s : Finset E, (if s ∈ ⋃ i ∈ W, A i then (1 : ℝ) else 0)
      ≤ ∑ i ∈ W, (if s ∈ A i then (1 : ℝ) else 0) := by
    intro s
    by_cases hs : s ∈ ⋃ i ∈ W, A i
    · rw [ite_eq_left hs]
      obtain ⟨i, hiW, hiA⟩ := Set.mem_iUnion₂.mp hs
      have hmem : (1 : ℝ) ≤ ∑ j ∈ W, (if s ∈ A j then (1 : ℝ) else 0) := by
        refine le_trans (le_of_eq ?_) (Finset.single_le_sum
          (f := fun j => if s ∈ A j then (1 : ℝ) else 0) (fun j _ => ?_) hiW)
        · simp [hiA]
        · by_cases h : s ∈ A j <;> simp [h]
      exact hmem
    · rw [ite_eq_right hs]
      exact Finset.sum_nonneg fun j _ => by by_cases h : s ∈ A j <;> simp [h]
  have h : prob p (⋃ i ∈ W, A i) ≤ ∑ s, PercLib.CriticalLRP.configurationLaw p s *
      (∑ i ∈ W, (if s ∈ A i then (1 : ℝ) else 0)) := by
    simp only [prob, PercLib.CriticalLRP.probability, PercLib.CriticalLRP.expectation]
    exact Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left (key s)
      (PercLib.CriticalLRP.configurationLaw_nonneg p hp hp1 s)
  have h2 : (∑ s, PercLib.CriticalLRP.configurationLaw p s *
      (∑ i ∈ W, (if s ∈ A i then (1 : ℝ) else 0))) = ∑ i ∈ W, prob p (A i) := by
    have hmul : ∀ s : Finset E, PercLib.CriticalLRP.configurationLaw p s *
        (∑ i ∈ W, (if s ∈ A i then (1 : ℝ) else 0))
        = ∑ i ∈ W, PercLib.CriticalLRP.configurationLaw p s *
            (if s ∈ A i then (1 : ℝ) else 0) := fun s => Finset.mul_sum ..
    simp only [hmul, prob, PercLib.CriticalLRP.probability, PercLib.CriticalLRP.expectation]
    rw [Finset.sum_comm]
  rw [h2] at h
  exact h

/-! ### Increasing events and the two encodings of disjoint occurrence -/

/-- An event is increasing if it is preserved by opening more edges. -/
def IsIncreasing (A : Set (Finset E)) : Prop := ∀ ⦃s⦄, s ∈ A → ∀ ⦃t⦄, s ⊆ t → t ∈ A

theorem conn_isIncreasing (ends : E → Sym2 V) (u v : V) :
    IsIncreasing {s | Conn ends s u v} :=
  fun _ hs _ hst => conn_mono hst hs

/-- `W` is a **witness** for `ω ∈ A` (p. 21 of the paper): every configuration agreeing with
`ω` on `W` belongs to `A`. -/
def IsWitness (A : Set (Finset E)) (W ω : Finset E) : Prop :=
  ∀ ω' : Finset E, ω' ∩ W = ω ∩ W → ω' ∈ A

/-- The paper's disjoint occurrence `A₀ ∘ ⋯ ∘ A_{k-1}`, with witnesses (p. 21 for `k = 2`). -/
def DisjOccW {k : ℕ} (A : Fin k → Set (Finset E)) : Set (Finset E) :=
  {ω | (∀ i, ω ∈ A i) ∧ ∃ W : Fin k → Finset E,
    (∀ i j, i ≠ j → Disjoint (W i) (W j)) ∧ ∀ i, IsWitness (A i) (W i) ω}

/-- Disjoint occurrence in the form "there are pairwise disjoint witness sets, contained in
the configuration, each of which already belongs to its event". Equivalent to `DisjOccW` for
increasing events (`disjOccW_eq_disjOccK`). -/
def DisjOccK {k : ℕ} (A : Fin k → Set (Finset E)) : Set (Finset E) :=
  {ω | ∃ W : Fin k → Finset E, (∀ i, W i ⊆ ω) ∧ (∀ i, W i ∈ A i) ∧
    ∀ i j, i ≠ j → Disjoint (W i) (W j)}

/-- For increasing events, a subset `W ⊆ ω` is a witness for `ω ∈ A` exactly when `W ∈ A`. -/
theorem isWitness_iff {A : Set (Finset E)} (hA : IsIncreasing A) {W ω : Finset E}
    (hW : W ⊆ ω) : IsWitness A W ω ↔ W ∈ A := by
  constructor
  · intro h
    refine h W ?_
    rw [Finset.inter_self]
    exact (Finset.inter_eq_right.mpr hW).symm
  · intro h ω' hω'
    refine hA h fun x hx => ?_
    have hx1 : x ∈ ω ∩ W := Finset.mem_inter.mpr ⟨hW hx, hx⟩
    rw [← hω', Finset.mem_inter] at hx1
    exact hx1.1

/-- A witness for `ω ∈ A` contains, inside `ω`, a set of edges that already belongs to `A`. -/
theorem IsWitness.inter_mem {A : Set (Finset E)} {W ω : Finset E} (h : IsWitness A W ω) :
    ω ∩ W ∈ A := by
  refine h (ω ∩ W) ?_
  rw [Finset.inter_assoc, Finset.inter_self]

theorem disjOccW_eq_disjOccK {k : ℕ} {A : Fin k → Set (Finset E)} (hA : ∀ i, IsIncreasing (A i)) :
    DisjOccW A = DisjOccK A := by
  ext ω
  constructor
  · rintro ⟨-, W, hdisj, hwit⟩
    refine ⟨fun i => ω ∩ W i, fun i => Finset.inter_subset_left, ?_, ?_⟩
    · intro i
      exact IsWitness.inter_mem (hwit i)
    · intro i j hij
      rw [Finset.disjoint_left]
      intro x hx hx'
      exact (Finset.disjoint_left.mp (hdisj i j hij))
        (Finset.mem_inter.mp hx).2 (Finset.mem_inter.mp hx').2
  · rintro ⟨W, hsub, hmem, hdisj⟩
    refine ⟨fun i => hA i (hmem i) (hsub i), W, hdisj, fun i => ?_⟩
    exact (isWitness_iff (hA i) (hsub i)).mpr (hmem i)

/-! ### The BK interface -/

/-- **BK inequality, increasing case, arbitrary arity.** This is the statement quoted on p. 21
of the paper (`k = 2` is van den Berg--Kesten; the general case is Reimer's inequality, which
the paper notes "will suffice for all our applications"). It is an explicit hypothesis of the
results below, not proved here. -/
def BKIncreasing (p : E → ℝ) : Prop :=
  ∀ (k : ℕ) (A : Fin k → Set (Finset E)), (∀ i, IsIncreasing (A i)) →
    prob p (DisjOccK A) ≤ ∏ i, prob p (A i)

/-- The function `Fin 3 → α` with values `A₀, A₁, A₂`. -/
def tri {α : Type*} (A₀ A₁ A₂ : α) : Fin 3 → α :=
  fun i => match (i : ℕ) with | 0 => A₀ | 1 => A₁ | _ => A₂

/-- Three-fold disjoint occurrence in separated form. -/
def DisjOcc3 (A₀ A₁ A₂ : Set (Finset E)) : Set (Finset E) :=
  {ω | ∃ W₀ W₁ W₂ : Finset E, W₀ ⊆ ω ∧ W₁ ⊆ ω ∧ W₂ ⊆ ω ∧
    W₀ ∈ A₀ ∧ W₁ ∈ A₁ ∧ W₂ ∈ A₂ ∧ Disjoint W₀ W₁ ∧ Disjoint W₀ W₂ ∧ Disjoint W₁ W₂}

/-- Three-fold BK inequality, derived from the arbitrary-arity interface. -/
theorem bk_three {p : E → ℝ} (hBK : BKIncreasing p) {A₀ A₁ A₂ : Set (Finset E)}
    (h₀ : IsIncreasing A₀) (h₁ : IsIncreasing A₁) (h₂ : IsIncreasing A₂) :
    prob p (DisjOcc3 A₀ A₁ A₂) ≤ prob p A₀ * prob p A₁ * prob p A₂ := by
  classical
  set Af : Fin 3 → Set (Finset E) := tri A₀ A₁ A₂ with hAf
  have hAinc : ∀ i, IsIncreasing (Af i) := by
    intro i
    fin_cases i
    · exact h₀
    · exact h₁
    · exact h₂
  have hset : DisjOcc3 A₀ A₁ A₂ = DisjOccK Af := by
    ext ω
    constructor
    · rintro ⟨W₀, W₁, W₂, h0, h1, h2, m0, m1, m2, d01, d02, d12⟩
      refine ⟨tri W₀ W₁ W₂, ?_, ?_, ?_⟩
      · intro i; fin_cases i <;> assumption
      · intro i; fin_cases i <;> assumption
      · intro i j hij
        fin_cases i <;> fin_cases j <;> simp_all [tri, disjoint_comm]
    · rintro ⟨W, hsub, hmem, hdisj⟩
      exact ⟨W 0, W 1, W 2, hsub 0, hsub 1, hsub 2, hmem 0, hmem 1, hmem 2,
        hdisj 0 1 (by decide), hdisj 0 2 (by decide), hdisj 1 2 (by decide)⟩
  rw [hset]
  refine le_trans (hBK 3 Af hAinc) ?_
  rw [Fin.prod_univ_three]
  rfl

/-- Every vertex outside `candF` is joined to `x` with probability zero, so the finite sum in
(I.2.1) is the paper's sum over all of `V` (compare `three_point_tree_graph_tsum`). -/
theorem prob_conn_eq_zero_of_not_mem_candF {p : E → ℝ} {ends : E → Sym2 V} {x y z w : V}
    (hw : w ∉ candF ends x y z) : prob p {s | Conn ends s x w} = 0 := by
  classical
  have hempty : {s : Finset E | Conn ends s x w} = ∅ := by
    ext s
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨p⟩
    have h1 := support_subset_insert_verts (ends := ends) (s := s) (x := x) p w
      (SimpleGraph.Walk.end_mem_support p)
    rcases Finset.mem_insert.mp h1 with hwx | h'
    · rw [hwx] at hw
      exact hw (Finset.mem_insert_self x _)
    · exact hw (verts_subset_candF ends s x y z h')
  rw [hempty]
  simp [prob, PercLib.CriticalLRP.probability, PercLib.CriticalLRP.expectation]

/-! ### (I.2.1): the three-point tree-graph inequality -/

/-- **Tree-graph inequality (I.2.1).** For Bernoulli bond percolation on a weighted graph,
`P(x ↔ y ↔ z) ≤ ∑_w P(x ↔ w) P(w ↔ y) P(w ↔ z)`.

The sum on the right runs over the finite set `candF ends x y z`, which contains every vertex
that can be joined to `x` in a configuration of the finite ambient edge type `E`; every other
term vanishes. -/
theorem three_point_tree_graph {p : E → ℝ} (hp : ∀ e, 0 ≤ p e) (hp1 : ∀ e, p e ≤ 1)
    (hBK : BKIncreasing p) (ends : E → Sym2 V) (x y z : V) :
    prob p {s | Conn ends s x y ∧ Conn ends s x z}
      ≤ ∑ w ∈ candF ends x y z, prob p {s | Conn ends s x w} *
          prob p {s | Conn ends s w y} * prob p {s | Conn ends s w z} := by
  classical
  have hsub : {s | Conn ends s x y ∧ Conn ends s x z} ⊆
      ⋃ w ∈ candF ends x y z,
        DisjOcc3 {s | Conn ends s x w} {s | Conn ends s w y} {s | Conn ends s w z} := by
    intro s hs
    obtain ⟨hxy, hxz⟩ := hs
    obtain ⟨w, p, q, r, hpq, hpr, hqr⟩ := exists_three_arms ends s hxy hxz
    refine Set.mem_iUnion₂.mpr ⟨w, end_mem_candF p, ?_⟩
    have hq' : Conn ends (s.filter fun a => ends a ∈ q.edges) w y :=
      (walk_restrict q).elim fun q' => ⟨q'.reverse⟩
    have hr' : Conn ends (s.filter fun a => ends a ∈ r.edges) w z :=
      (walk_restrict r).elim fun r' => ⟨r'.reverse⟩
    refine ⟨_, _, _, Finset.filter_subset _ _, Finset.filter_subset _ _, Finset.filter_subset _ _,
      walk_restrict p, hq', hr', ?_, ?_, ?_⟩
    · rw [Finset.disjoint_left]
      intro a ha hb
      rw [Finset.mem_filter] at ha hb
      exact (List.disjoint_left.mp hpq) ha.2 hb.2
    · rw [Finset.disjoint_left]
      intro a ha hb
      rw [Finset.mem_filter] at ha hb
      exact (List.disjoint_left.mp hpr) ha.2 hb.2
    · rw [Finset.disjoint_left]
      intro a ha hb
      rw [Finset.mem_filter] at ha hb
      exact (List.disjoint_left.mp hqr) ha.2 hb.2
  calc prob p {s | Conn ends s x y ∧ Conn ends s x z}
      ≤ prob p (⋃ w ∈ candF ends x y z,
          DisjOcc3 {s | Conn ends s x w} {s | Conn ends s w y} {s | Conn ends s w z}) :=
        prob_mono hp hp1 hsub
    _ ≤ ∑ w ∈ candF ends x y z, prob p (DisjOcc3 {s | Conn ends s x w}
          {s | Conn ends s w y} {s | Conn ends s w z}) :=
        prob_biUnion_le_sum hp hp1 _ _
    _ ≤ ∑ w ∈ candF ends x y z, prob p {s | Conn ends s x w} *
          prob p {s | Conn ends s w y} * prob p {s | Conn ends s w z} := by
        refine Finset.sum_le_sum fun w _ => ?_
        exact bk_three hBK (conn_isIncreasing ends x w) (conn_isIncreasing ends w y)
          (conn_isIncreasing ends w z)

end

end PercLib.CriticalLRP.TreeGraph
