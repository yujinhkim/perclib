/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

# A countable-product percolation model with no infinite cluster at any parameter
  and infinite first moment at every positive parameter

Source context: T. Hutchcroft, *Critical long-range percolation I: High effective
dimension*, arXiv:2508.18807v1, §I.1.2 and Lemma I.4.9.  The paper derives finite first
moments from an explicit bound on the *uniform* row sum `sup_v ∑_w J(v,w) ≤ M < ∞`
(`PowerLawHighTemp`), and the sharpness input of §I.4 concerns the *stationary lattice*
model.  This file records, on the genuine countable-product law `longRangeMeasure J hJ β`
of the library, that the general framework alone cannot transfer "no infinite cluster" into
"finite first moment".  The model is

* `kernel : Sym2 W → ℝ`, with `W = root | hub n | leaf n i` and `Fin ((n+1) * 4^n)` leaves;
* intensity `(1/2)^n` on the fan edge `{root, hub n}`, intensity `1` on the bush edges
  `{hub n, leaf n i}`, and `0` on every other pair (the diagonal included);

and the proved statements are

* `infiniteClusterProb_eq_zero` : at **every** `β`, `infiniteClusterProb kernel kernel_nonneg β = 0`
  (the percolation set is empty: `criticalBetaSet_eq_empty`), and
* `lintegral_clusterVol_root_eq_top` : at every `β > 0` the root's expected cluster volume is
  `⊤`, hence `exists_percolation_empty_firstMoment_top`.

The mechanism is worth noting, because it is what fails without uniformity:

* only finitely many fan edges `{root, hub n}` are open a.s.  This is Borel–Cantelli, proved
  as `measure_fanSet_infinite` from `∑_n (1 - e^{-β 2^{-n}}) ≤ β ∑_n 2^{-n} < ∞`;
* if only finitely many fan edges are open then every cluster is finite
  (`cluster_finite_of_fanSet_finite`): open edges are fan or bush edges only
  (`support_cases`), so a cluster either stays in one finite bush or meets the root through
  one of the finitely many open fan edges;
* on the other hand, each bush contributes its full size to the root's first moment
  (`tau_leaf_ge`, `le_sum_tau_leaf`, `sum_leaf_le_tsum`), because the two-edge cylinder event
  `{fanEdge n open} ∩ {hub n — leaf n i open}` has probability
  `(1 - e^{-β2^{-n}})(1 - e^{-β})` and forces `root ↔ leaf n i`.

The rows are *not uniformly bounded*: the `n`-th hub carries `(n+1) * 4^n` leaves, and
`rows_unbounded` proves that every finite `M` is exceeded by some row.  (Each row is a finite
sum: a hub has its own bush and the root as its only neighbours of positive intensity, a leaf
has only its hub, and the root's fan series `∑_n (1/2)^n` is summable — the formal content
used below is the lower bound `hub_row_ge`.)  That uniform bound is exactly the hypothesis used by the paper's high-temperature and
cut-off arguments, so this model does **not** contradict `PowerLawHighTemp`; it shows that
the uniformity is essential, i.e. that no argument from "there is no infinite cluster" (even
at every parameter) to "the first moment is finite" can exist in the general framework.
The two excluded general inferences are stated outright as
`not_forall_infiniteClusterProb_eq_zero_imp_lintegral_ne_top` and
`not_forall_infiniteClusterProb_all_eq_zero_imp_lintegral_ne_top`.

Scope: this is a model witness about the library's general countable-product interface.  It
says nothing about the paper's `lrKernel d α`, its `β_c`, or about the stationary lattice;
in particular it is not a counterexample to the sharpness statement `β < β_c ⟹ χ(β) < ∞`,
whose hypothesis includes translation invariance.

No `sorry`, no `admit`, no `native_decide`, no custom axioms; the only axioms are Lean's
(`propext`, `choice`, `Quot.sound`, checked with `#print axioms` at the end of the file).
-/
module

public import PercLib.CriticalLRP.CountableProduct.Critical
public import PercLib.Percolation.Bond.Susceptibility

set_option autoImplicit false

open MeasureTheory Set Classical
open scoped ENNReal NNReal

attribute [local instance] Classical.propDecidable

@[expose] public section

namespace PercLib.CriticalLRP.BushRefute

/-! ## The vertex type: a root, hubs, and finite bushes of growing size -/

/-- The number of leaves of the `n`-th bush. -/
def bushSize (n : ℕ) : ℕ := (n + 1) * 4 ^ n

/-- The vertex type: a root, one hub per `n : ℕ`, and `bushSize n` leaves at hub `n`. -/
inductive W : Type
  /-- The root, joined to every hub. -/
  | root : W
  /-- The `n`-th hub, joined to the root and to its own leaves. -/
  | hub : ℕ → W
  /-- The `i`-th leaf of the `n`-th bush, joined to the `n`-th hub only. -/
  | leaf : (n : ℕ) → Fin (bushSize n) → W
  deriving DecidableEq

namespace W

/-- An injection of `W` into a countable type, used only to register `Countable W`. -/
def toSum : W → Option (ℕ ⊕ Σ n : ℕ, Fin (bushSize n))
  | root => none
  | hub n => some (Sum.inl n)
  | leaf n i => some (Sum.inr ⟨n, i⟩)

theorem toSum_injective : Function.Injective toSum := by
  intro a b h
  cases a with
  | root =>
    cases b with
    | root => rfl
    | hub m => simp [toSum] at h
    | leaf m i => simp [toSum] at h
  | hub n =>
    cases b with
    | root => simp [toSum] at h
    | hub m => simpa [toSum] using h
    | leaf m i => simp [toSum] at h
  | leaf n i =>
    cases b with
    | root => simp [toSum] at h
    | hub m => simp [toSum] at h
    | leaf m j =>
      have h' : (⟨n, i⟩ : Σ n : ℕ, Fin (bushSize n)) = ⟨m, j⟩ := by
        simpa [toSum] using h
      simp only [Sigma.mk.injEq] at h'
      obtain ⟨rfl, rfl⟩ := h'
      rfl

instance : Countable W := toSum_injective.countable

theorem bushSize_pos (n : ℕ) : 0 < bushSize n := by unfold bushSize; positivity

/-- The block index: `none` at the root and `some n` on the `n`-th hub and its leaves. -/
def blk : W → Option ℕ
  | root => none
  | hub n => some n
  | leaf n _ => some n

end W

/-! ## The kernel -/

/-- The fan weight of a vertex: `(1/2)^n` at the `n`-th hub, `0` elsewhere. -/
noncomputable def fanWeight (x : W) : ℝ :=
  match x with
  | W.hub n => (1 / 2 : ℝ) ^ n
  | _ => 0

/-- The pair of vertices is a bush edge (a hub and one of its own leaves, in either order). -/
def bushPair (x y : W) : Prop :=
  (∃ (n : ℕ) (i : Fin (bushSize n)), x = W.hub n ∧ y = W.leaf n i) ∨
    (∃ (n : ℕ) (i : Fin (bushSize n)), x = W.leaf n i ∧ y = W.hub n)

theorem bushPair_comm (x y : W) : bushPair x y = bushPair y x := by
  have h : bushPair x y ↔ bushPair y x := by
    unfold bushPair
    constructor <;> intro h
    · rcases h with ⟨n, i, h1, h2⟩ | ⟨n, i, h1, h2⟩
      · exact Or.inr ⟨n, i, h2, h1⟩
      · exact Or.inl ⟨n, i, h2, h1⟩
    · rcases h with ⟨n, i, h1, h2⟩ | ⟨n, i, h1, h2⟩
      · exact Or.inr ⟨n, i, h2, h1⟩
      · exact Or.inl ⟨n, i, h2, h1⟩
  exact propext h

/-- The intensity at an ordered pair: `(1/2)^n` on the fan edge `{root, hub n}`, `1` on a
bush edge, and `0` on every other pair (the diagonal included). -/
noncomputable def pairIntensity (x y : W) : ℝ :=
  (if ∃ n, x = W.root ∧ y = W.hub n then fanWeight y else 0) +
    (if ∃ n, y = W.root ∧ x = W.hub n then fanWeight x else 0) +
      (if bushPair x y then 1 else 0)

theorem pairIntensity_comm (x y : W) : pairIntensity x y = pairIntensity y x := by
  unfold pairIntensity
  rw [bushPair_comm]
  exact add_right_cancel_iff.mpr (add_comm _ _).symm

/-- The symmetric edge intensity of the model. -/
noncomputable def kernel : Sym2 W → ℝ :=
  Sym2.lift ⟨pairIntensity, pairIntensity_comm⟩

theorem kernel_mk (x y : W) : kernel s(x, y) = pairIntensity x y :=
  Sym2.lift_mk _ x y

theorem fanWeight_nonneg (x : W) : 0 ≤ fanWeight x := by
  cases x with
  | root => exact le_refl 0
  | hub n => exact pow_nonneg (by norm_num) n
  | leaf n i => exact le_refl 0

theorem kernel_nonneg (e : Sym2 W) : 0 ≤ kernel e := by
  obtain ⟨x, y⟩ := e
  rw [kernel_mk]
  unfold pairIntensity bushPair
  have hy := fanWeight_nonneg y
  have hx := fanWeight_nonneg x
  split_ifs <;> simp_all [fanWeight_nonneg]

/-! ### Values of the kernel on the support -/

theorem pairIntensity_root_hub (n : ℕ) :
    pairIntensity W.root (W.hub n) = (1 / 2 : ℝ) ^ n := by
  have h1 : ∃ m, W.root = W.root ∧ W.hub n = W.hub m := ⟨n, rfl, rfl⟩
  have h2 : ¬ ∃ m, W.hub n = W.root ∧ W.root = W.hub m := by
    rintro ⟨m, h, -⟩; exact W.noConfusion h
  have h3 : ¬ bushPair W.root (W.hub n) := by
    rintro (⟨k, j, h, -⟩ | ⟨k, j, h, -⟩) <;> exact W.noConfusion h
  unfold pairIntensity
  rw [ite_eq_left h1, ite_eq_right h2, ite_eq_right h3]
  simp [fanWeight]

theorem pairIntensity_hub_root (n : ℕ) :
    pairIntensity (W.hub n) W.root = (1 / 2 : ℝ) ^ n := by
  rw [pairIntensity_comm]; exact pairIntensity_root_hub n

theorem pairIntensity_hub_leaf (n : ℕ) (i : Fin (bushSize n)) :
    pairIntensity (W.hub n) (W.leaf n i) = 1 := by
  have h1 : ¬ ∃ m, W.hub n = W.root ∧ W.leaf n i = W.hub m := by
    rintro ⟨m, h, -⟩; exact W.noConfusion h
  have h2 : ¬ ∃ m, W.leaf n i = W.root ∧ W.hub n = W.hub m := by
    rintro ⟨m, h, -⟩; exact W.noConfusion h
  have h3 : bushPair (W.hub n) (W.leaf n i) := Or.inl ⟨n, i, rfl, rfl⟩
  unfold pairIntensity
  rw [ite_eq_right h1, ite_eq_right h2, ite_eq_left h3]
  simp

theorem pairIntensity_leaf_hub (n : ℕ) (i : Fin (bushSize n)) :
    pairIntensity (W.leaf n i) (W.hub n) = 1 := by
  rw [pairIntensity_comm]; exact pairIntensity_hub_leaf n i

/-- Every pair with nonzero intensity is a fan pair or a bush pair. -/
theorem support_cases {x y : W} (h : pairIntensity x y ≠ 0) :
    (∃ n, (x = W.root ∧ y = W.hub n) ∨ (y = W.root ∧ x = W.hub n)) ∨ bushPair x y := by
  by_contra hcon
  have e1 : ¬ (∃ n, x = W.root ∧ y = W.hub n) := by
    rintro ⟨n, h1, h2⟩; exact hcon (Or.inl ⟨n, Or.inl ⟨h1, h2⟩⟩)
  have e2 : ¬ (∃ n, y = W.root ∧ x = W.hub n) := by
    rintro ⟨n, h1, h2⟩; exact hcon (Or.inl ⟨n, Or.inr ⟨h1, h2⟩⟩)
  have e3 : ¬ bushPair x y := fun hb => hcon (Or.inr hb)
  exact h (by unfold pairIntensity; rw [ite_eq_right e1, ite_eq_right e2, ite_eq_right e3]; ring)


/-! ## The combinatorial structure of the open graph

Every point with positive intensity is either a fan edge `{root, hub n}` or a bush edge
`{hub n, leaf n i}`.  Hence, with `F = {n | {root, hub n} is open}`, an open path can only
leave the `n`-th bush towards the root through a fan edge `n ∈ F`.  Consequently, when `F`
is finite, every cluster is finite. -/

/-- The fan edge from the root to the `n`-th hub. -/
def fanEdge (n : ℕ) : Sym2 W := s(W.root, W.hub n)

/-- The set of hubs joined to the root in `ω`. -/
def fanSet (ω : Config W) : Set ℕ := {n | fanEdge n ∈ ω}

/-- The `n`-th block: the `n`-th hub together with its own leaves. -/
def block (n : ℕ) : Set W := {W.hub n} ∪ {x | ∃ i : Fin (bushSize n), x = W.leaf n i}

/-- The union of the root with the blocks of the hubs joined to the root. -/
def bigSet (ω : Config W) : Set W := {x | x = W.root ∨ ∃ n ∈ fanSet ω, x ∈ block n}

theorem block_finite (n : ℕ) : (block n).Finite := by
  have h : {x : W | ∃ i : Fin (bushSize n), x = W.leaf n i} = Set.range (W.leaf n) := by
    ext x
    exact ⟨fun ⟨i, hi⟩ => ⟨i, hi.symm⟩, fun ⟨i, hi⟩ => ⟨i, hi.symm⟩⟩
  refine Set.Finite.union (Set.finite_singleton _) ?_
  rw [h]
  exact Set.finite_range _

theorem bigSet_finite {ω : Config W} (hF : (fanSet ω).Finite) : (bigSet ω).Finite := by
  have h : bigSet ω = {W.root} ∪ ⋃ n ∈ fanSet ω, block n := by
    ext x
    simp [bigSet]
  rw [h]
  exact Set.Finite.union (Set.finite_singleton _) (hF.biUnion (fun n _ => block_finite n))

theorem exists_fanSet_of_mem_bigSet {ω : Config W} {x : W} (hx : x ∈ bigSet ω)
    (hne : x ≠ W.root) : ∃ n ∈ fanSet ω, x ∈ block n := by
  rcases hx with h | h
  · exact absurd h hne
  · exact h

theorem block_cases {n : ℕ} {x : W} (h : x ∈ block n) :
    x = W.hub n ∨ ∃ i : Fin (bushSize n), x = W.leaf n i := by
  rcases h with h | ⟨i, hi⟩
  · exact Or.inl h
  · exact Or.inr ⟨i, hi⟩

theorem hub_mem_block {n k : ℕ} : W.hub k ∈ block n ↔ k = n := by
  unfold block
  constructor
  · rintro (h | ⟨i, hi⟩)
    · exact W.hub.inj h
    · exact absurd hi (by intro hh; exact W.noConfusion hh)
  · rintro rfl
    exact Or.inl rfl

theorem leaf_mem_block {n k : ℕ} {j : Fin (bushSize k)} : W.leaf k j ∈ block n ↔ n = k := by
  unfold block
  constructor
  · rintro (h | ⟨i, hi⟩)
    · exact absurd h (by intro hh; exact W.noConfusion hh)
    · have h2 := W.leaf.inj hi
      exact h2.1.symm
  · rintro rfl
    exact Or.inr ⟨j, rfl⟩

theorem mem_block_of_not_mem_bigSet {ω : Config W} {x : W} (hx : x ≠ W.root)
    (hxS : x ∉ bigSet ω) : ∃ n, x ∈ block n ∧ n ∉ fanSet ω := by
  cases x with
  | root => exact absurd rfl hx
  | hub n =>
    refine ⟨n, Or.inl rfl, ?_⟩
    intro hn
    exact hxS (Or.inr ⟨n, hn, Or.inl rfl⟩)
  | leaf n i =>
    refine ⟨n, Or.inr ⟨i, rfl⟩, ?_⟩
    intro hn
    exact hxS (Or.inr ⟨n, hn, Or.inr ⟨i, rfl⟩⟩)

/-- The open edge structure: an open edge with a non-root endpoint in a block stays in that
block, unless it is the fan edge of that block. -/
theorem adj_cases {ω : Config W} (hsupp : ∀ e, kernel e = 0 → e ∉ ω) {a b : W}
    (hab : (openGraph ω).Adj a b) :
    (∃ n, (a = W.root ∧ b = W.hub n) ∨ (b = W.root ∧ a = W.hub n)) ∨ bushPair a b := by
  have hmem : s(a, b) ∈ ω := (openGraph_adj.1 hab).2
  have hker : kernel s(a, b) ≠ 0 := fun h0 => hsupp _ h0 hmem
  rw [kernel_mk] at hker
  exact support_cases hker

/-- The big set is closed under open edges. -/
theorem bigSet_closed {ω : Config W} (hsupp : ∀ e, kernel e = 0 → e ∉ ω) {a b : W}
    (ha : a ∈ bigSet ω) (hab : (openGraph ω).Adj a b) : b ∈ bigSet ω := by
  have hmem : s(a, b) ∈ ω := (openGraph_adj.1 hab).2
  rcases adj_cases hsupp hab with ⟨n, h | h⟩ | hb
  · obtain ⟨rfl, rfl⟩ := h
    exact Or.inr ⟨n, hmem, Or.inl rfl⟩
  · obtain ⟨rfl, rfl⟩ := h
    exact Or.inl rfl
  · rcases hb with ⟨n, i, rfl, rfl⟩ | ⟨n, i, rfl, rfl⟩
    · obtain ⟨m, hm, hblk⟩ := exists_fanSet_of_mem_bigSet ha (by simp)
      have hmn : n = m := hub_mem_block.1 hblk
      exact Or.inr ⟨n, hmn ▸ hm, Or.inr ⟨i, rfl⟩⟩
    · obtain ⟨m, hm, hblk⟩ := exists_fanSet_of_mem_bigSet ha (by simp)
      have hmn : m = n := leaf_mem_block.1 hblk
      exact Or.inr ⟨n, hmn ▸ hm, Or.inl rfl⟩

/-- Each block is closed under open edges whose block index is not joined to the root. -/
theorem block_closed {ω : Config W} (hsupp : ∀ e, kernel e = 0 → e ∉ ω) {n : ℕ}
    (hn : n ∉ fanSet ω) {a b : W} (ha : a ∈ block n) (hab : (openGraph ω).Adj a b) :
    b ∈ block n := by
  have hmem : s(a, b) ∈ ω := (openGraph_adj.1 hab).2
  rcases adj_cases hsupp hab with ⟨m, h | h⟩ | hb
  · obtain ⟨rfl, rfl⟩ := h
    rcases block_cases ha with h' | ⟨i, h'⟩ <;> exact absurd h' (by intro hh; exact W.noConfusion hh)
  · obtain ⟨rfl, rfl⟩ := h
    have hmn : m = n := hub_mem_block.1 ha
    subst hmn
    have hmem' : fanEdge m ∈ ω := by
      rw [fanEdge]
      exact Sym2.eq_swap ▸ hmem
    exact absurd hmem' hn
  · rcases hb with ⟨m, i, rfl, rfl⟩ | ⟨m, i, rfl, rfl⟩
    · have hmn : m = n := hub_mem_block.1 ha
      subst hmn
      exact Or.inr ⟨i, rfl⟩
    · have hmn : n = m := leaf_mem_block.1 ha
      subst hmn
      exact Or.inl rfl

theorem mem_bigSet_of_reachable {ω : Config W} (hsupp : ∀ e, kernel e = 0 → e ∉ ω) {a b : W}
    (ha : a ∈ bigSet ω) (hab : (openGraph ω).Reachable a b) : b ∈ bigSet ω := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at hab
  induction hab with
  | refl => exact ha
  | tail _ hstep ih => exact bigSet_closed hsupp ih hstep

theorem mem_block_of_reachable {ω : Config W} (hsupp : ∀ e, kernel e = 0 → e ∉ ω) {n : ℕ}
    (hn : n ∉ fanSet ω) {a b : W} (ha : a ∈ block n) (hab : (openGraph ω).Reachable a b) :
    b ∈ block n := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at hab
  induction hab with
  | refl => exact ha
  | tail _ hstep ih => exact block_closed hsupp hn ih hstep

/-- **If only finitely many hubs are joined to the root, every cluster is finite.** -/
theorem cluster_finite_of_fanSet_finite {ω : Config W}
    (hsupp : ∀ e, kernel e = 0 → e ∉ ω) (hF : (fanSet ω).Finite) (x : W) :
    (PercLib.CriticalLRP.cluster ω x).Finite := by
  by_cases hxS : x ∈ bigSet ω
  · exact (bigSet_finite hF).subset (fun y hy => mem_bigSet_of_reachable hsupp hxS hy)
  · obtain ⟨n, hxb, hn⟩ := mem_block_of_not_mem_bigSet (ω := ω) (x := x)
      (by intro hx; exact hxS (Or.inl hx)) hxS
    exact (block_finite n).subset (fun y hy => mem_block_of_reachable hsupp hn hxb hy)


/-! ## The law: absence of an infinite cluster at every parameter -/

/-- The probability that a single edge is open. -/
theorem edgeMeasure_single (π : Sym2 W → unitInterval) (e : Sym2 W) :
    (edgeMeasure π) {ω : Config W | e ∈ ω} = ↑(unitInterval.toNNReal (π e)) := by
  have h := edgeMeasure_cylinder π ({e} : Finset (Sym2 W))
  have hset : {ω : Config W | e ∈ ω}
      = {ω : Config W | ∀ f ∈ ({e} : Finset (Sym2 W)), f ∈ ω} := by
    ext ω
    simp
  rw [hset, h]
  simp

/-- The `ℝ≥0∞`-valued edge probability of a unit-interval profile. -/
theorem coe_eq_ofReal (q : unitInterval) :
    ((unitInterval.toNNReal q : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal ((q : unitInterval) : ℝ) := by
  rw [← ENNReal.ofReal_coe_nnreal]
  congr 1

/-- Almost every configuration only opens edges of positive intensity. -/
theorem ae_support (β : NNReal) :
    ∀ᵐ ω ∂longRangeMeasure kernel kernel_nonneg β,
      ∀ e : Sym2 W, kernel e = 0 → e ∉ ω := by
  have hμ : longRangeMeasure kernel kernel_nonneg β
      = edgeMeasure (bernoulliEdgeProb kernel kernel_nonneg β) := rfl
  rw [hμ, ae_all_iff]
  intro e
  rw [ae_iff]
  have hset : {ω : Config W | ¬ (kernel e = 0 → e ∉ ω)}
      = {ω : Config W | kernel e = 0 ∧ e ∈ ω} := by
    ext ω
    simp only [Set.mem_ofPred_eq]
    tauto
  rw [hset]
  by_cases hk : kernel e = 0
  · have hset2 : {ω : Config W | kernel e = 0 ∧ e ∈ ω} = {ω : Config W | e ∈ ω} := by
      ext ω
      simp [hk]
    rw [hset2, edgeMeasure_single, coe_eq_ofReal]
    have hreal : ((bernoulliEdgeProb kernel kernel_nonneg β e : unitInterval) : ℝ) = 0 := by
      rw [bernoulliEdgeProb_coe, hk, mul_zero, neg_zero, Real.exp_zero, sub_self]
    rw [hreal]
    simp
  · have hset2 : {ω : Config W | kernel e = 0 ∧ e ∈ ω} = (∅ : Set (Config W)) := by
      ext ω
      simp [hk]
    rw [hset2]
    simp

theorem one_sub_exp_neg_le_self {x : ℝ} (_hx : 0 ≤ x) :
    1 - Real.exp (-x) ≤ x := by
  have h : -x + 1 ≤ Real.exp (-x) := Real.add_one_le_exp (-x)
  linarith

/-- The fan intensities are summable, so only finitely many fan edges are open. -/
theorem measure_fanSet_infinite (β : NNReal) :
    (longRangeMeasure kernel kernel_nonneg β) {ω : Config W | (fanSet ω).Infinite} = 0 := by
  have hμ : longRangeMeasure kernel kernel_nonneg β
      = edgeMeasure (bernoulliEdgeProb kernel kernel_nonneg β) := rfl
  set p : ℕ → ℝ≥0∞ := fun n =>
    ↑(unitInterval.toNNReal (bernoulliEdgeProb kernel kernel_nonneg β (fanEdge n))) with hpdef
  have hval : ∀ n, ((bernoulliEdgeProb kernel kernel_nonneg β (fanEdge n) : unitInterval) : ℝ)
      = 1 - Real.exp (-((β : ℝ) * (1 / 2 : ℝ) ^ n)) := by
    intro n
    rw [bernoulliEdgeProb_coe, fanEdge, kernel_mk, pairIntensity_root_hub]
  have hpbound : ∀ n, p n ≤ (β : ℝ≥0∞) * (1 / 2 : ℝ≥0∞) ^ n := by
    intro n
    have hb0 : (0 : ℝ) ≤ (β : ℝ) := β.coe_nonneg
    have hx0 : (0 : ℝ) ≤ (β : ℝ) * (1 / 2 : ℝ) ^ n := by positivity
    have hle := one_sub_exp_neg_le_self hx0
    have hpv : p n = ↑(unitInterval.toNNReal (bernoulliEdgeProb kernel kernel_nonneg β (fanEdge n))) :=
      rfl
    rw [hpv, coe_eq_ofReal, hval n]
    calc ENNReal.ofReal (1 - Real.exp (-((β : ℝ) * (1 / 2 : ℝ) ^ n)))
        ≤ ENNReal.ofReal ((β : ℝ) * (1 / 2 : ℝ) ^ n) := ENNReal.ofReal_le_ofReal hle
      _ = (β : ℝ≥0∞) * (1 / 2 : ℝ≥0∞) ^ n := by
          rw [ENNReal.ofReal_mul hb0, ← ENNReal.ofReal_coe_nnreal]
          congr 1
          rw [ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 1 / 2)]
          congr 1
          rw [show (1 / 2 : ℝ) = (((1 / 2 : ℝ≥0) : ℝ)) by norm_num,
            ENNReal.ofReal_coe_nnreal]
          simp
  have hsum_ne_top : (∑' n, p n) ≠ ⊤ := by
    have hle : (∑' n, p n) ≤ ∑' n, ((β : ℝ≥0∞) * (1 / 2 : ℝ≥0∞) ^ n) :=
      ENNReal.tsum_le_tsum hpbound
    have hgeom : (∑' n, ((β : ℝ≥0∞) * (1 / 2 : ℝ≥0∞) ^ n)) ≠ ⊤ := by
      rw [ENNReal.tsum_mul_left]
      refine ENNReal.mul_ne_top ENNReal.coe_ne_top ?_
      rw [ENNReal.tsum_geometric]
      exact ENNReal.inv_ne_top.2 (by norm_num)
    exact ne_top_of_le_ne_top hgeom hle
  have hkey : ∀ N : ℕ,
      (longRangeMeasure kernel kernel_nonneg β) {ω : Config W | (fanSet ω).Infinite}
        ≤ ∑' k : ℕ, p (k + (N + 1)) := by
    intro N
    rw [hμ]
    have hmono : (edgeMeasure (bernoulliEdgeProb kernel kernel_nonneg β))
          {ω : Config W | (fanSet ω).Infinite}
        ≤ (edgeMeasure (bernoulliEdgeProb kernel kernel_nonneg β))
          (⋃ k : ℕ, {ω : Config W | fanEdge (k + (N + 1)) ∈ ω}) := by
      refine measure_mono ?_
      intro ω hω
      obtain ⟨n, hmem, hn⟩ := Set.Infinite.exists_gt hω N
      obtain ⟨k, rfl⟩ : ∃ k, n = k + (N + 1) := ⟨n - (N + 1), by omega⟩
      exact Set.mem_iUnion.2 ⟨k, hmem⟩
    refine hmono.trans ?_
    refine (measure_iUnion_le _).trans (le_of_eq ?_)
    refine tsum_congr fun k => ?_
    simp only [edgeMeasure_single, coe_eq_ofReal, hpdef]
  have htail : Filter.Tendsto (fun N => ∑' k : ℕ, p (k + N)) Filter.atTop (nhds 0) :=
    ENNReal.tendsto_sum_nat_add p hsum_ne_top
  have htail' : Filter.Tendsto (fun N => ∑' k : ℕ, p (k + (N + 1))) Filter.atTop (nhds 0) :=
    htail.comp (Filter.tendsto_add_atTop_nat 1)
  exact le_antisymm
    (le_of_tendsto_of_tendsto tendsto_const_nhds htail' (Filter.Eventually.of_forall hkey))
    zero_le

/-- **No infinite cluster at any parameter.** -/
theorem infiniteClusterProb_eq_zero (β : NNReal) :
    infiniteClusterProb kernel kernel_nonneg β = 0 := by
  rw [infiniteClusterProb]
  refine measure_mono_null ?_ (measure_union_null (ae_support β) (measure_fanSet_infinite β))
  rintro ω ⟨v, hv⟩
  simp only [Set.mem_union, Set.mem_ofPred_eq]
  by_cases hfin : (fanSet ω).Infinite
  · exact Or.inr hfin
  · refine Or.inl ?_
    intro hsupp
    have hfin' : (fanSet ω).Finite := by
      by_contra h
      exact hfin h
    exact (inInfiniteCluster_iff_infinite ω v).1 hv
      (cluster_finite_of_fanSet_finite (ω := ω) hsupp hfin' v)

/-- The percolation set of the model is empty. -/
theorem criticalBetaSet_eq_empty : criticalBetaSet kernel kernel_nonneg = ∅ := by
  ext β
  simp only [Set.mem_empty_iff_false, iff_false]
  rw [mem_criticalBetaSet_iff, infiniteClusterProb_eq_zero]
  exact zero_ne_one


/-! ## The first moment is infinite at every positive parameter -/

theorem div_one_add_le_one_sub_exp_neg {y : ℝ} (hy : 0 ≤ y) :
    y / (1 + y) ≤ 1 - Real.exp (-y) := by
  have hpos : (0 : ℝ) < 1 + y := by linarith
  have hle : (1 + y) ≤ Real.exp y := by
    simpa [add_comm] using Real.add_one_le_exp y
  have h1 : Real.exp (-y) ≤ (1 + y)⁻¹ := by
    simpa [Real.exp_neg, one_div] using one_div_le_one_div_of_le hpos hle
  have h2 : 1 - (1 + y)⁻¹ = y / (1 + y) := by
    field_simp
    ring
  linarith

/-- The probability that the `i`-th leaf of the `n`-th bush is connected to the root is at
least the product of the two edge probabilities. -/
theorem tau_leaf_ge (β : NNReal) (n : ℕ) (i : Fin (bushSize n)) :
    ENNReal.ofReal ((1 - Real.exp (-((β : ℝ) * (2 : ℝ)⁻¹ ^ n))) *
        (1 - Real.exp (-(β : ℝ))))
      ≤ PercLib.Percolation.Bond.tau (bernoulliEdgeProb kernel kernel_nonneg β) W.root
          (W.leaf n i) := by
  set π := bernoulliEdgeProb kernel kernel_nonneg β with hπdef
  have hne : fanEdge n ≠ s(W.hub n, W.leaf n i) := by
    intro h
    rw [fanEdge] at h
    have hp : s((W.root, W.hub n).1, (W.root, W.hub n).2)
        = s((W.hub n, W.leaf n i).1, (W.hub n, W.leaf n i).2) := h
    have h' : ((W.root, W.hub n) : W × W) = (W.hub n, W.leaf n i) ∨
        ((W.root, W.hub n) : W × W) = (W.hub n, W.leaf n i).swap :=
      Sym2.mk_eq_mk_iff.1 hp
    rcases h' with h' | h'
    · exact W.noConfusion (congrArg Prod.fst h')
    · exact W.noConfusion (congrArg Prod.fst h')
  have hset : {ω : Config W | fanEdge n ∈ ω ∧ s(W.hub n, W.leaf n i) ∈ ω}
      = {ω : Config W | ∀ e ∈ ({fanEdge n, s(W.hub n, W.leaf n i)} : Finset (Sym2 W)), e ∈ ω} := by
    ext ω
    simp
  have hcyl : (edgeMeasure π) {ω : Config W | fanEdge n ∈ ω ∧ s(W.hub n, W.leaf n i) ∈ ω}
      = ENNReal.ofReal ((1 - Real.exp (-((β : ℝ) * (2 : ℝ)⁻¹ ^ n))) *
          (1 - Real.exp (-(β : ℝ)))) := by
    have hprod : (edgeMeasure π) {ω : Config W | fanEdge n ∈ ω ∧ s(W.hub n, W.leaf n i) ∈ ω}
        = ↑(unitInterval.toNNReal (π (fanEdge n))) *
            ↑(unitInterval.toNNReal (π s(W.hub n, W.leaf n i))) := by
      rw [hset, edgeMeasure_cylinder, Finset.prod_insert (by simp [hne]), Finset.prod_singleton]
    have hv1 : ((π (fanEdge n) : unitInterval) : ℝ)
        = 1 - Real.exp (-((β : ℝ) * (2 : ℝ)⁻¹ ^ n)) := by
      rw [bernoulliEdgeProb_coe, fanEdge, kernel_mk, pairIntensity_root_hub]
      norm_num
    have hv2 : ((π s(W.hub n, W.leaf n i) : unitInterval) : ℝ) = 1 - Real.exp (-(β : ℝ)) := by
      rw [bernoulliEdgeProb_coe, kernel_mk, pairIntensity_hub_leaf, mul_one]
    rw [hprod]
    calc ↑(unitInterval.toNNReal (π (fanEdge n))) *
          ↑(unitInterval.toNNReal (π s(W.hub n, W.leaf n i)))
        = ENNReal.ofReal ((π (fanEdge n) : unitInterval) : ℝ) *
            ENNReal.ofReal ((π s(W.hub n, W.leaf n i) : unitInterval) : ℝ) := by
          rw [coe_eq_ofReal, coe_eq_ofReal]
      _ = ENNReal.ofReal (((π (fanEdge n) : unitInterval) : ℝ) *
            ((π s(W.hub n, W.leaf n i) : unitInterval) : ℝ)) := by
          exact (ENNReal.ofReal_mul
            (p := ((π (fanEdge n) : unitInterval) : ℝ))
            (q := ((π s(W.hub n, W.leaf n i) : unitInterval) : ℝ))
            (π (fanEdge n)).2.1).symm
      _ = ENNReal.ofReal ((1 - Real.exp (-((β : ℝ) * (2 : ℝ)⁻¹ ^ n))) *
            (1 - Real.exp (-(β : ℝ)))) := by rw [hv1, hv2]
  have hsub : {ω : Config W | fanEdge n ∈ ω ∧ s(W.hub n, W.leaf n i) ∈ ω}
      ⊆ PercLib.Percolation.Bond.conn W.root (W.leaf n i) := by
    rintro ω ⟨h1, h2⟩
    exact ((openGraph_adj.2 ⟨by simp, h1⟩).reachable).trans
      ((openGraph_adj.2 ⟨by simp, h2⟩).reachable)
  rw [← hcyl]
  exact measure_mono hsub

/-- The threshold from which a single bush contributes at least its index to the moment. -/
theorem exists_threshold (β : NNReal) (hβ : 0 < β) :
    ∃ n₁ : ℕ, ∀ n : ℕ, n₁ ≤ n →
      1 ≤ (2 : ℝ) ^ n * ((β : ℝ) * (1 - Real.exp (-(β : ℝ))) / (1 + (β : ℝ))) := by
  have hβR : (0 : ℝ) < (β : ℝ) := by exact_mod_cast hβ
  have hqR : (0 : ℝ) < 1 - Real.exp (-(β : ℝ)) := by
    have hlt : Real.exp (-(β : ℝ)) < 1 := by
      rw [Real.exp_lt_one_iff]
      linarith
    linarith
  have hc : (0 : ℝ) < (β : ℝ) * (1 - Real.exp (-(β : ℝ))) / (1 + (β : ℝ)) := by positivity
  have ht : Filter.Tendsto (fun n : ℕ => (2 : ℝ) ^ n) Filter.atTop Filter.atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  obtain ⟨b, hb⟩ := (ht.eventually_ge_atTop
    (1 / ((β : ℝ) * (1 - Real.exp (-(β : ℝ))) / (1 + (β : ℝ))))).exists
  refine ⟨b, fun n hn => ?_⟩
  have h2n : (2 : ℝ) ^ b ≤ (2 : ℝ) ^ n := pow_le_pow_right₀ (by norm_num) hn
  have h1 : 1 / ((β : ℝ) * (1 - Real.exp (-(β : ℝ))) / (1 + (β : ℝ))) ≤ (2 : ℝ) ^ n :=
    le_trans hb h2n
  rw [div_le_iff₀ hc] at h1
  exact h1

/-- Each bush alone contributes at least its index to the first moment. -/
theorem le_sum_tau_leaf (β : NNReal) (hβ : 0 < β) {n : ℕ}
    (hn : 1 ≤ (2 : ℝ) ^ n * ((β : ℝ) * (1 - Real.exp (-(β : ℝ))) / (1 + (β : ℝ)))) :
    (n : ℝ≥0∞) ≤ ∑ i : Fin (bushSize n),
      PercLib.Percolation.Bond.tau (bernoulliEdgeProb kernel kernel_nonneg β) W.root (W.leaf n i) := by
  set π := bernoulliEdgeProb kernel kernel_nonneg β with hπdef
  have hβR : (0 : ℝ) < (β : ℝ) := by exact_mod_cast hβ
  have hqR : (0 : ℝ) < 1 - Real.exp (-(β : ℝ)) := by
    have hlt : Real.exp (-(β : ℝ)) < 1 := by
      rw [Real.exp_lt_one_iff]
      linarith
    linarith
  have hq0 : (0 : ℝ) ≤ 1 - Real.exp (-(β : ℝ)) := le_of_lt hqR
  have hp : ((β : ℝ) / (1 + (β : ℝ))) * ((2 : ℝ)⁻¹) ^ n
      ≤ 1 - Real.exp (-((β : ℝ) * (2 : ℝ)⁻¹ ^ n)) := by
    have hy : 0 ≤ (β : ℝ) * ((2 : ℝ)⁻¹) ^ n := by positivity
    have h := div_one_add_le_one_sub_exp_neg hy
    have h2 : ((2 : ℝ)⁻¹) ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have hle : (β : ℝ) * ((2 : ℝ)⁻¹) ^ n ≤ (β : ℝ) := by nlinarith [β.coe_nonneg]
    have h1 : (0 : ℝ) < 1 + (β : ℝ) * ((2 : ℝ)⁻¹) ^ n := by positivity
    have h2' : (0 : ℝ) < 1 + (β : ℝ) := by linarith
    have h3 : ((β : ℝ) / (1 + (β : ℝ))) * ((2 : ℝ)⁻¹) ^ n
        = ((β : ℝ) * ((2 : ℝ)⁻¹) ^ n) / (1 + (β : ℝ)) := by
      rw [div_mul_eq_mul_div]
    have h4 : ((β : ℝ) * ((2 : ℝ)⁻¹) ^ n) / (1 + (β : ℝ))
        ≤ ((β : ℝ) * ((2 : ℝ)⁻¹) ^ n) / (1 + (β : ℝ) * ((2 : ℝ)⁻¹) ^ n) := by
      gcongr
    linarith
  have hbush : ((bushSize n : ℕ) : ℝ) = ((n : ℝ) + 1) * (4 : ℝ) ^ n := by
    rw [bushSize]
    push_cast
    ring
  have hgeom : (4 : ℝ) ^ n * ((2 : ℝ)⁻¹) ^ n = (2 : ℝ) ^ n := by
    rw [← mul_pow]
    norm_num
  have hprod : ((bushSize n : ℕ) : ℝ) * (((β : ℝ) / (1 + (β : ℝ))) * ((2 : ℝ)⁻¹) ^ n)
        * (1 - Real.exp (-(β : ℝ)))
      = ((n : ℝ) + 1) * ((2 : ℝ) ^ n * ((β : ℝ) * (1 - Real.exp (-(β : ℝ))) / (1 + (β : ℝ)))) := by
    rw [hbush, ← hgeom]
    field_simp
  have hmain : (n : ℝ) ≤ ((bushSize n : ℕ) : ℝ) *
      ((1 - Real.exp (-((β : ℝ) * (2 : ℝ)⁻¹ ^ n))) * (1 - Real.exp (-(β : ℝ)))) := by
    have hstep : ((n : ℝ) + 1) * 1 ≤ ((n : ℝ) + 1) *
        ((2 : ℝ) ^ n * ((β : ℝ) * (1 - Real.exp (-(β : ℝ))) / (1 + (β : ℝ)))) :=
      mul_le_mul_of_nonneg_left hn (by positivity)
    calc (n : ℝ) ≤ ((n : ℝ) + 1) * 1 := by nlinarith
      _ ≤ ((n : ℝ) + 1) * ((2 : ℝ) ^ n * ((β : ℝ) * (1 - Real.exp (-(β : ℝ))) / (1 + (β : ℝ)))) := hstep
      _ = ((bushSize n : ℕ) : ℝ) * (((β : ℝ) / (1 + (β : ℝ))) * ((2 : ℝ)⁻¹) ^ n)
            * (1 - Real.exp (-(β : ℝ))) := hprod.symm
      _ ≤ ((bushSize n : ℕ) : ℝ) * (1 - Real.exp (-((β : ℝ) * (2 : ℝ)⁻¹ ^ n)))
            * (1 - Real.exp (-(β : ℝ))) := by
          have hb0 : (0 : ℝ) ≤ ((bushSize n : ℕ) : ℝ) := by positivity
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp hb0) hq0
      _ = ((bushSize n : ℕ) : ℝ) *
            ((1 - Real.exp (-((β : ℝ) * (2 : ℝ)⁻¹ ^ n))) * (1 - Real.exp (-(β : ℝ)))) := by ring
  calc (n : ℝ≥0∞) = ENNReal.ofReal (n : ℝ) := (ENNReal.ofReal_natCast n).symm
    _ ≤ ENNReal.ofReal (((bushSize n : ℕ) : ℝ) *
        ((1 - Real.exp (-((β : ℝ) * (2 : ℝ)⁻¹ ^ n))) * (1 - Real.exp (-(β : ℝ))))) :=
        ENNReal.ofReal_le_ofReal hmain
    _ = ∑ _i : Fin (bushSize n), ENNReal.ofReal ((1 - Real.exp (-((β : ℝ) * (2 : ℝ)⁻¹ ^ n))) *
        (1 - Real.exp (-(β : ℝ)))) := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast, Finset.sum_const,
          Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ ≤ ∑ i : Fin (bushSize n),
        PercLib.Percolation.Bond.tau π W.root (W.leaf n i) :=
        Finset.sum_le_sum (fun i _ => tau_leaf_ge β n i)

/-- The finite family of leaves of one bush embeds into `W`, so its finite sum is at most
the global `tsum`.  This is the step that lets a bush bound the ambient moment. -/
theorem sum_leaf_le_tsum (π : Sym2 W → unitInterval) (n : ℕ) :
    ∑ i : Fin (bushSize n), PercLib.Percolation.Bond.tau π W.root (W.leaf n i)
      ≤ ∑' y : W, PercLib.Percolation.Bond.tau π W.root y := by
  have hinj : Function.Injective (W.leaf n) := by
    intro i j h
    exact eq_of_heq (W.leaf.inj h).2
  have himg : ∑ y ∈ (Finset.univ.image (W.leaf n)),
      PercLib.Percolation.Bond.tau π W.root y
      = ∑ i : Fin (bushSize n), PercLib.Percolation.Bond.tau π W.root (W.leaf n i) := by
    rw [Finset.sum_image (fun i _ j _ h => hinj h)]
  rw [← himg]
  exact ENNReal.sum_le_tsum _

/-- **The root's first moment is infinite at every positive parameter.** -/
theorem lintegral_clusterVol_root_eq_top (β : NNReal) (hβ : 0 < β) :
    ∫⁻ ω, clusterVol ω W.root ∂longRangeMeasure kernel kernel_nonneg β = ⊤ := by
  set π := bernoulliEdgeProb kernel kernel_nonneg β with hπdef
  have hμ : longRangeMeasure kernel kernel_nonneg β = edgeMeasure π := rfl
  obtain ⟨n₁, hn₁⟩ := exists_threshold β hβ
  rw [hμ]
  change PercLib.Percolation.Bond.chi π W.root = ⊤
  rw [PercLib.Percolation.Bond.chi_eq_tsum_tau]
  have key : ∀ N : ℕ, (N : ℝ≥0∞) ≤ ∑' y : W, PercLib.Percolation.Bond.tau π W.root y := by
    intro N
    have h := le_sum_tau_leaf β hβ (n := n₁ + N) (hn₁ (n₁ + N) (Nat.le_add_right n₁ N))
    have hN : (N : ℝ≥0∞) ≤ ((n₁ + N : ℕ) : ℝ≥0∞) := by
      exact_mod_cast Nat.le_add_left N n₁
    exact hN.trans (h.trans (sum_leaf_le_tsum π (n₁ + N)))
  refine eq_top_iff.mpr ?_
  calc ⊤ = (⨆ N : ℕ, (N : ℝ≥0∞)) := by rw [ENNReal.iSup_natCast]
    _ ≤ ∑' y : W, PercLib.Percolation.Bond.tau π W.root y := iSup_le key

/-- **A countable symmetric kernel with an empty percolation set and infinite root first
moment at every positive parameter.** -/
theorem exists_percolation_empty_firstMoment_top :
    ∃ (J : Sym2 W → ℝ) (hJ : ∀ e, 0 ≤ J e),
      (∀ β : NNReal, infiniteClusterProb J hJ β = 0) ∧
        (∀ β : NNReal, 0 < β →
          ∫⁻ ω, clusterVol ω W.root ∂longRangeMeasure J hJ β = ⊤) :=
  ⟨kernel, kernel_nonneg, infiniteClusterProb_eq_zero,
    fun β hβ => lintegral_clusterVol_root_eq_top β hβ⟩

/-- The same kernel has an empty percolation set. -/
theorem exists_empty_criticalBetaSet :
    ∃ (J : Sym2 W → ℝ) (hJ : ∀ e, 0 ≤ J e), criticalBetaSet J hJ = ∅ :=
  ⟨kernel, kernel_nonneg, criticalBetaSet_eq_empty⟩


/-! ## The rows are finite but not uniformly bounded

The intensity rows are the quantity the paper bounds uniformly (`sup_v ∑_w J(v,w) ≤ M < ∞`
in `PowerLawHighTemp`, and translation invariance in Lemma I.4.9).  In this model the row at
the `n`-th hub contains the whole `n`-th bush: `bushSize n = (n+1) * 4^n` leaves of intensity
`1`, plus the fan edge of intensity `2^{-n}`.  So the rows are finite at every vertex but
unbounded, which is exactly why the model is not a counterexample to the paper's theorems
but shows that their uniformity hypothesis cannot be dropped. -/

theorem leaf_injective (n : ℕ) : Function.Injective (W.leaf n) := by
  intro i j h
  exact eq_of_heq (W.leaf.inj h).2

theorem kernel_hub_leaf (n : ℕ) (i : Fin (bushSize n)) :
    kernel s(W.hub n, W.leaf n i) = 1 := by
  rw [kernel_mk, pairIntensity_hub_leaf]

theorem nat_le_bushSize (n : ℕ) : n ≤ bushSize n := by
  have h1 : 0 < 4 ^ n := pow_pos (by norm_num) n
  rw [bushSize]
  calc n ≤ n + 1 := Nat.le_succ n
    _ ≤ (n + 1) * 4 ^ n := Nat.le_mul_of_pos_right _ h1

/-- The row bound at the `n`-th hub is at least the size of its bush. -/
theorem hub_row_ge (n : ℕ) :
    (bushSize n : ℝ≥0∞) ≤
      ∑' w : W, (if w = W.hub n then 0 else ENNReal.ofReal (kernel s(W.hub n, w))) := by
  have hterm : ∀ i : Fin (bushSize n),
      (if W.leaf n i = W.hub n then 0
          else ENNReal.ofReal (kernel s(W.hub n, W.leaf n i))) = 1 := by
    intro i
    rw [ite_eq_right (by simp), kernel_hub_leaf]
    simp
  have himg : ∑ w ∈ (Finset.univ.image (W.leaf n)),
      (if w = W.hub n then 0 else ENNReal.ofReal (kernel s(W.hub n, w)))
      = ∑ i : Fin (bushSize n),
        (if W.leaf n i = W.hub n then 0
          else ENNReal.ofReal (kernel s(W.hub n, W.leaf n i))) := by
    rw [Finset.sum_image (fun i _ j _ h => leaf_injective n h)]
  calc (bushSize n : ℝ≥0∞) = ∑ _i : Fin (bushSize n), (1 : ℝ≥0∞) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    _ = ∑ i : Fin (bushSize n),
        (if W.leaf n i = W.hub n then 0
          else ENNReal.ofReal (kernel s(W.hub n, W.leaf n i))) :=
        Finset.sum_congr rfl (fun i _ => (hterm i).symm)
    _ = ∑ w ∈ (Finset.univ.image (W.leaf n)),
        (if w = W.hub n then 0 else ENNReal.ofReal (kernel s(W.hub n, w))) := himg.symm
    _ ≤ ∑' w : W, (if w = W.hub n then 0 else ENNReal.ofReal (kernel s(W.hub n, w))) :=
        ENNReal.sum_le_tsum _

theorem exists_bushSize_ge (M : ℝ≥0∞) (hM : M ≠ ⊤) :
    ∃ n : ℕ, M ≤ (bushSize n : ℝ≥0∞) := by
  refine ⟨⌈M.toReal⌉₊, ?_⟩
  calc M = ENNReal.ofReal M.toReal := (ENNReal.ofReal_toReal hM).symm
    _ ≤ ENNReal.ofReal ((⌈M.toReal⌉₊ : ℕ) : ℝ) := ENNReal.ofReal_le_ofReal (Nat.le_ceil _)
    _ = ((⌈M.toReal⌉₊ : ℕ) : ℝ≥0∞) := ENNReal.ofReal_natCast _
    _ ≤ ((bushSize ⌈M.toReal⌉₊ : ℕ) : ℝ≥0∞) := by
        exact_mod_cast nat_le_bushSize ⌈M.toReal⌉₊

/-- **The intensity rows are not uniformly bounded**: every finite bound is exceeded at some
hub.  In particular the paper's hypothesis `sup_v ∑_w J(v,w) < ∞` fails for this kernel. -/
theorem rows_unbounded (M : ℝ≥0∞) (hM : M ≠ ⊤) :
    ∃ v : W, M ≤ ∑' w : W, (if w = v then 0 else ENNReal.ofReal (kernel s(v, w))) := by
  obtain ⟨n, hn⟩ := exists_bushSize_ge M hM
  exact ⟨W.hub n, hn.trans (hub_row_ge n)⟩


/-! ## The refuted general inference, in explicit form -/

/-- **The tempting general inference is false**: one cannot deduce finite first moments at
every vertex from the absence of an infinite cluster in the general countable-product
framework.  No uniformity of the intensity rows is available in the hypothesis. -/
theorem not_forall_infiniteClusterProb_eq_zero_imp_lintegral_ne_top :
    ¬ ∀ (V : Type) [Countable V] (J : Sym2 V → ℝ) (hJ : ∀ e, 0 ≤ J e) (β : NNReal),
        infiniteClusterProb J hJ β = 0 →
          ∀ v : V, ∫⁻ ω, clusterVol ω v ∂longRangeMeasure J hJ β ≠ ⊤ := by
  intro h
  have h0 := h W kernel kernel_nonneg 1 (infiniteClusterProb_eq_zero 1) W.root
  have htop := lintegral_clusterVol_root_eq_top 1 (by norm_num)
  exact h0 htop

/-- The same refutation for the stronger hypothesis "no infinite cluster at *every*
parameter". -/
theorem not_forall_infiniteClusterProb_all_eq_zero_imp_lintegral_ne_top :
    ¬ ∀ (V : Type) [Countable V] (J : Sym2 V → ℝ) (hJ : ∀ e, 0 ≤ J e),
        (∀ β : NNReal, infiniteClusterProb J hJ β = 0) →
          ∀ (β : NNReal), 0 < β →
            ∀ v : V, ∫⁻ ω, clusterVol ω v ∂longRangeMeasure J hJ β ≠ ⊤ := by
  intro h
  have h0 := h W kernel kernel_nonneg infiniteClusterProb_eq_zero 1 (by norm_num) W.root
  have htop := lintegral_clusterVol_root_eq_top 1 (by norm_num)
  exact h0 htop

end PercLib.CriticalLRP.BushRefute



#print axioms PercLib.CriticalLRP.BushRefute.cluster_finite_of_fanSet_finite
#print axioms PercLib.CriticalLRP.BushRefute.infiniteClusterProb_eq_zero
#print axioms PercLib.CriticalLRP.BushRefute.criticalBetaSet_eq_empty
#print axioms PercLib.CriticalLRP.BushRefute.tau_leaf_ge
#print axioms PercLib.CriticalLRP.BushRefute.exists_threshold
#print axioms PercLib.CriticalLRP.BushRefute.le_sum_tau_leaf
#print axioms PercLib.CriticalLRP.BushRefute.sum_leaf_le_tsum
#print axioms PercLib.CriticalLRP.BushRefute.lintegral_clusterVol_root_eq_top
#print axioms PercLib.CriticalLRP.BushRefute.exists_percolation_empty_firstMoment_top
#print axioms PercLib.CriticalLRP.BushRefute.exists_empty_criticalBetaSet
#print axioms PercLib.CriticalLRP.BushRefute.hub_row_ge
#print axioms PercLib.CriticalLRP.BushRefute.rows_unbounded
#print axioms PercLib.CriticalLRP.BushRefute.not_forall_infiniteClusterProb_eq_zero_imp_lintegral_ne_top
#print axioms PercLib.CriticalLRP.BushRefute.not_forall_infiniteClusterProb_all_eq_zero_imp_lintegral_ne_top
