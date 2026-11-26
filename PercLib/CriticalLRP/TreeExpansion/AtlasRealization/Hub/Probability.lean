/- Integrated from independently rebuilt Ultramath work.
Production base 50c2eed0682a7e1b078ae771dbef463ebe00701d.
Scratch source: repository-root .ultramath/.
-/

/-
Swarm smwwr4usj / member m1.  Direction (A), part 2: the BK inequalities and the consumer.

Integrated base: production commit `6b7eb1107b03297e4df33585eeac818682adb1d2`, Lean 4.35.0.

Everything here is stated for the *finite Bernoulli* edge law `pr : E → ℝ` of
`TreeGraph.ThreePoint` (`0 ≤ pr ≤ 1`, `prob`, `IsIncreasing`, `BKIncreasing`) and the honest
finite graph of `AtlasRealization` (`ends : E → Sym2 V`, `[Fintype V]`).  The only probabilistic
input is the increasing-event BK inequality `BKIncreasing pr`, exactly as in
`Real.prob_le_sum_shapes`.

The three probabilistic statements, in increasing strength:

* `prob_hubStarJoint_le` — **three-fold BK at one hub.**  The *joint* value `HubStarJoint` (the
  disjoint occurrence of the three connection events of the hub's 3-star) is at most the
  *product* `hubStarConnProd` of the three two-point connection probabilities.  This is the
  `k = 1` instance of the paper's "one copy of the three-point function" step; the joint value
  and the product are kept apart, since the joint value is what the moment layer must evaluate
  and the product is only an upper bound for it.
* `prob_hubStarAllJoint_le` / `prob_hubStarAllJoint_le_hubSplit` — the same at all `k` hubs
  simultaneously (`3k` edges, then regrouped as `k` three-factor blocks).
* `prob_diagEvent_le_hubSplit` / `prob_le_sum_shapes_hubSplit` — the per-shape bound and the
  finite union bound over shapes, with the atlas product regrouped into `k` three-factor blocks
  and `2p - 1 - 3k` single factors.

The witnesses at a hub are *the same* witnesses as in the atlas realization: `DiagEvent` is a
disjoint occurrence for all `2p - 1` atlas edges, and `disjOcc_restrict` restricts a single
family of pairwise disjoint witness sets to any subfamily.  No independence is used anywhere.
-/
module

public import PercLib.CriticalLRP.TreeExpansion.AtlasRealization.Hub.Main

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace PercLib.CriticalLRP.TreeExpansion.Real

open Finset
open PercLib.CriticalLRP.TreeGraph

variable {V : Type*} [DecidableEq V]
variable {E : Type*} [Fintype E] [DecidableEq E]
variable {α : Type*}

/-! ### Restricting a disjoint occurrence to a subfamily of the index type -/

/-- **A global disjoint occurrence restricts to every subfamily, with the same witnesses.**
Applied with the identity family this says: one realization of the whole atlas yields, at every
hub, three pairwise disjoint witnesses for the three edges of that hub's 3-star. -/
theorem disjOcc_restrict {ι : Type*} (s : Finset ι) (A : ι → Set (Finset E)) :
    DisjOcc A ⊆ DisjOcc (fun i : {i // i ∈ s} => A i.1) := by
  rintro ω ⟨W, hsub, hmem, hdisj⟩
  exact ⟨fun i => W i.1, fun i => hsub i.1, fun i => hmem i.1,
    fun i j hij => hdisj i.1 j.1 (fun h => hij (Subtype.ext h))⟩

/-- The atlas event implies the joint three-point event at every hub, with the witnesses of the
one global realization. -/
theorem diagEvent_subset_hubStarJoint (ends : E → Sym2 V) (y : α → V) (c : V) (t : RTree α)
    (φ : t.IPos → V) (v : t.IPos) :
    DiagEvent ends y c t φ ⊆ HubStarJoint ends y c t φ v := by
  rintro ω ⟨wit, hsub, hdisj, hconn⟩
  exact ⟨fun e => wit e.1, fun e => hsub e.1, fun e => hconn e.1,
    fun e e' hne => hdisj e.1 e'.1 (fun h => hne (Subtype.ext h))⟩

/-- The atlas event implies the joint event at all hubs at once, with the witnesses of the one
global realization. -/
theorem diagEvent_subset_hubStarAllJoint (ends : E → Sym2 V) (y : α → V) (c : V)
    (t : RTree α) (φ : t.IPos → V) (S : Finset t.IPos) :
    DiagEvent ends y c t φ ⊆ HubStarAllJoint ends y c t φ S := by
  rintro ω ⟨wit, hsub, hdisj, hconn⟩
  exact ⟨fun e => wit e.1, fun e => hsub e.1, fun e => hconn e.1,
    fun e e' hne => hdisj e.1 e'.1 (fun h => hne (Subtype.ext h))⟩

/-! ### Three-fold BK at a hub, and BK on the `3k` hub edges -/

/-- **Three-fold BK at one hub.**  The joint value at the 3-star is bounded by the product of
the three two-point connection probabilities of its edges. -/
theorem prob_hubStarJoint_le {pr : E → ℝ} (hBK : BKIncreasing pr) (ends : E → Sym2 V)
    (y : α → V) (c : V) (t : RTree α) (φ : t.IPos → V) (v : t.IPos) :
    prob pr (HubStarJoint ends y c t φ v) ≤ hubStarConnProd pr ends y c t φ v := by
  have h := bk_disjOcc hBK
    (A := fun e : {e : AEdge t // e ∈ hubStarAEdges t v} => ConnEvent ends y c t φ e.1)
    (fun e => conn_isIncreasing ends (srcPos t φ c e.1) (dstPos t φ y e.1))
  refine le_trans h (le_of_eq ?_)
  rw [hubStarConnProd]
  exact (Finset.prod_subtype (hubStarAEdges t v) (fun x => Iff.rfl)
    (fun e => prob pr (ConnEvent ends y c t φ e))).symm

/-- **BK on the `3k` hub edges**: the simultaneous joint event at all hubs is bounded by the
product of the connection probabilities of the `3k` star edges. -/
theorem prob_hubStarAllJoint_le {pr : E → ℝ} (hBK : BKIncreasing pr) (ends : E → Sym2 V)
    (y : α → V) (c : V) (t : RTree α) (φ : t.IPos → V) (S : Finset t.IPos) :
    prob pr (HubStarAllJoint ends y c t φ S)
      ≤ ∏ e ∈ hubAEdges t S, prob pr (ConnEvent ends y c t φ e) := by
  have h := bk_disjOcc hBK
    (A := fun e : {e : AEdge t // e ∈ hubAEdges t S} => ConnEvent ends y c t φ e.1)
    (fun e => conn_isIncreasing ends (srcPos t φ c e.1) (dstPos t φ y e.1))
  refine le_trans h (le_of_eq ?_)
  exact (Finset.prod_subtype (hubAEdges t S) (fun x => Iff.rfl)
    (fun e => prob pr (ConnEvent ends y c t φ e))).symm

/-- The same bound, regrouped as `k` three-factor blocks. -/
theorem prob_hubStarAllJoint_le_hubSplit {pr : E → ℝ} (hBK : BKIncreasing pr)
    (ends : E → Sym2 V) (y : α → V) (c : V) (t : RTree α) (φ : t.IPos → V)
    (S : Finset t.IPos)
    (hpar : (∀ v ∈ S, RTree.iposDepth t v % 2 = 0) ∨
      (∀ v ∈ S, RTree.iposDepth t v % 2 = 1)) :
    prob pr (HubStarAllJoint ends y c t φ S) ≤ ∏ v ∈ S, hubStarConnProd pr ends y c t φ v := by
  refine (prob_hubStarAllJoint_le hBK ends y c t φ S).trans (le_of_eq ?_)
  simp only [hubStarConnProd]
  rw [prod_hubAEdges t S hpar]

/-! ### The per-shape bound and the union bound over shapes -/

/-- The atlas BK bound `Real.prob_diagEvent_le` in the form used below: the right-hand side is
the named product `atlasConnProd`.  (Restated because the production lemma carries an unused
`[Fintype α]` section variable.) -/
theorem prob_diagEvent_le_atlasConnProd {pr : E → ℝ} (hp : ∀ e, 0 ≤ pr e)
    (hp1 : ∀ e, pr e ≤ 1) (hBK : BKIncreasing pr) (ends : E → Sym2 V) (y : α → V) (c : V)
    (t : RTree α) (φ : t.IPos → V) :
    prob pr (DiagEvent ends y c t φ) ≤ atlasConnProd pr ends y c t φ := by
  have hbk : prob pr (DisjOcc (ConnEvent ends y c t φ))
      ≤ ∏ e : AEdge t, prob pr (ConnEvent ends y c t φ e) :=
    bk_disjOcc hBK (ConnEvent ends y c t φ)
      (fun e => conn_isIncreasing ends (srcPos t φ c e) (dstPos t φ y e))
  refine le_trans (prob_mono hp hp1 ?_) hbk
  rintro ω ⟨wit, hsub, hdisj, hconn⟩
  exact ⟨wit, hsub, hconn, hdisj⟩

/-- **The atlas bound with the hub regrouping**, for one shape and one position assignment. -/
theorem prob_diagEvent_le_hubSplit {pr : E → ℝ} (hp : ∀ e, 0 ≤ pr e) (hp1 : ∀ e, pr e ≤ 1)
    (hBK : BKIncreasing pr) (ends : E → Sym2 V) (y : α → V) (c : V) (t : RTree α)
    (φ : t.IPos → V) (S : Finset t.IPos)
    (hpar : (∀ v ∈ S, RTree.iposDepth t v % 2 = 0) ∨
      (∀ v ∈ S, RTree.iposDepth t v % 2 = 1)) :
    prob pr (DiagEvent ends y c t φ) ≤ hubSplitConnProd pr ends y c t φ S :=
  (prob_diagEvent_le_atlasConnProd hp hp1 hBK ends y c t φ).trans
    (le_of_eq (atlasConnProd_eq_hubSplit pr ends y c t φ S hpar))

/-- **The per-shape hub structure with the probabilistic bound.**  For every atlas with `p`
leaves, every `k ≤ ⌈(p-1)/2⌉`, every finite Bernoulli law and every position assignment, there
is a hub set `S` of `k` same-parity vertices with `3k` star edges and `2p - 1 - 3k` remaining
edges such that the diagram event is bounded by the hub-regrouped product. -/
theorem exists_hub_product_bound {pr : E → ℝ} (hp : ∀ e, 0 ≤ pr e) (hp1 : ∀ e, pr e ≤ 1)
    (hBK : BKIncreasing pr) (ends : E → Sym2 V) (y : α → V) (c : V) (t : RTree α)
    (φ : t.IPos → V) {k : ℕ} (hk : k ≤ (t.numLeaves - 1 + 1) / 2) :
    ∃ S : Finset t.IPos,
      S.card = k ∧
      ((∀ v ∈ S, RTree.iposDepth t v % 2 = 0) ∨
        (∀ v ∈ S, RTree.iposDepth t v % 2 = 1)) ∧
      (hubAEdges t S).card = 3 * k ∧
      (offHubAEdges t S).card = 2 * t.numLeaves - 1 - 3 * k ∧
      3 * k ≤ 2 * t.numLeaves - 1 ∧
      prob pr (DiagEvent ends y c t φ) ≤ hubSplitConnProd pr ends y c t φ S := by
  obtain ⟨S, hcard, hpar, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ :=
    RTree.exists_hub_structure (k := k) t hk
  exact ⟨S, hcard, hpar,
    by rw [card_hubAEdges t S hpar, hcard],
    by rw [card_offHubAEdges t S hpar, hcard],
    h10,
    prob_diagEvent_le_hubSplit hp hp1 hBK ends y c t φ S hpar⟩

section ShapeSum

variable [Fintype α] [DecidableEq α]

/-- **The finite union bound over shapes, with the hub regrouping at a fixed `k`.**

For every nonempty finite label set `Z` of size `p` and every `k ≤ ⌈(p-1)/2⌉` there is a hub
selection `K`, one hub set of `k` same-parity vertices for every labelled shape `t` with leaf set
`Z`, such that the probability that the root is connected to all terminals is at most the sum
over shapes and internal positions of the hub-regrouped product: at each shape `k` blocks of
three connection probabilities and `2p - 1 - 3k` single connection probabilities.

This is the shape-level form of the `k`-hub step of Lemma I.4.16.  The position sums and the
identification of the blocks with `E|K|²`-type in-cluster quantities (which needs transitivity
of the model, absent from this finite-graph layer) are *not* part of this statement. -/
theorem prob_le_sum_shapes_hubSplit {pr : E → ℝ} (hp : ∀ e, 0 ≤ pr e) (hp1 : ∀ e, pr e ≤ 1)
    (hBK : BKIncreasing pr) [Fintype V] (ends : E → Sym2 V) (v : V) (y : α → V)
    {Z : Finset α} (hne : Z.Nonempty) {k : ℕ} (hk : k ≤ (Z.card - 1 + 1) / 2) :
    ∃ K : (t : LTon α Z) → Finset (t.1.IPos),
      (∀ t : LTon α Z,
        (K t).card = k ∧
        ((∀ w ∈ K t, RTree.iposDepth t.1 w % 2 = 0) ∨
          (∀ w ∈ K t, RTree.iposDepth t.1 w % 2 = 1)) ∧
        (hubAEdges t.1 (K t)).card = 3 * k ∧
        (offHubAEdges t.1 (K t)).card = 2 * t.1.numLeaves - 1 - 3 * k) ∧
      prob pr {ω | ∀ a ∈ Z, Conn ends ω v (y a)}
        ≤ ∑ t : LTon α Z, ∑ φ : t.1.IPos → V, hubSplitConnProd pr ends y v t.1 φ (K t) := by
  classical
  have hnum : ∀ t : LTon α Z, t.1.numLeaves = Z.card := by
    intro t
    rw [RTree.numLeaves, ← List.toFinset_card_of_nodup t.2.1, t.2.2]
  have hex : ∀ t : LTon α Z, ∃ S : Finset (t.1.IPos),
      S.card = k ∧
      ((∀ w ∈ S, RTree.iposDepth t.1 w % 2 = 0) ∨
        (∀ w ∈ S, RTree.iposDepth t.1 w % 2 = 1)) := by
    intro t
    have hk' : k ≤ (t.1.numLeaves - 1 + 1) / 2 := by rw [hnum t]; exact hk
    obtain ⟨S, hcard, hpar, -⟩ := RTree.exists_hub_structure (k := k) t.1 hk'
    exact ⟨S, hcard, hpar⟩
  choose K hK using hex
  refine ⟨K, fun t => ⟨(hK t).1, (hK t).2, ?_, ?_⟩, ?_⟩
  · rw [card_hubAEdges t.1 (K t) (hK t).2, (hK t).1]
  · rw [card_offHubAEdges t.1 (K t) (hK t).2, (hK t).1]
  · refine (prob_le_sum_shapes hp hp1 hBK ends v y hne).trans (Finset.sum_le_sum fun t _ => ?_)
    exact Finset.sum_le_sum fun φ _ =>
      le_of_eq (atlasConnProd_eq_hubSplit pr ends y v t.1 φ (K t) (hK t).2)

end ShapeSum

end PercLib.CriticalLRP.TreeExpansion.Real
