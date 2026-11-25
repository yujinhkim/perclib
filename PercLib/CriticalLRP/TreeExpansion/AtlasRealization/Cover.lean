/- Integrated from independently rebuilt Ultramath work.
Production base 70b027b0634874e65ce4bf8ec8fc8a7835e658e7.
Scratch source: repository-root .ultramath/smwwnvyp3/m4/.
-/

/-
The probabilistic consumer of the atlas covering theorem: disjoint occurrence and the
BK (Reimer) product bound, and the union bound over shapes and internal positions.

This is the part of the proof of Lemma I.4.16 of

  T. Hutchcroft, *Critical long-range percolation I: High effective dimension*,
  arXiv:2508.18807v1, pp. 43--45,

that follows the covering theorem `Real.exists_realization`: the source takes a union bound of
the event "the origin is connected to all `p` labelled terminals" over the combinatorial
structures of a tree, and bounds each structure's probability by the product of the connection
probabilities of the edges of its atlas (BK).  The result here is exactly that, with the product
taken over the `2 #Z - 1` atlas edges of the shape.

The remaining step of the source proof — regrouping the product into `k` three-point functions
and `2p - 1 - 3k` two-point functions with the hub 3-stars of `RTree.exists_hub_structure`, and
summing over the internal positions to produce `RTree.wt` — is not performed here; see
`docs` in the report for the precise statement that remains.
-/
module

public import PercLib.CriticalLRP.TreeExpansion.AtlasRealization.Realize

/-!
# Disjoint occurrence, BK and the union bound over shapes
-/
/-! Atlas realization, covering and cover lemmas. -/

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
variable {α : Type*} [Fintype α] [DecidableEq α]

/-! ### The atlas has `2p - 1` edges -/

/-- A shape with `p` leaves has exactly `2p - 1` atlas edges, matching production's
`RTree.AtlasEdge`. -/
theorem card_aedge (t : RTree α) : Fintype.card (AEdge t) = 2 * t.numLeaves - 1 := by
  have h : Fintype.card (AEdge t) = Fintype.card (t.IPos × Bool) + 1 := by
    simp [AEdge]
  rw [h, Fintype.card_prod, Fintype.card_bool, RTree.card_ipos]
  have := RTree.numLeaves_pos t
  omega

/-! ### Disjoint occurrence over an arbitrary finite index type -/

/- `DisjOcc` is defined in `AtlasRealization.Defs`. -/

/-- Disjoint occurrence only depends on the events, up to a relabelling of the index type. -/
theorem disjOcc_congr {ι κ : Type*} (e : ι ≃ κ) (A : ι → Set (Finset E))
    (B : κ → Set (Finset E)) (hAB : ∀ i, A i = B (e i)) : DisjOcc A = DisjOcc B := by
  ext ω
  constructor
  · rintro ⟨W, hsub, hmem, hdisj⟩
    refine ⟨fun k => W (e.symm k), fun k => hsub _, ?_, fun k k' hkk' => ?_⟩
    · intro k
      have h := hmem (e.symm k)
      rw [hAB (e.symm k)] at h
      simpa using h
    · exact hdisj _ _ (fun h => hkk' (e.symm.injective h))
  · rintro ⟨W, hsub, hmem, hdisj⟩
    refine ⟨fun i => W (e i), fun i => hsub _, ?_, fun i i' hii' => ?_⟩
    · intro i
      rw [hAB i]
      exact hmem (e i)
    · exact hdisj _ _ (fun h => hii' (e.injective h))

/-- **BK (Reimer) for a general finite index type**, derived from the `Fin k` form
`BKIncreasing`. -/
theorem bk_disjOcc {pr : E → ℝ} (hBK : BKIncreasing pr) {ι : Type*} [Fintype ι]
    (A : ι → Set (Finset E)) (hA : ∀ i, IsIncreasing (A i)) :
    prob pr (DisjOcc A) ≤ ∏ i, prob pr (A i) := by
  classical
  set e := (Fintype.equivFin ι).symm with he
  have hcongr : DisjOcc A = DisjOcc (fun j => A (e j)) :=
    (disjOcc_congr e (fun j => A (e j)) A (fun i => rfl)).symm
  rw [hcongr]
  refine le_trans (hBK (Fintype.card ι) (fun j => A (e j)) (fun j => hA _)) ?_
  exact le_of_eq (Fintype.prod_equiv e (fun j => prob pr (A (e j))) (fun i => prob pr (A i))
    (fun j => rfl))

/-- Finite union bound over an unbounded-index union. -/
theorem prob_iUnion_le_sum {pr : E → ℝ} (hp : ∀ e, 0 ≤ pr e) (hp1 : ∀ e, pr e ≤ 1)
    {ι : Type*} [Fintype ι] (A : ι → Set (Finset E)) :
    prob pr (⋃ i, A i) ≤ ∑ i, prob pr (A i) := by
  have h := prob_biUnion_le_sum hp hp1 (Finset.univ : Finset ι) A
  simpa using h

/-! ### The diagram event of a shape -/

/- `ConnEvent` and `DiagEvent` are defined in `AtlasRealization.Defs`. -/

/-- The diagram event is the disjoint occurrence of the atlas-edge connection events. -/
theorem diagEvent_eq_disjOcc (ends : E → Sym2 V) (y : α → V) (c : V) (t : RTree α)
    (φ : t.IPos → V) :
    DiagEvent ends y c t φ = DisjOcc (ConnEvent ends y c t φ) := by
  ext ω
  constructor
  · rintro ⟨wit, hsub, hdisj, hconn⟩
    exact ⟨wit, hsub, hconn, hdisj⟩
  · rintro ⟨W, hsub, hconn, hdisj⟩
    exact ⟨W, hsub, hdisj, hconn⟩

set_option maxHeartbeats 1000000 in
-- the dependent function-space unification over `RTree.IPos` needs more than the default here
/-- **BK for one fixed shape and position assignment**: the probability that the atlas is
realized disjointly is at most the product of the connection probabilities of its edges. -/
theorem prob_diagEvent_le {pr : E → ℝ} (hBK : BKIncreasing pr) (ends : E → Sym2 V)
    (y : α → V) (c : V) (t : RTree α) (φ : t.IPos → V) :
    prob pr (DiagEvent ends y c t φ) ≤ ∏ e : AEdge t, prob pr (ConnEvent ends y c t φ e) := by
  rw [diagEvent_eq_disjOcc]
  exact bk_disjOcc hBK (ConnEvent ends y c t φ)
    (fun e => conn_isIncreasing ends (srcPos t φ c e) (dstPos t φ y e))

/-! ### The union bound over shapes and internal positions -/

/-- The covering statement: every configuration connecting the root to all terminals lies in
the diagram event of some labelled shape and some assignment of internal positions. -/
theorem cover_union [Fintype V] (ends : E → Sym2 V) (v : V) (y : α → V) {Z : Finset α}
    (hne : Z.Nonempty) :
    {ω : Finset E | ∀ a ∈ Z, Conn ends ω v (y a)} ⊆
      ⋃ (t : LTon α Z) (φ : t.1.IPos → V), DiagEvent ends y v t.1 φ := by
  classical
  intro ω hω
  obtain ⟨t, φ, wit, hshape, hreal⟩ :
      ∃ (t : RTree α) (φ : t.IPos → V) (wit : AEdge t → Finset E),
        IsLabelledShape t Z ∧ IsRealization ends ω y v φ wit := exists_realization ends hne hω
  exact Set.mem_iUnion.mpr ⟨⟨t, hshape⟩, Set.mem_iUnion.mpr ⟨φ, ⟨wit, hreal⟩⟩⟩

set_option maxHeartbeats 1000000 in
-- the dependent function-space unification over `RTree.IPos` needs more than the default here
/-- **The covering + BK step of Lemma I.4.16.**

For every nonempty finite set `Z` of labels, the probability that the root `v` is connected to
all terminals `y a` (`a ∈ Z`) is at most the sum, over all labelled binary shapes `t` with leaf
set `Z` and all positions `φ` of the internal vertices, of the product of the connection
probabilities of the `2 #Z - 1` atlas edges.

Only the BK inequality (as the explicit hypothesis `BKIncreasing pr`) and the finiteness of `V`
enter beyond the covering theorem. -/
theorem prob_le_sum_shapes {pr : E → ℝ} (hp : ∀ e, 0 ≤ pr e) (hp1 : ∀ e, pr e ≤ 1)
    (hBK : BKIncreasing pr) [Fintype V] (ends : E → Sym2 V) (v : V) (y : α → V)
    {Z : Finset α} (hne : Z.Nonempty) :
    prob pr {ω | ∀ a ∈ Z, Conn ends ω v (y a)}
      ≤ ∑ t : LTon α Z, ∑ φ : t.1.IPos → V,
          ∏ e : AEdge t.1, prob pr (ConnEvent ends y v t.1 φ e) := by
  classical
  refine le_trans (prob_mono hp hp1 (cover_union ends v y hne)) ?_
  refine le_trans (prob_iUnion_le_sum hp hp1
    (fun t : LTon α Z => ⋃ φ : t.1.IPos → V, DiagEvent ends y v t.1 φ)) ?_
  refine Finset.sum_le_sum fun t (_ : t ∈ Finset.univ) => ?_
  refine le_trans (prob_iUnion_le_sum hp hp1
    (fun φ : t.1.IPos → V => DiagEvent ends y v t.1 φ)) ?_
  exact Finset.sum_le_sum fun φ (_ : φ ∈ Finset.univ) => prob_diagEvent_le hBK ends y v t.1 φ

/-! ### Degenerate witnesses are honest -/

/-- With no open edges, connectivity is equality: an empty witness cannot hide open edges. -/
theorem conn_empty_eq {ends : E → Sym2 V} {u v : V} (h : Conn ends (∅ : Finset E) u v) :
    u = v := by
  have hbot : openGraph ends (∅ : Finset E) = ⊥ := by
    ext a b; rw [openGraph_adj]; simp
  have h' : (openGraph ends (∅ : Finset E)).Reachable u v := h
  rw [hbot] at h'
  have h2 : v = u := by simpa using h'.symm
  exact h2.symm

/-- **A degenerate atlas edge is a genuine empty path.**  If the witness of an atlas edge of a
realization is empty, then its two ends coincide, so the factor it contributes to the product
of connection probabilities is exactly `P(w ↔ w) = 1` and no open edge is hidden behind it. -/
theorem srcPos_eq_dstPos_of_wit_eq_empty {ends : E → Sym2 V} {s : Finset E} {y : α → V}
    {c : V} {t : RTree α} {φ : t.IPos → V} {wit : AEdge t → Finset E}
    (h : IsRealization ends s y c φ wit) {e : AEdge t} (he : wit e = ∅) :
    srcPos t φ c e = dstPos t φ y e := by
  have hc := h.conn e
  rw [he] at hc
  exact conn_empty_eq hc

end PercLib.CriticalLRP.TreeExpansion.Real
