/- Independently rebuilt and verified at production revision
    eb9b71a3cf20a0fe9906271415f5b17efd80f5ad.
    Original scratch source is recorded below. -/
/-
Direction A of swarm `smwwt6noq`: the finite marked atlas bound for the base factor of
Lemma I.4.17, at production HEAD `4c53bb5a8e76a4358a426adf71169b916b90f51f`.

Everything here is a *real instantiation* of the production results

* `PercLib.CriticalLRP.TreeExpansion.Real.cover_union` (covering of the terminal-connected
  event by diagram events of labelled shapes and internal positions),
* `PercLib.CriticalLRP.TreeExpansion.Real.prob_diagEvent_le` (BK for one shape), and
* `PercLib.CriticalLRP.TreeExpansion.Real.prob_le_sum_shapes` (covering + BK together),

at the marked label type `Fin p ⊕ PUnit`, with `p : ℕ` arbitrary, `p = 0` included.  The new
content, beyond the instantiation, is:

* the marked leaf position `markPos` and its uniqueness (`markPos_unique`), which is what makes
  "the marked leaf is pinned at `w`" a statement about *all* shapes rather than one chosen shape;
* the marked depth `markDepth` and its elementary bounds `1 ≤ ℓ ≤ #Z`, with `#Z = p + 1`;
* the finite marked coefficient `markCoeff ℓ`, the sum over shapes of marked depth `ℓ` and over
  internal positions, and the proof that the full finite diagram sum is exactly the sum of the
  coefficients over `ℓ` (`sum_markDiag_eq_sum_markCoeff`, an equality, not a bound);
* the final finite marked bound `prob_markedBase_le_markCoeff`, with range `p + 2` on `ℓ`.

The degenerate cases are not excluded anywhere: the marked event allows `f i = f j`, `f i = w`,
`f i = x` and `w = x`, and the covering/BK instantiation is applied to the *non-injective*
terminal map `markTerm f w`.  The only place a degenerate atlas edge is consumed is
`pconn_self` below: an empty witness connects `a` to `a` (`conn_refl`), so such an edge
contributes exactly the factor `P(a ↔ a) = 1` of the source.
-/
module

public import PercLib.CriticalLRP.TreeExpansion.AtlasRealization.MarkedAtlas.Defs

/-! # The finite marked atlas bound -/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace PercLib.CriticalLRP.MarkedAtlas

open Finset
open PercLib.CriticalLRP.TreeExpansion (RTree LTon)
open PercLib.CriticalLRP.TreeExpansion.Real
open PercLib.CriticalLRP.TreeGraph (Conn conn_refl prob prob_nonneg prob_mono BKIncreasing)

variable {V : Type*} [DecidableEq V] {E : Type*} [Fintype E] [DecidableEq E]
variable {α : Type*} [DecidableEq α]

/-! ## The marked base event -/

/-- Membership in the marked base event, in the two-parameter form used by the source:
`p` arms at `x` and the extra mark `w`. -/
theorem mem_markedBaseEvent_iff (ends : E → Sym2 V) (x : V) {p : ℕ} (f : Fin p → V) (w : V)
    {ω : Finset E} :
    ω ∈ MarkedBaseEvent ends x f w ↔
      (∀ i : Fin p, Conn ends ω x (f i)) ∧ Conn ends ω x w := by
  constructor
  · intro h
    exact ⟨fun i => h (Sum.inl i) (Finset.mem_univ _), h (Sum.inr ⟨⟩) (Finset.mem_univ _)⟩
  · rintro ⟨h1, h2⟩ a -
    rcases a with (i | u)
    · exact h1 i
    · rw [markTerm_mark]
      exact h2

/-- The marked base event is exactly "all arms and the mark are connected to the root", so it
is the finite event whose `prob` is the base factor `E[|K_x|^p 1(w ∈ K_x)]` of Lemma I.4.17.
No injectivity of `f` is assumed, so repeated arms and a mark equal to an arm or to the root are
included. -/
theorem markedBaseEvent_eq (ends : E → Sym2 V) (x : V) {p : ℕ} (f : Fin p → V) (w : V) :
    MarkedBaseEvent ends x f w =
      {ω : Finset E | (∀ i : Fin p, Conn ends ω x (f i)) ∧ Conn ends ω x w} := by
  ext ω
  exact mem_markedBaseEvent_iff ends x f w

/-- **Repeated terminal values are collapsed, not double counted.**  The marked base event only
sees the *set* of terminal values of the `p + 1` labels, so coincidences among the arms, or of an
arm with the mark or with the root, neither add nor remove conditions.  (The corresponding atlas
diagram still has a distinct leaf per label; the coincidence is absorbed by the degenerate branch
split, whose empty witnesses contribute the factor `P(a ↔ a) = 1`.) -/
theorem markedBaseEvent_eq_image (ends : E → Sym2 V) (x : V) {p : ℕ} (f : Fin p → V) (w : V) :
    MarkedBaseEvent ends x f w =
      {ω : Finset E | ∀ z ∈ (markLabels p).image (markTerm f w), Conn ends ω x z} := by
  ext ω
  constructor
  · intro h z hz
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hz
    exact h a (Finset.mem_univ a)
  · intro h a _
    exact h (markTerm f w a) (Finset.mem_image.mpr ⟨a, Finset.mem_univ a, rfl⟩)

/-! ## The marked leaf position and the marked depth -/

variable {t : RTree α}

/-- The chosen marked leaf position really carries the marked label. -/
theorem leafOfPos_markPos (t : RTree α) (a : α) (ha : a ∈ t.leaves) :
    t.leafOfPos (markPos t a ha) = a :=
  Classical.choose_spec (RTree.exists_leafOfPos t a ha)

/-- **The marked leaf position is unique.**  Since a labelled shape has injective leaf labels,
any leaf position carrying the marked label is *the* marked leaf; the marked depth is therefore
a property of the shape, not of a choice. -/
theorem markPos_unique (t : RTree α) (a : α) (ha : a ∈ t.leaves) (hnd : t.leaves.Nodup)
    {q : t.LeafPos} (hq : t.leafOfPos q = a) : q = markPos t a ha :=
  RTree.leafOfPos_injective hnd (by rw [hq, leafOfPos_markPos])

/-- Every label used by a shape is a leaf label. -/
theorem mark_mem_leaves {Z : Finset α} (t : LTon α Z) {c : α} (hc : c ∈ Z) : c ∈ t.1.leaves := by
  rw [← List.mem_toFinset, t.2.2]
  exact hc

/-- A shape on `Z` has exactly `#Z` leaves, hence `2 * #Z - 1` atlas edges. -/
theorem numLeaves_eq_card {Z : Finset α} (t : LTon α Z) : t.1.numLeaves = Z.card := by
  rw [RTree.numLeaves, ← List.toFinset_card_of_nodup t.2.1, t.2.2]

/-- A shape with `#Z` labelled leaves has `2 * #Z - 1` atlas edges; at `Z = markLabels p` this
is the source's `2p + 2q + 1` for `q = 0`. -/
theorem card_aedge_ltOn {α : Type*} [Fintype α] [DecidableEq α] {Z : Finset α}
    (t : LTon α Z) : Fintype.card (AEdge t.1) = 2 * Z.card - 1 := by
  rw [card_aedge, numLeaves_eq_card]

/-- Every leaf hangs at positive depth. -/
theorem depth_pos : ∀ (t : RTree α) (q : t.LeafPos), 0 < RTree.depth t q
  | RTree.leaf _, _ => Nat.one_pos
  | RTree.node _ _, Sum.inl _ => Nat.succ_pos _
  | RTree.node _ _, Sum.inr _ => Nat.succ_pos _

/-- The marked depth is positive. -/
theorem markDepth_pos {Z : Finset α} (c : α) (t : LTon α Z) (hc : c ∈ Z) :
    0 < markDepth c t hc :=
  depth_pos t.1 _

/-- **The marked depth is at most the number of leaves `#Z = p + 1`**, the elementary depth
constraint behind the source's range `3 ≤ ℓ ≤ p + q + 1`. -/
theorem markDepth_le_card {Z : Finset α} (c : α) (t : LTon α Z) (hc : c ∈ Z) :
    markDepth c t hc ≤ Z.card := by
  rw [markDepth, ← numLeaves_eq_card t]
  exact RTree.depth_le_numLeaves t.1 _

/-! ## Covering and BK at the marked label type -/

/-- **The marked covering statement.**  Any configuration in which the root is connected to all
`p` arms and to the mark contains an edge-disjoint atlas for some labelled shape on all `p + 1`
labels, with the marked leaf at `w`.  This is `Real.cover_union` instantiated at
`α = Fin p ⊕ PUnit`, `Z = univ`; the terminal map is `markTerm f w`, so the marked leaf's
terminal is `w` and no injectivity is needed. -/
theorem markedBase_subset_cover [Fintype V] (ends : E → Sym2 V) (x : V) {p : ℕ} (f : Fin p → V)
    (w : V) :
    MarkedBaseEvent ends x f w ⊆
      ⋃ (t : LTon (MarkLabel p) (markLabels p)) (φ : t.1.IPos → V),
        DiagEvent ends (markTerm f w) x t.1 φ := by
  have hne : (markLabels p).Nonempty := ⟨markLabelOf, markLabelOf_mem p⟩
  have h := cover_union (V := V) (E := E) (α := MarkLabel p) ends x (markTerm f w)
    (Z := markLabels p) hne
  simpa only [MarkedBaseEvent] using h

/-- **The BK upper bound for the marked base event.**  The probability that the root is
connected to all `p` arms and to the mark is at most the sum, over labelled binary shapes on the
`p + 1` marked labels and over internal positions, of the product of the connection
probabilities of the `2p + 1` atlas edges.  Instantiation of
`Real.prob_le_sum_shapes`; the marked leaf is pinned through `markTerm f w`, and the ordinary
leaves keep their values, so this is a genuine marked finite diagram expression. -/
theorem prob_markedBase_le_shapeSum [Fintype V] (pr : E → ℝ) (hp : ∀ e, 0 ≤ pr e)
    (hp1 : ∀ e, pr e ≤ 1) (hBK : BKIncreasing pr) (ends : E → Sym2 V) (x : V) {p : ℕ}
    (f : Fin p → V) (w : V) :
    prob pr (MarkedBaseEvent ends x f w) ≤
      ∑ t : LTon (MarkLabel p) (markLabels p), markDiag pr ends x (markTerm f w) t := by
  have hne : (markLabels p).Nonempty := ⟨markLabelOf, markLabelOf_mem p⟩
  have h := prob_le_sum_shapes (V := V) (E := E) (α := MarkLabel p) (pr := pr) hp hp1 hBK
    ends x (markTerm f w) (Z := markLabels p) hne
  simpa only [MarkedBaseEvent, markDiag] using h

/-! ## The marked finite coefficient: decomposition by marked depth -/

variable [Fintype V] [Fintype α]

/-- **The finite diagram sum is the sum of the marked coefficients over depths.**  An equality:
every labelled shape has a unique marked depth in `{1, …, #Z}`, so summing the marked coefficient
`markCoeff ℓ` (all shapes of marked depth `ℓ`, all internal positions) over `ℓ` recovers the full
finite sum, with no loss of terms and no `(2p-1)!!` normalisation slipped in. -/
theorem sum_markDiag_eq_sum_markCoeff (pr : E → ℝ) (ends : E → Sym2 V) (x : V) (y : α → V)
    (c : α) {Z : Finset α} (hc : c ∈ Z) :
    ∑ t : LTon α Z, markDiag pr ends x y t
      = ∑ ℓ ∈ Finset.range (Z.card + 1), markCoeff pr ends x y c hc ℓ := by
  have hmaps : ∀ t ∈ (Finset.univ : Finset (LTon α Z)),
      markDepth c t hc ∈ Finset.range (Z.card + 1) := by
    intro t _
    rw [Finset.mem_range]
    have := markDepth_le_card c t hc
    omega
  have h := Finset.sum_fiberwise_of_maps_to (s := (Finset.univ : Finset (LTon α Z)))
    (t := Finset.range (Z.card + 1)) (g := fun t => markDepth c t hc)
    (f := fun t => markDiag pr ends x y t) hmaps
  rw [← h]
  rfl

/-- **The finite marked atlas bound, with an explicit finite coefficient and explicit depth
range.**  For every `p : ℕ` — including `p = 0` — the probability that the root `x` is connected
to the `p` arms `f` and to the mark `w` is at most the sum over marked depths `ℓ ∈ {0, …, p+1}`
of the finite marked coefficient `markCoeff ℓ`, which sums the marked diagrams of all labelled
binary shapes on the `p + 1` marked labels whose marked leaf hangs at depth `ℓ`. -/
theorem prob_markedBase_le_markCoeff (pr : E → ℝ) (hp : ∀ e, 0 ≤ pr e)
    (hp1 : ∀ e, pr e ≤ 1) (hBK : BKIncreasing pr) (ends : E → Sym2 V) (x : V) {p : ℕ}
    (f : Fin p → V) (w : V) :
    prob pr (MarkedBaseEvent ends x f w) ≤
      ∑ ℓ ∈ Finset.range (p + 2),
        markCoeff pr ends x (markTerm f w) (markLabelOf (p := p)) (markLabelOf_mem p) ℓ := by
  have hdecomp := sum_markDiag_eq_sum_markCoeff (pr := pr) (ends := ends) (x := x)
    (y := markTerm f w) (c := markLabelOf (p := p)) (Z := markLabels p) (markLabelOf_mem p)
  rw [markLabels_card] at hdecomp
  exact le_trans (prob_markedBase_le_shapeSum pr hp hp1 hBK ends x f w) (le_of_eq hdecomp)

/-- The same bound in the named form `markedBound` of `Defs.lean`. -/
theorem prob_markedBase_le_markedBound (pr : E → ℝ) (hp : ∀ e, 0 ≤ pr e)
    (hp1 : ∀ e, pr e ≤ 1) (hBK : BKIncreasing pr) (ends : E → Sym2 V) (x : V) {p : ℕ}
    (f : Fin p → V) (w : V) :
    prob pr (MarkedBaseEvent ends x f w) ≤ markedBound pr ends x f w := by
  simpa only [markedBound, markBound, markLabels_card] using
    prob_markedBase_le_markCoeff pr hp hp1 hBK ends x f w

/-- **The finite marked moment bound** (all arm positions summed, mark pinned at `w`).  Summing
`prob_markedBase_le_markedBound` over the `#V ^ p` arm tuples gives the bound on the finite
`p`-th marked moment `∑_f P(f ⊆ K_x, w ∈ K_x)`, the base factor of Lemma I.4.17 in its
moment-expansion form.  The mark is still pinned in every term. -/
theorem sum_prob_markedBase_le_markedBound (pr : E → ℝ) (hp : ∀ e, 0 ≤ pr e)
    (hp1 : ∀ e, pr e ≤ 1) (hBK : BKIncreasing pr) (ends : E → Sym2 V) (x : V) (p : ℕ)
    (w : V) :
    (∑ f : Fin p → V, prob pr (MarkedBaseEvent ends x f w))
      ≤ ∑ f : Fin p → V, markedBound pr ends x f w :=
  Finset.sum_le_sum fun f _ => prob_markedBase_le_markedBound pr hp hp1 hBK ends x f w

/-! ## The two-point function: nonnegativity, bounds, and the degenerate edge -/

/-- The full space has probability one under the finite Bernoulli law. -/
theorem prob_univ (pr : E → ℝ) : prob pr (Set.univ : Set (Finset E)) = 1 := by
  simp only [prob, PercLib.CriticalLRP.probability, PercLib.CriticalLRP.expectation]
  simp [PercLib.CriticalLRP.configurationLaw_sum]

/-- The two-point function is nonnegative. -/
theorem pconn_nonneg (pr : E → ℝ) (hp : ∀ e, 0 ≤ pr e) (hp1 : ∀ e, pr e ≤ 1)
    (ends : E → Sym2 V) (a b : V) : 0 ≤ pconn pr ends a b :=
  prob_nonneg hp hp1 _

/-- The two-point function is at most one. -/
theorem pconn_le_one (pr : E → ℝ) (hp : ∀ e, 0 ≤ pr e) (hp1 : ∀ e, pr e ≤ 1)
    (ends : E → Sym2 V) (a b : V) : pconn pr ends a b ≤ 1 := by
  refine le_trans (prob_mono hp hp1 (Set.subset_univ _)) ?_
  exact le_of_eq (prob_univ pr)

/-- **The degenerate edge is free.**  A vertex is always connected to itself, by the empty set of
open edges, so a degenerate atlas edge contributes the factor `P(a ↔ a) = 1` that the source
writes explicitly.  This is the only degenerate case the atlas realization can produce, and it is
handled by the empty-witness branch of `Real.exists_split`. -/
theorem pconn_self (pr : E → ℝ) (ends : E → Sym2 V) (a : V) : pconn pr ends a a = 1 := by
  have h : {ω : Finset E | Conn ends ω a a} = Set.univ := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    exact conn_refl ends ω a
  rw [pconn, h, prob_univ]

end PercLib.CriticalLRP.MarkedAtlas
