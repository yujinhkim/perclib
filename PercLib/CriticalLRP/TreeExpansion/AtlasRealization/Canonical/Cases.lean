/-
Independently built case analysis and interface for swarm `smwwtd5t5`, member `m1`
(direction A).

## Contents

* `labelEvent_eq_conn` -- production's labelled event `I417A.labelEvent x f` (the tuple `f` lies
  in the cluster of `x`, Lemma I.4.17 of Hutchcroft, arXiv:2508.18807v1) is *exactly* the event
  `∀ i, Connects ω x (f i)` to which the covering theorem of `Cover.lean` applies.  This is a
  rewriting lemma, so that the probabilistic consumer can pass between the two descriptions
  without an extra hypothesis.

* `labelEvent_subset_canonCover` -- **the target statement**: for `1 ≤ q`,
  `I417A.labelEvent x f ⊆ CanonCover q f x`, i.e. every configuration in the labelled event lies in
  the countable union of canonical atlas-diagram events.  By `Cover.exists_canonical_realization`
  the witnessing structure is explicit: a fully labelled shape `t : RTree (Fin q)`, positions
  `φ : t.IPos → V`, and pairwise disjoint finite sets of open edges of `ω`, one for each of the
  `2q - 1` atlas edges (`CanonAtlas.IsCanonRealization`).

* `canonRealization_leaf_one`, `labelEvent_one_eq` -- the case `q = 1`, proved as an *exact*
  identity: for a single label, the shape is the one-leaf shape `RTree.leaf 0` and the atlas has
  exactly one edge, the root leaf edge.  So the `q = 1` instance of the covering theorem is an
  equality of events, not merely an inclusion, and it can be checked directly: the diagonal
  degenerate case does not arise here (the single atlas edge joins the root `x` to the terminal
  `f 0`), while the empty-witness degenerate case is covered by
  `srcPos_eq_dstPos_of_wit_eq_empty` below.

* `isEmpty_atlasIndex_zero`, `canonCover_zero_eq_empty`, `not_conn_subset_canonCover_zero` -- the
  honest treatment of `q = 0`.  A rooted binary shape always has at least one leaf
  (`RTree.numLeaves_pos`), so there is *no* fully labelled shape on zero labels: the atlas cover
  is the empty union.  Meanwhile the labelled event with zero labels is the whole space.  Hence
  the covering statement genuinely fails at `q = 0` and the hypothesis `1 ≤ q` in the theorems
  above is not removable: it is not an artefact of the formalization.  (In the source the
  parameter is the number of labelled terminals, which is at least one when the inequality is
  applied.)  No `q = 0` case is smuggled in by an empty product or by a fictitious edge.

* `openGraph_empty`, `connects_empty_eq`, `srcPos_eq_dstPos_of_wit_eq_empty` -- empty witnesses
  are honest: connectivity in the empty configuration is equality, so an atlas edge whose
  witness is empty has coinciding ends.  This is the canonical-model counterpart of production's
  `Real.srcPos_eq_dstPos_of_wit_eq_empty` and is what justifies reading a degenerate atlas edge as
  the factor `P(w ↔ w) = 1` of the source, with no open edge hidden behind it.

* `mem_connSet_wit` -- each witness of a canonical realization is an element of the connection
  event `connSet (srcPos …) (dstPos …)` of the two ends, which is the form in which the canonical
  BK law (`edgeMeasure_bk_list`) is applied.
-/
module

public import PercLib.CriticalLRP.TreeExpansion.AtlasRealization.Canonical.Cover
public import PercLib.CriticalLRP.Correlation.I417.Nonnegative.Defs

/-!
# The labelled event, the `q = 1` case, and honest degeneracies
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace CanonAtlas

open Finset

open PercLib.CriticalLRP (Config Connects connSet pathConnects_iff mem_cluster_iff)

open PercLib.CriticalLRP.TreeExpansion (RTree LTon)

open PercLib.CriticalLRP.TreeExpansion.Real (AEdge srcPos dstPos IsLabelledShape rootPos
  srcPos_root dstPos_root rootPos_leaf)

variable {V : Type*} [DecidableEq V] [Countable V]
variable {α : Type*}

/-! ### The labelled event of Lemma I.4.17 -/

/-- The labelled event `I417A.labelEvent x f` is the event that `x` is connected to every label. -/
theorem labelEvent_eq_conn {x : V} {q : ℕ} (f : Fin q → V) :
    PercLib.CriticalLRP.I417A.labelEvent x f = {ω : Config V | ∀ i, Connects ω x (f i)} := by
  ext ω
  simp only [PercLib.CriticalLRP.I417A.labelEvent, Set.mem_ofPred_eq]
  exact forall_congr' fun i => mem_cluster_iff

/-- **The covering statement for the labelled event of Lemma I.4.17, in the paper's shape.**  For
`1 ≤ q`, every configuration in which the root `x` is connected to all the labelled terminals
`f i` lies in the union, over all fully labelled binary shapes `t` on `q` leaves and all positions
`φ` of the internal vertices, of the canonical atlas events. -/
theorem labelEvent_subset_canonAtlas_iUnion (x : V) {q : ℕ} (hq : 1 ≤ q) (f : Fin q → V) :
    PercLib.CriticalLRP.I417A.labelEvent x f ⊆
      ⋃ (t : LTon (Fin q) Finset.univ) (φ : t.1.IPos → V), CanonAtlasEvent f x t.1 φ := by
  rw [labelEvent_eq_conn]
  exact conn_subset_canonAtlas_iUnion hq x f

/-- The same covering statement indexed by the single countable sigma type of shapes and
positions. -/
theorem labelEvent_subset_canonCover (x : V) {q : ℕ} (hq : 1 ≤ q) (f : Fin q → V) :
    PercLib.CriticalLRP.I417A.labelEvent x f ⊆ CanonCover q f x := by
  rw [labelEvent_eq_conn]
  exact conn_subset_canonCover hq x f

/-- Each witness of a canonical realization lies in the connection event of the two ends of its
atlas edge.  This is the exact form in which the canonical BK law consumes the realization. -/
theorem mem_connSet_wit {ω : Config V} {y : α → V} {c : V} {t : RTree α} {φ : t.IPos → V}
    {wit : AEdge t → Finset (Sym2 V)} (h : IsCanonRealization ω y c φ wit) (e : AEdge t) :
    (wit e : Set (Sym2 V)) ∈ connSet (srcPos t φ c e) (dstPos t φ y e) :=
  h.conn e

/-! ### Honest empty witnesses -/

/-- The open graph of the empty configuration is the empty graph. -/
theorem openGraph_empty : PercLib.CriticalLRP.openGraph (∅ : Set (Sym2 V)) = ⊥ := by
  ext a b
  rw [PercLib.CriticalLRP.openGraph_adj]
  simp

/-- Connectivity in the empty configuration is equality: an empty witness cannot hide an open
edge, and in particular cannot connect two distinct vertices. -/
theorem connects_empty_eq {u v : V} (h : Connects (∅ : Set (Sym2 V)) u v) : u = v := by
  have h' : (⊥ : SimpleGraph V).Reachable u v := by
    rw [← openGraph_empty]
    exact h
  have h2 : v = u := by simpa using h'.symm
  exact h2.symm

/-- **A degenerate atlas edge is a genuine empty path.**  If the witness of an atlas edge of a
canonical realization is empty, then its two ends coincide, so the factor it contributes to the
product of connection probabilities is exactly `P(w ↔ w) = 1`, with no open edge hidden behind it.
-/
theorem srcPos_eq_dstPos_of_wit_eq_empty {ω : Config V} {y : α → V} {c : V} {t : RTree α}
    {φ : t.IPos → V} {wit : AEdge t → Finset (Sym2 V)} (h : IsCanonRealization ω y c φ wit)
    {e : AEdge t} (he : wit e = ∅) : srcPos t φ c e = dstPos t φ y e := by
  have hc := h.conn e
  rw [he, Finset.coe_empty] at hc
  exact connects_empty_eq hc

/-! ### The case `q = 1` -/

/-- Any two atlas edges of a one-leaf shape coincide: a leaf has no internal vertex, so the only
atlas edge is the root leaf edge. -/
theorem subsingleton_aedge_leaf (a : α) : Subsingleton (AEdge (RTree.leaf a)) := by
  constructor
  intro e e'
  rcases e with (⟨u, b⟩ | x) <;> rcases e' with (⟨u', b'⟩ | x')
  · exact nomatch u
  · exact nomatch u
  · exact nomatch u'
  · rw [Subsingleton.elim x x']

/-- The canonical realization of the atlas of the one-leaf shape at a single label `f 0`: the only
atlas edge is the root leaf edge, joining `x` to `f 0`, and any finite witness of that connection
serves.  This holds for *every* position assignment `φ` of the (empty) internal vertex set, so no
side condition on `φ` is needed. -/
theorem canonRealization_leaf_one (ω : Config V) (x : V) (f : Fin 1 → V) (W : Finset (Sym2 V))
    (hW : (W : Set (Sym2 V)) ⊆ ω)
    (hconn : Connects ((W : Finset (Sym2 V)) : Set (Sym2 V)) x (f 0))
    (φ : (RTree.leaf (0 : Fin 1)).IPos → V) :
    IsCanonRealization ω f x φ (fun _ => W) where
  subset _ := hW
  disjoint e e' hne := absurd ((subsingleton_aedge_leaf (0 : Fin 1)).elim e e') hne
  conn e := by
    have he : e = Sum.inr ⟨⟩ := (subsingleton_aedge_leaf (0 : Fin 1)).elim e _
    rw [he, srcPos_root, dstPos_root, rootPos_leaf]
    exact hconn

/-- **The `q = 1` case, exactly.**  For a single labelled terminal the shape is the one-leaf shape
`RTree.leaf 0`, its only atlas edge is the root leaf edge `x — f 0`, and the cover is an equality
of events: the labelled event is precisely the event that the atlas of the one-leaf shape is
realized. -/
theorem labelEvent_one_eq (x : V) (f : Fin 1 → V) :
    PercLib.CriticalLRP.I417A.labelEvent x f =
      ⋃ (φ : (RTree.leaf (0 : Fin 1)).IPos → V), CanonAtlasEvent f x (RTree.leaf 0) φ := by
  rw [labelEvent_eq_conn]
  ext ω
  constructor
  · intro hω
    -- the finite witness of the single connection `x ↔ f 0`
    obtain ⟨W, hWsub, hWconn⟩ := exists_finset_conn_witness ω x f hω
    let φ₀ : (RTree.leaf (0 : Fin 1)).IPos → V := fun u => nomatch u
    exact Set.mem_iUnion.mpr
      ⟨φ₀, mem_canonAtlasEvent.mpr ⟨fun _ => W,
        canonRealization_leaf_one ω x f W hWsub (hWconn 0) φ₀⟩⟩
  · intro hmem
    obtain ⟨φ, hφ⟩ := Set.mem_iUnion.mp hmem
    obtain ⟨wit, hreal⟩ := mem_canonAtlasEvent.mp hφ
    intro i
    -- the root leaf edge of the one-leaf shape joins `x` to `f 0`
    have h0 : Connects ((wit (Sum.inr ⟨⟩) : Finset (Sym2 V)) : Set (Sym2 V)) x (f 0) := by
      have hc := hreal.conn (Sum.inr ⟨⟩ : AEdge (RTree.leaf (0 : Fin 1)))
      rw [srcPos_root, dstPos_root, rootPos_leaf] at hc
      exact hc
    have hmem : Connects ω x (f 0) :=
      PercLib.CriticalLRP.connects_mono (fun e he => hreal.subset _ he) h0
    rw [Subsingleton.elim i 0]
    exact hmem

/-! ### The degenerate case `q = 0`, honestly -/

/-- There is no fully labelled shape on zero labels: a rooted binary tree always has at least one
leaf.  Hence the atlas cover at `q = 0` is the empty union, and it is not the whole space. -/
theorem isEmpty_atlasIndex_zero :
    IsEmpty (Σ t : LTon (Fin 0) Finset.univ, t.1.IPos → V) := by
  refine ⟨fun p => ?_⟩
  have huniv : (Finset.univ : Finset (Fin 0)) = ∅ := by
    ext i
    exact i.elim0
  have hleaves : p.1.1.leaves = [] := by
    induction p.1.1.leaves with
    | nil => rfl
    | cons a _ _ => exact a.elim0
  have hpos := RTree.numLeaves_pos p.1.1
  have hzero : p.1.1.numLeaves = 0 := by
    rw [RTree.numLeaves, hleaves]
    rfl
  omega

/-- At `q = 0` the canonical atlas cover is empty. -/
theorem canonCover_zero_eq_empty (y : Fin 0 → V) (c : V) : CanonCover 0 y c = ∅ := by
  refine Set.eq_empty_iff_forall_notMem.mpr fun ω hω => ?_
  rw [mem_canonCover] at hω
  obtain ⟨p, -⟩ := hω
  exact (isEmpty_atlasIndex_zero (V := V)).false p

/-- At `q = 0` the labelled event is the whole space. -/
theorem labelEvent_zero (x : V) (f : Fin 0 → V) :
    PercLib.CriticalLRP.I417A.labelEvent x f = Set.univ := by
  rw [labelEvent_eq_conn]
  ext ω
  simp

/-- **The covering statement fails at `q = 0`**, so the hypothesis `1 ≤ q` is genuinely needed:
there is no one-leaf-free binary shape to cover the (vacuous) terminal event with.  This is the
honest degenerate case; no fictitious edge and no empty product is used to patch it. -/
theorem not_conn_subset_canonCover_zero (x : V) (f : Fin 0 → V) :
    ¬ ({ω : Config V | ∀ i, Connects ω x (f i)} ⊆ CanonCover 0 f x) := by
  intro hsub
  have hmem : (∅ : Config V) ∈ ({ω : Config V | ∀ i, Connects ω x (f i)}) := by
    intro i
    exact i.elim0
  have hempty := canonCover_zero_eq_empty f x
  rw [hempty] at hsub
  exact hsub hmem

end CanonAtlas
