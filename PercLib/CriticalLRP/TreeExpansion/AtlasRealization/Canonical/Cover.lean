/-
Independently built covering theorem for swarm `smwwtd5t5`, member `m1` (direction A).

## The theorem, and where it sits in the source

Hutchcroft, *Critical long-range percolation I: High effective dimension*, arXiv:2508.18807v1,
pp. 43--45, proves the generalized tree-graph inequality (I.4.16) by, first, choosing for each
terminal-connected configuration a *combinatorial structure*: a rooted binary shape with the `p`
terminal leaves, positions for its internal vertices, and `2p - 1` pairwise edge-disjoint open
paths, and then, second, taking a union bound over structures and applying BK to each.

Production already contains both halves *of the finite model*: `Real.exists_realization` (every
terminal-connected finite configuration carries an atlas) and `Real.prob_le_sum_shapes` (the union
bound plus BK, for `[Fintype V]` and a finite edge type `E`).  The canonical countable model on
which the rest of the paper runs -- `Config V = Set (Sym2 V)`, `Connects`, §I.1.2 -- has neither a
finite edge type nor a finite vertex type, so neither half applies verbatim.  This file supplies
the deterministic half for the canonical model, with no finiteness assumption on `V` and no
finiteness assumption on `Sym2 V`:

* `exists_finset_conn_witness` -- finitely many connection requirements `c ↔ f i` in `ω` are
  already met inside a single **finite** set `W` of open edges of `ω`.  This is where the
  finiteness comes from, and it comes from the configuration itself: a connection is a walk, a
  walk has finitely many edges (`pathConnects_iff`, a proved equivalence in production, not an
  extra assumption).  No bound on `W` is claimed and none is used.

* `exists_canonical_realization` -- for `1 ≤ q`, every `ω` in which `c` is connected to all of
  `f : Fin q → V` admits a fully labelled shape `t : RTree (Fin q)`, positions `φ : t.IPos → V`,
  and pairwise disjoint finite open witness sets `wit e ⊆ ω` for the `2q - 1` atlas edges,
  connecting their ends **in `ω`** (`CanonAtlas.IsCanonRealization`).  The proof applies
  production's `Real.exists_realization` to the finite edge type `↥W` with incidence
  `Subtype.val : ↥W → Sym2 V` and to the full finite configuration `Finset.univ`, and then
  transports every witness back to `Sym2 V` with `witLift`; the connectivity transport is
  `CanonAtlas.treeConn_iff_connects`, proved by explicit walks in `Transport.lean`.

* `conn_subset_canonCover` / `conn_subset_canonAtlas_iUnion` -- the covering statement itself: the
  terminal-connection event is contained in the countable union of the canonical atlas events,
  indexed by the finite (hence countable) shape family `LTon (Fin q) Finset.univ` and the
  countable position space `t.IPos → V` (`countable_atlasIndex`).

* `isUpperSet_canonAtlasEvent`, `finiteWitness_canonAtlasEvent` -- the canonical atlas event is
  increasing and finitely witnessed.  These are exactly the two hypotheses under which the
  canonical BK law `edgeMeasure_bk_list` (`PercLib.CriticalLRP.BK.CanonicalBridge`) applies to it,
  so the per-diagram product bound can be supplied from BK without any further set-theoretic
  work: there is no need to re-derive `DisjointOccurrence` on the canonical side.

* `card_aedge_of_labelled` -- a fully labelled shape on `Fin q` has `2q - 1` atlas edges, matching
  the paper's count.

## What is *not* proved here, and why that is deliberate

The union bound over the (countable) cover, i.e. the passage from
`(edgeMeasure π) (terminal event) ≤ ∑ over structures (edgeMeasure π) (atlas event)` and the
product bound for each atlas event, is not proved here.  The per-diagram product bound is BK for
the *canonical* iterated disjoint-occurrence law at an arbitrary finite index type, which is the
separate task of direction B; this file deliberately stops at the deterministic cover plus the
exact hypotheses (`IsUpperSet`, `FiniteWitness`) that the canonical BK law consumes, so that the
two halves compose without an assumption of the cover and without any interchange of limits.
-/
module

public import PercLib.CriticalLRP.TreeExpansion.AtlasRealization.Canonical.Transport
public import PercLib.CriticalLRP.TreeExpansion.AtlasRealization.Realize
public import PercLib.CriticalLRP.TreeExpansion.AtlasRealization.Cover
public import PercLib.CriticalLRP.BK.CanonicalBridge

/-!
# The covering theorem in the canonical countable model
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace CanonAtlas

open Finset

open PercLib.CriticalLRP (Config Connects connSet pathConnects_iff)

open PercLib.CriticalLRP.TreeGraph (Conn)

open PercLib.CriticalLRP.TreeExpansion (RTree LTon)

open PercLib.CriticalLRP.TreeExpansion.Real (AEdge srcPos dstPos IsLabelledShape IsRealization)

variable {V : Type*} [DecidableEq V] [Countable V]
variable {α : Type*}

/-! ### Finitely many connections have one finite witness -/

/-- **A finite witness for finitely many connections.**  If `c` is connected to each of the
finitely many vertices `y i` in the configuration `ω`, then there is a single finite set `W` of
open edges of `ω` inside which all those connections already hold.

The proof is the honest one: each connection is a walk of open edges (`pathConnects_iff`), a walk
has finitely many edges, and `W` is the union of those finitely many finite edge sets.  Nothing is
truncated, and `W` is not assumed to be a box, a cluster approximation, or anything else. -/
theorem exists_finset_conn_witness {ι : Type*} [Fintype ι] (ω : Config V) (c : V) (y : ι → V)
    (h : ∀ i, Connects ω c (y i)) :
    ∃ W : Finset (Sym2 V), (W : Set (Sym2 V)) ⊆ ω ∧
      ∀ i, Connects ((W : Finset (Sym2 V)) : Set (Sym2 V)) c (y i) := by
  classical
  choose p hp using fun i => pathConnects_iff.mpr (h i)
  refine ⟨Finset.univ.sup (fun i => (p i).edges.toFinset), ?_, ?_⟩
  · intro e he
    obtain ⟨i, -, hie⟩ := Finset.mem_sup.mp he
    exact hp i e (List.mem_toFinset.mp hie)
  · intro i
    refine pathConnects_iff.mp ⟨p i, fun e he => ?_⟩
    exact Finset.mem_sup.mpr ⟨i, Finset.mem_univ i, List.mem_toFinset.mpr he⟩

/-! ### The all-configurations realization in the canonical model -/

/-- **Every terminally connected configuration carries an edge-disjoint atlas, in the canonical
countable model.**

For `1 ≤ q`, let `c` be a root vertex and `f : Fin q → V` the positions of the terminal leaves
(labels are distinct, positions may repeat).  If `c` is connected to every `f i` in `ω`, then some
fully labelled binary shape `t : RTree (Fin q)`, some assignment `φ` of positions to its internal
vertices, and some family of pairwise disjoint finite sets `wit e ⊆ ω` of open edges realize the
whole atlas of `t` inside `ω`: each `wit e` joins the two ends `srcPos t φ c e` and
`dstPos t φ f e` of its atlas edge by a path that stays inside `wit e`.

No finiteness of `V` or of `Sym2 V` is assumed, and the configuration is not truncated: the
finiteness comes from `exists_finset_conn_witness`, and the selected finite edge set `W` is used
only as a finite edge type via `↥W → Sym2 V`.  Production's `Real.exists_realization` is applied
to `E = ↥W`, `s = univ`, and the witnesses are transported back along `witLift`. -/
theorem exists_canonical_realization {q : ℕ} (hq : 1 ≤ q) (c : V) {ω : Config V}
    (f : Fin q → V) (h : ∀ i, Connects ω c (f i)) :
    ∃ (t : RTree (Fin q)) (φ : t.IPos → V) (wit : AEdge t → Finset (Sym2 V)),
      IsLabelledShape t Finset.univ ∧ IsCanonRealization ω f c φ wit := by
  classical
  obtain ⟨W, hWsub, hWconn⟩ := exists_finset_conn_witness ω c f h
  -- connectivity in the finite graph on `↥W` with all of its edges open
  have hfin : ∀ a : Fin q, Conn (Subtype.val : ↥W → Sym2 V) (Finset.univ : Finset ↥W) c (f a) :=
    fun a => (treeConn_univ_iff_connects c (f a)).mpr (hWconn a)
  obtain ⟨t, φ, wit, hshape, hreal⟩ :=
    PercLib.CriticalLRP.TreeExpansion.Real.exists_realization
      (Subtype.val : ↥W → Sym2 V) (W := Finset.univ) (v := c) (y := f) (Z := Finset.univ)
      ⟨⟨0, by omega⟩, Finset.mem_univ _⟩ (fun a _ => hfin a)
  exact ⟨t, φ, fun e => witLift (wit e), hshape, isCanonRealization_of_isRealization hWsub hreal⟩

/-! ### The covering statement -/

/-- **The canonical covering statement, in the paper's shape.**  The event that the root `c` is
connected to all the terminals `f i` is contained in the union of the canonical atlas events, over
all fully labelled binary shapes `t` with `q` leaves and all assignments `φ` of positions to their
internal vertices. -/
theorem conn_subset_canonAtlas_iUnion {q : ℕ} (hq : 1 ≤ q) (c : V) (f : Fin q → V) :
    {ω : Config V | ∀ i, Connects ω c (f i)} ⊆
      ⋃ (t : LTon (Fin q) Finset.univ) (φ : t.1.IPos → V), CanonAtlasEvent f c t.1 φ := by
  intro ω hω
  obtain ⟨t, φ, wit, hshape, hreal⟩ := exists_canonical_realization hq c f hω
  exact Set.mem_iUnion.mpr ⟨⟨t, hshape⟩, Set.mem_iUnion.mpr ⟨φ, wit, hreal⟩⟩

/-- The covering statement indexed by the single sigma type of shape-and-positions; this is the
form in which the union bound over the countable cover is taken. -/
theorem conn_subset_canonCover {q : ℕ} (hq : 1 ≤ q) (c : V) (f : Fin q → V) :
    {ω : Config V | ∀ i, Connects ω c (f i)} ⊆ CanonCover q f c := by
  intro ω hω
  obtain ⟨t, φ, wit, hshape, hreal⟩ := exists_canonical_realization hq c f hω
  rw [mem_canonCover]
  exact ⟨⟨⟨t, hshape⟩, φ⟩, wit, hreal⟩

/-- **The index type of the canonical cover is countable.**  It is a sigma type over the finite
shape family `LTon (Fin q) Finset.univ` (production `LTon.instFintype`) and the position space
`t.IPos → V`, which is countable because `t.IPos` is finite and `V` is countable.  Hence the cover
`CanonCover` is a genuinely countable union, with no finiteness of `V`. -/
theorem countable_atlasIndex (q : ℕ) :
    Countable (Σ t : LTon (Fin q) Finset.univ, t.1.IPos → V) :=
  inferInstance

/-! ### The shape count -/

/-- A fully labelled shape on `Fin q` has exactly `q` leaves. -/
theorem numLeaves_of_isLabelledShape {q : ℕ} {t : RTree (Fin q)}
    (h : IsLabelledShape t Finset.univ) : t.numLeaves = q := by
  have hcard : t.leaves.toFinset.card = t.numLeaves := by
    rw [List.toFinset_card_of_nodup h.1]
    rfl
  rw [← hcard, h.2, Finset.card_univ, Fintype.card_fin]

/-- A fully labelled shape on `Fin q` has `2q - 1` atlas edges, matching the paper's count for `p`
labelled terminals. -/
theorem card_aedge_of_labelled {q : ℕ} {t : RTree (Fin q)}
    (h : IsLabelledShape t Finset.univ) : Fintype.card (AEdge t) = 2 * q - 1 := by
  rw [PercLib.CriticalLRP.TreeExpansion.Real.card_aedge, numLeaves_of_isLabelledShape h]

/-! ### The atlas event is increasing and finitely witnessed -/

/-- The canonical atlas event is increasing: an atlas realized inside `ω` is realized inside any
larger configuration. -/
theorem isUpperSet_canonAtlasEvent {y : α → V} {c : V} {t : RTree α} {φ : t.IPos → V} :
    IsUpperSet (CanonAtlasEvent y c t φ) := by
  rintro ω ω' hωω' ⟨wit, hsub, hdisj, hconn⟩
  -- the witnesses and their connectivity do not mention `ω`; only `subset` has to be transported
  exact ⟨wit, fun e x hx => hωω' (hsub e hx), hdisj, hconn⟩

/-- The canonical atlas event is finitely witnessed: the (finite) union of the witnesses of the
atlas edges already forces the event.  This is the hypothesis `Percolation.FiniteWitness` that the
canonical BK law `edgeMeasure_bk_list` requires, and it is where the finiteness of the witnesses --
not of the graph -- enters the probabilistic argument. -/
theorem finiteWitness_canonAtlasEvent {y : α → V} {c : V} {t : RTree α} {φ : t.IPos → V} :
    PercLib.CriticalLRP.Percolation.FiniteWitness (CanonAtlasEvent y c t φ) := by
  intro ω ⟨wit, hsub, hdisj, hconn⟩
  -- the finite union of the witnesses already forces the event: the same witness family, whose
  -- connectivity does not mention the configuration, witnesses the event inside the union
  refine ⟨Finset.univ.sup wit, ?_, wit, ?_, hdisj, hconn⟩
  · intro e he
    obtain ⟨i, -, hie⟩ := Finset.mem_sup.mp he
    exact hsub i hie
  · intro e x hx
    exact Finset.mem_sup.mpr ⟨e, Finset.mem_univ e, hx⟩

end CanonAtlas
