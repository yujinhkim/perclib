/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
# The BFS tree pieces of an open cluster are disjoint open BK witnesses

Reference: T. Hutchcroft, arXiv:2008.11197v2, Section 2.1, proof of Theorem 2.3, step (2.10).

`BFSParent.lean` supplies the BFS parent map of the open cluster `K_r` of a vertex `r`;
`TreePieces.lean` cuts the parent tree of a rooted forest into `lam`-sized rooted pieces.
This file puts the two together at a percolation configuration `ω`:

* `markSet Λ` is the set of marked vertices of the cluster (`Λ` is the finite window), as a `Finset`
  of the cluster's vertex type — the set `A` to which the tree-piece lemma is applied.
* `pieceWt v P` is the set of *open* edges of the piece: the parent edge of every vertex of
  `P \ {v}`.  `pieceWt_subset` shows it is a subset of `ω`.
* `piece_conn_pieceWt`: inside one piece, all vertices are connected **using only the edges of
  `pieceWt v P`**; hence `pieceWt v P` is a witness, in the BK sense, for the event that a cluster
  meets the window in at least `lam` vertices.
* `pieceWt_disjoint`: for two distinct pieces of the family, the witness edge sets are disjoint.
* `exists_open_pieces`: from `3^k * lam` marked vertices of the cluster one gets at least
  `3^(k-1)+1` pairwise disjoint open witness sets, each of order `lam` — the combinatorial input of
  (2.10).
* `markSet_inter_card`: the marked count of a piece is the same whether computed in the cluster's
  vertex type or in `V` (so the `lam ≤ #(A ∩ P) ≤ 2lam-1` bounds are literally about vertices of
  the window).

Nothing here assumes that `V` is connected, or even that the cluster of `r` spans `V`: everything
happens inside the subtype `Cl G ω r` of the one cluster of `r`.
-/
module

public import Mathlib
public import PercLib.CriticalLRP.Tightness.BFSParent

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

set_option autoImplicit true

@[expose] public section

namespace Hutchcroft

open PercLib.CriticalLRP.Percolation Hutchcroft

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V] [DecidableEq V] {E : Type*} [DecidableEq E] [Nonempty E]

/-! ### The marked vertices of one cluster -/

section Marked

variable (G : BondGraph V E) (ω : Set E) (r : V)

/-- `markSet Λ`: the vertices of the window `Λ` that lie in the cluster of `r`, regarded as
elements of the cluster's vertex type.  This is the set `A` of marked vertices to which the
tree-piece lemma is applied. -/
noncomputable def markSet (Λ : Finset V) : Finset (Cl G ω r) :=
  Λ.subtype (fun x => Conn G ω r x)

@[simp] theorem mem_markSet {Λ : Finset V} {a : Cl G ω r} :
    a ∈ markSet G ω r Λ ↔ (a : V) ∈ Λ := by
  classical
  simp [markSet]

/-- The marked count of a piece is the same computed in the cluster's vertex type and in `V`. -/
theorem markSet_inter_card (Λ : Finset V) (P : Finset (Cl G ω r)) :
    (markSet G ω r Λ ∩ P).card = (Λ ∩ P.image (Subtype.val : Cl G ω r → V)).card := by
  classical
  refine Finset.card_bij (fun a _ => (a : V)) ?_ ?_ ?_
  · intro a ha
    rw [Finset.mem_inter] at ha ⊢
    exact ⟨(mem_markSet G ω r).mp ha.1, Finset.mem_image_of_mem _ ha.2⟩
  · intro a₁ _ a₂ _ h
    exact Subtype.ext h
  · intro b hb
    rw [Finset.mem_inter] at hb
    obtain ⟨a, haP, rfl⟩ := Finset.mem_image.mp hb.2
    exact ⟨a, by rw [Finset.mem_inter]; exact ⟨(mem_markSet G ω r).mpr hb.1, haP⟩, rfl⟩

end Marked

/-! ### The parent edges of a piece, as a set of open edges -/

section Witness

variable (G : BondGraph V E) (ω : Set E) (r : V)

/-- A vertex of the cluster different from the root is different from `r` as a vertex of `V`. -/
theorem ne_val_of_ne_root {x : Cl G ω r} (h : x ≠ clRoot G ω r) : (x : V) ≠ r :=
  fun hc => h (Subtype.ext hc)

/-- The edge from a vertex of the cluster to its BFS parent (junk at the root, where there is no
parent edge). -/
noncomputable def wtEdge (x : Cl G ω r) : E :=
  if h : x = clRoot G ω r then Classical.arbitrary E
  else Classical.choose (bfsParent_open G ω r (x := x) (ne_val_of_ne_root G ω r h))

/-- At a non-root vertex the chosen edge is an open edge to the parent. -/
theorem wtEdge_spec {x : Cl G ω r} (h : x ≠ clRoot G ω r) :
    wtEdge G ω r x ∈ ω ∧ G (wtEdge G ω r x) = s((x : V), (bfsParent G ω r x : V)) := by
  classical
  unfold wtEdge
  rw [dite_eq_right h]
  exact Classical.choose_spec (bfsParent_open G ω r (x := x) (ne_val_of_ne_root G ω r h))

/-- The witness edge set of the piece `P` rooted at `v`: the parent edges of `P \ {v}`. -/
noncomputable def pieceWt (v : Cl G ω r) (P : Finset (Cl G ω r)) : Finset E :=
  (P.erase v).image (wtEdge G ω r)

theorem mem_pieceWt {v : Cl G ω r} {P : Finset (Cl G ω r)} {e : E} :
    e ∈ pieceWt G ω r v P ↔ ∃ x ∈ P.erase v, wtEdge G ω r x = e :=
  Finset.mem_image

/-- Vertices of a rooted piece other than its root are not the root of the cluster; in particular
their parent edge is a genuine open edge. -/
theorem piece_erase_ne_clRoot {v : Cl G ω r} {P : Finset (Cl G ω r)}
    (h : IsRootedPiece (bfsParent G ω r) v P) {x : Cl G ω r} (hx : x ∈ P.erase v) :
    x ≠ clRoot G ω r := by
  intro hxr
  obtain ⟨hxv, hxP⟩ := Finset.mem_erase.mp hx
  obtain ⟨n, hn⟩ := h.2.2 x hxP
  rw [hxr] at hn
  have hv : v = clRoot G ω r := hn.symm.trans (isRootedForest_fix (bfsParent_isRootedForest G ω r) n)
  exact hxv (hxr.trans hv.symm)

/-- **The witness edges of a piece are open.** -/
theorem pieceWt_subset {v : Cl G ω r} {P : Finset (Cl G ω r)}
    (h : IsRootedPiece (bfsParent G ω r) v P) : (pieceWt G ω r v P : Set E) ⊆ ω := by
  intro e he
  obtain ⟨x, hx, rfl⟩ := mem_pieceWt G ω r |>.mp he
  exact (wtEdge_spec G ω r (piece_erase_ne_clRoot G ω r h hx)).1

/-- **Two distinct vertices of the cluster have distinct parent edges.** -/
theorem wtEdge_inj {x y : Cl G ω r} (hx : x ≠ clRoot G ω r) (hy : y ≠ clRoot G ω r)
    (h : wtEdge G ω r x = wtEdge G ω r y) : x = y := by
  classical
  obtain ⟨-, hx'⟩ := wtEdge_spec G ω r hx
  obtain ⟨-, hy'⟩ := wtEdge_spec G ω r hy
  have he : s((x : V), (bfsParent G ω r x : V)) = s((y : V), (bfsParent G ω r y : V)) := by
    rw [← hx', ← hy', h]
  rcases Sym2.eq_iff.mp he with ⟨h1, -⟩ | ⟨h1, h2⟩
  · exact Subtype.ext h1
  · exfalso
    have h1' : (x : V) = (bfsParent G ω r y : V) := h1
    have h2' : (bfsParent G ω r x : V) = (y : V) := h2
    have e1 := bfsParent_bdist_succ G ω r (ne_val_of_ne_root G ω r hy)
    have e2 := bfsParent_bdist_succ G ω r (ne_val_of_ne_root G ω r hx)
    rw [← h1'] at e1
    rw [h2'] at e2
    omega

/-- **The pieces' witness sets are pairwise disjoint** (they live on disjoint vertex sets and
distinct vertices have distinct parent edges). -/
theorem pieceWt_disjoint {p q : Cl G ω r × Finset (Cl G ω r)}
    (hdisj : Disjoint (p.2.erase p.1) (q.2.erase q.1))
    (hp : IsRootedPiece (bfsParent G ω r) p.1 p.2) (hq : IsRootedPiece (bfsParent G ω r) q.1 q.2) :
    Disjoint (pieceWt G ω r p.1 p.2) (pieceWt G ω r q.1 q.2) := by
  classical
  rw [Finset.disjoint_left]
  intro e he he'
  obtain ⟨x, hx, hxe⟩ := mem_pieceWt G ω r |>.mp he
  obtain ⟨y, hy, hye⟩ := mem_pieceWt G ω r |>.mp he'
  have hxy : x = y :=
    wtEdge_inj G ω r (piece_erase_ne_clRoot G ω r hp hx) (piece_erase_ne_clRoot G ω r hq hy)
      (hxe.trans hye.symm)
  subst hxy
  exact Finset.disjoint_left.mp hdisj hx hy

/-- Transport of reachability along the coercion from the cluster to `V`. -/
theorem conn_of_reflTransGen {W : Set E} {a b : Cl G ω r}
    (h : Relation.ReflTransGen (fun x y : Cl G ω r => ∃ e ∈ W, G e = s((x : V), (y : V))) a b) :
    Conn G W (a : V) (b : V) := by
  induction h with
  | refl => exact conn_refl G W _
  | tail _ hstep ih => exact ih.tail hstep

/-- **A piece is connected through its own witness edges.**  All vertices of a rooted piece are
joined using only edges of `pieceWt v P` (in particular, all vertices of the piece lie in one
cluster of the open graph). -/
theorem piece_conn_pieceWt {v : Cl G ω r} {P : Finset (Cl G ω r)}
    (h : IsRootedPiece (bfsParent G ω r) v P) {x y : Cl G ω r} (hx : x ∈ P) (hy : y ∈ P) :
    Conn G ((pieceWt G ω r v P : Finset E) : Set E) x y := by
  classical
  have hopen : ∀ a ∈ P, a ≠ v →
      ∃ e ∈ ((pieceWt G ω r v P : Finset E) : Set E), G e = s((a : V), ((bfsParent G ω r) a : V)) := by
    intro a ha hav
    exact ⟨wtEdge G ω r a,
      mem_pieceWt G ω r |>.mpr ⟨a, Finset.mem_erase.mpr ⟨hav, ha⟩, rfl⟩,
      (wtEdge_spec G ω r (piece_erase_ne_clRoot G ω r h (Finset.mem_erase.mpr ⟨hav, ha⟩))).2⟩
  have hsymm : Std.Symm fun a b : Cl G ω r =>
      ∃ e ∈ ((pieceWt G ω r v P : Finset E) : Set E), G e = s((a : V), (b : V)) := by
    constructor
    rintro a b ⟨e, he, hE⟩
    exact ⟨e, he, by rw [hE, Sym2.eq_swap]⟩
  exact conn_of_reflTransGen G ω r (isRootedPiece_reachable _ hsymm h hopen hx hy)

end Witness

/-! ### The pieces of a cluster, with open disjoint witnesses -/

section Pieces

variable (G : BondGraph V E) (ω : Set E) (r : V)

/-- **Disjoint open witnesses for the `3^k λ`-to-`λ` step, inside one cluster.**

Let `Λ` be a finite window and suppose the cluster of `r` contains at least `3^k * lam` vertices of
`Λ`.  Then there is a family `s` of at least `3^(k-1)+1` rooted pieces of the BFS parent tree of the
cluster, each carrying between `lam` and `2*lam - 1` marked vertices, such that

* the parent-edge set `pieceWt v P` of each piece is a set of **open** edges,
* the sets `pieceWt v P` are **pairwise disjoint**,
* each piece is **connected through its own witness set** and therefore certifies, using only its
  own edges, the event that a cluster meets the window `Λ` in at least `lam` vertices — the
  disjoint-occurrence inputs of (2.10) in arXiv:2008.11197v2.

No connectivity of `V`, and no global root, is assumed: everything happens in the cluster of `r`. -/
theorem exists_open_pieces (Λ : Finset V) {lam k : ℕ} (hlam : 2 ≤ lam) (hk : 1 ≤ k)
    (hΛ : 3 ^ k * lam ≤ (markSet G ω r Λ).card) :
    ∃ s : Finset (Cl G ω r × Finset (Cl G ω r)),
      3 ^ (k - 1) + 1 ≤ s.card ∧
      (∀ p ∈ s, IsRootedPiece (bfsParent G ω r) p.1 p.2) ∧
      (∀ p ∈ s, lam ≤ (markSet G ω r Λ ∩ p.2).card ∧
        (markSet G ω r Λ ∩ p.2).card ≤ 2 * lam - 1) ∧
      (∀ p ∈ s, (pieceWt G ω r p.1 p.2 : Set E) ⊆ ω) ∧
      (∀ p ∈ s, ∀ q ∈ s, p ≠ q →
        Disjoint (pieceWt G ω r p.1 p.2) (pieceWt G ω r q.1 q.2)) ∧
      (∀ p ∈ s, ∃ t : Finset V, t ⊆ Λ ∧ lam ≤ t.card ∧ ∃ u : V, ∀ y ∈ t,
        Conn G ((pieceWt G ω r p.1 p.2 : Finset E) : Set E) u y) := by
  classical
  obtain ⟨s, hcard, hpiece, hmark, hdisj⟩ :=
    exists_tree_pieces (bfsParent_isRootedForest G ω r) (markSet G ω r Λ) hlam hk hΛ
  refine ⟨s, hcard, hpiece, hmark, ?_, ?_, ?_⟩
  · intro p hp
    exact pieceWt_subset G ω r (hpiece p hp)
  · intro p hp q hq hpq
    exact pieceWt_disjoint G ω r (hdisj p hp q hq hpq) (hpiece p hp) (hpiece q hq)
  · intro p hp
    obtain ⟨v, P⟩ := p
    have hP : IsRootedPiece (bfsParent G ω r) v P := hpiece _ hp
    have hne : P.erase v ⊆ P := Finset.erase_subset v P
    -- a root of the piece: the piece is nonempty since it carries `lam ≥ 2 ≥ 1` marked vertices
    have hpos : 0 < (markSet G ω r Λ ∩ P).card := lt_of_lt_of_le (by omega) (hmark _ hp).1
    have hne' : (markSet G ω r Λ ∩ P).Nonempty := Finset.card_pos.mp hpos
    obtain ⟨u, hu⟩ := hne'
    have huP : u ∈ P := (Finset.mem_inter.mp hu).2
    refine ⟨(markSet G ω r Λ ∩ P).image (Subtype.val : Cl G ω r → V), ?_, ?_, u, ?_⟩
    · intro y hy
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hy
      exact (mem_markSet G ω r).mp (Finset.mem_inter.mp ha).1
    · rw [Finset.card_image_of_injective _ (fun a b h => Subtype.ext h)]
      exact (hmark _ hp).1
    · intro y hy
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hy
      exact piece_conn_pieceWt G ω r hP huP (Finset.mem_inter.mp ha).2

end Pieces

end Hutchcroft
