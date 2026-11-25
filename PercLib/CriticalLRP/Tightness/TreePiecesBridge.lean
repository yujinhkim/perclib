/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
Bridge between the tree-partition lemma (`TreePieces.lean`) and the repository's percolation
language (`BondGraph`, `Conn`, `cluster`), showing that each tree piece is a connected witness:
if the parent edges of a piece are open then all its vertices lie in one cluster, hence the piece
certifies that the cluster of any of its points meets `Λ` in at least `lam` vertices.  This is the
set-theoretic half of step (2.10)/(2.11) in the proof of Theorem I.2.3 (BK witnesses).
-/
module

public import PercLib.CriticalLRP.Tightness.TreePieces
public import PercLib.CriticalLRP.BK.Graph

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

set_option autoImplicit true

@[expose] public section

namespace Hutchcroft

open PercLib.CriticalLRP.Percolation

variable {V : Type*} [Fintype V] [DecidableEq V] {E : Type*}

/-- The open-edge adjacency relation of a configuration is symmetric. -/
theorem openAdj_symm (G : BondGraph V E) (ω : Set E) :
    Std.Symm (fun x y => ∃ e ∈ ω, G e = s(x, y)) := by
  constructor
  intro a b ⟨e, he, hE⟩
  exact ⟨e, he, by rw [hE, Sym2.eq_swap]⟩

/-- **Pieces are clusters.**  If every parent edge of a rooted piece is open, then all vertices of
the piece lie in a single cluster. -/
theorem piece_conn (G : BondGraph V E) (ω : Set E) {pp : V → V} {v : V} {P : Finset V}
    (h : IsRootedPiece pp v P)
    (hopen : ∀ x ∈ P, x ≠ v → ∃ e ∈ ω, G e = s(x, pp x))
    {x y : V} (hx : x ∈ P) (hy : y ∈ P) : Conn G ω x y :=
  isRootedPiece_reachable (fun a b => ∃ e ∈ ω, G e = s(a, b)) (openAdj_symm G ω) h hopen hx hy

/-- **Pieces are disjoint witnesses.**  If a rooted piece has `lam` vertices in `Λ` and its parent
edges are open, then for every point `u` of the piece the event "the cluster of `u` meets `Λ` in
at least `lam` vertices" holds — the event for which the BK inequality is applied in the source. -/
theorem piece_witness (G : BondGraph V E) (ω : Set E) {pp : V → V} {v : V} {P : Finset V}
    {Λ : Finset V} {lam : ℕ} {u : V} (h : IsRootedPiece pp v P) (hu : u ∈ P)
    (hopen : ∀ x ∈ P, x ≠ v → ∃ e ∈ ω, G e = s(x, pp x))
    (hmark : lam ≤ (Λ ∩ P).card) :
    ∃ t : Finset V, t ⊆ Λ ∧ lam ≤ t.card ∧ ∀ y ∈ t, Conn G ω u y := by
  refine ⟨Λ ∩ P, Finset.inter_subset_left, hmark, ?_⟩
  intro y hy
  exact piece_conn G ω h hopen hu (Finset.mem_inter.mp hy).2

end Hutchcroft
