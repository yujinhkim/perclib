/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
-/

module

public import PercLib.CriticalLRP.Correlation.I411.Basic

@[expose] public section

namespace PercLib.CriticalLRP.TreeExpansion

open Set
open scoped ENNReal
open PercLib.Percolation.Bond

variable {V : Type*}
/-! ### Definitions (to move to `Defs.lean`) -/

/-- The five edge lists of one labelled binary tree on the four leaves `root, a, b, c`:
`root` and `a` are joined at the branch vertex `u`, `b` and `c` at `v`, and `u` is joined to `v`
by the spine.  The five arms are required to have pairwise disjoint edge lists, which is exactly
what the BK inequality consumes.  Taking `u = v` gives the degenerate star trees (the spine is
then the empty walk), so all four-arm star configurations are included. -/
def ShapeWitness (G : SimpleGraph V) (root a b c u v : V) : Prop :=
  ∃ (p : G.Walk root u) (q : G.Walk a u) (s : G.Walk b v) (t : G.Walk c v) (r : G.Walk u v),
    p.edges.Disjoint q.edges ∧ p.edges.Disjoint s.edges ∧ p.edges.Disjoint t.edges ∧
    p.edges.Disjoint r.edges ∧ q.edges.Disjoint s.edges ∧ q.edges.Disjoint t.edges ∧
    q.edges.Disjoint r.edges ∧ s.edges.Disjoint t.edges ∧ s.edges.Disjoint r.edges ∧
    t.edges.Disjoint r.edges

/-- The event that five pairwise disjoint finite certificates force the five connections
`root↔u`, `a↔u`, `b↔v`, `c↔v` and `u↔v`, all inside `ω`. -/
def ShapeEvent (root a b c u v : V) : Set (Config V) :=
  {ω | ∃ W₀ W₁ W₂ W₃ W₄ : Set (Sym2 V),
        W₀.Finite ∧ W₁.Finite ∧ W₂.Finite ∧ W₃.Finite ∧ W₄.Finite ∧
        W₀ ⊆ ω ∧ W₁ ⊆ ω ∧ W₂ ⊆ ω ∧ W₃ ⊆ ω ∧ W₄ ⊆ ω ∧
        W₀ ∈ conn root u ∧ W₁ ∈ conn a u ∧ W₂ ∈ conn b v ∧ W₃ ∈ conn c v ∧
        W₄ ∈ conn u v ∧
        Disjoint W₀ W₁ ∧ Disjoint W₀ W₂ ∧ Disjoint W₀ W₃ ∧ Disjoint W₀ W₄ ∧
        Disjoint W₁ W₂ ∧ Disjoint W₁ W₃ ∧ Disjoint W₁ W₄ ∧
        Disjoint W₂ W₃ ∧ Disjoint W₂ W₄ ∧ Disjoint W₃ W₄}

/-! ### From walks to certificates -/

/-- The set of edges of a walk, as a subset of the configuration space. -/
noncomputable def walkEdges [Countable V] {ω : Config V} {a b : V}
    (p : (openGraph ω).Walk a b) : Set (Sym2 V) :=
  {e | e ∈ p.edges}


end PercLib.CriticalLRP.TreeExpansion
