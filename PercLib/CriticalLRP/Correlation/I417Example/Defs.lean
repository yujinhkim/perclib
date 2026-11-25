/- Integrated from independently rebuilt Ultramath work, base revision 75f8858d8e30ea17b20f9ff1d216bc1508c01ce2.
Scratch source: ../../.ultramath/smwpxw774/m1/S474A/Defs.lean ; module path rewritten only.
-/

/-
# Lemma I.4.17, `p = 2`, `q = 1`: the five-edge tree diagrams for `E[|Kx|² 1(w ∈ Kx)]`

Direction A of swarm `smwpxw774`.  Object of study (definitions only in this file):

  `jointSq π x w = E[|Kx|² 1(w ∈ Kx)] = ∑_{x₁,x₂} P(x₁, x₂, w ∈ Kx)`

(the last identity is `PercLib.CriticalLRP.I417.tsum_tsum_inter_mark_eq`, from direction B of
swarm `smwpwq50m`).  The event `{x₁, x₂, w ∈ Kx}` is the four-point connectivity event; its
tree-graph expansion with root `x` and three summed terminals `w, x₁, x₂` produces the three
rooted binary trees with three labelled leaves, i.e. the five-edge diagrams

* `D2 u v`     : `x — u — w` with a two-leaf branch `u — v — {x₁, x₂}`  (`w` at depth 2),
* `D3a u v`    : `x — v — u — w` with `x₁` at `u` and `x₂` at `v`      (`w` at depth 3),
* `D3b u v`    : `x — u — v — w` with `x₁` at `u` and `x₂` at `v`      (`w` at depth 3),

where every edge is a two-point connection event `connSet · ·`.  The drawing is the one of the
printed figure of Lemma I.4.17 at `p = 2`, `q = 1` after the two fresh arms `w — y` and
`w — y₁` are attached (see `I417Example/Excess.lean`).

Each diagram is encoded as the five-fold *disjoint occurrence* (`Tree5`) of its edge events,
which is what the iterated BK inequality bounds by the product of the five two-point
functions.  The definitions live here; all proofs are in the other files.
-/
module

public import PercLib.CriticalLRP.Correlation.I417.Defs
public import PercLib.CriticalLRP.Correlation.TreeGraphCanonical
public import PercLib.CriticalLRP.BK.Finite

open MeasureTheory Measure ProbabilityTheory unitInterval
open scoped ENNReal NNReal

@[expose] public section

namespace PercLib.CriticalLRP.I417Example

variable {V : Type*} [Countable V]

attribute [local instance] Classical.propDecidable

/-- **Five-fold disjoint occurrence** of the events `A, B, C, D, E`: the configuration contains
five pairwise disjoint finite witnesses, one for each event.  This is
`Percolation.DisjointOccurrenceFin` for the vector `![A, B, C, D, E]`. -/
def Tree5 (A B C D E : Set (Config V)) : Set (Config V) :=
  Percolation.DisjointOccurrenceFin (fun i : Fin 5 => ![A, B, C, D, E] i)

/-- The `w`-at-depth-2 five-edge diagram at `(u, v)`:
`{x↔u} ∘ {u↔w} ∘ {u↔v} ∘ {v↔x₁} ∘ {v↔x₂}`. -/
def D2 (x w x₁ x₂ u v : V) : Set (Config V) :=
  Tree5 (connSet x u) (connSet u w) (connSet u v) (connSet v x₁) (connSet v x₂)

/-- The first `w`-at-depth-3 five-edge diagram at `(u, v)`:
`{x↔v} ∘ {v↔u} ∘ {u↔w} ∘ {u↔x₁} ∘ {v↔x₂}` (the path from `x` to `w` enters the branch
point `u` from the `v`-side; `x₁` sits at `u` and `x₂` at `v`). -/
def D3a (x w x₁ x₂ u v : V) : Set (Config V) :=
  Tree5 (connSet x v) (connSet v u) (connSet u w) (connSet u x₁) (connSet v x₂)

/-- The second `w`-at-depth-3 five-edge diagram at `(u, v)`:
`{x↔u} ∘ {u↔v} ∘ {v↔w} ∘ {u↔x₁} ∘ {v↔x₂}` (the path from `x` to `w` passes through `u`
first; `x₁` sits at `u` and `x₂` at `v`). -/
def D3b (x w x₁ x₂ u v : V) : Set (Config V) :=
  Tree5 (connSet x u) (connSet u v) (connSet v w) (connSet u x₁) (connSet v x₂)

/-- The finite set of edges of a list, with the classical decidable equality fixed once and for
all.  Using a named definition (rather than `List.toFinset` at each occurrence) keeps the
elaborated `DecidableEq` instance from varying between statements. -/
noncomputable def edgeFinset {V : Type*} (l : List (Sym2 V)) : Finset (Sym2 V) := l.toFinset

@[simp] theorem mem_edgeFinset {V : Type*} {l : List (Sym2 V)} {a : Sym2 V} :
    a ∈ edgeFinset l ↔ a ∈ l := by
  classical
  simp [edgeFinset]

theorem edgeFinset_coe {V : Type*} (l : List (Sym2 V)) :
    ((edgeFinset l : Finset (Sym2 V)) : Set (Sym2 V)) = {a | a ∈ l} := by
  ext a
  simp

end PercLib.CriticalLRP.I417Example
