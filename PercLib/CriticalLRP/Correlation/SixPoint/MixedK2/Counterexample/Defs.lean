/-
Coordinator-integrated from the independently rebuilt `smwxb4a1l/m3` Line6 artifact
at production base `8d1c9eb3738a26cc63afc07f525ba4af357bd905`.
-/
/-
Counterexample data for the `p = 5`, `k = 2` two-hub slot bound of
`PercLib.CriticalLRP.TreeExpansion.HubK2`.

Ultramath swarm `smwxb4a1l`, member `m3`, direction `HUB-LINK-COUNTEREXAMPLE`.

The vertex type is `Fin 6`, and the profile opens only the five consecutive pairs
`0—1`, `1—2`, `2—3`, `3—4`, `4—5` of the line `0—1—2—3—4—5`, each with probability `θ`.
The five leaves of the counterexample are the five non-root vertices `1,2,3,4,5`.
Everything here is data: the probabilistic and combinatorial statements live in the
sibling modules.
-/
module

public import PercLib.CriticalLRP.Correlation.SixPoint.MixedK2.Assembly

/-!
# Definitions for the six-vertex line counterexample
-/

@[expose] public section

namespace PercLib.CriticalLRP.Counterexample.Line6

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators
open PercLib.Percolation.Bond
open PercLib.Probability

/-- The vertex of `Fin 6` at position `i`. -/
def vt (i : ℕ) (h : i < 6) : Fin 6 := ⟨i, h⟩

/-- The `i`-th edge `i—(i+1)` of the line `0—1—2—3—4—5`. -/
def peAt (i : ℕ) (h : i < 5) : Sym2 (Fin 6) := s(vt i (by omega), vt (i + 1) (by omega))

/-- The five edges of the line. -/
def lineEdges : Finset (Sym2 (Fin 6)) :=
  (Finset.range 5).attach.image fun p =>
    peAt p.val (by have h := p.prop; simp only [Finset.mem_range] at h; omega)

/-- The profile that opens exactly the five line edges, each with probability `θ`. -/
def lineProfile (θ : unitInterval) : Sym2 (Fin 6) → unitInterval :=
  fun e => if e ∈ lineEdges then θ else 0

/-- The opening probability used in the counterexample, `1/64`. -/
noncomputable def theta : unitInterval := ⟨1 / 64, by norm_num⟩

/-- The opening probability `1/64` as an `ℝ≥0∞`-valued weight. -/
noncomputable def eps : ℝ≥0∞ := ((unitInterval.toNNReal theta : ℝ≥0) : ℝ≥0∞)

/-- The set of line edges spanned by `x` and `y`. -/
def seg (x y : Fin 6) : Finset (Sym2 (Fin 6)) :=
  (Finset.Ico (min x.val y.val) (max x.val y.val)).attach.image fun p =>
    peAt p.val (by have h := p.prop; simp only [Finset.mem_Ico] at h; omega)

/-- The neighbour of `x` on the line towards the vertex at position `6`. -/
def nxt (x : Fin 6) (hx : x.val < 5) : Fin 6 := ⟨x.val + 1, by omega⟩

/-- The number of line edges between `x` and `y`, i.e. the line distance. -/
def pdist (x y : Fin 6) : ℕ := max x.val y.val - min x.val y.val

/-- The five leaves `1,2,3,4,5` of the line, in slot order. -/
def leaves : Fin 5 → Fin 6 := ![1, 2, 3, 4, 5]

/-- The set of configurations whose open pairs are all line edges. -/
def lineSupport : Set (Config (Fin 6)) := {ω | ω ⊆ (lineEdges : Set (Sym2 (Fin 6)))}

/-- The configurations with an open pair outside the line. -/
def lineSupportCompl : Set (Config (Fin 6)) :=
  ⋃ (e : {e : Sym2 (Fin 6) // e ∉ lineEdges}),
    {ω : Config (Fin 6) | (e.1 : Sym2 (Fin 6)) ∈ ω}

end PercLib.CriticalLRP.Counterexample.Line6
