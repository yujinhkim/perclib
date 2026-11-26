/-
Independently built for swarm `smwxcafk7`, member `m1`, direction
`GENERAL-Q-WEIGHTED-EVALUATION`.  Read-only against production
`repo/.scratch/critical-lrp-orchestration` at HEAD `8d1c9eb`.

Definitions only, as required; every other file of this directory contains theorems.
-/
module

public import PercLib.CriticalLRP.Correlation.I417.Fresh.Eval.Moment
public import PercLib.CriticalLRP.Correlation.I417.Fresh.Depth.Main

/-!
# Definitions for the generic spine tree-sum (`GENERAL-Q-WEIGHTED-EVALUATION`)

Source: T. Hutchcroft, *Critical long-range percolation I: High effective dimension*,
arXiv:2508.18807v1, Lemma I.4.17 and its proof (supplied paper text pp. 43--46, lines 2444--2513):

> "We obtain a bound in terms of tree diagrams with two pinned vertices at `x` and `y`, with
> `2p + 2q + 1` edges in total, some number `3 ≤ ℓ ≤ p + q + 1` of them belong to the path
> connecting `x` and `y`."

The fresh side of that lemma is a tree diagram with `2q` legs, the pin `y` as its root, the mark `w`
an interior vertex, and one two-point factor `τ` per leg.  Evaluating such a diagram means summing
it over *all* free vertices.  Two objects capture that sum independently of the diagram's shape:

* `Hang` --- a hanging rooted forest.  Its value `Hang.val` is the nested vertex-sum of the product
  of the two-point factors of the forest's legs, and `Hang.size` is the number of its vertices.  A
  forest hanging from a vertex `a` contributes exactly one `χ` per vertex (`Hang.val_eq_pow` in
  `SpineSum.lean`), **for every base vertex `a`**.  That base-independence is what removes the
  dependence on the peel order and hence on the branch.
* `spineVal` --- a `y`--`w` chain of `ℓ` legs with a hanging forest at every spine vertex.  Its
  chain recursion is peeled at `y`, i.e. it matches `I417Base.iterPow`'s own recursion
  `iterPow k (n+1) y w = ∑_u k y u * iterPow k n u w`, so the spine evaluates to `T^ℓ(y,w)`
  (`spineVal_eq`).

Production's general-`q` fresh evaluation (`I417GenIter.GenFreshEval`) is proved at `q = 4` by
enumerating the 48 members of the cover with one hand-chosen peel order each
(`Fresh/Eval/Branch.lean`) and would need 384 at `q = 5`; no uniform nested-sum order exists, since
the peel order depends on the branch.  `spineVal` is the order-free normal form: every tree diagram
with a distinguished `y`--`w` spine is *one* `spineVal` instance, whatever the tree.

The profile comparison at `q = 5` uses the already integrated
`I417FreshFive.freshFiveProfile`; no candidate-specific profile definition is duplicated.
The analytic evaluation here does not identify `Hist.legs` with a spine diagram.-/

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.style.longLine false
set_option linter.style.show false





open MeasureTheory Measure ProbabilityTheory unitInterval
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.style.longLine false

@[expose] public section

namespace PercLib.CriticalLRP.I417FreshGenSpine

open PercLib.CriticalLRP

variable {V : Type*}

/-! ## Hanging rooted forests -/

/-- **A hanging rooted forest.**  `nil` is the empty forest; `cons c r` is the forest whose first
tree is a root carrying the (already flattened) forest `c` of its children, followed by `r`.

The type is deliberately vertex-free: a forest is pure shape, and its value below is a number that
does not depend on the vertex it hangs from.  This is what makes the peel uniform --- unlike the
per-branch peel orders of `Fresh/Eval/Branch.lean`. -/
inductive Hang : Type
  | nil : Hang
  | cons : Hang → Hang → Hang

namespace Hang

/-- Number of vertices of a hanging forest; each vertex contributes exactly one leg. -/
def size : Hang → ℕ
  | .nil => 0
  | .cons c r => c.size + 1 + r.size

/-- The value of a hanging forest rooted at the vertex `a`: the nested sum over the values of *all*
forest vertices of the product of the two-point factors `tau` of all forest legs. -/
noncomputable def val (tau : V → V → ℝ≥0∞) : Hang → V → ℝ≥0∞
  | .nil, _ => 1
  | .cons c r, a => (∑' b : V, tau a b * val tau c b) * val tau r a

/-- A forest of `m` single arms hanging from the same vertex. -/
def star : ℕ → Hang
  | 0 => .nil
  | (m + 1) => .cons .nil (star m)

end Hang

variable [DecidableEq V]

/-- **The value of a decorated `y`--`w` spine.**  `Fs : Fin (ℓ+1) → Hang` records the hanging
forest at each spine vertex: `Fs 0` at `y`, `Fs ℓ` at `w`, and `Fs i` at the `i`-th interior spine
vertex.  The chain is peeled at `y`, which matches `I417Base.iterPow`'s recursion. -/
noncomputable def spineVal (tau : V → V → ℝ≥0∞) :
    (ℓ : ℕ) → (Fin (ℓ + 1) → Hang) → V → V → ℝ≥0∞
  | 0, Fs, y, w => if y = w then Hang.val tau (Fs 0) y else 0
  | (ℓ + 1), Fs, y, w =>
      Hang.val tau (Fs 0) y *
        ∑' u : V, tau y u * spineVal tau ℓ (fun i : Fin (ℓ + 1) => Fs i.succ) u w

variable [Countable V]


end PercLib.CriticalLRP.I417FreshGenSpine
