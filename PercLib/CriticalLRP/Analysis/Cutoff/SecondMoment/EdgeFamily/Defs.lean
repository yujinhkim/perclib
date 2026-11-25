/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

# The `p = 2` oriented endpoint-pair weight and the unordered edge weight

Swarm `smwvc1d9z`, member `m2`, direction `d1`

Integration donor: `.ultramath/smwvc1d9z/m2`; independently reviewed at
`a6a74fb05eb13da61d4ce2cb87e2f55e7bd7c31f` after one connectivity-composition repair in `Count.lean`. (unordered-edge orientation count).

At `p = 2` the quadratic increment of a cluster volume carried by a single edge `{x,y}` is the
*sum of its two orientations*: the exact `ℝ≥0∞` value proved in `RussoInf/Merge`
(`flipDiff_clusterVol_sq_eq_cases`) is `2|K_o||K_y| + |K_y|²` for the orientation whose base
point already lies in the cluster of the root, and `0` for the other one.  This file records the
two weights as definitions and nothing else:

* `quadPairWeight dt ω o b c` — the exact quadratic increment carried by the *oriented* pair
  `(b,c)`: it fires when `b` is connected to the root `o`, `c` is not connected to `b`, and the
  range predicate `dt c b` holds, and then contributes `2|K_b||K_c| + |K_c|²`.  The two cluster
  volumes are those of the two endpoints; on the event `o ↔ b` they agree with `|K_o|`, which is
  what makes the weight the increment of `|K_o|²`.
* `quadEdgeWeight dt ω o e` — the unordered-edge version, i.e. the sum of the two orientations
  of `e`, packaged through `Sym2.lift`.

No theorem is proved here (this is a definition module).  The orientation count
(`∑_{b,c} [s(b,c) = e] · quadPairWeight b c = quadEdgeWeight e`) and the edge-to-vertex
identity are in the companion files.
-/
module

public import PercLib.CriticalLRP.RussoInf.Merge

/-!
# Quadratic endpoint-pair weights (definitions)

`quadPairWeight` and `quadEdgeWeight` only; the exactness of `quadEdgeWeight` as the increment
of `|K_o|²` at a closed edge is the donor lemma `clusterVol_sq_union_pair_eq_add_quadEdgeWeight`
(not restated here to keep this module a pure definition layer).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open scoped ENNReal

namespace PercLib.CriticalLRP

attribute [local instance] Classical.propDecidable

variable {V : Type*}

/-- **The `p = 2` oriented endpoint-pair weight.**  For a range predicate `dt`, a configuration
`ω` and a root `o`, the oriented pair `(b,c)` contributes the exact quadratic increment
`2 |K_b| |K_c| + |K_c|^2` when `b` is connected to `o`, `c` is not connected to `b`, and
`dt c b` holds (in the source: `M.S.dist c b ≤ r`).

The two cluster volumes are the *clusters of the two endpoints*, not of the root; on the event
`b ↔ o` they agree with `|K_o|`, which is what makes this the exact increment. -/
noncomputable def quadPairWeight (dt : V → V → Prop) (ω : Config V) (o : V) (b c : V) : ℝ≥0∞ :=
  (if Connects ω o b then (1 : ℝ≥0∞) else 0) * (if dt c b then 1 else 0) *
    (if ¬ Connects ω b c then 1 else 0) *
      (2 * clusterVol ω b * clusterVol ω c + clusterVol ω c ^ 2)

/-- **The `p = 2` unordered edge weight**: the sum of the two orientations of the edge.  This is
the exact `ℝ≥0∞` increment of `|K_o|^2` when the closed edge is opened
(`clusterVol_sq_union_pair_eq_add_quadEdgeWeight`, donor file `smwvbcnfb/m2/EdgeToVertex.lean`). -/
noncomputable def quadEdgeWeight (dt : V → V → Prop) (ω : Config V) (o : V) (e : Sym2 V) : ℝ≥0∞ :=
  Sym2.lift ⟨fun x y => quadPairWeight dt ω o x y + quadPairWeight dt ω o y x,
    fun _ _ => add_comm _ _⟩ e

end PercLib.CriticalLRP
