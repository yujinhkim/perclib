/-
Ultramath swarm `smwziumdb`, member `m7`, direction `d4`.

Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Accepted and independently rebuilt from Ultramath `smwziumdb`.
Supporting integration based on production commit `5d2d681b941eb1c687f1ba17e6a798b8f0175aa0`.

# The four-label event realization of the `q = 0`, `p = 3` star in the canonical model

`Defs.lean` fixes the atlas side (`starLabels`, `starAtlasSum`).  This file proves the
realization

  `E[|K_x|³ 1(x ↔ y)]  ≤  ∑_{x_1 x_2 x_3} ∑_{t} ∑_{φ} ∏_{e ∈ AEdge t} P(srcPos e ↔ dstPos e)`

for the canonical countable model, with **no** hypothesis beyond `π e < 1`: the labelled event
`{x_1, x_2, x_3 ∈ K_x} ∩ {x ↔ y}` is literally the four-label event of the tuple
`(x_1, x_2, x_3, y)`, so production's covering + per-diagram BK chain
(`CanonAtlas.Measure.measure_labelEvent_le_tsum_shapes_bk`, which is unconditional) applies at
`q = 4`.

What this does and does not settle.  The displayed inequality is the `q = 0`, `p = 3` instance
of (I.2.2) in the source's own diagram language: fifteen rooted binary trees on four labels,
seven edges each (`2p + 2q + 1` at `p = 3`, `q = 0`), the mark `y` pinned as the last leaf
label.  It does **not** by itself perform the two evaluations that turn the right-hand side
into the printed polygon monomials: the grouping of the fifteen shapes by the length `ℓ` of
the root-to-`y` path, and the leaf/internal sum `χ^(7-ℓ) k^ℓ(x,y)` of each shape.  In
particular nothing here removes the `ℓ = 2` class, which the printed range `3 ≤ ℓ ≤ p+q+1`
does not cover at `q = 0`.

No `sorry`, no custom axioms.
-/
module

public import PercLib.CriticalLRP.Correlation.I417.General.QZeroStarAtlas4.Defs

/-! # Canonical realization of the four-labelled star event -/

open MeasureTheory Measure ProbabilityTheory unitInterval
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false

@[expose] public section

namespace PercLib.CriticalLRP.QZeroStarAtlas4

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Countable V]

/-! ## The labelled event of the marked tuple -/

/-- **The `(3+1)`-point event is a four-label event.**  Requiring the three arms `f` to lie in
the cluster of `x` *and* `x ↔ y` is the same as requiring the four labels
`(f 0, f 1, f 2, y)` to lie in the cluster of `x`. -/
theorem labelEvent_starLabels (x y : V) (f : Fin 3 → V) :
    I417A.labelEvent x (starLabels f y) = I417A.labelEvent x f ∩ connSet x y := by
  ext ω
  simp only [I417A.labelEvent, Set.mem_ofPred_eq, Set.mem_inter_iff, connSet, mem_cluster_iff]
  constructor
  · intro h
    exact ⟨fun i => by simpa using h i.castSucc, by simpa using h (Fin.last 3)⟩
  · rintro ⟨h1, h2⟩ i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa using h2
    · simpa using h1 j

/-! ## The realization -/

/-- **The four-label event realization of the `q = 0`, `p = 3` star.**  The star moment is
dominated by the canonical atlas sum: the fifteen labelled four-leaf shapes with the positions
of their three internal vertices summed over, and the product of the two-point function over the
seven atlas edges of each shape. -/
theorem starMoment_le_starAtlasSum (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1) (x y : V) :
    I417Gen.starMoment π x y 3 ≤ starAtlasSum π x y := by
  rw [I417Gen.starMoment_eq_tsum_labelEvent]
  refine ENNReal.tsum_le_tsum fun f => ?_
  rw [← labelEvent_starLabels]
  exact CanonAtlas.Measure.measure_labelEvent_le_tsum_shapes_bk (q := 4) π hπ (by norm_num) x
    (starLabels f y)

/-- The same realization with the sums reordered, shape-major: the outer sum runs over the
fifteen shapes, then over that shape's internal positions, then over the three arms. -/
theorem starMoment_le_tsum_shapes (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1) (x y : V) :
    I417Gen.starMoment π x y 3 ≤
      ∑' t : PercLib.CriticalLRP.TreeExpansion.LTon (Fin 4) Finset.univ,
        ∑' φ : t.1.IPos → V, ∑' f : Fin 3 → V,
          CanonAtlas.Measure.atlasProduct π x (starLabels f y) t.1 φ := by
  refine le_trans (starMoment_le_starAtlasSum π hπ x y) (le_of_eq ?_)
  simp only [starAtlasSum]
  rw [ENNReal.tsum_comm]
  exact tsum_congr fun t => ENNReal.tsum_comm

end PercLib.CriticalLRP.QZeroStarAtlas4
