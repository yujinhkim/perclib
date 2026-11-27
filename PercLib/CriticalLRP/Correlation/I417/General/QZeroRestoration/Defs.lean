/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Accepted from Ultramath `smwzg77c3`, member `m8`, independently rebuilt.
Production integration based on commit `81c6038182e9a883ffcd3d870aed7cd4829649d4`.
Original direction d8.

# The restored two-copy moment of Lemma I.4.17 (definition layer)

Source: Tom Hutchcroft, *Critical long-range percolation I: High effective dimension*,
arXiv:2508.18807v1, Lemma I.4.17 and its proof (pp. 45–46).

The printed proof works with the *restoration coupling* of Lemma I.4.12: for independent
configurations `ω₁` (base) and `ω₂` (fresh), the restored configuration is
`ω̃ = forceOn (touchSet ω₁ x)ᶜ ω₂ ω₁`, i.e. `ω̃(e) = ω₁(e)` on every edge touching the base cluster
`K_x(ω₁)` and `ω̃(e) = ω₂(e)` otherwise (this is `restoreMap x`).  The lemma's left-hand side is
built from the **restored** cluster `K̃_y = K_y(ω̃)`:

```
E|K|^p E|K|^q − E[|K_x|^p |K̃_y|^q 1(x ↮ y)]  =  E[|K_x|^p |K̃_y|^q 1(y ∈ K_x)] .
```

This file introduces exactly the two objects of that identity.

* `restoredTotal π x y p q = ∫∫ |K_x(ω₁)|^p |K̃_y(ω)|^q` — the restored two-copy *total*;
* `restoredDiag  π x y p q = ∫∫ 1(y ∉ K_x(ω₁)) |K_x(ω₁)|^p |K̃_y(ω)|^q` — its excluded part;
* `restoredConn  π x y p q = ∫∫ 1(y ∈ K_x(ω₁)) |K_x(ω₁)|^p |K̃_y(ω)|^q` — the connected part.

`restoredConn` is the object `Main.lean` identifies with the `q = 0` connected star moment
`I417Gen.starMoment`.  Nothing is asserted here; this is a definition layer.
-/
module

public import PercLib.CriticalLRP.Correlation.I417.General.QZeroStar.Defs

/-! # Restored two-copy moments -/

noncomputable section

open MeasureTheory Measure ProbabilityTheory unitInterval
open scoped ENNReal NNReal

@[expose] public section

namespace PercLib.CriticalLRP.I417Gen

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Countable V]

/-- The restored two-copy **connected** moment of Lemma I.4.17 at `(x,y)`: the `(μ ⊗ μ)`-integral of
`1(y ∈ K_x(ω₁)) · |K_x(ω₁)|^p · |K_y(ω̃)|^q`, where `ω̃ = restoreMap x (ω₂,ω₁)` is the restored
configuration of the printed proof (`ρ.1` is the fresh copy `ω₂`, `ρ.2` the base copy `ω₁`). -/
noncomputable def restoredConn (π : Sym2 V → unitInterval) (x y : V) (p q : ℕ) : ℝ≥0∞ :=
  ∫⁻ ρ : Config V × Config V,
    (cluster ρ.2 x).indicator (fun _ => (1 : ℝ≥0∞)) y *
      (Percolation.cardFun (cluster ρ.2 x) ^ p *
        Percolation.cardFun (cluster (restoreMap x ρ) y) ^ q)
    ∂((edgeMeasure π).prod (edgeMeasure π))

/-- The restored two-copy **excluded** (diagonal) moment: the same integrand with `y ∉ K_x(ω₁)`. -/
noncomputable def restoredDiag (π : Sym2 V → unitInterval) (x y : V) (p q : ℕ) : ℝ≥0∞ :=
  ∫⁻ ρ : Config V × Config V,
    (cluster ρ.2 x)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) y *
      (Percolation.cardFun (cluster ρ.2 x) ^ p *
        Percolation.cardFun (cluster (restoreMap x ρ) y) ^ q)
    ∂((edgeMeasure π).prod (edgeMeasure π))

/-- The restored two-copy **total** moment `∫∫ |K_x(ω₁)|^p |K̃_y(ω)|^q`, without the indicator.
`restoredConn + restoredDiag = restoredTotal` by the indicator split. -/
noncomputable def restoredTotal (π : Sym2 V → unitInterval) (x y : V) (p q : ℕ) : ℝ≥0∞ :=
  ∫⁻ ρ : Config V × Config V,
    Percolation.cardFun (cluster ρ.2 x) ^ p *
      Percolation.cardFun (cluster (restoreMap x ρ) y) ^ q
    ∂((edgeMeasure π).prod (edgeMeasure π))

end PercLib.CriticalLRP.I417Gen
