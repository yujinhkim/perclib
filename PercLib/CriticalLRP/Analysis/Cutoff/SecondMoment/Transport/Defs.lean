/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

# Vertex-side pair weights of the `p = 2` Russo sum

Swarm `smwvbcnfb`, member `m3`, direction `d3`.

Integration donor: `.ultramath/smwvbcnfb/m3`; independently checked at
`8dbe14ef7e6200b83fb48c8568674f938e03bd50`.

The `p = 1` machinery (`Analysis/Cutoff/FluxODE`) reindexes the paper's double sum
`∑_{b ∈ K_0} ∑_{c ∈ B_r(b)} 1(c ∉ K_0) |K_c|` to the excluded mass
`E[|K_0| ∑_{c ∈ B_r} 1(c ∉ K_0) |K_c|]` by one mass transport of the covariant triple
`(a,b,c) ↦ pivotWeight r ω a b c`.

At `p = 2` the single-edge increment of `|K_0|²` on the off-region is

  `2 |K_0| |K_c| + |K_c|²`,

i.e. the source's two weights `|K|² |K_c|` and `|K| |K_c|²`.  The two terms have
*different* covariance: the squared term transports on its own (weight `|K_c|²`, giving
`exclMassQuad`), while the cross term must transport the **pair**
`(clusterVol a, pivotWeight a b c)` together, because the `|K_0|` factor is itself a cluster
functional at the anchor.  This file only introduces the two weights; the transport and the
identification with `p2RHS` are in `Main.lean`.

Nothing here differentiates in the radius or assumes a moment; the weights are `ℝ≥0∞`-valued
and the sums over `M.V` are honest `tsum`s.
-/
module

public import PercLib.CriticalLRP.Analysis.Cutoff.FluxODE
public import PercLib.CriticalLRP.Analysis.Cutoff.SecondMoment.Defs
public import PercLib.CriticalLRP.RussoInf.Merge
public import PercLib.CriticalLRP.Analysis.Cutoff.Deriv.Defs

/-!
# `p = 2` vertex-side pair weights

`pivotWeightSq` is the target-cluster-squared companion of `pivotWeight`, `p2Weight` is the
per-pair `p = 2` increment at the fixed anchor `0`, and `p2PaperSum`/`ballSumSq` are the two
double sums (pre- and post-mass-transport).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal

namespace PercLib.CriticalLRP

namespace PivotFlux

open Orchestration

/-- **The `p = 2` pivotal weight of a single pair.**

`pivotWeightSq M r ω a b c` is `pivotWeight` with the target cluster volume `|K_c|` replaced by
`|K_c|²`.  It is the weight of the source's `|K| ∑_{y} 1(y ∉ K) |K_y|²` term: opening `{b,c}`
merges `K_b` into `K_a` and adds `|K_c|²` to the second moment of `|K_a|` in the diagonal
(`|K_c|²`) part of `flipDiff_sq`.

The three indicators are exactly those of `pivotWeight`: the anchor `a` is connected to `b`,
the target `c` lies in the `r`-ball of `b`, and `b` is not connected to `c`. -/
noncomputable def pivotWeightSq (M : SourceModelData) (r : ℝ) (ω : Config M.V) (a b c : M.V) :
    ℝ≥0∞ :=
  configIndicator {ω' : Config M.V | Connects ω' a b} ω *
    (if M.S.dist c b ≤ r then 1 else 0) *
    configIndicator {ω' : Config M.V | ¬ Connects ω' b c} ω * clusterVol ω c ^ 2

/-- **The `p = 2` per-pair increment at the anchor `0`.**

This is the pointwise off-region increment `2 |K_0| |K_c| + |K_c|²` of
`flipDiff_clusterVol_sq_eq`, written on the pair `(b,c)` of the paper's double sum with `b`
ranging over `K_0` and `c` over the radius-`r` ball of `b`. -/
noncomputable def p2Weight (M : SourceModelData) (r : ℝ) (ω : Config M.V) (b c : M.V) : ℝ≥0∞ :=
  2 * clusterVol ω (0 : M.V) * pivotWeight M r ω 0 b c + pivotWeightSq M r ω 0 b c

/-- **The `p = 2` paper double sum, before mass transport**:
`∑_{b ∈ K_0} ∑_{c ∈ B_r(b)} 1(c ∉ K_0) (2 |K_0| |K_c| + |K_c|²)`. -/
noncomputable def p2PaperSum (M : SourceModelData) (r : ℝ) (ω : Config M.V) : ℝ≥0∞ :=
  ∑' b : M.V, ∑' c : M.V, p2Weight M r ω b c

/-- The root-anchored squared excluded ball sum `∑_{c ∈ B_r} 1(c ∉ K_0) |K_c|²`, the inner sum
of `exclSumQuad`, in the `tsum` form used by the mass-transport proof (the `p = 1` companion is
`ballSum`). -/
noncomputable def ballSumSq (M : SourceModelData) (r : ℝ) (ω : Config M.V) : ℝ≥0∞ :=
  ∑' c : M.V, (if M.S.ρ (toVec c) ≤ r then 1 else 0) *
    configIndicator {ω' : Config M.V | ¬ Connects ω' (0 : M.V) c} ω * clusterVol ω c ^ 2

end PivotFlux

end PercLib.CriticalLRP

end

/-! ## Axiom audit of the definitions -/

namespace PercLib.CriticalLRP

#print axioms PivotFlux.pivotWeightSq
#print axioms PivotFlux.p2Weight
#print axioms PivotFlux.p2PaperSum
#print axioms PivotFlux.ballSumSq

end PercLib.CriticalLRP

/-! ## The oriented real-valued off-region edge weight

`p2OrientReal` is the real-valued orientation of the `p = 2` increment: the term that the ordered
pair `(x,y)` contributes when `0 ↔ x`, `x ↮ y` and `y` lies in the `r`-ball of `x`.  It is the
interface between the committed pointwise increment `flipDiff_clusterVol_sq_eq_cases` (which
carries no radius) and the transported vertex-side weight `p2Weight` (which carries the radius
through `pivotWeight`).
-/

namespace PercLib.CriticalLRP

namespace PivotFlux

open Orchestration

attribute [local instance] Classical.propDecidable

/-- The oriented `p = 2` off-region increment of `|K_0|²` contributed by the ordered pair
`(x,y)`: `1(0 ↔ x) · 1(|y - x| ≤ r) · 1(x ↮ y) · (2 |K_0| |K_y| + |K_y|²)`. -/
noncomputable def p2OrientReal (M : SourceModelData) (r : ℝ) (ω : Config M.V) (x y : M.V) : ℝ :=
  (if Connects ω (0 : M.V) x then (1 : ℝ) else 0) * (if M.S.dist y x ≤ r then (1 : ℝ) else 0) *
    (if Connects ω x y then (0 : ℝ) else 1) *
      (2 * (clusterVol ω (0 : M.V)).toReal * (clusterVol ω y).toReal
        + (clusterVol ω y).toReal ^ 2)

end PivotFlux

end PercLib.CriticalLRP

/-! ## The closed-edge factor of the cutoff derivative weight

`M.cutEdgeDeriv r e = M.coeffRHS r * M.cutEdgeClosedWeight r e`, where `M.coeffRHS r` is the
radius-only coefficient `β_c (-K'(r))` and `cutEdgeClosedWeight` is the remaining exponential
`e^{-β_c J_r(e)}` — which is also `1 - q_e(r)`, the deficit of the cut-off edge probability.
Splitting `M.coeffRHS r` off the edge sum is the `coeffRHS` bookkeeping of the `p = 2` assembly;
the factorization theorem is in `Coeff.lean`.
-/

namespace PercLib.CriticalLRP

namespace Orchestration

namespace SourceModelData

variable (M : SourceModelData)

/-- **The closed-edge weight of a cut-off edge**: `e^{-β_c J_r(e)}` on the non-loop edges of
length `≤ r`, and `0` elsewhere (in particular on the loop edges `s(x,x)`, where `cutEdgeDeriv`
is `0` too, matching the construction of `radialSym`).  It is `1 - q_e(r)` for the cut-off edge
probability `q_e(r) = 1 - e^{-β_c J_r(e)}`. -/
noncomputable def cutEdgeClosedWeight (r : ℝ) : Sym2 M.V → ℝ :=
  Sym2.lift ⟨fun x y =>
    if x = y then 0 else
      (if M.S.dist x y ≤ r then
        Real.exp (-((M.betaCrit : ℝ) *
          FiniteVolume.cutoffProfile M.K r (M.S.dist x y)))
       else 0), by
    intro x y
    by_cases h : x = y
    · subst h; simp
    · have h' : y ≠ x := fun hh => h hh.symm
      change (if x = y then (0 : ℝ) else
          (if M.S.dist x y ≤ r then
            Real.exp (-((M.betaCrit : ℝ) *
              FiniteVolume.cutoffProfile M.K r (M.S.dist x y)))
           else 0))
        = (if y = x then (0 : ℝ) else
          (if M.S.dist y x ≤ r then
            Real.exp (-((M.betaCrit : ℝ) *
              FiniteVolume.cutoffProfile M.K r (M.S.dist y x)))
           else 0))
      rw [ite_eq_right h, ite_eq_right h', SourceNormData.dist_comm M.S y x]⟩

end SourceModelData

end Orchestration

/-! ## Axiom audit of the new definition -/

#print axioms Orchestration.SourceModelData.cutEdgeClosedWeight

end PercLib.CriticalLRP
