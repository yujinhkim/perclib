/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Accepted and independently rebuilt from Ultramath `smwzf17v9`, member `m2`, direction `d1`.

# The window-averaged ℓ = 3 polygon driver of Proposition I.4.15, Case 3

Hutchcroft, *Critical long-range percolation I*, arXiv:2508.18807v1, proof of
Proposition I.4.15, Case 3 (p. 47), together with Lemma I.4.17 (p. 45) and
Lemma I.4.18 (p. 46).

The source's Case-3 numerator estimate is

```
  E_{2,r} ⪯ (∇_{r^c} + r^{-c}) (E_{β_c,r}|K|)^4 / (E_{β_c,r}|K| E_{β_c,r}|K|^2),
```

obtained by applying Lemma I.4.18 *vertexwise* to the two terms of Lemma I.4.17 at
`p = 3`, `q = 0`.  At `ℓ = 3` that application is not available: Lemma I.4.18's printed
display for `ℓ = 3` reads `sup_x T^3_{β_c,r}(0,x) ≤ C (∇_{r^c} + r^{-c}) (E|K|)^0`, whose
left side is at least `1` at `x = 0` at *every* cutoff (`I418C.one_le_polyK_three`) while
the right side tends to `0` (`I418C.LowOrder.not_forall_le_tail_add_rpow`).  The existing
`SecondMomentCase3.connCubeMass_le_of_windowGap` therefore keeps the vertexwise ℓ = 3
input as the hypothesis `hT3`.

The repair recorded here is the one the source itself already uses for the *first*-moment
defect `𝓔_{1,r}`: the ℓ = 3 term is only ever needed **summed over the window**, and the
honest object there is not the sup-tail `∇_{r^c}` but the *normalized window average*
`|B_r|^{-1} Σ_{y ∈ B_r} ∇_{β_c}(0,y)` (Lemma I.4.11's error term; see the text between
(I.4.10) and (I.4.13), and `TriangleAverage.normalized_ballSum_le_two_scale`).

This file only introduces the resulting two drivers.  No theorem is asserted here.
-/
module

public import PercLib.CriticalLRP.Analysis.SecondMomentCase3.Case3
public import PercLib.CriticalLRP.VolumeMoments.HigherMoments.I420Case3.SplitPolygon.NearWindow

/-! # Drivers for the split (summed ℓ = 3 / vertexwise ℓ = 4) Case-3 numerator -/

noncomputable section

open MeasureTheory Measure ProbabilityTheory unitInterval Filter Topology
open scoped ENNReal NNReal Topology BigOperators

@[expose] public section

namespace PercLib.CriticalLRP
namespace Orchestration
namespace SourceModelData

variable (M : SourceModelData)

/-- **The honest `ℓ = 3` Case-3 driver: the normalized window average of the open triangle.**

`case3ThreeDriver s θ r = (∇_{β_c}(0, r^θ)).toReal + (|s r| / |B_r|) · ∇_{β_c}`,
where `s r ⊆ B_r` is the near set of radius `r ^ θ` (so `y ∉ s r ⇒ r^θ ≤ ‖y‖`), the symbol
`∇_R` is the model's uncut open-triangle tail `M.nablaTail R`, and `∇_{β_c} = M.triSelf` is
the triangle diagram of the triangle condition.

This is the quantity that the *sum* `Σ_{y ∈ B_r} T^3_{β_c,r}(0,y)` is controlled by, and it
is what replaces the refuted vertexwise `sup_y T^3_{β_c,r}(0,y) ≤ C (∇_{r^c} + r^{-c})` at
`ℓ = 3`.  The two summands are the source's near/far split of Lemma I.4.18's proof at
`R = r^θ`: the far part is bounded by `∇_{r^θ}` through cutoff-versus-uncut monotonicity,
the near part by `∇_{β_c}` times the near-set cardinality ratio.

`r ^ θ` is written as an argument so that the two-scale choice stays visible; the source
uses `R = r^{α/(2d)}` in Lemma I.4.18 and `R = sqrt r` in the ℓ = 3 near sum. -/
def case3ThreeDriver (s : ℝ → Finset M.V) (θ r : ℝ) : ℝ :=
  (M.nablaTail (r ^ θ)).toReal +
    (((s r).card : ℝ) / ((M.ball r).ncard : ℝ)) * M.triSelf

/-- **The `ℓ ≥ 4` Case-3 driver**, `C * (∇_{r^c} + r^{-c})`, unchanged from
`SourceModelData.case3Driver`; here it is only packaged with the polygon constant so that the
split numerator has a single `ℓ ≥ 4` driver. -/
def case3TailDriver (Cp c r : ℝ) : ℝ := Cp * M.case3Driver c r

/-- The split numerator driver `C_3 * (ℓ = 3 driver) + C_4 * (ℓ ≥ 4 driver)`, i.e. exactly the
factor by which the Case-3 numerator `E[|K_0|^3 |K_0 ∩ B_r|]` exceeds `|B_r| (E|K|)^4`. -/
def case3SplitDriver (s : ℝ → Finset M.V) (θ : ℝ) (C3 C4 Cp c r : ℝ) : ℝ :=
  C3 * M.case3ThreeDriver s θ r + C4 * M.case3TailDriver Cp c r

theorem case3ThreeDriver_nonneg {s : ℝ → Finset M.V} {θ r : ℝ}
    (hcard : 0 ≤ ((s r).card : ℝ) / ((M.ball r).ncard : ℝ))
    (htri : 0 ≤ M.triSelf) :
    0 ≤ M.case3ThreeDriver s θ r := by
  have h1 := M.nablaTail_toReal_nonneg (r ^ θ)
  have h2 : 0 ≤ (((s r).card : ℝ) / ((M.ball r).ncard : ℝ)) * M.triSelf :=
    mul_nonneg hcard htri
  unfold case3ThreeDriver
  linarith

theorem case3TailDriver_nonneg {Cp c r : ℝ} (hCp : 0 ≤ Cp) (hdrv : 0 ≤ M.case3Driver c r) :
    0 ≤ M.case3TailDriver Cp c r :=
  mul_nonneg hCp hdrv

end SourceModelData
end Orchestration
end PercLib.CriticalLRP

end
