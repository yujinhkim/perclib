/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Accepted and independently rebuilt from Ultramath `smwzlje3f`.
Production base `a59bc6c22aba42e69160666c17feac870d4cb887`; reviewed scratch source `.ultramath/smwzlje3f/m4/Defs.lean`.

Swarm `smwzlje3f`, member `m4`, direction `d4` — (E) the HD(3) / triangle / tail inputs.

# The Case-3 (HD)(3) input and the real-valued two-point profile

The Case-3 consumer `secondMoment_asymptotic_case3_of_source_p21` retains, besides the moment
data, two *structural* inputs of the source's §I.4.1:

* `hTri : TriTail.openTriangleSelf M.kernel M.kernel_nonneg M.betaCrit 0 < ⊤`
  — Kozma's `∇_{β_c} < ∞` (the triangle condition), and
* `hF : Analysis.LogRadialBound (M.S.dist 0 ·) (openTriangle … 0 ·) C₀ p`, `1 < p`
  — the open-triangle log-radial decay (I.4.13) of Lemma I.4.3.

In the source, (I.4.13) is *derived* from Case 3 of (HD) by the log-corrected convolution
estimate (I.4.12) applied twice, and the paper then *assumes* `∇ < ∞` separately in Proposition
I.4.15.  This packet derives both from Case 3 of (HD) alone, on `ℤ^d`, at the model's own
normalized source norm `S.ρ`.

This file fixes the definitions.  There are no axioms and no model input beyond
`SourceModelData`.

## Layout

* `tau M` — the real-valued origin profile `z ↦ τ_{β_c}(0,z) = (twoPointFunction … 0 z).toReal`,
  which is exactly `M.twoPoint M.betaCrit 0 z`.
* `Case3HD M` — the literal third disjunct of the source's (HD) (p. 9), with `d = 6`, `α = 2`
  and the log-corrected two-point upper bound.
-/
module

public import PercLib.CriticalLRP.Analysis.LatticeConvolution.MargSrcNorm.Main
public import PercLib.CriticalLRP.Analysis.TriTailNormalization.Main
public import PercLib.CriticalLRP.Analysis.LogTail.Defs
public import PercLib.CriticalLRP.Orchestration.Defs

set_option linter.style.longLine false
set_option linter.hashCommand false
@[expose] public section

open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP.Orchestration
namespace SourceModelData

variable (M : SourceModelData)

/-- **Case 3 of (HD)** exactly as printed on p. 9 of Hutchcroft, *Critical long-range
percolation I*: `d = 6`, `α = 2`, and the log-corrected two-point upper bound
`P_{β_c}(x ↔ y) ⪯ (log ‖x-y‖)^{-1} ‖x-y‖^{-d+2}` for all `x ≠ y`.

This is the third disjunct of `Orchestration.HD`, restated as a standalone predicate so that
packets consuming only Case 3 do not have to unpack the disjunction. -/
def Case3HD : Prop :=
  M.d = 6 ∧ M.α = 2 ∧ ∃ C : ℝ, 0 < C ∧ ∀ x y : M.V, x ≠ y →
    M.twoPoint M.betaCrit x y
      ≤ C * (Real.log (M.S.ρ (toVec (x - y))))⁻¹ * (M.S.ρ (toVec (x - y))) ^ (-(M.d : ℝ) + 2)

/-- `Case3HD` is exactly the third disjunct of the source's (HD). -/
theorem case3HD_iff_hd_third :
    M.Case3HD ↔
      (M.d = 6 ∧ M.α = 2 ∧ ∃ C : ℝ, 0 < C ∧ ∀ x y : M.V, x ≠ y →
        M.twoPoint M.betaCrit x y
          ≤ C * (Real.log (M.S.ρ (toVec (x - y))))⁻¹
              * (M.S.ρ (toVec (x - y))) ^ (-(M.d : ℝ) + 2)) :=
  Iff.rfl

/-- The real-valued **origin two-point profile** `τ(z) = τ_{β_c}(0,z)`, the kernel of the open
triangle.  It is `M.twoPoint M.betaCrit 0 z` by `tau_apply`, and by translation invariance it
carries the whole two-point function. -/
noncomputable def tau : M.V → ℝ := fun z => (twoPointFunction M.kernel M.kernel_nonneg M.betaCrit 0 z).toReal

/-- `τ` is the model's own two-point function at the origin. -/
theorem tau_apply (z : M.V) : M.tau z = M.twoPoint M.betaCrit 0 z := rfl

/-- The **double convolution** `τ * τ` of the origin profile.  This is `M.twoPoint` convolved with
itself, i.e. the two-point contribution of the middle polygon leg. -/
noncomputable def tauConv (x : M.V) : ℝ := ∑' y : M.V, M.tau y * M.tau (x - y)

/-- The **triple convolution** `τ * τ * τ`, the whole uncut open triangle `∇_{β_c}(0,·)` at the
origin profile.  Its finiteness (at any point) is exactly the triangle condition. -/
noncomputable def tauConvConv (x : M.V) : ℝ := ∑' y : M.V, M.tau y * M.tauConv (x - y)

end SourceModelData
end PercLib.CriticalLRP.Orchestration
