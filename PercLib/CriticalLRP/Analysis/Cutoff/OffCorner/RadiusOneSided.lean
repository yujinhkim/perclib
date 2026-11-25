module

public import PercLib.CriticalLRP.Analysis.Cutoff.OffCorner.RadiusPivotalWeight
public import PercLib.CriticalLRP.Analysis.Cutoff.CornerOneSided
public import PercLib.CriticalLRP.Analysis.Cutoff.Continuity

/-!
# One-sided regularity of the infinite singleton flux

Swarm `smwuinbxz`, member `m2`, direction **d2 (B: one-sided regularity)**.

This file determines what *one-sided* regularity the infinite-volume singleton flux

  `r ↦ sMomentInfFlux 0 {y} 1 M.cutProb M.cutEdgeDeriv r = ∑'_e c_r(e) · π_r(e)`

has, using only monotonicity of the edge law in the cutoff radius (never uniform continuity),
and states exactly what is missing for the two-sided premise `hcontinf`.

## What is proved

1. `monotoneOn_cutLaw_touchSet` — the infinite-volume touching mass
   `r ↦ P_r(e ∈ touchSet · 0)` is nondecreasing in `r`, from the exact edge law change
   `q_e(r) = 1 - exp(-β_c (K |e| - K r))` (closed convention).  Consequently
   `eventually_cutLaw_touchSet_le_left` and `eventually_cutLaw_touchSet_ge_right` give the
   one-sided *semicontinuity* of that mass: it can only jump upward at a radius.

2. `abs_cutEdgeDeriv_le_scale_strict` — the per-edge weight comparison against the *strict*
   weight `cutEdgeDerivLeft` at the right endpoint `r0`: for `r < r0`,
   `|c_r(e)| ≤ Λ · |cutEdgeDerivLeft r0 e|`, `Λ = (C / (-K'(r0))) exp(β_c (K a' - K r0))`.
   The point of the strict weight is that an edge of length exactly `r0` (the *shell* of the
   corner at `r0`) contributes `0` to the right-hand side.

3. `abs_sMomentInfFlux_le_strictWeight_at_endpoint` — **the main one-sided bound**: for
   `r ∈ [a', r0)` the flux is bounded by `Λ` times the strict-weight pivotal total at `r0`,

     `|flux r| ≤ Λ · ∑'_e |cutEdgeDerivLeft r0 e| · 2 P_{r0}(e ∈ touchSet · 0)`.

   Hence the shell at `r0` — the only place where `cutEdgeDeriv` jumps — never contributes to the
   flux from the left.  This is an upper-semicontinuity statement about the infinite-volume flux.

4. `eventually_abs_sMomentInfFlux_le_strictWeight_of_continuousAt_deriv` — the same with the
   comparison constant collapsed to `1 + ε`: if `deriv M.K` is continuous at `r0` (an *explicit
   input*: `SourceModelData` gives differentiability, never continuity of `deriv K`), then for
   every `ε > 0`, `|flux r| ≤ (1 + ε) · (strict total at r0)` for `r < r0` close to `r0`.

5. `strictWeight_le_closedWeight` and `abs_sMomentInfFlux_le_weight_at_endpoint` — the strict total
   is at most the closed total at `r0`, so (3) also reads `|flux r| ≤ Λ · (total pivotal weight at
   r0)`, i.e. the left limit of the flux is dominated by the weight at the endpoint.

## What is *not* proved, and why the method stops here

* No lower bound of any kind is obtained.  Monotone-law arguments control the *dominating* mass
  (the touching probability, an increasing event), but they do not apply to the pivotal probability
  `π_r(e) = ∫ flipDiff (1{y ∈ K_0}) e dP_r`: `flipDiff = (indicator at `e` forced open) -
  (indicator at `e` forced closed)` is a difference of two increasing functionals, hence not
  monotone in the configuration (an edge opened elsewhere can connect `0` to `y` and destroy the
  pivotality of `e`), so the stochastic monotonicity `P_r ≤ P_{r'}` does not compare `π_r` with
  `π_{r'}` in either direction.  Consequently nothing here yields `liminf_{r↑r0} |flux r|`, and in
  particular **`hcontinf` is not proved, not implied, and not restated in disguise**: the results
  above are one-sided upper bounds, not continuity.
* The right-hand side is genuinely worse than the left: from the right the touching mass
  *increases*, so the same argument can only produce the envelope value at the right endpoint
  `r0 + δ`, which is the already-landed `m1_abs_infFlux_le_envSum` with nothing added.  The
  asymmetry (left good, right not) is exactly the asymmetry of the monotone edge law.
* What would upgrade (4) to left-continuity is *edgewise* one-sided Russo continuity
  `Tendsto (fun r => c_r(e) · π_r(e)) (𝓝[<] r0) (𝓝 (c_{r0}(e) · π_{r0}(e)))` for each `e`
  together with the envelope (3), and symmetrically from the right; neither is available, and
  both are strictly weaker than `hcontinf`.
-/

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.hashCommand false

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP.Orchestration

namespace SourceModelData

variable (M : SourceModelData)

attribute [local instance] Classical.propDecidable

/-! ## 1. Monotonicity and one-sided semicontinuity of the touching mass -/

/-- **The infinite-volume touching mass is nondecreasing in the cutoff radius.**  This is the exact
edge-law content of `q_e(r) = 1 - exp(-β_c (K |e| - K r))` with `K` antitone: the profile rises in
`r` on the support and stays `0` below it. -/
theorem monotoneOn_cutLaw_touchSet (e : Sym2 M.V) :
    MonotoneOn (fun r : ℝ => (M.cutLaw r).real {ω : Config M.V | e ∈ touchSet ω (0 : M.V)})
      (Set.Ioi 0) :=
  fun _ hr _ hr' hrr' => M.m1_real_touchSet_mono_radius hr hr' hrr' e

/-- **Left-sided semicontinuity of the touching mass**: approaching `r0` from below, the mass is
eventually at most its value at `r0`.  The touching mass can jump upward at a radius, never
downward. -/
theorem eventually_cutLaw_touchSet_le_left {r0 : ℝ} (hr0 : 0 < r0) (e : Sym2 M.V) :
    ∀ᶠ r in 𝓝[<] r0, (M.cutLaw r).real {ω : Config M.V | e ∈ touchSet ω (0 : M.V)} ≤
      (M.cutLaw r0).real {ω : Config M.V | e ∈ touchSet ω (0 : M.V)} := by
  have hpos : ∀ᶠ r in 𝓝[<] r0, 0 < r :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds (Ioi_mem_nhds hr0)
  have hlt : ∀ᶠ r in 𝓝[<] r0, r < r0 := self_mem_nhdsWithin
  filter_upwards [hpos, hlt] with r hrpos hrlt
  exact M.m1_real_touchSet_mono_radius hrpos hr0 hrlt.le e

/-- **Right-sided semicontinuity of the touching mass**: approaching `r0` from above, the mass is
eventually at least its value at `r0` (the mirror image of the previous statement). -/
theorem eventually_cutLaw_touchSet_ge_right {r0 : ℝ} (hr0 : 0 < r0) (e : Sym2 M.V) :
    ∀ᶠ r in 𝓝[>] r0, (M.cutLaw r0).real {ω : Config M.V | e ∈ touchSet ω (0 : M.V)} ≤
      (M.cutLaw r).real {ω : Config M.V | e ∈ touchSet ω (0 : M.V)} := by
  have hpos : ∀ᶠ r in 𝓝[>] r0, 0 < r :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds (Ioi_mem_nhds hr0)
  have hgt : ∀ᶠ r in 𝓝[>] r0, r0 < r := self_mem_nhdsWithin
  filter_upwards [hpos, hgt] with r hrpos hrgt
  exact M.m1_real_touchSet_mono_radius hr0 hrpos hrgt.le e

/-! ## 2. The strict edge weight: nonnegativity and comparison with the closed weight -/

/-- The strict derivative weight is nonnegative off the origin. -/
theorem cutEdgeDerivLeft_nonneg {r : ℝ} (hr : 0 < r) (e : Sym2 M.V) :
    0 ≤ M.cutEdgeDerivLeft r e := by
  classical
  induction e using Sym2.ind with
  | _ x y =>
    rw [M.cutEdgeDerivLeft_mk]
    by_cases hxy : x = y
    · rw [ite_eq_left hxy]
    · rw [ite_eq_right hxy]
      by_cases hd : M.S.dist x y < r
      · rw [ite_eq_left hd]
        have h1 : (0 : ℝ) ≤ -(deriv M.K r) := M.neg_deriv_K_nonneg hr
        positivity
      · rw [ite_eq_right hd]

/-- The strict weight is dominated by the closed weight (they differ exactly by the shell). -/
theorem abs_cutEdgeDerivLeft_le_cutEdgeDeriv {r : ℝ} (hr : 0 < r) (e : Sym2 M.V) :
    |M.cutEdgeDerivLeft r e| ≤ |M.cutEdgeDeriv r e| := by
  classical
  have hleft := M.cutEdgeDerivLeft_nonneg hr e
  have hright := M.cutEdgeDeriv_nonneg (M.neg_deriv_K_nonneg hr) e
  rw [abs_of_nonneg hleft, abs_of_nonneg hright]
  induction e using Sym2.ind with
  | _ x y =>
    by_cases hxy : x = y
    · subst hxy
      rw [M.cutEdgeDerivLeft_mk, ite_eq_left rfl, M.cutEdgeDeriv_mk, ite_eq_left rfl]
    · have hleftmk : M.cutEdgeDerivLeft r s(x, y) =
          (if M.S.dist x y < r then
            (M.betaCrit : ℝ) * (-(deriv M.K r)) *
              Real.exp (-((M.betaCrit : ℝ) *
                PercLib.CriticalLRP.FiniteVolume.cutoffProfile M.K r (M.S.dist x y)))
           else 0) := by
        rw [M.cutEdgeDerivLeft_mk, ite_eq_right hxy]
      by_cases hd : M.S.dist x y < r
      · rw [hleftmk, ite_eq_left hd, M.cutEdgeDeriv_mk_of_le hxy hd.le,
          M.cutKernel_offdiag r hxy,
          PercLib.CriticalLRP.FiniteVolume.cutoffProfile_of_le hd.le]
      · rw [hleftmk, ite_eq_right hd]
        exact hright

/-- **The per-edge weight comparison against the strict weight at the right endpoint.**  For
`r ∈ [a', r0)` and `r0` carrying a strictly negative derivative,

  `|c_r(e)| ≤ (C / (-K'(r0))) exp(β_c (K a' - K r0)) · |cutEdgeDerivLeft r0 e|`,

where `C` bounds `-K'` on `[a', r0]`.  An edge of length exactly `r0` is invisible on both sides,
so the shell at `r0` does not enter. -/
theorem abs_cutEdgeDeriv_le_scale_strict {a' r0 C : ℝ} (ha' : 0 < a')
    (hCb : ∀ r ∈ Icc a' r0, -(deriv M.K r) ≤ C) (hC0 : 0 ≤ C) (hKr0 : deriv M.K r0 < 0)
    {r : ℝ} (hr : r ∈ Ico a' r0) (e : Sym2 M.V) :
    |M.cutEdgeDeriv r e| ≤
      (C / (-(deriv M.K r0)) * Real.exp ((M.betaCrit : ℝ) * (M.K a' - M.K r0))) *
        |M.cutEdgeDerivLeft r0 e| := by
  classical
  have hr0 : 0 < r := lt_of_lt_of_le ha' hr.1
  have hrK : (0 : ℝ) ≤ -(deriv M.K r) := M.neg_deriv_K_nonneg hr0
  have hβ0 : (0 : ℝ) ≤ (M.betaCrit : ℝ) := M.betaCrit.coe_nonneg
  have hKr00 : (0 : ℝ) ≤ -(deriv M.K r0) := le_of_lt (by linarith)
  have hΛ0 : (0 : ℝ) ≤
      C / (-(deriv M.K r0)) * Real.exp ((M.betaCrit : ℝ) * (M.K a' - M.K r0)) := by
    have : (0 : ℝ) ≤ C / (-(deriv M.K r0)) := div_nonneg hC0 hKr00
    positivity
  induction e using Sym2.ind with
  | _ x y =>
    by_cases hxy : x = y
    · subst hxy
      rw [M.cutEdgeDeriv_mk, ite_eq_left rfl, M.cutEdgeDerivLeft_mk, ite_eq_left rfl]
      simp
    · by_cases hdr : M.S.dist x y ≤ r
      · have hd0 : M.S.dist x y < r0 := lt_of_le_of_lt hdr hr.2
        rw [M.cutEdgeDeriv_mk_of_le hxy hdr, M.cutEdgeDerivLeft_mk, ite_eq_right hxy,
          ite_eq_left hd0, M.cutKernel_offdiag r hxy,
          PercLib.CriticalLRP.FiniteVolume.cutoffProfile_of_le hdr,
          PercLib.CriticalLRP.FiniteVolume.cutoffProfile_of_le hd0.le]
        have hAr : (0 : ℝ) ≤ Real.exp
            (-((M.betaCrit : ℝ) * (M.K (M.S.dist x y) - M.K r))) := Real.exp_nonneg _
        have hKrC : -(deriv M.K r) ≤ C := hCb r (Ico_subset_Icc_self hr)
        have hKmono : M.K r ≤ M.K a' :=
          M.K_antitone (Set.mem_Ioi.mpr ha') (Set.mem_Ioi.mpr hr0) hr.1
        have hAA : Real.exp (-((M.betaCrit : ℝ) * (M.K (M.S.dist x y) - M.K r)))
            ≤ Real.exp ((M.betaCrit : ℝ) * (M.K a' - M.K r0)) *
              Real.exp (-((M.betaCrit : ℝ) * (M.K (M.S.dist x y) - M.K r0))) := by
          rw [← Real.exp_add]
          apply Real.exp_le_exp.2
          nlinarith
        have habs_r : |(M.betaCrit : ℝ) * (-(deriv M.K r)) *
            Real.exp (-((M.betaCrit : ℝ) * (M.K (M.S.dist x y) - M.K r)))|
            = (M.betaCrit : ℝ) * (-(deriv M.K r)) *
              Real.exp (-((M.betaCrit : ℝ) * (M.K (M.S.dist x y) - M.K r))) :=
          abs_of_nonneg (by positivity)
        have habs_0 : |(M.betaCrit : ℝ) * (-(deriv M.K r0)) *
            Real.exp (-((M.betaCrit : ℝ) * (M.K (M.S.dist x y) - M.K r0)))|
            = (M.betaCrit : ℝ) * (-(deriv M.K r0)) *
              Real.exp (-((M.betaCrit : ℝ) * (M.K (M.S.dist x y) - M.K r0))) :=
          abs_of_nonneg (by positivity)
        rw [habs_r, habs_0]
        have hK0ne : (-(deriv M.K r0)) ≠ 0 := ne_of_gt (by linarith)
        have hident : C / (-(deriv M.K r0)) *
              Real.exp ((M.betaCrit : ℝ) * (M.K a' - M.K r0)) *
            ((M.betaCrit : ℝ) * (-(deriv M.K r0)) *
              Real.exp (-((M.betaCrit : ℝ) * (M.K (M.S.dist x y) - M.K r0))))
            = C * Real.exp ((M.betaCrit : ℝ) * (M.K a' - M.K r0)) * ((M.betaCrit : ℝ) *
              Real.exp (-((M.betaCrit : ℝ) * (M.K (M.S.dist x y) - M.K r0)))) := by
          rw [div_eq_mul_inv]
          calc C * (-(deriv M.K r0))⁻¹ * Real.exp ((M.betaCrit : ℝ) * (M.K a' - M.K r0)) *
                ((M.betaCrit : ℝ) * (-(deriv M.K r0)) *
                  Real.exp (-((M.betaCrit : ℝ) * (M.K (M.S.dist x y) - M.K r0))))
              = C * Real.exp ((M.betaCrit : ℝ) * (M.K a' - M.K r0)) * ((M.betaCrit : ℝ) *
                  Real.exp (-((M.betaCrit : ℝ) * (M.K (M.S.dist x y) - M.K r0)))) *
                  ((-(deriv M.K r0))⁻¹ * (-(deriv M.K r0))) := by ring
            _ = C * Real.exp ((M.betaCrit : ℝ) * (M.K a' - M.K r0)) * ((M.betaCrit : ℝ) *
                  Real.exp (-((M.betaCrit : ℝ) * (M.K (M.S.dist x y) - M.K r0)))) := by
                rw [inv_mul_cancel₀ hK0ne, mul_one]
        rw [hident]
        have hstep : (M.betaCrit : ℝ) * (-(deriv M.K r)) *
            Real.exp (-((M.betaCrit : ℝ) * (M.K (M.S.dist x y) - M.K r)))
            ≤ (M.betaCrit : ℝ) * C * Real.exp ((M.betaCrit : ℝ) * (M.K a' - M.K r0)) *
              Real.exp (-((M.betaCrit : ℝ) * (M.K (M.S.dist x y) - M.K r0))) := by
          have h1 : (M.betaCrit : ℝ) * (-(deriv M.K r)) ≤ (M.betaCrit : ℝ) * C :=
            mul_le_mul_of_nonneg_left hKrC hβ0
          calc (M.betaCrit : ℝ) * (-(deriv M.K r)) *
                Real.exp (-((M.betaCrit : ℝ) * (M.K (M.S.dist x y) - M.K r)))
              ≤ ((M.betaCrit : ℝ) * C) *
                (Real.exp ((M.betaCrit : ℝ) * (M.K a' - M.K r0)) *
                  Real.exp (-((M.betaCrit : ℝ) * (M.K (M.S.dist x y) - M.K r0)))) :=
                mul_le_mul h1 hAA hAr (by positivity)
            _ = (M.betaCrit : ℝ) * C * Real.exp ((M.betaCrit : ℝ) * (M.K a' - M.K r0)) *
                  Real.exp (-((M.betaCrit : ℝ) * (M.K (M.S.dist x y) - M.K r0))) := by ring
        calc (M.betaCrit : ℝ) * (-(deriv M.K r)) *
              Real.exp (-((M.betaCrit : ℝ) * (M.K (M.S.dist x y) - M.K r)))
            ≤ (M.betaCrit : ℝ) * C * Real.exp ((M.betaCrit : ℝ) * (M.K a' - M.K r0)) *
                Real.exp (-((M.betaCrit : ℝ) * (M.K (M.S.dist x y) - M.K r0))) := hstep
          _ = C * Real.exp ((M.betaCrit : ℝ) * (M.K a' - M.K r0)) * ((M.betaCrit : ℝ) *
                Real.exp (-((M.betaCrit : ℝ) * (M.K (M.S.dist x y) - M.K r0)))) := by ring
      · rw [M.cutEdgeDeriv_eq_zero_of_lt_dist (x := x) (y := y) (not_le.mp hdr), abs_zero]
        exact mul_nonneg hΛ0 (abs_nonneg _)

/-! ## 3. The one-sided bound for the infinite singleton flux -/

set_option maxHeartbeats 1200000 in
-- the tsum/abs elaboration over the singleton moment is expensive; the default budget is exceeded
/-- **The infinite singleton flux is bounded from the left by the strict pivotal total at the right
endpoint.**  For `r ∈ [a', r0)`, with `C` bounding `-K'` on `[a', r0]` and `-K'(r0) > 0`,

  `|flux r| ≤ Λ · ∑'_e |cutEdgeDerivLeft r0 e| · 2 P_{r0}(e ∈ touchSet · 0)`,
  `Λ = (C / (-K'(r0))) exp(β_c (K a' - K r0))`.

Only the finite first moment at `r0` enters (`hvol`).  This is an upper-semicontinuity statement
about the infinite-volume flux: the shell of length exactly `r0`, which is the entire source of the
discontinuity of `cutEdgeDeriv`, contributes nothing from the left. -/
theorem abs_sMomentInfFlux_le_strictWeight_at_endpoint {a' r0 C : ℝ} (ha' : 0 < a')
    (hCb : ∀ r ∈ Icc a' r0, -(deriv M.K r) ≤ C) (hC0 : 0 ≤ C)
    (hKr0 : deriv M.K r0 < 0) (hr0 : 0 < r0) (hvol : M.cutMoment 1 r0 ≠ ⊤) (y : M.V)
    {r : ℝ} (hr : r ∈ Ico a' r0) :
    |PercLib.CriticalLRP.sMomentInfFlux (0 : M.V) ({y} : Finset M.V) (fun _ => (1 : ℝ))
        M.cutProb M.cutEdgeDeriv r| ≤
      (C / (-(deriv M.K r0)) * Real.exp ((M.betaCrit : ℝ) * (M.K a' - M.K r0))) *
        ∑' e : Sym2 M.V, |M.cutEdgeDerivLeft r0 e| *
          (2 * (M.cutLaw r0).real {ω : Config M.V | e ∈ touchSet ω (0 : M.V)}) := by
  classical
  have hr0' : 0 < r := lt_of_lt_of_le ha' hr.1
  have hKr00 : (0 : ℝ) ≤ -(deriv M.K r0) := le_of_lt (by linarith)
  have hΛ0 : (0 : ℝ) ≤
      C / (-(deriv M.K r0)) * Real.exp ((M.betaCrit : ℝ) * (M.K a' - M.K r0)) := by
    have : (0 : ℝ) ≤ C / (-(deriv M.K r0)) := div_nonneg hC0 hKr00
    positivity
  -- summability of the strict total at `r0`
  have hbase : Summable fun e : Sym2 M.V => |M.cutEdgeDeriv r0 e| *
      (2 * (M.cutLaw r0).real {ω : Config M.V | e ∈ touchSet ω (0 : M.V)}) :=
    M.summable_hdom_of_cutMoment hr0 hvol
  have hstrict : Summable fun e : Sym2 M.V => |M.cutEdgeDerivLeft r0 e| *
      (2 * (M.cutLaw r0).real {ω : Config M.V | e ∈ touchSet ω (0 : M.V)}) :=
    Summable.of_nonneg_of_le (fun e => by positivity)
      (fun e => mul_le_mul_of_nonneg_right
        (M.abs_cutEdgeDerivLeft_le_cutEdgeDeriv hr0 e) (by positivity)) hbase
  -- the termwise one-sided comparison
  have hterm : ∀ e : Sym2 M.V, |M.cutEdgeDeriv r e *
      PercLib.CriticalLRP.pivotalFlux (M.cutLaw r)
        (PercLib.CriticalLRP.sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V)
          ({y} : Finset M.V)) e|
      ≤ (C / (-(deriv M.K r0)) * Real.exp ((M.betaCrit : ℝ) * (M.K a' - M.K r0))) *
        (|M.cutEdgeDerivLeft r0 e| *
          (2 * (M.cutLaw r0).real {ω : Config M.V | e ∈ touchSet ω (0 : M.V)})) := by
    intro e
    have hscale := M.abs_cutEdgeDeriv_le_scale_strict ha' hCb hC0 hKr0 hr e
    have hpiv : |PercLib.CriticalLRP.pivotalFlux (M.cutLaw r)
        (PercLib.CriticalLRP.sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V)
          ({y} : Finset M.V)) e|
        ≤ 2 * (M.cutLaw r).real {ω : Config M.V | e ∈ touchSet ω (0 : M.V)} :=
      M.m1_abs_pivotalFlux_sMomentTrunc_le y r e
    have hPmono : (M.cutLaw r).real {ω : Config M.V | e ∈ touchSet ω (0 : M.V)}
        ≤ (M.cutLaw r0).real {ω : Config M.V | e ∈ touchSet ω (0 : M.V)} :=
      M.m1_real_touchSet_mono_radius hr0' hr0 hr.2.le e
    have hpiv' : |PercLib.CriticalLRP.pivotalFlux (M.cutLaw r)
        (PercLib.CriticalLRP.sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V)
          ({y} : Finset M.V)) e|
        ≤ 2 * (M.cutLaw r0).real {ω : Config M.V | e ∈ touchSet ω (0 : M.V)} :=
      hpiv.trans (mul_le_mul_of_nonneg_left hPmono (by norm_num))
    calc |M.cutEdgeDeriv r e * PercLib.CriticalLRP.pivotalFlux (M.cutLaw r)
          (PercLib.CriticalLRP.sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V)
            ({y} : Finset M.V)) e|
        = |M.cutEdgeDeriv r e| * |PercLib.CriticalLRP.pivotalFlux (M.cutLaw r)
          (PercLib.CriticalLRP.sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V)
            ({y} : Finset M.V)) e| := abs_mul _ _
      _ ≤ ((C / (-(deriv M.K r0)) * Real.exp ((M.betaCrit : ℝ) * (M.K a' - M.K r0))) *
            |M.cutEdgeDerivLeft r0 e|) * (2 *
              (M.cutLaw r0).real {ω : Config M.V | e ∈ touchSet ω (0 : M.V)}) :=
          mul_le_mul hscale hpiv' (abs_nonneg _) (by positivity)
      _ = (C / (-(deriv M.K r0)) * Real.exp ((M.betaCrit : ℝ) * (M.K a' - M.K r0))) *
            (|M.cutEdgeDerivLeft r0 e| *
              (2 * (M.cutLaw r0).real {ω : Config M.V | e ∈ touchSet ω (0 : M.V)})) := by
          ring
  have hnorm : Summable fun e : Sym2 M.V => ‖M.cutEdgeDeriv r e *
      PercLib.CriticalLRP.pivotalFlux (M.cutLaw r)
        (PercLib.CriticalLRP.sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V)
          ({y} : Finset M.V)) e‖ :=
    Summable.of_nonneg_of_le (fun e => norm_nonneg _)
      (fun e => by rw [Real.norm_eq_abs]; exact hterm e) (hstrict.mul_left _)
  have habs : Summable fun e : Sym2 M.V => |M.cutEdgeDeriv r e *
      PercLib.CriticalLRP.pivotalFlux (M.cutLaw r)
        (PercLib.CriticalLRP.sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V)
          ({y} : Finset M.V)) e| :=
    hnorm.congr fun e => Real.norm_eq_abs _
  have htp : PercLib.CriticalLRP.sMomentInfFlux (0 : M.V) ({y} : Finset M.V)
      (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv r
      = ∑' e : Sym2 M.V, M.cutEdgeDeriv r e *
          PercLib.CriticalLRP.pivotalFlux (M.cutLaw r)
            (PercLib.CriticalLRP.sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V)
              ({y} : Finset M.V)) e := rfl
  rw [htp]
  refine (norm_tsum_le_tsum_norm hnorm).trans ?_
  have hcongr : (∑' e : Sym2 M.V, ‖M.cutEdgeDeriv r e *
        PercLib.CriticalLRP.pivotalFlux (M.cutLaw r)
          (PercLib.CriticalLRP.sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V)
            ({y} : Finset M.V)) e‖)
      = ∑' e : Sym2 M.V, |M.cutEdgeDeriv r e *
          PercLib.CriticalLRP.pivotalFlux (M.cutLaw r)
            (PercLib.CriticalLRP.sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V)
              ({y} : Finset M.V)) e| :=
    tsum_congr fun e => Real.norm_eq_abs _
  rw [hcongr]
  refine (Summable.tsum_le_tsum hterm habs (hstrict.mul_left _)).trans_eq ?_
  exact tsum_mul_left

/-! ## 4. Collapsing the comparison constant: continuity of `deriv K` at the endpoint -/

set_option maxHeartbeats 1200000 in
-- elaboration of the strict-weight tsum together with the `ε`-comparison is expensive
/-- **Left one-sided bound at an endpoint with a continuous derivative.**  If `deriv M.K` is
continuous at `r0` and `K'(r0) < 0`, then for every `ε > 0` the singleton flux is eventually (from
the left) at most `1 + ε` times the strict pivotal total at `r0`:

  `∀ ε > 0, ∀ᶠ r in 𝓝[<] r0, |flux r| ≤ (1 + ε) · ∑'_e |cutEdgeDerivLeft r0 e| · 2 P_{r0}(touch)`.

This is the sharpest form of the one-sided statement obtained here.  It is *not* continuity: it is
an upper bound on the left oscillation, and it carries two explicit inputs that `SourceModelData`
does not provide, namely `ContinuousAt (fun r => deriv M.K r) r0` and the finite first moment
`M.cutMoment 1 r0 ≠ ⊤` at `r0`. -/
theorem eventually_abs_sMomentInfFlux_le_strictWeight_of_continuousAt_deriv
    {r0 : ℝ} (hr0 : 0 < r0) (hKr0 : deriv M.K r0 < 0)
    (hKc : ContinuousAt (fun r => deriv M.K r) r0)
    (hvol : M.cutMoment 1 r0 ≠ ⊤) (y : M.V) :
    ∀ ε > 0, ∀ᶠ r in 𝓝[<] r0,
      |PercLib.CriticalLRP.sMomentInfFlux (0 : M.V) ({y} : Finset M.V) (fun _ => (1 : ℝ))
          M.cutProb M.cutEdgeDeriv r| ≤
        (1 + ε) * ∑' e : Sym2 M.V, |M.cutEdgeDerivLeft r0 e| *
          (2 * (M.cutLaw r0).real {ω : Config M.V | e ∈ touchSet ω (0 : M.V)}) := by
  classical
  intro ε hε
  obtain ⟨η, hηpos, hηsq⟩ : ∃ η : ℝ, 0 < η ∧ (1 + η) * (1 + η) ≤ 1 + ε := by
    refine ⟨Real.sqrt (1 + ε) - 1, ?_, ?_⟩
    · have h1 : (1 : ℝ) < Real.sqrt (1 + ε) := by
        rw [Real.lt_sqrt (by linarith)]
        linarith
      linarith
    · have h1η : 1 + (Real.sqrt (1 + ε) - 1) = Real.sqrt (1 + ε) := by ring
      rw [h1η]
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 1 + ε by linarith)]
  set W : ℝ := ∑' e : Sym2 M.V, |M.cutEdgeDerivLeft r0 e| *
      (2 * (M.cutLaw r0).real {ω : Config M.V | e ∈ touchSet ω (0 : M.V)}) with hW
  have hW0 : 0 ≤ W := tsum_nonneg fun e => by positivity
  have hKr00 : (0 : ℝ) < -(deriv M.K r0) := by linarith
  -- the two eventual bounds at `r0`
  have hA : ∀ᶠ s in 𝓝 r0, -(deriv M.K s) < (1 + η) * (-(deriv M.K r0)) := by
    have htend : Tendsto (fun s => -(deriv M.K s)) (𝓝 r0) (𝓝 (-(deriv M.K r0))) := hKc.neg
    exact htend.eventually (Iio_mem_nhds (by nlinarith))
  have hB : ∀ᶠ s in 𝓝 r0,
      Real.exp ((M.betaCrit : ℝ) * (M.K s - M.K r0)) ≤ 1 + η := by
    have hKcont : ContinuousAt M.K r0 := M.continuousAt_deriv_free_K r0 hr0
    have hdiff : Tendsto (fun s => M.K s - M.K r0) (𝓝 r0) (𝓝 0) := by
      have h : Tendsto (fun s => M.K s - M.K r0) (𝓝 r0) (𝓝 (M.K r0 - M.K r0)) :=
        hKcont.tendsto.sub tendsto_const_nhds
      simpa using h
    have harg : Tendsto (fun s => (M.betaCrit : ℝ) * (M.K s - M.K r0)) (𝓝 r0) (𝓝 0) := by
      have h : Tendsto (fun s => (M.betaCrit : ℝ) * (M.K s - M.K r0)) (𝓝 r0)
          (𝓝 ((M.betaCrit : ℝ) * 0)) :=
        tendsto_const_nhds.mul hdiff
      simpa using h
    have hexp : Tendsto (fun s => Real.exp ((M.betaCrit : ℝ) * (M.K s - M.K r0)))
        (𝓝 r0) (𝓝 (Real.exp 0)) :=
      Real.continuous_exp.tendsto 0 |>.comp harg
    have hlt : ∀ᶠ s in 𝓝 r0,
        Real.exp ((M.betaCrit : ℝ) * (M.K s - M.K r0)) < 1 + η :=
      hexp.eventually (Iio_mem_nhds (by simpa using hηpos))
    filter_upwards [hlt] with s hs using hs.le
  obtain ⟨δ, hδ0, hδ⟩ := Metric.mem_nhds_iff.mp (hA.and hB)
  set δ' : ℝ := min δ (r0 / 2) with hδ'def
  have hδ'0 : 0 < δ' := lt_min hδ0 (by linarith)
  have hδ'δ : δ' ≤ δ := min_le_left _ _
  have hδ'r : δ' ≤ r0 / 2 := min_le_right _ _
  have hball : Set.Ioo (r0 - δ') (r0 + δ') ∈ 𝓝 r0 :=
    Ioo_mem_nhds (by linarith) (by linarith)
  filter_upwards [Filter.Eventually.filter_mono nhdsWithin_le_nhds hball, self_mem_nhdsWithin]
    with r hr hlt
  have hrpos : 0 < r := by linarith [hr.1]
  have hdist : |r - r0| < δ := by
    rw [abs_lt]
    constructor
    · linarith [hr.1]
    · linarith
  have hPr : -(deriv M.K r) < (1 + η) * (-(deriv M.K r0)) ∧
      Real.exp ((M.betaCrit : ℝ) * (M.K r - M.K r0)) ≤ 1 + η :=
    hδ (by rw [Metric.mem_ball, Real.dist_eq]; exact hdist)
  -- the compact-window hypothesis of the endpoint bound
  have hCb : ∀ s ∈ Set.Icc r r0, -(deriv M.K s) ≤ (1 + η) * (-(deriv M.K r0)) := by
    intro s hs
    have hds : |s - r0| < δ := by
      rw [abs_lt]
      constructor
      · linarith [hs.1, hr.1]
      · linarith [hs.2]
    exact (hδ (by rw [Metric.mem_ball, Real.dist_eq]; exact hds)).1.le
  have hC0 : (0 : ℝ) ≤ (1 + η) * (-(deriv M.K r0)) := by
    have : (0 : ℝ) < 1 + η := by linarith
    exact mul_nonneg this.le hKr00.le
  have hb := M.abs_sMomentInfFlux_le_strictWeight_at_endpoint (a' := r) (r0 := r0)
    (C := (1 + η) * (-(deriv M.K r0))) hrpos hCb hC0 hKr0 hr0 hvol y
    (show r ∈ Set.Ico r r0 from ⟨le_rfl, hlt⟩)
  rw [← hW] at hb
  have hcancel : (1 + η) * (-(deriv M.K r0)) / (-(deriv M.K r0)) = 1 + η :=
    mul_div_cancel_right₀ _ (ne_of_gt hKr00)
  rw [hcancel] at hb
  refine hb.trans (mul_le_mul_of_nonneg_right ?_ hW0)
  nlinarith [hPr.2, hηpos, hηsq,
    Real.exp_nonneg ((M.betaCrit : ℝ) * (M.K r - M.K r0))]

/-! ## 5. The strict total is at most the closed total, and the bound in terms of the value at `r0` -/

set_option maxHeartbeats 1200000 in
-- same elaboration cost as the strict-weight endpoint bound
/-- **The strict pivotal total never exceeds the closed one**: the shell of length `r0` is the only
difference between the two per-edge weights, and it is dropped on the left. -/
theorem strictWeight_le_closedWeight {r0 : ℝ} (hr0 : 0 < r0)
    (hvol : M.cutMoment 1 r0 ≠ ⊤) :
    (∑' e : Sym2 M.V, |M.cutEdgeDerivLeft r0 e| *
        (2 * (M.cutLaw r0).real {ω : Config M.V | e ∈ touchSet ω (0 : M.V)})) ≤
      ∑' e : Sym2 M.V, |M.cutEdgeDeriv r0 e| *
        (2 * (M.cutLaw r0).real {ω : Config M.V | e ∈ touchSet ω (0 : M.V)}) := by
  classical
  have hbase : Summable fun e : Sym2 M.V => |M.cutEdgeDeriv r0 e| *
      (2 * (M.cutLaw r0).real {ω : Config M.V | e ∈ touchSet ω (0 : M.V)}) :=
    M.summable_hdom_of_cutMoment hr0 hvol
  have hstrict : Summable fun e : Sym2 M.V => |M.cutEdgeDerivLeft r0 e| *
      (2 * (M.cutLaw r0).real {ω : Config M.V | e ∈ touchSet ω (0 : M.V)}) :=
    Summable.of_nonneg_of_le (fun e => by positivity)
      (fun e => mul_le_mul_of_nonneg_right
        (M.abs_cutEdgeDerivLeft_le_cutEdgeDeriv hr0 e) (by positivity)) hbase
  exact Summable.tsum_le_tsum (fun e => mul_le_mul_of_nonneg_right
    (M.abs_cutEdgeDerivLeft_le_cutEdgeDeriv hr0 e) (by positivity)) hstrict hbase

set_option maxHeartbeats 1200000 in
-- the same tsum elaboration as the strict bound, with the extra `tsum_le_tsum` comparison
/-- **The one-sided flux bound in terms of the value of the total pivotal weight at `r0`.**  For
`r ∈ [a', r0)`, with `C` bounding `-K'` on `[a', r0]` and `-K'(r0) > 0`,

  `|flux r| ≤ Λ · ∑'_e |cutEdgeDeriv r0 e| · 2 P_{r0}(e ∈ touchSet · 0)`,

i.e. exactly `Λ` times the weight at `r0`, so the left limit of the flux is dominated by the weight
*at* the endpoint.  There is no matching right-sided statement: from the right the touching mass
increases and only the envelope at `r0 + δ` is available. -/
theorem abs_sMomentInfFlux_le_weight_at_endpoint {a' r0 C : ℝ} (ha' : 0 < a')
    (hCb : ∀ r ∈ Icc a' r0, -(deriv M.K r) ≤ C) (hC0 : 0 ≤ C)
    (hKr0 : deriv M.K r0 < 0) (hr0 : 0 < r0) (hvol : M.cutMoment 1 r0 ≠ ⊤) (y : M.V)
    {r : ℝ} (hr : r ∈ Ico a' r0) :
    |PercLib.CriticalLRP.sMomentInfFlux (0 : M.V) ({y} : Finset M.V) (fun _ => (1 : ℝ))
        M.cutProb M.cutEdgeDeriv r| ≤
      (C / (-(deriv M.K r0)) * Real.exp ((M.betaCrit : ℝ) * (M.K a' - M.K r0))) *
        ∑' e : Sym2 M.V, |M.cutEdgeDeriv r0 e| *
          (2 * (M.cutLaw r0).real {ω : Config M.V | e ∈ touchSet ω (0 : M.V)}) := by
  classical
  have hKr00 : (0 : ℝ) ≤ -(deriv M.K r0) := le_of_lt (by linarith)
  have hΛ0 : (0 : ℝ) ≤
      C / (-(deriv M.K r0)) * Real.exp ((M.betaCrit : ℝ) * (M.K a' - M.K r0)) := by
    have : (0 : ℝ) ≤ C / (-(deriv M.K r0)) := div_nonneg hC0 hKr00
    positivity
  refine (M.abs_sMomentInfFlux_le_strictWeight_at_endpoint ha' hCb hC0 hKr0 hr0 hvol y
    hr).trans ?_
  exact mul_le_mul_of_nonneg_left (M.strictWeight_le_closedWeight hr0 hvol) hΛ0

end SourceModelData

end PercLib.CriticalLRP.Orchestration

/-! ## Axiom audit -/

set_option linter.hashCommand false

namespace PercLib.CriticalLRP.Orchestration

#print axioms SourceModelData.monotoneOn_cutLaw_touchSet
#print axioms SourceModelData.eventually_cutLaw_touchSet_le_left
#print axioms SourceModelData.eventually_cutLaw_touchSet_ge_right
#print axioms SourceModelData.cutEdgeDerivLeft_nonneg
#print axioms SourceModelData.abs_cutEdgeDerivLeft_le_cutEdgeDeriv
#print axioms SourceModelData.abs_cutEdgeDeriv_le_scale_strict
#print axioms SourceModelData.abs_sMomentInfFlux_le_strictWeight_at_endpoint
#print axioms SourceModelData.eventually_abs_sMomentInfFlux_le_strictWeight_of_continuousAt_deriv
#print axioms SourceModelData.strictWeight_le_closedWeight
#print axioms SourceModelData.abs_sMomentInfFlux_le_weight_at_endpoint

end PercLib.CriticalLRP.Orchestration
