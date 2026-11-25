/-
Member m1, swarm smwuges40, direction d3.

Radius-monotonicity of the source cut-off edge probability and a single `r'`-independent
summable dominating family for the per-`y` off-corner flux terms

  r' ↦ |cutEdgeDeriv r' e * pivotalFlux (cutLaw r') (sMomentTrunc 1 0 {y}) e|

on a compact off-corner subinterval `[a', b']` of the model's off-corner range.  The envelope is
sitting at the larger endpoint `b'` (where the cut-off probabilities dominate those at every
`r' ∈ [a', b']`, since the profile is antitone in the radius) and does not depend on `r'`.
-/
module

public import PercLib.CriticalLRP.Analysis.Cutoff.OffCorner.EdgeMajorant
public import PercLib.CriticalLRP.RussoInf.CutoffFluxMajorant
public import PercLib.CriticalLRP.RussoInf.Sharpness

/-!
# Measurable envelope for off-corner singleton flux
-/

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedVariables false

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP.Orchestration

namespace SourceModelData

variable (M : SourceModelData)

attribute [local instance] Classical.propDecidable

/-! ## 1. Monotonicity of the cut-off edge probability in the cut-off radius -/

/-- The cut-off kernel is nondecreasing in the cut-off radius. -/
theorem m1_cutKernel_mono {r r' : ℝ} (hr : 0 < r) (hr' : 0 < r') (h : r ≤ r')
    (e : Sym2 M.V) : M.cutKernel r e ≤ M.cutKernel r' e := by
  classical
  induction e using Sym2.ind with
  | _ x y =>
    rw [M.cutKernel_mk r x y, M.cutKernel_mk r' x y]
    by_cases hxy : x = y
    · rw [ite_eq_left hxy, ite_eq_left hxy]
    · rw [ite_eq_right hxy, ite_eq_right hxy]
      exact FiniteVolume.cutoffProfile_mono_r M.K_antitone hr hr' (M.S.dist_pos hxy) h

/-- The cut-off edge probability is nondecreasing in the cut-off radius. -/
theorem m1_cutProb_mono {r r' : ℝ} (hr : 0 < r) (hr' : 0 < r') (h : r ≤ r')
    (e : Sym2 M.V) : M.cutProb r e ≤ M.cutProb r' e := by
  rw [← Subtype.coe_le_coe, M.cutProb_coe r e, M.cutProb_coe r' e]
  have hJ : M.cutKernel r e ≤ M.cutKernel r' e := M.m1_cutKernel_mono hr hr' h e
  have hβ : (0 : ℝ) ≤ (M.betaCrit : ℝ) := M.betaCrit.coe_nonneg
  have hexp : Real.exp (-((M.betaCrit : ℝ) * M.cutKernel r' e)) ≤
      Real.exp (-((M.betaCrit : ℝ) * M.cutKernel r e)) := by
    apply Real.exp_le_exp.2
    nlinarith
  linarith

/-- The probability that a fixed edge touches the cluster of `0` is nondecreasing in the radius. -/
theorem m1_real_touchSet_mono_radius {r r' : ℝ} (hr : 0 < r) (hr' : 0 < r') (h : r ≤ r')
    (e : Sym2 M.V) :
    (M.cutLaw r).real {ω | e ∈ touchSet ω (0 : M.V)} ≤
      (M.cutLaw r').real {ω | e ∈ touchSet ω (0 : M.V)} :=
  real_touchSet_mono (p := M.cutProb r) (q := M.cutProb r')
    (fun e' => M.m1_cutProb_mono hr hr' h e') 0 e

/-! ## 2. A radius-independent comparison of the derivative weight with an interior scale -/

/-- **The derivative weight is comparable on a compact interval to its value at an interior
radius.**  If `-K'` is bounded above by `C` on `[a', b']` and `-K'(ρ) > 0` with `b' ≤ ρ`, then

  `|c_r(e)| ≤ Λ · |c_ρ(e)|`,   `Λ = C / (-K'(ρ)) · exp(β_c (K a' - K ρ))`,

for every `r ∈ [a', b']` and every edge.  Both sides vanish outside the support at `ρ`,
and on the
support the exponential factor of the two cut-off kernels differs by `exp(β_c (K r - K ρ))` which
is at most `exp(β_c (K a' - K ρ))` because `K` is antitone. -/
theorem m1_abs_cutEdgeDeriv_le_scale {a' b' ρ C : ℝ} (ha' : 0 < a') (ha'b' : a' ≤ b')
    (hb'ρ : b' ≤ ρ) (hCb : ∀ r ∈ Icc a' b', -(deriv M.K r) ≤ C) (hC0 : 0 ≤ C)
    (hKρ : deriv M.K ρ < 0) {r : ℝ} (hr : r ∈ Icc a' b') (e : Sym2 M.V) :
    |M.cutEdgeDeriv r e| ≤
      (C / (-(deriv M.K ρ)) * Real.exp ((M.betaCrit : ℝ) * (M.K a' - M.K ρ))) *
        |M.cutEdgeDeriv ρ e| := by
  classical
  have hρ0 : 0 < ρ := lt_of_lt_of_le (lt_of_lt_of_le ha' ha'b') hb'ρ
  have hr0 : 0 < r := lt_of_lt_of_le ha' hr.1
  have hβ0 : (0 : ℝ) ≤ (M.betaCrit : ℝ) := M.betaCrit.coe_nonneg
  have hKr0 : (0 : ℝ) ≤ -(deriv M.K r) := M.neg_deriv_K_nonneg hr0
  have hKρ0 : (0 : ℝ) ≤ -(deriv M.K ρ) := le_of_lt (by linarith)
  have hΛ0 : (0 : ℝ) ≤
      C / (-(deriv M.K ρ)) * Real.exp ((M.betaCrit : ℝ) * (M.K a' - M.K ρ)) := by
    have : (0 : ℝ) ≤ C / (-(deriv M.K ρ)) := div_nonneg hC0 hKρ0
    positivity
  induction e using Sym2.ind with
  | _ x y =>
    by_cases hxy : x = y
    · subst hxy
      rw [M.cutEdgeDeriv_mk, ite_eq_left rfl, M.cutEdgeDeriv_mk, ite_eq_left rfl]
      simp
    · by_cases hdr : M.S.dist x y ≤ r
      · have hdρ : M.S.dist x y ≤ ρ := le_trans hdr (le_trans hr.2 hb'ρ)
        rw [M.cutEdgeDeriv_mk_of_le hxy hdr, M.cutEdgeDeriv_mk_of_le hxy hdρ,
          M.cutKernel_offdiag r hxy, M.cutKernel_offdiag ρ hxy,
          PercLib.CriticalLRP.FiniteVolume.cutoffProfile_of_le hdr,
          PercLib.CriticalLRP.FiniteVolume.cutoffProfile_of_le hdρ]
        have hAr : (0 : ℝ) ≤ Real.exp
            (-((M.betaCrit : ℝ) * (M.K (M.S.dist x y) - M.K r))) := Real.exp_nonneg _
        have hAρ : (0 : ℝ) ≤ Real.exp
            (-((M.betaCrit : ℝ) * (M.K (M.S.dist x y) - M.K ρ))) := Real.exp_nonneg _
        have hAe : (0 : ℝ) ≤
            Real.exp ((M.betaCrit : ℝ) * (M.K a' - M.K ρ)) := Real.exp_nonneg _
        have hKrC : -(deriv M.K r) ≤ C := hCb r hr
        have hKmono : M.K r ≤ M.K a' :=
          M.K_antitone (Set.mem_Ioi.mpr ha') (Set.mem_Ioi.mpr hr0) hr.1
        have hAA : Real.exp (-((M.betaCrit : ℝ) * (M.K (M.S.dist x y) - M.K r)))
            ≤ Real.exp ((M.betaCrit : ℝ) * (M.K a' - M.K ρ)) *
              Real.exp (-((M.betaCrit : ℝ) * (M.K (M.S.dist x y) - M.K ρ))) := by
          rw [← Real.exp_add]
          apply Real.exp_le_exp.2
          nlinarith
        have habs_r : |(M.betaCrit : ℝ) * (-(deriv M.K r)) *
            Real.exp (-((M.betaCrit : ℝ) * (M.K (M.S.dist x y) - M.K r)))|
            = (M.betaCrit : ℝ) * (-(deriv M.K r)) *
              Real.exp (-((M.betaCrit : ℝ) * (M.K (M.S.dist x y) - M.K r))) :=
          abs_of_nonneg (by positivity)
        have habs_ρ : |(M.betaCrit : ℝ) * (-(deriv M.K ρ)) *
            Real.exp (-((M.betaCrit : ℝ) * (M.K (M.S.dist x y) - M.K ρ)))|
            = (M.betaCrit : ℝ) * (-(deriv M.K ρ)) *
              Real.exp (-((M.betaCrit : ℝ) * (M.K (M.S.dist x y) - M.K ρ))) :=
          abs_of_nonneg (by positivity)
        rw [habs_r, habs_ρ]
        have hKρne : (-(deriv M.K ρ)) ≠ 0 := ne_of_gt (by linarith)
        have hident : C / (-(deriv M.K ρ)) * Real.exp ((M.betaCrit : ℝ) * (M.K a' - M.K ρ)) *
            ((M.betaCrit : ℝ) * (-(deriv M.K ρ)) *
              Real.exp (-((M.betaCrit : ℝ) * (M.K (M.S.dist x y) - M.K ρ))))
            = C * Real.exp ((M.betaCrit : ℝ) * (M.K a' - M.K ρ)) * ((M.betaCrit : ℝ) *
              Real.exp (-((M.betaCrit : ℝ) * (M.K (M.S.dist x y) - M.K ρ)))) := by
          rw [div_eq_mul_inv]
          calc C * (-(deriv M.K ρ))⁻¹ * Real.exp ((M.betaCrit : ℝ) * (M.K a' - M.K ρ)) *
                ((M.betaCrit : ℝ) * (-(deriv M.K ρ)) *
                  Real.exp (-((M.betaCrit : ℝ) * (M.K (M.S.dist x y) - M.K ρ))))
              = C * Real.exp ((M.betaCrit : ℝ) * (M.K a' - M.K ρ)) * ((M.betaCrit : ℝ) *
                  Real.exp (-((M.betaCrit : ℝ) * (M.K (M.S.dist x y) - M.K ρ)))) *
                  ((-(deriv M.K ρ))⁻¹ * (-(deriv M.K ρ))) := by ring
            _ = C * Real.exp ((M.betaCrit : ℝ) * (M.K a' - M.K ρ)) * ((M.betaCrit : ℝ) *
                  Real.exp (-((M.betaCrit : ℝ) * (M.K (M.S.dist x y) - M.K ρ)))) := by
                rw [inv_mul_cancel₀ hKρne, mul_one]
        rw [hident]
        have hstep : (M.betaCrit : ℝ) * (-(deriv M.K r)) *
            Real.exp (-((M.betaCrit : ℝ) * (M.K (M.S.dist x y) - M.K r)))
            ≤ (M.betaCrit : ℝ) * C * Real.exp ((M.betaCrit : ℝ) * (M.K a' - M.K ρ)) *
              Real.exp (-((M.betaCrit : ℝ) * (M.K (M.S.dist x y) - M.K ρ))) := by
          have h1 : (M.betaCrit : ℝ) * (-(deriv M.K r)) ≤ (M.betaCrit : ℝ) * C :=
            mul_le_mul_of_nonneg_left hKrC hβ0
          calc (M.betaCrit : ℝ) * (-(deriv M.K r)) *
                Real.exp (-((M.betaCrit : ℝ) * (M.K (M.S.dist x y) - M.K r)))
              ≤ ((M.betaCrit : ℝ) * C) *
                (Real.exp ((M.betaCrit : ℝ) * (M.K a' - M.K ρ)) *
                  Real.exp (-((M.betaCrit : ℝ) * (M.K (M.S.dist x y) - M.K ρ)))) :=
                mul_le_mul h1 hAA hAr (by positivity)
            _ = (M.betaCrit : ℝ) * C * Real.exp ((M.betaCrit : ℝ) * (M.K a' - M.K ρ)) *
                  Real.exp (-((M.betaCrit : ℝ) * (M.K (M.S.dist x y) - M.K ρ))) := by ring
        calc (M.betaCrit : ℝ) * (-(deriv M.K r)) *
              Real.exp (-((M.betaCrit : ℝ) * (M.K (M.S.dist x y) - M.K r)))
            ≤ (M.betaCrit : ℝ) * C * Real.exp ((M.betaCrit : ℝ) * (M.K a' - M.K ρ)) *
                Real.exp (-((M.betaCrit : ℝ) * (M.K (M.S.dist x y) - M.K ρ))) := hstep
          _ = C * Real.exp ((M.betaCrit : ℝ) * (M.K a' - M.K ρ)) * ((M.betaCrit : ℝ) *
                Real.exp (-((M.betaCrit : ℝ) * (M.K (M.S.dist x y) - M.K ρ)))) := by ring
      · rw [M.cutEdgeDeriv_eq_zero_of_lt_dist (x := x) (y := y) (not_le.mp hdr), abs_zero]
        exact mul_nonneg hΛ0 (abs_nonneg _)

/-! ## 3. The radius-independent per-`y` flux envelope -/

/-- The pivotal flux of a single-vertex cluster indicator is bounded by twice the probability that
the edge touches the cluster of the origin. -/
theorem m1_abs_pivotalFlux_sMomentTrunc_le (y : M.V) (r : ℝ) (e : Sym2 M.V) :
    |pivotalFlux (M.cutLaw r)
        (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) ({y} : Finset M.V)) e|
      ≤ 2 * (M.cutLaw r).real {ω | e ∈ touchSet ω (0 : M.V)} := by
  have hm : (0 : ℝ) ≤ 1 := zero_le_one
  have hbound : ∀ ω,
      |sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) ({y} : Finset M.V) ω| ≤ 1 := by
    intro ω
    have h := abs_sMomentTrunc_le (fun _ => (1 : ℝ)) (0 : M.V) ({y} : Finset M.V) ω
    simpa using h
  have h := abs_pivotalFlux_le (o := (0 : M.V)) (M.cutLaw r) hm hbound
    (measurable_sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) ({y} : Finset M.V))
    (sMomentTrunc_dep (fun _ => (1 : ℝ)) (0 : M.V) ({y} : Finset M.V)) e
  simpa using h

/-- **The radius-independent per-`y` flux envelope.**  On `[a', b']`, every edge term of the
per-`y` off-corner flux is dominated by one fixed function of the edge, built from the cut-off
derivative and the touching probability at an interior radius `ρ ≥ b'`. -/
theorem m1_abs_flux_le_env {a' b' ρ C : ℝ} (ha' : 0 < a') (ha'b' : a' ≤ b')
    (hb'ρ : b' ≤ ρ) (hCb : ∀ r ∈ Icc a' b', -(deriv M.K r) ≤ C) (hC0 : 0 ≤ C)
    (hKρ : deriv M.K ρ < 0) (y : M.V) {r : ℝ} (hr : r ∈ Icc a' b') (e : Sym2 M.V) :
    |M.cutEdgeDeriv r e * pivotalFlux (M.cutLaw r)
        (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) ({y} : Finset M.V)) e|
      ≤ (C / (-(deriv M.K ρ)) * Real.exp ((M.betaCrit : ℝ) * (M.K a' - M.K ρ))) *
        (|M.cutEdgeDeriv ρ e| *
          (2 * (M.cutLaw b').real {ω | e ∈ touchSet ω (0 : M.V)})) := by
  have hr0 : 0 < r := lt_of_lt_of_le ha' hr.1
  have hρ0 : 0 < ρ := lt_of_lt_of_le (lt_of_lt_of_le ha' ha'b') hb'ρ
  have hb'0 : 0 < b' := lt_of_lt_of_le ha' ha'b'
  have hβ0 : (0 : ℝ) ≤ (M.betaCrit : ℝ) := M.betaCrit.coe_nonneg
  have hKρ0 : (0 : ℝ) ≤ -(deriv M.K ρ) := le_of_lt (by linarith)
  have hΛ0 : (0 : ℝ) ≤
      C / (-(deriv M.K ρ)) * Real.exp ((M.betaCrit : ℝ) * (M.K a' - M.K ρ)) := by
    have : (0 : ℝ) ≤ C / (-(deriv M.K ρ)) := div_nonneg hC0 hKρ0
    positivity
  have hPmono : (M.cutLaw r).real {ω | e ∈ touchSet ω (0 : M.V)}
      ≤ (M.cutLaw b').real {ω | e ∈ touchSet ω (0 : M.V)} :=
    M.m1_real_touchSet_mono_radius hr0 hb'0 hr.2 e
  have hscale := M.m1_abs_cutEdgeDeriv_le_scale ha' ha'b' hb'ρ hCb hC0 hKρ hr e
  have hpiv := M.m1_abs_pivotalFlux_sMomentTrunc_le y r e
  have hpiv' : |pivotalFlux (M.cutLaw r)
      (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) ({y} : Finset M.V)) e|
      ≤ 2 * (M.cutLaw b').real {ω | e ∈ touchSet ω (0 : M.V)} :=
    hpiv.trans (mul_le_mul_of_nonneg_left hPmono (by norm_num))
  calc |M.cutEdgeDeriv r e * pivotalFlux (M.cutLaw r)
        (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) ({y} : Finset M.V)) e|
      = |M.cutEdgeDeriv r e| * |pivotalFlux (M.cutLaw r)
        (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) ({y} : Finset M.V)) e| := abs_mul _ _
    _ ≤ ((C / (-(deriv M.K ρ)) * Real.exp ((M.betaCrit : ℝ) * (M.K a' - M.K ρ))) *
          |M.cutEdgeDeriv ρ e|) *
          (2 * (M.cutLaw b').real {ω | e ∈ touchSet ω (0 : M.V)}) :=
        mul_le_mul hscale hpiv' (abs_nonneg _) (by positivity)
    _ = (C / (-(deriv M.K ρ)) * Real.exp ((M.betaCrit : ℝ) * (M.K a' - M.K ρ))) *
          (|M.cutEdgeDeriv ρ e| *
            (2 * (M.cutLaw b').real {ω | e ∈ touchSet ω (0 : M.V)})) := by ring

/-- **The envelope is summable.**  The dominating family is the landed per-edge pivotal-mass
majorant at the interior radius `ρ`, which is summable by `summable_hdom_of_cutMoment` from a
finite first moment at `ρ`, plus the radius monotonicity of the touching probability. -/
theorem m1_summable_env {a' b' ρ C : ℝ} (ha' : 0 < a') (ha'b' : a' ≤ b')
    (hb'ρ : b' ≤ ρ) (hCb : ∀ r ∈ Icc a' b', -(deriv M.K r) ≤ C) (hC0 : 0 ≤ C)
    (hKρ : deriv M.K ρ < 0) (hρ : 0 < ρ)
    (hvol : M.cutMoment 1 ρ ≠ ⊤) :
    Summable fun e : Sym2 M.V =>
      (C / (-(deriv M.K ρ)) * Real.exp ((M.betaCrit : ℝ) * (M.K a' - M.K ρ))) *
        (|M.cutEdgeDeriv ρ e| *
          (2 * (M.cutLaw b').real {ω | e ∈ touchSet ω (0 : M.V)})) := by
  have hb'0 : 0 < b' := lt_of_lt_of_le ha' ha'b'
  have hβ0 : (0 : ℝ) ≤ (M.betaCrit : ℝ) := M.betaCrit.coe_nonneg
  have hKρ0 : (0 : ℝ) ≤ -(deriv M.K ρ) := le_of_lt (by linarith)
  have hΛ0 : (0 : ℝ) ≤
      C / (-(deriv M.K ρ)) * Real.exp ((M.betaCrit : ℝ) * (M.K a' - M.K ρ)) := by
    have : (0 : ℝ) ≤ C / (-(deriv M.K ρ)) := div_nonneg hC0 hKρ0
    positivity
  have hbase : Summable fun e : Sym2 M.V =>
      |M.cutEdgeDeriv ρ e| * (2 * (M.cutLaw ρ).real {ω | e ∈ touchSet ω (0 : M.V)}) :=
    M.summable_hdom_of_cutMoment hρ hvol
  have hdom : Summable fun e : Sym2 M.V =>
      |M.cutEdgeDeriv ρ e| * (2 * (M.cutLaw b').real {ω | e ∈ touchSet ω (0 : M.V)}) := by
    refine Summable.of_nonneg_of_le (fun e => ?_) (fun e => ?_) hbase
    · exact mul_nonneg (abs_nonneg _) (by positivity)
    · exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left
          (M.m1_real_touchSet_mono_radius hb'0 hρ hb'ρ e) (by norm_num)) (abs_nonneg _)
  exact hdom.mul_left _

/-- **The single summable radius-independent envelope for the per-`y` off-corner flux.** -/
theorem m1_exists_uniform_fluxEnvelope {a' b' ρ C : ℝ} (ha' : 0 < a') (ha'b' : a' ≤ b')
    (hb'ρ : b' ≤ ρ) (hCb : ∀ r ∈ Icc a' b', -(deriv M.K r) ≤ C) (hC0 : 0 ≤ C)
    (hKρ : deriv M.K ρ < 0) (hρ : 0 < ρ) (hvol : M.cutMoment 1 ρ ≠ ⊤) (y : M.V) :
    Summable (fun e : Sym2 M.V =>
        (C / (-(deriv M.K ρ)) * Real.exp ((M.betaCrit : ℝ) * (M.K a' - M.K ρ))) *
          (|M.cutEdgeDeriv ρ e| *
            (2 * (M.cutLaw b').real {ω | e ∈ touchSet ω (0 : M.V)})))
      ∧ ∀ r ∈ Icc a' b', ∀ e : Sym2 M.V,
        |M.cutEdgeDeriv r e * pivotalFlux (M.cutLaw r)
          (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) ({y} : Finset M.V)) e|
        ≤ (C / (-(deriv M.K ρ)) * Real.exp ((M.betaCrit : ℝ) * (M.K a' - M.K ρ))) *
          (|M.cutEdgeDeriv ρ e| *
            (2 * (M.cutLaw b').real {ω | e ∈ touchSet ω (0 : M.V)})) :=
  ⟨M.m1_summable_env ha' ha'b' hb'ρ hCb hC0 hKρ hρ hvol,
    fun r hr e => M.m1_abs_flux_le_env ha' ha'b' hb'ρ hCb hC0 hKρ y hr e⟩

/-! ## 4. Interval-uniform bounds from the envelope -/

/-- **The infinite per-`y` flux is bounded on the whole interval by one summable total.**  In
particular the per-`y` off-corner flux cannot blow up inside `[a', b']`, and the bound is a single
number built from the finite first moment at the interior radius `ρ`. -/
theorem m1_abs_infFlux_le_envSum {a' b' ρ C : ℝ} (ha' : 0 < a') (ha'b' : a' ≤ b')
    (hb'ρ : b' ≤ ρ) (hCb : ∀ r ∈ Icc a' b', -(deriv M.K r) ≤ C) (hC0 : 0 ≤ C)
    (hKρ : deriv M.K ρ < 0) (hρ : 0 < ρ) (hvol : M.cutMoment 1 ρ ≠ ⊤)
    (y : M.V) {r : ℝ} (hr : r ∈ Icc a' b') :
    |sMomentInfFlux (0 : M.V) ({y} : Finset M.V) (fun _ => (1 : ℝ))
        M.cutProb M.cutEdgeDeriv r| ≤
      ∑' e : Sym2 M.V,
        (C / (-(deriv M.K ρ)) * Real.exp ((M.betaCrit : ℝ) * (M.K a' - M.K ρ))) *
          (|M.cutEdgeDeriv ρ e| *
            (2 * (M.cutLaw b').real {ω | e ∈ touchSet ω (0 : M.V)})) := by
  classical
  obtain ⟨henv, hdom⟩ :=
    M.m1_exists_uniform_fluxEnvelope ha' ha'b' hb'ρ hCb hC0 hKρ hρ hvol y
  have habs : Summable fun e : Sym2 M.V =>
      ‖M.cutEdgeDeriv r e * pivotalFlux (M.cutLaw r)
        (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) ({y} : Finset M.V)) e‖ :=
    Summable.of_nonneg_of_le (fun e => abs_nonneg _) (fun e => hdom r hr e) henv
  refine (norm_tsum_le_tsum_norm habs).trans ?_
  refine Summable.tsum_le_tsum (fun e => ?_) habs henv
  simpa using hdom r hr e

end SourceModelData

end PercLib.CriticalLRP.Orchestration

namespace PercLib.CriticalLRP

/-- **`hmeasinf` follows from `hmeasK`.**  `StronglyMeasurableAtFilter` only asks for measurability
on a neighbourhood, so the pointwise convergence of the window fluxes to the infinite flux (already
available as `tendsto_windowFlux`) upgrades measurability of the windows to measurability of the
limit.  This removes the separate `hmeasinf` input of the exchange theorems. -/
theorem m1_stronglyMeasurableAtFilter_infFlux_of_window {V : Type*} [Countable V]
    (o : V) (g : Config V → ℝ) (S : ℕ → Finset (Sym2 V))
    (π : ℝ → Sym2 V → unitInterval) (c : ℝ → Sym2 V → ℝ) {I : Set ℝ}
    (hI : IsOpen I) {r0 : ℝ}
    (hr0 : r0 ∈ I)
    (hmeasK : ∀ k, AEStronglyMeasurable (windowFluxOf o g S π c k) volume)
    (hconv : ∀ r ∈ I, Tendsto (fun k => windowFluxOf o g S π c k r) atTop
      (𝓝 (infFluxOf g π c r))) :
    StronglyMeasurableAtFilter (infFluxOf g π c) (𝓝 r0) volume := by
  refine ⟨I, hI.mem_nhds hr0, ?_⟩
  have hconv' : ∀ᵐ r ∂(volume.restrict I),
      Tendsto (fun k => windowFluxOf o g S π c k r) atTop (𝓝 (infFluxOf g π c r)) := by
    filter_upwards [ae_restrict_mem hI.measurableSet] with r hr
    exact hconv r hr
  exact aestronglyMeasurable_of_tendsto_ae atTop
    (fun k => (hmeasK k).mono_measure Measure.restrict_le_self) hconv'

end PercLib.CriticalLRP

namespace PercLib.CriticalLRP.Orchestration.SourceModelData

end SourceModelData

end PercLib.CriticalLRP.Orchestration

namespace PercLib.CriticalLRP.Orchestration.SourceModelData

#print axioms m1_cutKernel_mono
#print axioms m1_cutProb_mono
#print axioms m1_abs_cutEdgeDeriv_le_scale
#print axioms m1_summable_env
#print axioms m1_abs_pivotalFlux_sMomentTrunc_le
#print axioms m1_abs_flux_le_env
#print axioms m1_exists_uniform_fluxEnvelope
#print axioms m1_abs_infFlux_le_envSum

end PercLib.CriticalLRP.Orchestration.SourceModelData

namespace PercLib.CriticalLRP

#print axioms m1_stronglyMeasurableAtFilter_infFlux_of_window

end PercLib.CriticalLRP
