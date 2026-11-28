/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Accepted and independently rebuilt from Ultramath `smwznoz6j`, member m8.
Latest independent rebuild at production HEAD `bd25afb1130f7fe93446b447f9a68a4d3aba08cc`; reviewed scratch source `.scratch/review-smwznoz6j/m8/Defs.lean`.
-/

/-
Ultramath swarm `smwznoz6j`, member `m8`, direction `d4`.

# Corner structure of the cutoff flux coefficient, and the corrected continuity input

Production `Analysis/SecondMomentCase3/RadialRegularity/FirstMomentSource.lean` carries the
continuity input

`hcontinf : ∀ y r, a₀ ≤ r → ContinuousAt (sMomentInfFlux 0 {y} 1 M.cutProb M.cutEdgeDeriv) r`

with **no** side condition on `r`.  This file establishes the model-side facts that decide
whether that is the right shape:

* the summand `e ↦ M.cutEdgeDeriv · e` of the flux series is the **right** derivative of the
  cutoff edge probability `r ↦ 1 - exp (-β_c (K (dist e) - K r)_+)`; it is identically `0`
  for `r < M.S.dist x y` and takes the value `β_c (-K'(r))` at `r = M.S.dist x y`, so it has a
  jump discontinuity there whenever `K'(r) ≠ 0`;
* `deriv M.K` is eventually nonzero (from the model's own error representation), and attained
  radii `M.attainedRadii` are unbounded above, so such corners occur above every threshold;
* off the corners the coefficient *is* continuous, given `ContinuousAt (deriv M.K) r₀`;
* consequently the correct form of the input is the corner-free one
  (`m8_hcontinf_corrected`, hence a.e. on `(a₀, ∞)` via `m8_ae_continuousAt_sMomentInfFlux`);
* and, modulo monotonicity and pointwise convergence of the window fluxes, `hcontinf` is
  *equivalent* to an explicit uniform-in-`r` window-tail estimate
  (`m8_hcontinf_iff_uniform_windowTail`).

Source: T. Hutchcroft, *Critical long-range percolation I*, arXiv:2508.18807v1,
Definition I.1.5 (`J_r(x,y) = (J(x,y) - J(r))_+`) and §I.1.2 (`p_r(e) = 1 - exp(-β J_r(e))`).
-/
module

public import PercLib.CriticalLRP.Analysis.SecondMomentCase3.RadialRegularity.FirstMomentSource
public import PercLib.CriticalLRP.Analysis.Cutoff.CornerRadii.Defs
public import PercLib.CriticalLRP.Analysis.Cutoff.OffCorner.RadiusHorizon.Main

@[expose] public section

noncomputable section

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.hashCommand false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP

/-! ## 0. A local Weierstrass criterion for continuity of a `tsum`

Production has the `ContinuousOn` form (`continuousOn_tsum`) and the uniform-convergence-in-the-
window-index form (`continuousAt_infFlux_of_hunif`).  The criterion used below is the *local*
domination form: continuity of every summand at `r₀` together with a single summable dominator
valid only on a neighbourhood of `r₀`.  This is the exact shape of the flux-domination bound of
the source (total pivotal mass), and it is strictly local: nothing is asserted about `r` away
from `r₀`. -/

/-- **Continuity of a `tsum` from termwise continuity and a locally valid summable dominator.** -/
theorem m8_continuousAt_tsum_of_locally_dominated {ι : Type*} {f : ι → ℝ → ℝ} {u : ι → ℝ}
    {r₀ : ℝ} (hu : Summable u) (hdom : ∀ᶠ r in 𝓝 r₀, ∀ e, ‖f e r‖ ≤ u e)
    (hcont : ∀ e, ContinuousAt (f e) r₀) :
    ContinuousAt (fun r => ∑' e, f e r) r₀ := by
  exact tendsto_tsum_of_dominated_convergence (𝓕 := 𝓝 r₀)
    (f := fun r e => f e r) (g := fun e => f e r₀) hu hcont hdom

end PercLib.CriticalLRP

namespace PercLib.CriticalLRP

namespace Orchestration

namespace SourceModelData

variable (M : SourceModelData)

/-! ## 1. Unfolding the cutoff edge derivative -/

/-- The `Sym2` unfolding of the cutoff edge derivative. -/
theorem m8_cutEdgeDeriv_mk (r : ℝ) (x y : M.V) :
    M.cutEdgeDeriv r s(x, y) =
      (if x = y then (0 : ℝ) else
        (if M.S.dist x y ≤ r then
          (M.betaCrit : ℝ) * (-(deriv M.K r)) *
            Real.exp (-((M.betaCrit : ℝ) *
              FiniteVolume.cutoffProfile M.K r (M.S.dist x y)))
         else 0)) := rfl

/-- For `r` below the edge length the cutoff edge probability is identically `0`, hence so is
its derivative. -/
theorem m8_cutEdgeDeriv_eq_zero_of_lt {x y : M.V} {r : ℝ} (h : r < M.S.dist x y) :
    M.cutEdgeDeriv r s(x, y) = 0 := by
  rcases eq_or_ne x y with hxy | hxy
  · rw [hxy, M.m8_cutEdgeDeriv_mk, ite_eq_left rfl]
  · rw [M.m8_cutEdgeDeriv_mk, ite_eq_right hxy, ite_eq_right (not_le.mpr h)]

/-- On an edge of length `≤ r` with distinct endpoints, the coefficient is the right derivative
`β_c (-K'(r)) exp (-β_c J_r(e))`. -/
theorem m8_cutEdgeDeriv_eq_of_le {x y : M.V} {r : ℝ} (hxy : x ≠ y) (h : M.S.dist x y ≤ r) :
    M.cutEdgeDeriv r s(x, y) =
      (M.betaCrit : ℝ) * (-(deriv M.K r)) *
        Real.exp (-((M.betaCrit : ℝ) *
          FiniteVolume.cutoffProfile M.K r (M.S.dist x y))) := by
  rw [M.m8_cutEdgeDeriv_mk, ite_eq_right hxy, ite_eq_left h]

/-- At the attained radius `r = M.S.dist x y` the cutoff profile vanishes, so the coefficient
equals `β_c (-K'(r))` while its left limit is `0`. -/
theorem m8_cutEdgeDeriv_at_dist {x y : M.V} (hxy : x ≠ y) :
    M.cutEdgeDeriv (M.S.dist x y) s(x, y)
      = (M.betaCrit : ℝ) * (-(deriv M.K (M.S.dist x y))) := by
  rw [M.m8_cutEdgeDeriv_eq_of_le hxy le_rfl, FiniteVolume.cutoffProfile_of_le le_rfl, sub_self,
    mul_zero, neg_zero, Real.exp_zero, mul_one]

/-- **The left limit of the cutoff edge derivative at an attained radius is `0`.** -/
theorem m8_tendsto_cutEdgeDeriv_nhdsLT_at_dist {x y : M.V} (hxy : x ≠ y) :
    Tendsto (fun r => M.cutEdgeDeriv r s(x, y)) (𝓝[<] (M.S.dist x y)) (𝓝 0) := by
  refine (tendsto_const_nhds (x := (0 : ℝ))).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with r hr
  exact (M.m8_cutEdgeDeriv_eq_zero_of_lt hr).symm

/-- **The cutoff edge derivative is discontinuous at every attained radius with `K' ≠ 0`.** -/
theorem m8_not_continuousAt_cutEdgeDeriv_at_dist {x y : M.V} (hxy : x ≠ y)
    (hβ : (0 : ℝ) < (M.betaCrit : ℝ))
    (hK' : deriv M.K (M.S.dist x y) ≠ 0) :
    ¬ ContinuousAt (fun r => M.cutEdgeDeriv r s(x, y)) (M.S.dist x y) := by
  intro hcont
  have hleft := M.m8_tendsto_cutEdgeDeriv_nhdsLT_at_dist hxy
  have hright : Tendsto (fun r => M.cutEdgeDeriv r s(x, y)) (𝓝[<] (M.S.dist x y))
      (𝓝 (M.cutEdgeDeriv (M.S.dist x y) s(x, y))) :=
    hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hzero : M.cutEdgeDeriv (M.S.dist x y) s(x, y) = 0 :=
    tendsto_nhds_unique hright hleft
  rw [M.m8_cutEdgeDeriv_at_dist hxy] at hzero
  rcases mul_eq_zero.1 hzero with h | h
  · exact hβ.ne' h
  · exact hK' (neg_eq_zero.1 h)

/-- **The cutoff edge derivative is right-continuous at every attained radius.**  Together with
`m8_tendsto_cutEdgeDeriv_nhdsLT_at_dist` this pins down the one-sided character of the
coefficient: the left limit is `0`, the value and the right limit are `β_c (-K'(r))`. -/
theorem m8_tendsto_cutEdgeDeriv_nhdsGT_at_dist {x y : M.V} (hxy : x ≠ y) (hr : 0 < M.S.dist x y)
    (hK : ContinuousAt (fun r => deriv M.K r) (M.S.dist x y)) :
    Tendsto (fun r => M.cutEdgeDeriv r s(x, y)) (𝓝[>] (M.S.dist x y))
      (𝓝 (M.cutEdgeDeriv (M.S.dist x y) s(x, y))) := by
  have hs := hr
  have hKcont : ContinuousAt M.K (M.S.dist x y) :=
    M.K_diff.continuousOn.continuousAt (Ioi_mem_nhds hs)
  have hmem : ∀ᶠ r in 𝓝[>] (M.S.dist x y), M.S.dist x y ≤ r :=
    mem_of_superset self_mem_nhdsWithin (fun r hr => le_of_lt hr)
  have hval : Tendsto (fun r => (M.betaCrit : ℝ) * (-(deriv M.K r)) *
      Real.exp (-((M.betaCrit : ℝ) *
        FiniteVolume.cutoffProfile M.K r (M.S.dist x y))))
      (𝓝[>] (M.S.dist x y)) (𝓝 (M.cutEdgeDeriv (M.S.dist x y) s(x, y))) := by
    have hexp : Tendsto (fun r => Real.exp (-((M.betaCrit : ℝ) *
        FiniteVolume.cutoffProfile M.K r (M.S.dist x y)))) (𝓝[>] (M.S.dist x y)) (𝓝 1) := by
      have h1 : Tendsto (fun r => Real.exp (-((M.betaCrit : ℝ) *
          (M.K (M.S.dist x y) - M.K r)))) (𝓝[>] (M.S.dist x y)) (𝓝 1) := by
        have hbase : Tendsto M.K (𝓝[>] (M.S.dist x y)) (𝓝 (M.K (M.S.dist x y))) :=
          hKcont.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (M.S.dist x y)))
        have h3 : Tendsto (fun r => (M.betaCrit : ℝ) * (M.K (M.S.dist x y) - M.K r))
            (𝓝[>] (M.S.dist x y)) (𝓝 0) := by
          have h4 := (hbase.const_sub (M.K (M.S.dist x y))).const_mul (M.betaCrit : ℝ)
          simpa using h4
        have h2 : Tendsto (fun r => -((M.betaCrit : ℝ) *
            (M.K (M.S.dist x y) - M.K r))) (𝓝[>] (M.S.dist x y)) (𝓝 0) := by
          simpa using h3.neg
        have hcomp : Tendsto (fun r => Real.exp (-((M.betaCrit : ℝ) *
            (M.K (M.S.dist x y) - M.K r)))) (𝓝[>] (M.S.dist x y)) (𝓝 (Real.exp 0)) :=
          (Real.continuous_exp.tendsto (0 : ℝ)).comp h2
        simpa only [Real.exp_zero] using hcomp
      refine h1.congr' ?_
      filter_upwards [hmem] with r hr
      rw [FiniteVolume.cutoffProfile_of_le hr]
    have hkbase : Tendsto (fun r => deriv M.K r) (𝓝[>] (M.S.dist x y))
        (𝓝 (deriv M.K (M.S.dist x y))) :=
      hK.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (M.S.dist x y)))
    have hcoef : Tendsto (fun r => (M.betaCrit : ℝ) * (-(deriv M.K r)))
        (𝓝[>] (M.S.dist x y)) (𝓝 ((M.betaCrit : ℝ) * (-(deriv M.K (M.S.dist x y))))) :=
      hkbase.neg.const_mul (M.betaCrit : ℝ)
    have := hcoef.mul hexp
    rw [M.m8_cutEdgeDeriv_at_dist hxy]
    simpa using this
  refine hval.congr' ?_
  filter_upwards [hmem] with r hr
  exact (M.m8_cutEdgeDeriv_eq_of_le hxy hr).symm

/-- **Off the attained radii the coefficient is continuous**, given continuity of
`r ↦ deriv M.K r` at the point.  This is the correct side condition for the flux continuity
input: the coefficient is a genuine one-sided object at `r = M.S.dist x y` and two-sided
elsewhere. -/
theorem m8_continuousAt_cutEdgeDeriv_of_ne_dist {x y : M.V} {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hne : M.S.dist x y ≠ r₀) (hK : ContinuousAt (fun r => deriv M.K r) r₀) :
    ContinuousAt (fun r => M.cutEdgeDeriv r s(x, y)) r₀ := by
  rcases eq_or_ne x y with hxy | hxy
  · subst hxy
    have h0 : (fun r => M.cutEdgeDeriv r s(x, x)) = fun _ => (0 : ℝ) := by
      funext r
      rw [M.m8_cutEdgeDeriv_mk, ite_eq_left rfl]
    rw [h0]
    exact continuousAt_const
  have hKcont : ContinuousAt M.K r₀ :=
    M.K_diff.continuousOn.continuousAt (Ioi_mem_nhds hr₀)
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hmem : ∀ᶠ r in 𝓝 r₀, M.S.dist x y ≤ r := eventually_ge_nhds hlt
    have hexp : ContinuousAt
        (fun r => Real.exp (-((M.betaCrit : ℝ) *
          FiniteVolume.cutoffProfile M.K r (M.S.dist x y)))) r₀ := by
      have h1 : ContinuousAt (fun r => Real.exp (-((M.betaCrit : ℝ) *
          (M.K (M.S.dist x y) - M.K r)))) r₀ := by
        have h2 : ContinuousAt (fun r => (M.betaCrit : ℝ) *
            (M.K (M.S.dist x y) - M.K r)) r₀ :=
          continuousAt_const.mul (hKcont.const_sub _)
        exact Real.continuous_exp.continuousAt.comp h2.neg
      refine h1.congr ?_
      filter_upwards [hmem] with r hr
      rw [FiniteVolume.cutoffProfile_of_le hr]
    have hcoef : ContinuousAt (fun r => (M.betaCrit : ℝ) * (-(deriv M.K r))) r₀ :=
      continuousAt_const.mul hK.neg
    refine ContinuousAt.congr (hcoef.mul hexp) (Filter.EventuallyEq.symm ?_)
    filter_upwards [hmem] with r hr
    simp only [Pi.mul_apply]
    exact M.m8_cutEdgeDeriv_eq_of_le hxy hr
  · have hmem : ∀ᶠ r in 𝓝 r₀, r < M.S.dist x y := eventually_lt_nhds hgt
    have hzero : ContinuousAt (fun _ : ℝ => (0 : ℝ)) r₀ := continuousAt_const
    refine ContinuousAt.congr hzero ?_
    filter_upwards [hmem] with r hr
    exact (M.m8_cutEdgeDeriv_eq_zero_of_lt hr).symm

/-! ## 2. Corners above every threshold -/

/-- The model's own error representation forces `deriv M.K` to be eventually nonzero. -/
theorem m8_exists_deriv_K_ne_zero :
    ∃ R : ℝ, ∀ r : ℝ, R ≤ r → deriv M.K r ≠ 0 := by
  obtain ⟨δ, hδabs, hδlog⟩ := M.exists_error
  have hδ0 : Tendsto δ atTop (𝓝 0) := hδlog.2
  have hev : ∀ᶠ r : ℝ in atTop, (1 / 2 : ℝ) < 1 + δ r := by
    have h := hδ0.eventually (lt_mem_nhds (show (-1 / 2 : ℝ) < 0 by norm_num))
    filter_upwards [h] with r hr
    linarith
  obtain ⟨R, hR⟩ := eventually_atTop.1 hev
  refine ⟨max R 1, fun r hr => ?_⟩
  have hr1 : 1 ≤ r := le_trans (le_max_right _ _) hr
  have hr0 : 0 < r := lt_of_lt_of_le one_pos hr1
  have habs := hδabs r hr0
  have hpos : 0 < (1 + δ r) * r ^ (-(M.d : ℝ) - M.α - 1) :=
    mul_pos (by linarith [hR r (le_trans (le_max_left _ _) hr)]) (Real.rpow_pos_of_pos hr0 _)
  have hne : |deriv M.K r| ≠ 0 := by rw [habs]; exact hpos.ne'
  exact abs_ne_zero.mp hne

/-- **Attained radii are unbounded above**: for every threshold there is a modulus `r ≥ a₀`
which the model's norm attains at a nonzero lattice vector. -/
theorem m8_exists_attainedRadii_ge (a₀ : ℝ) :
    ∃ r : ℝ, a₀ ≤ r ∧ r ∈ M.attainedRadii := by
  classical
  haveI : Nonempty (Fin M.d) := ⟨⟨0, by have := M.hd; omega⟩⟩
  obtain ⟨i⟩ := ‹Nonempty (Fin M.d)›
  set v : Fin M.d → ℝ := Pi.single i 1 with hv
  have hvne : v ≠ 0 := by
    intro h
    have := congrFun h i
    simp [hv] at this
  have hvpos : 0 < M.S.ρ v := M.S.ρ_pos v hvne
  have htoVec : ∀ k : ℤ, toVec (Pi.single i k) = (k : ℝ) • v := by
    intro k
    funext j
    by_cases hj : j = i
    · subst hj; simp [toVec, hv]
    · simp [toVec, hv, Pi.single_eq_of_ne hj]
  set n : ℕ := ⌈max a₀ 1 / M.S.ρ v⌉₊ + 1 with hn
  have hnR : (0 : ℝ) < (n : ℝ) := by positivity
  have hlarge : a₀ ≤ (n : ℝ) * M.S.ρ v := by
    have h1 : ⌈max a₀ 1 / M.S.ρ v⌉₊ ≤ n := Nat.le_succ _
    have h2 : (max a₀ 1 / M.S.ρ v) ≤ ((⌈max a₀ 1 / M.S.ρ v⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
    have h3 : (max a₀ 1 / M.S.ρ v) ≤ (n : ℝ) := le_trans h2 (by exact_mod_cast h1)
    have h4 : a₀ ≤ max a₀ 1 := le_max_left _ _
    have := mul_le_mul_of_nonneg_right h3 hvpos.le
    rw [div_mul_cancel₀ _ hvpos.ne'] at this
    linarith
  refine ⟨(n : ℝ) * M.S.ρ v, hlarge, Pi.single i (n : ℤ), ?_, ?_⟩
  · intro h
    have h0 : (Pi.single i (n : ℤ) : M.V) i = (0 : M.V) i := by rw [h]
    simp only [Pi.single_eq_same, Pi.zero_apply] at h0
    have hn0 : n = 0 := by exact_mod_cast h0
    omega
  · rw [SourceNormData.dist_zero_right, htoVec, M.S.ρ_smul, abs_of_nonneg (by positivity)]
    push_cast
    ring

/-! ## 3. The flux summand, and the corrected continuity input -/

/-- The `e`-th summand of the infinite flux of the truncated spatial moment at the source model,
written with the model's own cutoff law. -/
noncomputable def m8FluxTerm (g : Config M.V → ℝ) (r : ℝ) (e : Sym2 M.V) : ℝ :=
  M.cutEdgeDeriv r e * pivotalFlux (M.cutLaw r) g e

/-- `sMomentInfFlux` really is the series of `m8FluxTerm` summands. -/
theorem m8_sMomentInfFlux_eq_tsum (o : M.V) (A : Finset M.V) (q : M.V → ℝ) (r : ℝ) :
    sMomentInfFlux o A q M.cutProb M.cutEdgeDeriv r
      = ∑' e, M.m8FluxTerm (sMomentTrunc q o A) r e := by
  simp only [m8FluxTerm, sMomentInfFlux, infFluxOf]
  exact tsum_congr fun e => by rw [E1Sign.cutLaw_eq M r]

/-- **A flux summand is continuous at `r₀` off the corner set.**  The two inputs are exactly the
coefficient continuity (`hK`) and continuity in the radius of the pivotal flux, which is the
single measure-side residual of this route. -/
theorem m8_continuousAt_m8FluxTerm_of_ne_dist {g : Config M.V → ℝ} {x y : M.V} {r₀ : ℝ}
    (hr₀ : 0 < r₀) (hne : M.S.dist x y ≠ r₀) (hK : ContinuousAt (fun r => deriv M.K r) r₀)
    (hpiv : ContinuousAt (fun r => pivotalFlux (M.cutLaw r) g s(x, y)) r₀) :
    ContinuousAt (fun r => M.m8FluxTerm g r s(x, y)) r₀ :=
  (M.m8_continuousAt_cutEdgeDeriv_of_ne_dist hr₀ hne hK).mul hpiv

/-- **The corrected continuity input of `RadialRegularity/FirstMomentSource`.**

Production's `hcontinf` asks for `ContinuousAt (sMomentInfFlux …) r` at **every** `r ≥ a₀`.
The coefficient is a one-sided object at the corners `M.attainedRadii`
(`m8_not_continuousAt_cutEdgeDeriv_at_dist`), so the honest statement is the corner-free one
below, and it follows from the two explicit residuals of this route: termwise continuity of the
flux summands and a *local* summable dominator (the total-pivotal-mass bound). -/
theorem m8_hcontinf_corrected
    (hK : ∀ r : ℝ, 0 < r → ContinuousAt (fun r' => deriv M.K r') r)
    (hpiv : ∀ y : M.V, ∀ (e : Sym2 M.V), ∀ r : ℝ, 0 < r →
      ContinuousAt (fun r' => pivotalFlux (M.cutLaw r')
        (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) {y}) e) r)
    (hdom : ∀ y : M.V, ∀ r₀ : ℝ, 0 < r₀ → ∃ u : Sym2 M.V → ℝ, Summable u ∧
      ∀ᶠ r in 𝓝 r₀, ∀ e : Sym2 M.V,
        ‖M.m8FluxTerm (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) {y}) r e‖ ≤ u e) :
    ∀ y : M.V, ∀ r : ℝ, 0 < r → r ∉ M.attainedRadii → ContinuousAt
      (sMomentInfFlux (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv) r := by
  intro y r₀ hr₀ hcorner
  have heq : sMomentInfFlux (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv
      = fun r => ∑' e, M.m8FluxTerm (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) {y}) r e := by
    funext r
    exact M.m8_sMomentInfFlux_eq_tsum (0 : M.V) {y} (fun _ => (1 : ℝ)) r
  rw [heq]
  obtain ⟨u, hu, hdom'⟩ := hdom y r₀ hr₀
  refine m8_continuousAt_tsum_of_locally_dominated hu hdom' ?_
  intro e
  induction e using Sym2.ind with
  | h x z =>
    refine M.m8_continuousAt_m8FluxTerm_of_ne_dist hr₀ ?_ (hK r₀ hr₀) (hpiv y s(x, z) r₀ hr₀)
    intro hc
    rcases eq_or_ne x z with rfl | hxz
    · rw [SourceNormData.dist, toVec_sub, sub_self, M.S.ρ_zero] at hc
      exact hr₀.ne' hc.symm
    · have hmem : M.S.dist x z ∈ M.attainedRadii := M.S.mem_attainedRadii_of_dist hxz
      rw [hc] at hmem
      exact hcorner hmem

/-- The attained radii form a countable set: they are the range of `x ↦ M.S.dist x 0` over the
countable lattice.  Hence they are Lebesgue-null, which is why the corner-free form of the
continuity input is enough for the almost-everywhere derivative consumers. -/
theorem m8_countable_attainedRadii : M.attainedRadii.Countable := by
  have h : M.attainedRadii ⊆ Set.range (fun x : M.V => M.S.dist x 0) := by
    rintro r ⟨x, -, rfl⟩
    exact ⟨x, rfl⟩
  exact Set.Countable.mono h (Set.countable_range _)

/-- **Almost-everywhere continuity of the flux at the source model.**  The corner-free form
`m8_hcontinf_corrected` upgrades to an `∀ᵐ r` statement, because `M.attainedRadii` is countable
and therefore null.  This is the form in which the almost-everywhere derivative consumers
(`hac`/`hae` in `RadialRegularity/ACAE`) actually use the continuity input. -/
theorem m8_ae_continuousAt_sMomentInfFlux (a₀ : ℝ) (ha₀ : 0 < a₀)
    (hK : ∀ r : ℝ, 0 < r → ContinuousAt (fun r' => deriv M.K r') r)
    (hpiv : ∀ y : M.V, ∀ (e : Sym2 M.V), ∀ r : ℝ, 0 < r →
      ContinuousAt (fun r' => pivotalFlux (M.cutLaw r')
        (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) {y}) e) r)
    (hdom : ∀ y : M.V, ∀ r₀ : ℝ, 0 < r₀ → ∃ u : Sym2 M.V → ℝ, Summable u ∧
      ∀ᶠ r in 𝓝 r₀, ∀ e : Sym2 M.V,
        ‖M.m8FluxTerm (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) {y}) r e‖ ≤ u e)
    (y : M.V) :
    ∀ᵐ r ∂(volume.restrict (Set.Ioi a₀)), ContinuousAt
      (sMomentInfFlux (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv) r := by
  have hnull : volume M.attainedRadii = 0 := M.m8_countable_attainedRadii.measure_zero volume
  have hmeas : MeasurableSet M.attainedRadii := M.m8_countable_attainedRadii.measurableSet
  have hμ : (volume.restrict (Set.Ioi a₀)) M.attainedRadii = 0 := by
    rw [Measure.restrict_apply hmeas]
    exact measure_mono_null Set.inter_subset_left hnull
  have h1 : ∀ᵐ r ∂(volume.restrict (Set.Ioi a₀)), r ∉ M.attainedRadii := by
    rw [ae_iff]
    simpa using hμ
  have h2 : ∀ᵐ r ∂(volume.restrict (Set.Ioi a₀)), 0 < r := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    exact lt_trans ha₀ hr
  filter_upwards [h1, h2] with r hr hpos
  exact M.m8_hcontinf_corrected hK hpiv hdom y r hpos hr

/-- **Headline: above every threshold there is an attained radius at which the flux coefficient
provably fails to be continuous.**

This is the obstruction to the un-side-conditioned `hcontinf` of
`RadialRegularity/FirstMomentSource`: that statement asks for two-sided continuity of
`sMomentInfFlux …` at **every** `r ≥ a₀`, hence in particular at the radius produced here,
where one of its summands `e ↦ M.cutEdgeDeriv · e` has a jump of size `β_c |K'(r)| > 0`.  The
correct form is the corner-free `m8_hcontinf_corrected`. -/
theorem m8_exists_discontinuous_cutEdgeDeriv (a₀ : ℝ) (hβ : (0 : ℝ) < M.betaCrit) :
    ∃ (r : ℝ) (x : M.V), a₀ ≤ r ∧ x ≠ 0 ∧ M.S.dist x 0 = r ∧
      ¬ ContinuousAt (fun r' => M.cutEdgeDeriv r' s(x, 0)) r := by
  obtain ⟨R, hR⟩ := M.m8_exists_deriv_K_ne_zero
  obtain ⟨r, hge, hmem⟩ := M.m8_exists_attainedRadii_ge (max a₀ R)
  obtain ⟨x, hx0, hdist⟩ := hmem
  refine ⟨r, x, le_trans (le_max_left a₀ R) hge, hx0, hdist, ?_⟩
  rw [← hdist]
  refine M.m8_not_continuousAt_cutEdgeDeriv_at_dist hx0 hβ ?_
  have h := hR r (le_trans (le_max_right a₀ R) hge)
  rw [hdist]
  exact h

/-- **The flux analogue of `continuousAt_iff_uniform_tail`.**

`RadiusHorizon/Main.lean` proves, for monotone approximations of an *event mass*, that
continuity of the limit is equivalent to a uniform-in-`r` tail estimate.  This is the same
statement for the pivotal flux: given that the window fluxes are monotone in the window index,
converge pointwise to `sMomentInfFlux` and are continuous in the radius, the two-sided
continuity input `hcontinf` is **equivalent** to the explicit uniform estimate
`sup_{|r−r₀|<δ} (sMomentInfFlux r − windowFluxOf N r) ≤ ε`.

So `hcontinf` carries exactly one piece of quantitative information: uniformity in `r` of the
window tail of the flux.  Nothing weaker than that can replace it. -/
theorem m8_hcontinf_iff_uniform_windowTail
    (o : M.V) (A : Finset M.V) (q : M.V → ℝ) (S : ℕ → Finset (Sym2 M.V)) {r₀ : ℝ}
    (hmono : Monotone (fun n : ℕ => fun r : ℝ =>
      windowFluxOf o (sMomentTrunc q o A) S M.cutProb M.cutEdgeDeriv n r))
    (hcont : ∀ n : ℕ, ContinuousAt (fun r : ℝ =>
      windowFluxOf o (sMomentTrunc q o A) S M.cutProb M.cutEdgeDeriv n r) r₀)
    (htend : ∀ r : ℝ, Tendsto (fun n : ℕ =>
      windowFluxOf o (sMomentTrunc q o A) S M.cutProb M.cutEdgeDeriv n r) atTop
      (𝓝 (sMomentInfFlux o A q M.cutProb M.cutEdgeDeriv r))) :
    ContinuousAt (sMomentInfFlux o A q M.cutProb M.cutEdgeDeriv) r₀ ↔
      ∀ ε > 0, ∃ N : ℕ, ∃ δ : ℝ, 0 < δ ∧ ∀ r : ℝ, |r - r₀| < δ →
        sMomentInfFlux o A q M.cutProb M.cutEdgeDeriv r
          - windowFluxOf o (sMomentTrunc q o A) S M.cutProb M.cutEdgeDeriv N r ≤ ε := by
  refine continuousAt_iff_uniform_tail (u := fun n : ℕ => fun r : ℝ =>
    windowFluxOf o (sMomentTrunc q o A) S M.cutProb M.cutEdgeDeriv n r) hmono ?_ htend hcont
  intro n r
  exact le_of_tendsto_of_tendsto tendsto_const_nhds (htend r)
    (eventually_atTop.mpr ⟨n, fun m hm => hmono hm r⟩)

end SourceModelData

end Orchestration

/-! ## Axiom audit -/

set_option linter.hashCommand false in
#print axioms PercLib.CriticalLRP.m8_continuousAt_tsum_of_locally_dominated
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.m8_cutEdgeDeriv_mk
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.m8_cutEdgeDeriv_eq_zero_of_lt
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.m8_cutEdgeDeriv_eq_of_le
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.m8_cutEdgeDeriv_at_dist
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.m8_tendsto_cutEdgeDeriv_nhdsLT_at_dist
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.m8_not_continuousAt_cutEdgeDeriv_at_dist
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.m8_tendsto_cutEdgeDeriv_nhdsGT_at_dist
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.m8_continuousAt_cutEdgeDeriv_of_ne_dist
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.m8_exists_deriv_K_ne_zero
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.m8_exists_attainedRadii_ge
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.m8_sMomentInfFlux_eq_tsum
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.m8_continuousAt_m8FluxTerm_of_ne_dist
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.m8_hcontinf_corrected
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.m8_countable_attainedRadii
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.m8_ae_continuousAt_sMomentInfFlux
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.m8_exists_discontinuous_cutEdgeDeriv
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.m8_hcontinf_iff_uniform_windowTail

end PercLib.CriticalLRP
