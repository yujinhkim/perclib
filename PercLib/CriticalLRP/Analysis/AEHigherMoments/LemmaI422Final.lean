/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Integrated and independently rebuilt from accepted Ultramath `smwypth8o`, member `m2`.
Swarm `smwypth8o`, member `m2`, direction (2).

Lemma I.4.22 in the off-corner (a.e.) form: the conclusion of
`Analysis.Lemma_I_4_22.lemma_I_4_22_of_hasDerivAt_bound` from

* absolute continuity of `f` on every compact radius window of a tail,
* an a.e. derivative `f'` of `f` on that tail,
* an **a.e.** one-sided ODE `f' ≤ (1 + δ) (a f + h)/r` with a *measurable defect* `δ → 0`,

i.e. no derivative is assumed at the corner radii, and the driving ODE is only required off a
null set.  The defect `δ` is allowed to take both signs, so this covers the model's
`(1 - cutError)` normalisation with `cutError → 0`, not just bounds that are already sharp.
-/
module

public import PercLib.CriticalLRP.Analysis.AEHigherMoments.LemmaI422


/-! # Almost-everywhere higher-moment interface: LemmaI422Final -/

set_option autoImplicit false
set_option linter.style.multiGoal false

open MeasureTheory Filter Set Topology
open scoped Topology

@[expose] public section

namespace PercLib.CriticalLRP.Analysis.AE

/-- **Lemma I.4.22 with an a.e. derivative and an a.e. one-sided ODE.**

Let `f` be absolutely continuous on every `[r₀, R]`, let `f'` be a derivative of `f` at almost
every radius of `[r₀, ∞)`, and suppose that at almost every radius

`f'(r) ≤ (1 + δ r) (a f(r) + h(r)) / r`

for a measurable defect `δ` with `δ → 0` and `|δ| ≤ 1` on the tail, and that
`h` is regularly varying of positive index `b > a` with the usual positivity.  Then
`f r ≤ (1 + ε) h r / (b - a)` eventually, for every `ε > 0`.

Compared with `lemma_I_4_22_of_hasDerivAt_bound`, the derivative hypothesis is replaced by
absolute continuity plus an a.e. derivative, and the `(1+o(1))` ODE on a tail by its a.e. form
with an explicit measurable defect. -/
theorem ae_lemma_I_4_22_of_defect_bound {f f' δ : ℝ → ℝ} {h : ℝ → ℝ} {b : ℝ}
    (D : RVPosData h b) {a r₀ : ℝ} (ha : 0 < a) (hab : a < b) (hr₀ : 0 < r₀)
    (hpos : ∀ x, 0 < x → 0 < h x) (hfpos : ∀ x, 0 < x → 0 < f x)
    (hac : AbsolutelyContinuousOnTail f r₀) (hae : AeHasDerivAtOnTail f f' r₀)
    (hδm : Measurable δ) (hδ0 : Tendsto δ atTop (𝓝 0))
    (hδ1 : ∀ x, r₀ ≤ x → |δ x| ≤ 1)
    (hfbd : ∀ᵐ x ∂(volume.restrict (Set.Ici r₀)),
      f' x ≤ (1 + δ x) * (a * f x + h x) / x) :
    ∀ ε > 0, ∀ᶠ r in atTop, f r ≤ (1 + ε) * (h r / (b - a)) := by
  let θ : ℝ → ℝ := fun x => max 1 (1 + δ x)
  have hθm : Measurable θ := measurable_const.max (measurable_const.add hδm)
  have hθlower : ∀ x, r₀ ≤ x → 1 ≤ θ x := fun _ _ => le_max_left _ _
  have hθ0 : Tendsto θ atTop (𝓝 1) := by
    have h1 : Tendsto (fun x => 1 + δ x) atTop (𝓝 (1 + 0)) := tendsto_const_nhds.add hδ0
    have h2 := (tendsto_const_nhds (x := (1 : ℝ))).max h1
    simpa [θ] using h2
  have hδ'm : Measurable (fun x => 1 - θ x) := measurable_const.sub hθm
  have hδ'0 : Tendsto (fun x => 1 - θ x) atTop (𝓝 0) := by
    have h := (tendsto_const_nhds (x := (1 : ℝ))).sub hθ0
    simpa using h
  have hδ'1 : ∀ x, r₀ ≤ x → |1 - θ x| ≤ 1 := by
    intro x hx
    have hδle : δ x ≤ 1 := (le_abs_self (δ x)).trans (hδ1 x hx)
    have hθle : θ x ≤ 2 := max_le (by norm_num) (by linarith)
    have hθge : 1 ≤ θ x := le_max_left _ _
    rw [abs_le]
    constructor <;> linarith
  have hfbdθ : AeDrivingBound f f' θ h a r₀ := by
    filter_upwards [hfbd, ae_restrict_mem measurableSet_Ici] with x hx hmem
    have hx0 : 0 < x := lt_of_lt_of_le hr₀ hmem
    have hnum : 0 ≤ (a * f x + h x) / x := by
      have h1 := hfpos x hx0
      have h2 := hpos x hx0
      positivity
    have hle : 1 + δ x ≤ θ x := le_max_right _ _
    calc f' x ≤ (1 + δ x) * ((a * f x + h x) / x) := by
          simpa only [mul_div_assoc] using hx
      _ ≤ θ x * ((a * f x + h x) / x) := mul_le_mul_of_nonneg_right hle hnum
      _ = θ x * (a * f x + h x) / x := (mul_div_assoc _ _ _).symm
  intro ε hε
  let t : ℝ := Real.sqrt (1 + ε) - 1
  have hsqrt : 1 < Real.sqrt (1 + ε) := by
    have hsq0 : 0 ≤ Real.sqrt (1 + ε) := Real.sqrt_nonneg _
    by_contra! hn
    have hsle : Real.sqrt (1 + ε) ≤ 1 := hn
    have hsquare_le : (Real.sqrt (1 + ε)) ^ 2 ≤ 1 := by nlinarith
    have hsquare : (Real.sqrt (1 + ε)) ^ 2 = 1 + ε := Real.sq_sqrt (by linarith)
    linarith
  have ht : 0 < t := sub_pos.mpr hsqrt
  let c : ℝ := b - (b - a) / (1 + t)
  let q : ℝ := 1 / (b - c)
  have hgap : 0 < b - a := sub_pos.mpr hab
  have hgt0 : 0 < 1 + t := by linarith
  have hlt : (b - a) / (1 + t) < b - a := by
    apply (div_lt_iff₀ hgt0).2
    nlinarith [mul_pos hgap ht]
  have hca : a < c := by
    have hq0 : 0 < (b - a) / (1 + t) := div_pos hgap hgt0
    dsimp [c]
    linarith
  have hcb : c < b := by
    have hq0 : 0 < (b - a) / (1 + t) := div_pos hgap hgt0
    dsimp [c]
    linarith
  have hbcc : b - c = (b - a) / (1 + t) := by dsimp [c]; ring
  have hsmall : 0 < min (c / a - 1) 1 := by
    have hac' : 1 < c / a := (lt_div_iff₀ ha).2 (by simpa using hca)
    exact lt_min (sub_pos.mpr hac') one_pos
  obtain ⟨R, hR⟩ := Metric.tendsto_atTop.1 hθ0 (min (c / a - 1) 1) hsmall
  have hupper : ∀ x, R ≤ x → θ x ≤ min 2 (c / a) := by
    intro x hx
    have hd := hR x hx
    rw [Real.dist_eq] at hd
    have hd' := abs_lt.1 hd
    have hlt' : θ x < 1 + min (c / a - 1) 1 := by linarith [hd'.1, hd'.2]
    have hca' : 1 + min (c / a - 1) 1 ≤ c / a := by
      have h0 := min_le_left (c / a - 1) 1
      linarith
    have hcc' : 1 + min (c / a - 1) 1 ≤ 2 := by
      have h0 := min_le_right (c / a - 1) 1
      linarith
    exact le_min (le_trans hlt'.le hcc') (le_trans hlt'.le hca')
  let R₀ : ℝ := max r₀ (max D.threshold R)
  have hR₀r₀ : r₀ ≤ R₀ := le_max_left _ _
  have hR₀D : D.threshold ≤ R₀ := le_trans (le_max_left _ _) (le_max_right _ _)
  have hR₀R : R ≤ R₀ := le_trans (le_max_right _ _) (le_max_right _ _)
  have hR₀1 : 1 ≤ R₀ := le_trans D.one_le_threshold hR₀D
  have hR₀pos : 0 < R₀ := lt_of_lt_of_le one_pos hR₀1
  have hAC' : AbsolutelyContinuousOnTail f R₀ := by
    intro R' hR'
    refine AbsolutelyContinuousOnInterval.mono (hac R' (le_trans hR₀r₀ hR')) ?_
    rw [uIcc_of_le hR', uIcc_of_le (le_trans hR₀r₀ hR')]
    exact Icc_subset_Icc hR₀r₀ le_rfl
  have hAE' : AeHasDerivAtOnTail f f' R₀ :=
    ae_mono (Measure.restrict_mono (fun _ hx => le_trans hR₀r₀ hx) le_rfl) hae
  have hfbd' : AeDrivingBound f f' θ h a R₀ :=
    ae_mono (Measure.restrict_mono (fun _ hx => le_trans hR₀r₀ hx) le_rfl) hfbdθ
  have hηpos : 0 < t / (b - a) := div_pos ht hgap
  have hu := ae_eventually_ratio_le_of_driving_bound D ha hca hcb hR₀pos hR₀1 hR₀D
    hAC' hAE'
    (fun x hx => hfpos x (lt_of_lt_of_le hR₀pos hx))
    hθm (fun x hx => hθlower x (le_trans hR₀r₀ hx))
    (fun x hx => hupper x (le_trans hR₀R hx))
    hθ0
    (by
      refine ae_mono (Measure.restrict_mono (fun _ hx => le_trans hR₀r₀ hx) le_rfl) hfbdθ)
    (t / (b - a)) hηpos
  have hba : (1 + t) * (b - c) = b - a := by
    rw [hbcc]
    field_simp
  have hbudget : (b - a) * (q + t / (b - a)) = 1 + 2 * t := by
    have hbc0 : 0 < b - c := sub_pos.mpr hcb
    rw [← hba]
    dsimp [q]
    field_simp [hbc0.ne', hgt0.ne']
    ring
  filter_upwards [hu, eventually_gt_atTop (0 : ℝ)] with r hu hr
  have hfactor : 0 < (1 + t) * (b - c) := mul_pos hgt0 (sub_pos.mpr hcb)
  have hmul := mul_le_mul_of_nonneg_left hu hfactor.le
  have hgf : (b - a) * (f r / h r) ≤ 1 + 2 * t := by
    calc (b - a) * (f r / h r) = ((1 + t) * (b - c)) * (f r / h r) := by rw [← hba]
      _ ≤ ((1 + t) * (b - c)) * (q + t / (b - a)) := by simpa [q] using hmul
      _ = (b - a) * (q + t / (b - a)) := by rw [hba]
      _ = 1 + 2 * t := hbudget
  have hden : 0 < h r / (b - a) := div_pos (hpos r hr) hgap
  have hne : h r ≠ 0 := (hpos r hr).ne'
  have heq : f r = (h r / (b - a)) * ((b - a) * (f r / h r)) := by
    field_simp [hne, hgap.ne']
  have hineq1 : (h r / (b - a)) * ((b - a) * (f r / h r)) ≤
      (h r / (b - a)) * (1 + 2 * t) :=
    mul_le_mul_of_nonneg_left hgf hden.le
  have hineq2 : (h r / (b - a)) * (1 + 2 * t) ≤ (h r / (b - a)) * (1 + ε) := by
    have hle : 1 + 2 * t ≤ 1 + ε := by
      have hsquare : (1 + t) ^ 2 = 1 + ε := by
        have hts : 1 + t = Real.sqrt (1 + ε) := by dsimp [t]; ring
        rw [hts]
        exact Real.sq_sqrt (by linarith)
      nlinarith [sq_nonneg t]
    exact mul_le_mul_of_nonneg_left hle hden.le
  have hcomm : (h r / (b - a)) * (1 + ε) = (1 + ε) * (h r / (b - a)) := by ring
  exact (heq.le.trans (hineq1.trans hineq2)).trans_eq hcomm

/-- **The sharp a.e. one-sided ODE version of Lemma I.4.22** (`δ = 0`). -/
theorem ae_lemma_I_4_22_of_ae_sharp_bound {f f' : ℝ → ℝ} {h : ℝ → ℝ} {b : ℝ}
    (D : RVPosData h b) {a r₀ : ℝ} (ha : 0 < a) (hab : a < b) (hr₀ : 0 < r₀)
    (hpos : ∀ x, 0 < x → 0 < h x) (hfpos : ∀ x, 0 < x → 0 < f x)
    (hac : AbsolutelyContinuousOnTail f r₀) (hae : AeHasDerivAtOnTail f f' r₀)
    (hfbd : ∀ᵐ x ∂(volume.restrict (Set.Ici r₀)),
      f' x ≤ (a * f x + h x) / x) :
    ∀ ε > 0, ∀ᶠ r in atTop, f r ≤ (1 + ε) * (h r / (b - a)) := by
  refine ae_lemma_I_4_22_of_defect_bound D ha hab hr₀ hpos hfpos hac hae
    (δ := fun _ => 0) measurable_const tendsto_const_nhds ?_ ?_
  · intro x _
    simp
  · filter_upwards [hfbd] with x hx
    simpa using hx

end PercLib.CriticalLRP.Analysis.AE
