/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
# Proposition I.5.2 reduced to the gyration ODE (Lemma I.5.7) and the first moment

Source: T. Hutchcroft, *Critical long-range percolation I*:
Prop. I.5.2 (`prop:radius_of_gyration`), Lemma I.5.5 (`lem:ODE_with_possibly_negligible_driving_term`),
Lemma I.5.6 (`lem:ODE_with_critical_driving_term`), Lemma I.5.7 (`lem:gyration_derivative`),
Prop. I.4.2 (`prop:first_moment`, `E_{β_c,r}|K| ~ (α/β_c) r^α`).

This file assembles the *analytic reduction* half of Prop. I.5.2.  The two inputs
that belong to the percolation model, and are therefore kept as explicit
hypotheses (never as axioms), are:

* `GyrationAsymptotic`: the exact content of Lemma I.5.7,
  `F' r ~ (2α/r) F r + (α²/β_c) r^{α+1} Q`, with
  `F r = E_{β_c,r}[Σ_{x∈K}<x,u>²]`, `Q = ∫_B <y,u>² dy`, `c = α²/β_c`;
* `FirstMomentAsymptotic`: `E_{β_c,r}|K| ~ (α/β_c) r^α` (Prop. I.4.2).

Everything else is proved: the regular-variation index `max{2α,2+α}`, and the
three regime asymptotics of Prop. I.5.2 (α < 2, α = 2, α > 2), together with the
resulting `ξ₂²` asymptotics.  `GyrationODE.lean` complements this by solving the
*exact* ODE explicitly, which also identifies the α > 2 limit constant.

Note on constants: the TeX statement (p. 54) prints `ξ₂²(r) ~ A r^{2α}` in the
α > 2 case; with `E_{β_c,r}|K| ~ (α/β_c) r^α` that is inconsistent with the same
proposition's `ξ₂(r) ~ √A r^{α/2}`.  The book draft (`tom1.txt`, Lemma I.5.7
discussion) has the correct form `E_r[Σ] ~ A(u) r^α E_r|K|`; the statements below
follow the draft.
-/
module

public import PercLib.CriticalLRP.Analysis.Lemma_I_5_5
public import PercLib.CriticalLRP.Analysis.Lemma_I_5_6
public import PercLib.CriticalLRP.Analysis.GyrationODE

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

set_option autoImplicit true

@[expose] public section

open Filter Set MeasureTheory
open scoped Topology

namespace PercLib.CriticalLRP.Analysis.Gyration

/-! ### The driving term `h r = c Q r^{2+α}` of Lemma I.5.7 -/

/-- The driving term of Lemma I.5.7: `h r = c Q r^{2+α}`, where `c = α²/β_c` and
`Q = ∫_B <y,u>² dy`.  Note `h r / r = c Q r^{α+1}`, matching the lemma. -/
noncomputable def driver (α c Q : ℝ) : ℝ → ℝ := fun r => c * Q * r ^ (2 + α)

theorem measurable_driver {α c Q : ℝ} (hα : 0 ≤ 2 + α) : Measurable (driver α c Q) := by
  unfold driver
  exact measurable_const.mul (Real.continuous_rpow_const hα).measurable

theorem driver_pos {α c Q : ℝ} (hcQ : 0 < c * Q) : ∀ r : ℝ, 0 < r → 0 < driver α c Q r := by
  intro r hr
  exact mul_pos hcQ (Real.rpow_pos_of_pos hr _)

/-- `r ↦ A r^p` is regularly varying of index `p` when `A ≠ 0`. -/
theorem regularlyVarying_const_mul_rpow {A p : ℝ} (hA : A ≠ 0) :
    RegularlyVaryingAtTop (fun r : ℝ => A * r ^ p) p := by
  constructor
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
    exact mul_ne_zero hA (Real.rpow_pos_of_pos hr p).ne'
  · intro l hl
    have hconst : Tendsto (fun _ : ℝ => l ^ p) atTop (𝓝 (l ^ p)) := tendsto_const_nhds
    refine hconst.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
    have hsplit : (l * r) ^ p = l ^ p * r ^ p := Real.mul_rpow hl.le hr.le
    have hrp : (0:ℝ) < r ^ p := Real.rpow_pos_of_pos hr p
    rw [hsplit]
    field_simp

/-- The driving term is regularly varying of index `2 + α`. -/
theorem driver_rv {α c Q : ℝ} (hcQ : c * Q ≠ 0) :
    RegularlyVaryingAtTop (driver α c Q) (2 + α) :=
  regularlyVarying_const_mul_rpow hcQ

/-! ### The regular-variation conclusion of Prop. I.5.2 -/

/-- **Lemma I.5.7 ⟹ regular variation** (first sentence of Prop. I.5.2):
the moment `F` is regularly varying of index `max{2α, 2+α}`. -/
theorem regularlyVarying_of_gyration_asymptotic {F F' : ℝ → ℝ} {α c Q : ℝ}
    (hα : 0 < α) (hcQ : 0 < c * Q)
    (hfpos : ∀ x, 0 < x → 0 < F x)
    (hderiv : ∀ x, 0 < x → HasDerivAt F (F' x) x)
    (hasym : Tendsto (fun r => F' r / ((2 * α * F r + driver α c Q r) / r)) atTop (𝓝 1)) :
    RegularlyVaryingAtTop F (max (2 * α) (2 + α)) := by
  have hb : 0 < 2 + α := by linarith
  have hpos : ∀ r : ℝ, 0 < r → 0 < driver α c Q r := driver_pos hcQ
  have hD : RVPosData (driver α c Q) (2 + α) :=
    RVPosData.of hb (measurable_driver (by linarith)) (driver_rv hcQ.ne')
      (by filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx; exact hpos x hx)
  exact (lemma_I_5_5 (show (0:ℝ) < 2 * α by linarith) hb (measurable_driver (by linarith))
    (driver_rv hcQ.ne') hpos hfpos hderiv hasym).1

/-- Under Lemma I.5.7 with `α > 2`, the driving term is negligible: `h r / F r → 0`. -/
theorem tendsto_driver_div_of_two_lt {F F' : ℝ → ℝ} {α c Q : ℝ}
    (hα : 0 < α) (hα2 : 2 < α) (hcQ : 0 < c * Q)
    (hfpos : ∀ x, 0 < x → 0 < F x)
    (hderiv : ∀ x, 0 < x → HasDerivAt F (F' x) x)
    (hasym : Tendsto (fun r => F' r / ((2 * α * F r + driver α c Q r) / r)) atTop (𝓝 1)) :
    Tendsto (fun r => driver α c Q r / F r) atTop (𝓝 0) := by
  have hb : 0 < 2 + α := by linarith
  have hpos : ∀ r : ℝ, 0 < r → 0 < driver α c Q r := driver_pos hcQ
  have hle : 2 + α ≤ 2 * α := by linarith
  have hD : RVPosData (driver α c Q) (2 + α) :=
    RVPosData.of hb (measurable_driver (by linarith)) (driver_rv hcQ.ne')
      (by filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx; exact hpos x hx)
  exact (lemma_I_5_5 (show (0:ℝ) < 2 * α by linarith) hb (measurable_driver (by linarith))
    (driver_rv hcQ.ne') hpos hfpos hderiv hasym).2 hle |>.1

/-! ### Prop. I.5.2, item 1: `α < 2` -/

/-- **Prop. I.5.2(1)**, ratio form: `F r / h r → 1/(2-α)` where `h r = c Q r^{2+α}`
(this is the conclusion of Lemma I.4.21 in the case `a < b`). -/
theorem tendsto_div_driver_of_lt {F F' : ℝ → ℝ} {α c Q : ℝ}
    (hα : 0 < α) (hα2 : α < 2) (hcQ : 0 < c * Q)
    (hfpos : ∀ x, 0 < x → 0 < F x)
    (hderiv : ∀ x, 0 < x → HasDerivAt F (F' x) x)
    (hasym : Tendsto (fun r => F' r / ((2 * α * F r + driver α c Q r) / r)) atTop (𝓝 1)) :
    Tendsto (fun r => F r / driver α c Q r) atTop (𝓝 (1 / (2 - α))) := by
  have hb : 0 < 2 + α := by linarith
  have hab : 2 * α < 2 + α := by linarith
  have hpos : ∀ r : ℝ, 0 < r → 0 < driver α c Q r := driver_pos hcQ
  have hD : RVPosData (driver α c Q) (2 + α) :=
    RVPosData.of hb (measurable_driver (by linarith)) (driver_rv hcQ.ne')
      (by filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx; exact hpos x hx)
  have hlim := lemma_I_4_21_tendsto_of_hasDerivAt hD (by linarith : 0 < 2 * α) hab
    hpos hfpos hderiv hasym
  -- `F r / (h r / (2 + α - 2α)) → 1`, so `F r / h r → 1/(2-α)`
  have hne : (2 : ℝ) + α - 2 * α ≠ 0 := by linarith
  have hmul := hlim.const_mul (1 / (2 + α - 2 * α))
  simp only [mul_one] at hmul
  have key : Tendsto (fun r => F r / driver α c Q r) atTop (𝓝 (1 / (2 + α - 2 * α))) := by
    refine hmul.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
    have hh : driver α c Q r ≠ 0 := (hpos r hr).ne'
    field_simp
  have hspan : (2 : ℝ) + α - 2 * α = 2 - α := by ring
  rwa [hspan] at key

/-- **Prop. I.5.2(1)**, as printed: for `α < 2`,
`F r / r^{2+α} → c Q/(2-α)`. -/
theorem tendsto_div_rpow_of_asymptotic_lt {F F' : ℝ → ℝ} {α c Q : ℝ}
    (hα : 0 < α) (hα2 : α < 2) (hcQ : 0 < c * Q)
    (hfpos : ∀ x, 0 < x → 0 < F x)
    (hderiv : ∀ x, 0 < x → HasDerivAt F (F' x) x)
    (hasym : Tendsto (fun r => F' r / ((2 * α * F r + driver α c Q r) / r)) atTop (𝓝 1)) :
    Tendsto (fun r => F r / r ^ (2 + α)) atTop (𝓝 (c * Q / (2 - α))) := by
  have hlim := tendsto_div_driver_of_lt hα hα2 hcQ hfpos hderiv hasym
  have hmul := hlim.mul_const (c * Q)
  have hlim2 : Tendsto (fun r => F r / driver α c Q r * (c * Q)) atTop (𝓝 (c * Q / (2 - α))) := by
    have hval : 1 / (2 - α) * (c * Q) = c * Q / (2 - α) := by ring
    rwa [hval] at hmul
  refine hlim2.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  have hrp : (0:ℝ) < r ^ (2 + α) := Real.rpow_pos_of_pos hr _
  have hcQne : c * Q ≠ 0 := hcQ.ne'
  unfold driver
  field_simp
  rw [show F r * c * Q = F r * (c * Q) by ring, mul_div_cancel_right₀ _ hcQne]


/-! ### Prop. I.5.2, item 2: the critical case `α = 2` (Lemma I.5.6) -/

/-- **Prop. I.5.2(2)**: in the critical case `α = 2`, if Lemma I.5.7 holds in the
`log`-integrable-error form `F' = (1-δ) 4 F/r + c Q r^3` with `δ` a log-error
function, then `F r / (r^4 log r) → c Q`. -/
theorem tendsto_div_rpow_log_of_asymptotic {F F' δ : ℝ → ℝ} {c Q : ℝ}
    (hcQ : 0 < c * Q)
    (hfpos : ∀ x, 0 < x → 0 < F x)
    (hderiv : ∀ x, 0 < x → HasDerivAt F (F' x) x)
    (hδ : IsLogErrorFunction δ)
    (hode : ∀ x, 0 < x → F' x = (1 - δ x) * 4 * F x / x + (c * Q * x ^ (4 : ℝ)) / x) :
    Tendsto (fun r => F r / (r ^ (4 : ℝ) * Real.log r)) atTop (𝓝 (c * Q)) := by
  have hhmeas : Measurable (fun r : ℝ => c * Q * r ^ (4 : ℝ)) :=
    measurable_const.mul (Real.continuous_rpow_const (by norm_num)).measurable
  have hhrv : RegularlyVaryingAtTop (fun r : ℝ => c * Q * r ^ (4 : ℝ)) 4 :=
    regularlyVarying_const_mul_rpow hcQ.ne'
  have hpos : ∀ᶠ x in atTop, 0 < c * Q * x ^ (4 : ℝ) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    exact mul_pos hcQ (Real.rpow_pos_of_pos hx _)
  have hhA : Tendsto (fun r : ℝ => (c * Q * r ^ (4 : ℝ)) / ((c * Q) * r ^ (4 : ℝ)))
      atTop (𝓝 1) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
    have hrp : (0:ℝ) < r ^ (4 : ℝ) := Real.rpow_pos_of_pos hr _
    rw [show c * Q * r ^ (4:ℝ) = (c * Q) * r ^ (4:ℝ) by ring,
      div_self (mul_pos hcQ hrp).ne']
  have hmain := lemma_I_5_6_log_of_tendsto (a := (4 : ℝ)) (A := c * Q)
    (h := fun r : ℝ => c * Q * r ^ (4 : ℝ)) (by norm_num) hcQ hhmeas hhrv hpos hfpos
    hderiv hδ hode hhA
  have hmul := hmain.mul_const (c * Q)
  simp only [one_mul] at hmul
  refine hmul.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with r hr
  have hr0 : 0 < r := by linarith
  have hlog : Real.log r ≠ 0 := ne_of_gt (Real.log_pos hr)
  have hrp : (0:ℝ) < r ^ (4 : ℝ) := Real.rpow_pos_of_pos hr0 _
  field_simp
  rw [show F r * c * Q = F r * (c * Q) by ring, mul_div_cancel_right₀ _ hcQ.ne']

/-! ### Division of two asymptotic power laws -/

/-- If `F/r^p → a` and `G/r^q → b ≠ 0` then `F/(r^{p-q} G) → a/b`. -/
theorem tendsto_div_rpow_of_div {F G : ℝ → ℝ} {p q a b : ℝ}
    (hF : Tendsto (fun r => F r / r ^ p) atTop (𝓝 a))
    (hG : Tendsto (fun r => G r / r ^ q) atTop (𝓝 b)) (hb : b ≠ 0) :
    Tendsto (fun r => F r / (r ^ (p - q) * G r)) atTop (𝓝 (a / b)) := by
  have hdiv := hF.div hG hb
  refine hdiv.congr' ?_
  have hnev : ∀ᶠ r : ℝ in atTop, G r ≠ 0 := by
    have h1 : ∀ᶠ r : ℝ in atTop, G r / r ^ q ≠ 0 :=
      hG.eventually (eventually_ne_nhds hb)
    filter_upwards [h1, eventually_gt_atTop (0 : ℝ)] with r hr hr0 hG0
    rw [hG0, zero_div] at hr
    exact hr rfl
  filter_upwards [hnev, eventually_gt_atTop (0 : ℝ)] with r hG0 hr0
  change F r / r ^ p / (G r / r ^ q) = F r / (r ^ (p - q) * G r)
  have h1 : r ^ p = r ^ (p - q) * r ^ q := by
    rw [← Real.rpow_add hr0]
    congr 1
    ring
  have hq : (0:ℝ) < r ^ q := Real.rpow_pos_of_pos hr0 q
  have hpq : (0:ℝ) < r ^ (p - q) := Real.rpow_pos_of_pos hr0 (p - q)
  rw [h1]
  field_simp

/-- **Prop. I.5.2(1) for the radius of gyration**: with `F r = E_r[Σ<x,u>²]`,
`G r = E_r|K|`, `c = α²/β_c` and the first-moment asymptotic `G r ~ (α/β_c) r^α`,
the `α < 2` asymptotic reads `F r / (r² G r) → (α/(2-α)) Q`, i.e.
`F r ~ (α/(2-α)) Q r² G r`. -/
theorem tendsto_xi2sq_of_lt {F G : ℝ → ℝ} {α β Q : ℝ}
    (hβ : 0 < β) (hα : α < 2) (hQ : 0 < Q) (hαpos : 0 < α)
    (hF : Tendsto (fun r => F r / r ^ (2 + α)) atTop (𝓝 (α ^ 2 / β * Q / (2 - α))))
    (hG : Tendsto (fun r => G r / r ^ α) atTop (𝓝 (α / β))) :
    Tendsto (fun r => F r / (r ^ (2:ℝ) * G r)) atTop (𝓝 (α / (2 - α) * Q)) := by
  have hb : α / β ≠ 0 := div_ne_zero hαpos.ne' hβ.ne'
  have h := tendsto_div_rpow_of_div (p := 2 + α) (q := α) hF hG hb
  have hpq : 2 + α - α = (2:ℝ) := by ring
  rw [hpq] at h
  have hval : α ^ 2 / β * Q / (2 - α) / (α / β) = α / (2 - α) * Q := by
    field_simp
  rwa [hval] at h

/-- **Prop. I.5.2(2) for the radius of gyration**: at `α = 2` with `c = 4/β_c`,
`F r ~ c Q r^4 log r` and `G r ~ (2/β_c) r^2` give
`F r / (r² log r · G r) → 2 Q = α Q`. -/
theorem tendsto_xi2sq_of_two {F G : ℝ → ℝ} {β Q : ℝ}
    (hβ : 0 < β) (hQ : 0 < Q)
    (hF : Tendsto (fun r => F r / (r ^ (4 : ℝ) * Real.log r)) atTop (𝓝 (4 / β * Q)))
    (hG : Tendsto (fun r => G r / r ^ (2 : ℝ)) atTop (𝓝 (2 / β))) :
    Tendsto (fun r => F r / (r ^ (2 : ℝ) * Real.log r * G r)) atTop (𝓝 (2 * Q)) := by
  have hb : (2 : ℝ) / β ≠ 0 := div_ne_zero (by norm_num) hβ.ne'
  have h := hF.div hG hb
  have hval : 4 / β * Q / (2 / β) = 2 * Q := by
    field_simp
    norm_num
  rw [hval] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with r hr
  change F r / (r ^ (4 : ℝ) * Real.log r) / (G r / r ^ (2 : ℝ)) =
    F r / (r ^ (2 : ℝ) * Real.log r * G r)
  have hr0 : 0 < r := by linarith
  have hlog : Real.log r ≠ 0 := ne_of_gt (Real.log_pos hr)
  have hrp : (0:ℝ) < r ^ (2 : ℝ) := Real.rpow_pos_of_pos hr0 _
  have h4 : r ^ (4:ℝ) = r ^ (2:ℝ) * r ^ (2:ℝ) := by
    rw [← Real.rpow_add hr0]
    norm_num
  rw [h4]
  field_simp

/-! ### Positivity in the `α > 2` regime -/

/-- For `α > 2` and the exact gyration ODE, the limit `A = lim F r / r^{2α}` is
`A = F 1 + c Q/(α-2)`, and it is non-negative as soon as `F ≥ 0` (which holds in
the model since `F r = E_r[Σ<x,u>²] ≥ 0`).  This is the analytic part of the
positivity of the limiting constant `A(u)` in Prop. I.5.2(3). -/
theorem nonneg_limit_of_gt {F : ℝ → ℝ} {α c Q : ℝ} (hα : 2 < α) (hcQ : 0 < c * Q)
    (hF : ∀ r : ℝ, 0 < r → HasDerivAt F ((2 * α / r) * F r + c * r ^ (α + 1) * Q) r)
    (hnonneg : ∀ r : ℝ, 0 < r → 0 ≤ F r) :
    0 ≤ F 1 + c * Q / (α - 2) := by
  have hlim := tendsto_div_rpow_of_gt hα hF
  refine le_of_tendsto_of_tendsto tendsto_const_nhds hlim ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  exact div_nonneg (hnonneg r hr) (Real.rpow_pos_of_pos hr _).le

/-- **Prop. I.5.2(3) for the radius of gyration**: if `F r / r^{2α} → A` and the
first-moment asymptotic `G r / r^α → α/β_c` hold, then
`F r / (r^α G r) → A β_c/α`, i.e. `F r ~ (A β_c/α) r^α G r`.  With
`ξ₂² = F/G` this says `ξ₂²(r) ≍ r^α`, so `ξ₂` is regularly varying of index `α/2`. -/
theorem tendsto_xi2sq_of_gt {F G : ℝ → ℝ} {α β A : ℝ}
    (hβ : 0 < β) (hαpos : 0 < α)
    (hF : Tendsto (fun r => F r / r ^ (2 * α)) atTop (𝓝 A))
    (hG : Tendsto (fun r => G r / r ^ α) atTop (𝓝 (α / β))) :
    Tendsto (fun r => F r / (r ^ α * G r)) atTop (𝓝 (A * β / α)) := by
  have hb : α / β ≠ 0 := div_ne_zero hαpos.ne' hβ.ne'
  have h := tendsto_div_rpow_of_div (p := 2 * α) (q := α) hF hG hb
  have hpq : 2 * α - α = α := by ring
  rw [hpq] at h
  have hval : A / (α / β) = A * β / α := by
    field_simp
  rwa [hval] at h

/-- In the exact `α > 2` gyration ODE, nonnegativity forces the limiting
coefficient to be strictly positive. If it vanished, the exact solution would
be `-(cQ/(α-2)) r^(2+α)`, which is negative at every positive radius. -/
theorem pos_limit_of_gt {F : ℝ → ℝ} {α c Q : ℝ} (hα : 2 < α) (hcQ : 0 < c * Q)
    (hF : ∀ r : ℝ, 0 < r → HasDerivAt F ((2 * α / r) * F r + c * r ^ (α + 1) * Q) r)
    (hnonneg : ∀ r : ℝ, 0 < r → 0 ≤ F r) :
    0 < F 1 + c * Q / (α - 2) := by
  have hnn := nonneg_limit_of_gt hα hcQ hF hnonneg
  rcases eq_or_lt_of_le hnn with hzero | hpos
  · exfalso
    have hden : 0 < α - 2 := by linarith
    have hM : 0 < c * Q / (α - 2) := div_pos hcQ hden
    have hF1 : F 1 = -(c * Q / (α - 2)) := by linarith
    have hsign : c * Q / (2 - α) = -(c * Q / (α - 2)) := by
      have hden' : α - 2 ≠ 0 := hden.ne'
      have hother : (2 : ℝ) - α ≠ 0 := by linarith
      field_simp
      ring
    have hex := gyration_exact (ne_of_gt hα) hF (2 : ℝ) (by norm_num)
    rw [hF1] at hex
    have hpow : 0 < (2 : ℝ) ^ (2 + α) := Real.rpow_pos_of_pos (by norm_num) _
    have hneg : F (2 : ℝ) < 0 := by
      rw [hex]
      have heq : (2 : ℝ) ^ (2 * α) * (-(c * Q / (α - 2))) +
          (c * Q / (2 - α)) * ((2 : ℝ) ^ (2 + α) - (2 : ℝ) ^ (2 * α)) =
          -(c * Q / (α - 2)) * (2 : ℝ) ^ (2 + α) := by
        rw [hsign]
        ring
      rw [heq]
      nlinarith [mul_pos hM hpow]
    exact (not_lt_of_ge (hnonneg 2 (by norm_num))) hneg
  · exact hpos

/-! ### The case `u = 0` -/

/-- **The `u = 0` caveat.**  When `u = 0` the moment `F r = E_r[Σ<x,u>²]` vanishes
identically, and the identically zero function is *not* regularly varying: the
definition requires eventual non-vanishing.  Hence the regular-variation claim of
Prop. I.5.2 must be read for `u ≠ 0` (for which `Q(u) = ∫_B <y,u>² dy > 0`). -/
theorem not_regularlyVarying_zero (α : ℝ) :
    ¬ RegularlyVaryingAtTop (fun _ : ℝ => (0 : ℝ)) (max (2 * α) (2 + α)) := by
  intro hrv
  obtain ⟨x, hx⟩ := hrv.1.exists
  exact hx rfl

/-! ### Positive semidefiniteness of the limiting bilinear form -/

/-- **The limiting bilinear form is positive semidefinite** (end of the proof of
Prop. I.5.2): the pointwise limit of positive semidefinite bilinear forms is
positive semidefinite.  In the application `B_r` is the covariance form
`⟨u, Σ_r v⟩ = ξ₂(r)^{-2} Ê_r[⟨X,u⟩⟨X,v⟩]`, which is positive semidefinite because
it is a covariance, and `B_r → B` pointwise is the content of items (1)-(3). -/
theorem isPosSemidef_of_tendsto {E : Type*} [AddCommGroup E] [Module ℝ E]
    {B : ℝ → LinearMap.BilinForm ℝ E} {Blim : LinearMap.BilinForm ℝ E}
    (hconv : ∀ u v : E, Tendsto (fun r => B r u v) atTop (𝓝 (Blim u v)))
    (hpsd : ∀ r, (B r).IsPosSemidef) : Blim.IsPosSemidef := by
  refine ⟨⟨?_⟩, ⟨fun u => ?_⟩⟩
  · intro u v
    have h1 := hconv u v
    have h2 := hconv v u
    have h3 : (fun r => B r u v) = (fun r => B r v u) := by
      funext r
      exact (hpsd r).isSymm.eq u v
    rw [h3] at h1
    exact tendsto_nhds_unique h1 h2
  · exact le_of_tendsto_of_tendsto tendsto_const_nhds (hconv u u)
      (Eventually.of_forall fun r => (hpsd r).isNonneg.nonneg u)

end PercLib.CriticalLRP.Analysis.Gyration

#print axioms PercLib.CriticalLRP.Analysis.Gyration.nonneg_limit_of_gt
#print axioms PercLib.CriticalLRP.Analysis.Gyration.pos_limit_of_gt
#print axioms PercLib.CriticalLRP.Analysis.Gyration.tendsto_xi2sq_of_gt
#print axioms PercLib.CriticalLRP.Analysis.Gyration.not_regularlyVarying_zero
#print axioms PercLib.CriticalLRP.Analysis.Gyration.isPosSemidef_of_tendsto

#print axioms PercLib.CriticalLRP.Analysis.Gyration.gyration_ratio_form
#print axioms PercLib.CriticalLRP.Analysis.Gyration.gyration_exact
#print axioms PercLib.CriticalLRP.Analysis.Gyration.tendsto_div_rpow_of_lt
#print axioms PercLib.CriticalLRP.Analysis.Gyration.tendsto_div_rpow_of_gt
#print axioms PercLib.CriticalLRP.Analysis.Gyration.tendsto_div_rpow_log
#print axioms PercLib.CriticalLRP.Analysis.Gyration.regularlyVarying_const_mul_rpow
#print axioms PercLib.CriticalLRP.Analysis.Gyration.regularlyVarying_of_gyration_asymptotic
#print axioms PercLib.CriticalLRP.Analysis.Gyration.tendsto_driver_div_of_two_lt
#print axioms PercLib.CriticalLRP.Analysis.Gyration.tendsto_div_driver_of_lt
#print axioms PercLib.CriticalLRP.Analysis.Gyration.tendsto_div_rpow_of_asymptotic_lt
#print axioms PercLib.CriticalLRP.Analysis.Gyration.tendsto_div_rpow_log_of_asymptotic
#print axioms PercLib.CriticalLRP.Analysis.Gyration.tendsto_div_rpow_of_div
#print axioms PercLib.CriticalLRP.Analysis.Gyration.tendsto_xi2sq_of_lt
#print axioms PercLib.CriticalLRP.Analysis.Gyration.tendsto_xi2sq_of_two
