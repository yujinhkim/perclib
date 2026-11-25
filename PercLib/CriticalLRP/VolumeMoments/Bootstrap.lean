/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
Hutchcroft, *Critical long-range percolation I: High effective dimension*,
arXiv:2508.18807v1, Lemma I.4.9 (pp. 37–38): the bootstrapping argument for the
first moment when `d > 3α`.

The paper's proof has three ingredients:
* the exact ODE identity `∂_r E_{β,r}|K| = (1 - Ē_{1,r,β}) β r^{-α-1} (E_{β,r}|K|)²`;
* the tree-graph bound on the error,
  `Ē_{1,r,β} ≤ C r^{3α-d} (E_{β,r}|K| / ((α/β) r^α))³`;
* monotonicity of `r ↦ E_{β,r}|K|` and the a priori bound
  `E_{β,r}|K| ≤ (2α/β) r^α` for `r ≥ r₀(β)` (sharpness of the phase transition),
  with `r₀(β)` *minimal* with that property.

Given those, the paper concludes `r₀(β) ≤ (32C)^{1/(d-3α)}` by putting
`r = (32C)^{1/d} max{r,r₀}^{3α/d}`, showing the error is `≤ 1/4` on `[r,∞)`, so
that Lemma I.4.5(1) gives `E_{β,r}|K| ≤ (4α/3β) r^α ≤ (2α/β) r^α` beyond `r`;
by minimality of `r₀` this forces `r₀ ≤ r`, which yields the bound.

`bootstrap_high_dim` below isolates exactly this analytic content.  Two
deliberate deviations from the paper's wording:

* `error_bound_eight` uses only `|e s| ≤ 8C (max s r₀)^{3α} s^{-d}`, obtained
  from the a priori bound and monotonicity; no continuity of `e` is needed
  because we use the continuity-free form of Lemma I.4.5(1) (`ODENocont`).
* the conclusion is `r₀ ≤ max 1 ((32C)^{1/(d-3α)})`.  The paper omits the
  `max 1`; as stated its conclusion is false when `32C < 1` (then
  `(32C)^{1/(d-3α)} < 1 ≤ r₀`), so `max 1` is the honest unconditional form.
  It implies the paper's statement whenever `32C ≥ 1`, which is the only case
  in which the paper's conclusion is not vacuous.
-/
module

public import PercLib.CriticalLRP.VolumeMoments.ODENocont

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

set_option autoImplicit true

noncomputable section

@[expose] public section

open Filter Set
open scoped Topology

namespace PercLib.CriticalLRP.VolumeMoments

/-- `(x^a)^3 = x^(3a)` for `x ≥ 0`. -/
lemma rpow_cube {x : ℝ} (hx : 0 ≤ x) (a : ℝ) : (x ^ a) ^ 3 = x ^ (3 * a) := by
  rw [← Real.rpow_natCast (x ^ a) 3, ← Real.rpow_mul hx]
  congr 1
  push_cast
  ring

/-- **The error bound of Lemma I.4.9, step 1.**  Under the a priori bound
`F s ≤ (2α/β) (max s r₀)^α`, the multiplicative error of the paper's equation
satisfies `|e s| ≤ 8C (max s r₀)^{3α} s^{-d}`. -/
theorem error_bound_eight
    {α β d C : ℝ} (hα : 0 < α) (hβ : 0 < β) (hC : 0 < C)
    {F e : ℝ → ℝ}
    (hFpos : ∀ r, 1 ≤ r → 0 < F r)
    (hmono : ∀ r s, 1 ≤ r → r ≤ s → F r ≤ F s)
    (herr : ∀ r, 1 ≤ r → |e r| ≤ C * r ^ (-(d - 3 * α)) * (F r / (α / β * r ^ α)) ^ 3)
    {r₀ : ℝ} (hr₀ : 1 ≤ r₀) (hbdd : ∀ r, r₀ ≤ r → F r ≤ 2 * α / β * r ^ α) :
    ∀ s, 1 ≤ s → |e s| ≤ 8 * C * ((max s r₀) ^ (3 * α)) * s ^ (-d) := by
  intro s hs
  have hs0 : 0 < s := lt_of_lt_of_le zero_lt_one hs
  have hmaxpos : 0 < max s r₀ := lt_of_lt_of_le hs0 (le_max_left s r₀)
  have hmaxnonneg : 0 ≤ max s r₀ := le_of_lt hmaxpos
  have hFmax : F s ≤ (2 * α / β) * ((max s r₀) ^ α) := by
    rcases le_total r₀ s with h | h
    · rw [max_eq_left h]; exact hbdd s h
    · have h1 : F s ≤ F r₀ := hmono s r₀ hs h
      have h2 : F r₀ ≤ 2 * α / β * r₀ ^ α := hbdd r₀ le_rfl
      rw [max_eq_right h]
      linarith
  have hcube : (F s / (α / β * s ^ α)) ^ 3 ≤ 8 * (((max s r₀) / s) ^ (3 * α)) := by
    have hspos : 0 < s ^ α := Real.rpow_pos_of_pos hs0 α
    have hratio : F s / (α / β * s ^ α) ≤ 2 * (((max s r₀) / s) ^ α) := by
      rw [div_le_iff₀ (by positivity)]
      calc F s ≤ (2 * α / β) * ((max s r₀) ^ α) := hFmax
        _ = 2 * (((max s r₀) / s) ^ α) * (α / β * s ^ α) := by
            rw [Real.div_rpow hmaxnonneg hs0.le]
            field_simp
    have hnonneg : 0 ≤ F s / (α / β * s ^ α) :=
      le_of_lt (div_pos (hFpos s hs) (by positivity))
    calc (F s / (α / β * s ^ α)) ^ 3
        ≤ (2 * (((max s r₀) / s) ^ α)) ^ 3 := pow_le_pow_left₀ hnonneg hratio 3
      _ = 8 * (((max s r₀) / s) ^ (3 * α)) := by
          rw [mul_pow, rpow_cube (by positivity)]
          norm_num
  calc |e s| ≤ C * s ^ (-(d - 3 * α)) * (F s / (α / β * s ^ α)) ^ 3 := herr s hs
    _ ≤ C * s ^ (-(d - 3 * α)) * (8 * (((max s r₀) / s) ^ (3 * α))) := by
        apply mul_le_mul_of_nonneg_left hcube (by positivity)
    _ = 8 * C * ((max s r₀) ^ (3 * α)) * s ^ (-d) := by
        have hd1 : ((max s r₀) / s) ^ (3 * α)
            = ((max s r₀) ^ (3 * α)) * (s ^ (3 * α))⁻¹ := by
          rw [Real.div_rpow hmaxnonneg hs0.le, div_eq_mul_inv]
        have hkey : s ^ (-(d - 3 * α)) * (s ^ (3 * α))⁻¹ = s ^ (-d) := by
          rw [← Real.rpow_neg hs0.le, ← Real.rpow_add hs0]
          congr 1
          ring
        rw [hd1]
        calc C * s ^ (-(d - 3 * α)) * (8 * (((max s r₀) ^ (3 * α)) * (s ^ (3 * α))⁻¹))
            = 8 * C * ((max s r₀) ^ (3 * α))
                * (s ^ (-(d - 3 * α)) * (s ^ (3 * α))⁻¹) := by ring
          _ = 8 * C * ((max s r₀) ^ (3 * α)) * s ^ (-d) := by rw [hkey]

/-- **The bootstrapping engine of Lemma I.4.9.** -/
theorem bootstrap_high_dim
    {α β d C : ℝ} (hα : 0 < α) (hβ : 0 < β) (hC : 0 < C) (hγ : 0 < d - 3 * α)
    {F F' e : ℝ → ℝ}
    (hderiv : ∀ r, 1 ≤ r → HasDerivAt F (F' r) r)
    (hODE : ∀ r, 1 ≤ r → F' r = (1 - e r) * β * r ^ (-α - 1) * (F r) ^ 2)
    (hpos : ∀ r, 1 ≤ r → 0 < F r)
    (hmono : ∀ r s, 1 ≤ r → r ≤ s → F r ≤ F s)
    (herr : ∀ r, 1 ≤ r → |e r| ≤ C * r ^ (-(d - 3 * α)) * (F r / (α / β * r ^ α)) ^ 3)
    {r₀ : ℝ} (hr₀ : 1 ≤ r₀) (hbdd : ∀ r, r₀ ≤ r → F r ≤ 2 * α / β * r ^ α)
    (hmin : ∀ b, 1 ≤ b → (∀ r, b ≤ r → F r ≤ 2 * α / β * r ^ α) → r₀ ≤ b) :
    r₀ ≤ max 1 ((32 * C) ^ (1 / (d - 3 * α))) := by
  set g := d - 3 * α with hg
  have hgpos : 0 < g := by rw [hg]; exact hγ
  set P := 32 * C with hP
  have hPpos : 0 < P := by positivity
  have hP32 : P / 32 = C := by rw [hP]; ring
  have hdpos : 0 < d := by rw [hg] at hγ; linarith
  have hg3 : g + 3 * α = d := by rw [hg]; ring
  have hr₀0 : 0 < r₀ := lt_of_lt_of_le zero_lt_one hr₀
  by_contra hcon
  rw [not_le] at hcon
  have hfloor : P ^ (1 / g) < r₀ := lt_of_le_of_lt (le_max_right _ _) hcon
  have h1lt : (1 : ℝ) < r₀ := lt_of_le_of_lt (le_max_left _ _) hcon
  set r := max 1 (P ^ (1 / d) * r₀ ^ (3 * α / d)) with hr
  have hr1 : 1 ≤ r := le_max_left _ _
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr1
  have hprodpos : 0 < P ^ (1 / d) * r₀ ^ (3 * α / d) := by positivity
  have hrprod : P ^ (1 / d) * r₀ ^ (3 * α / d) ≤ r := le_max_right _ _
  have hrlt : r < r₀ := by
    have hPg : P ≤ r₀ ^ g := by
      have h2 : (P ^ (1 / g)) ^ g ≤ r₀ ^ g :=
        Real.rpow_le_rpow (by positivity) (le_of_lt hfloor) hgpos.le
      have h3 : (P ^ (1 / g)) ^ g = P := by
        rw [← Real.rpow_mul hPpos.le, one_div, inv_mul_cancel₀ (ne_of_gt hgpos), Real.rpow_one]
      rwa [h3] at h2
    have h8 : P < r₀ ^ g := by
      have h9 : (P ^ (1 / g)) ^ g < r₀ ^ g :=
        Real.rpow_lt_rpow (by positivity) hfloor hgpos
      have h10 : (P ^ (1 / g)) ^ g = P := by
        rw [← Real.rpow_mul hPpos.le, one_div, inv_mul_cancel₀ (ne_of_gt hgpos), Real.rpow_one]
      rwa [h10] at h9
    have h1 : P ^ (1 / d) < r₀ ^ (g / d) := by
      have h11 : P ^ (1 / d) < (r₀ ^ g) ^ (1 / d) :=
        Real.rpow_lt_rpow (le_of_lt hPpos) h8 (by positivity)
      have h6 : (r₀ ^ g) ^ (1 / d) = r₀ ^ (g / d) := by
        rw [← Real.rpow_mul hr₀0.le, mul_one_div]
      rwa [h6] at h11
    have h5 : P ^ (1 / d) * r₀ ^ (3 * α / d) < r₀ := by
      have h6 : r₀ ^ (3 * α / d) * r₀ ^ (g / d) = r₀ := by
        rw [← Real.rpow_add hr₀0]
        rw [show 3 * α / d + g / d = 1 by rw [hg]; field_simp; ring]
        exact Real.rpow_one r₀
      have hp1 : 0 < r₀ ^ (3 * α / d) := Real.rpow_pos_of_pos hr₀0 _
      nlinarith [h1, hp1, hr₀0, h6]
    rw [hr, max_lt_iff]
    exact ⟨h1lt, h5⟩
  -- the two scale inequalities, proved once
  have hPg : P ≤ r₀ ^ g := by
    have h2 : (P ^ (1 / g)) ^ g ≤ r₀ ^ g :=
      Real.rpow_le_rpow (by positivity) (le_of_lt hfloor) hgpos.le
    have h3 : (P ^ (1 / g)) ^ g = P := by
      rw [← Real.rpow_mul hPpos.le, one_div, inv_mul_cancel₀ (ne_of_gt hgpos), Real.rpow_one]
    rwa [h3] at h2
  have hrd : P * r₀ ^ (3 * α) ≤ r ^ d := by
    have h1 : (P ^ (1 / d) * r₀ ^ (3 * α / d)) ^ d ≤ r ^ d :=
      Real.rpow_le_rpow hprodpos.le hrprod hdpos.le
    have h2 : (P ^ (1 / d) * r₀ ^ (3 * α / d)) ^ d = P * r₀ ^ (3 * α) := by
      rw [Real.mul_rpow (by positivity) (by positivity),
        ← Real.rpow_mul hPpos.le, ← Real.rpow_mul hr₀0.le]
      have e1 : (1 / d) * d = 1 := by field_simp
      have e2 : (3 * α / d) * d = 3 * α := by field_simp
      rw [e1, e2, Real.rpow_one]
    linarith
  have hrP : P ^ (1 / g) ≤ r := by
    have h1 : P ^ (3 * α / g) ≤ r₀ ^ (3 * α) := by
      have h2 : (P ^ (1 / g)) ^ (3 * α) ≤ r₀ ^ (3 * α) :=
        Real.rpow_le_rpow (by positivity) (le_of_lt hfloor) (by positivity)
      rwa [← Real.rpow_mul hPpos.le, show (1 / g) * (3 * α) = 3 * α / g by field_simp] at h2
    have h3 : (P ^ (1 / g)) ^ d = P * P ^ (3 * α / g) := by
      rw [← Real.rpow_mul hPpos.le]
      have e1 : (1 / g) * d = 1 + 3 * α / g := by
        field_simp
        rw [hg]; ring
      rw [e1, Real.rpow_add hPpos, Real.rpow_one]
    have h4 : P * P ^ (3 * α / g) ≤ P * r₀ ^ (3 * α) := by
      have := h1
      nlinarith [hPpos, Real.rpow_pos_of_pos hPpos (3 * α / g)]
    have h5 : (P ^ (1 / g)) ^ d ≤ r ^ d := by rw [h3]; linarith
    exact (Real.rpow_le_rpow_iff (by positivity) (le_of_lt hr0) hdpos).mp h5
  have herr14 : ∀ s, r ≤ s → |e s| ≤ 1 / 4 := by
    intro s hrs
    have hs1 : 1 ≤ s := le_trans hr1 hrs
    have hs0 : 0 < s := lt_of_lt_of_le zero_lt_one hs1
    have h8 := error_bound_eight hα hβ hC hpos hmono herr hr₀ hbdd s hs1
    rcases le_total r₀ s with h | h
    · -- `s ≥ r₀`: `|e s| ≤ 8C s^{-g} ≤ 8C r^{-g} ≤ 8C P^{-1} = 1/4`
      have hmax : max s r₀ = s := max_eq_left h
      rw [hmax] at h8
      have h8' : 8 * C * s ^ (3 * α) * s ^ (-d) = 8 * C * s ^ (-g) := by
        have hexp : s ^ (3 * α) * s ^ (-d) = s ^ (-g) := by
          rw [← Real.rpow_add hs0]
          congr 1
          rw [hg]; ring
        rw [mul_assoc, hexp]
      rw [h8'] at h8
      have hrg : r ^ (-g) ≤ P⁻¹ := by
        have h1 : r ^ (-g) ≤ (P ^ (1 / g)) ^ (-g) :=
          Real.rpow_le_rpow_of_nonpos (by positivity) hrP (by linarith : -g ≤ 0)
        have h2 : (P ^ (1 / g)) ^ (-g) = P⁻¹ := by
          rw [← Real.rpow_mul hPpos.le, show (1 / g) * (-g) = -1 by field_simp,
            Real.rpow_neg_one]
        rwa [h2] at h1
      have hsrg : s ^ (-g) ≤ r ^ (-g) :=
        Real.rpow_le_rpow_of_nonpos hr0 hrs (by linarith : -g ≤ 0)
      have hPeq : 8 * C * P⁻¹ = 1 / 4 := by
        have hCne : C ≠ 0 := ne_of_gt hC
        rw [hP]
        field_simp
        ring
      have step1 : 8 * C * s ^ (-g) ≤ 8 * C * r ^ (-g) := by
        have hC0 : 0 ≤ 8 * C := by positivity
        nlinarith [hsrg, hC0, Real.rpow_pos_of_pos hs0 (-g), Real.rpow_pos_of_pos hr0 (-g)]
      have step2 : 8 * C * r ^ (-g) ≤ 8 * C * P⁻¹ := by
        have hC0 : 0 ≤ 8 * C := by positivity
        nlinarith [hrg, hC0, Real.rpow_pos_of_pos hr0 (-g)]
      linarith [h8, step1, step2, hPeq]
    · -- `s < r₀`: `|e s| ≤ 8C r₀^{3α} s^{-d} ≤ 8C r₀^{3α} r^{-d} ≤ 8C r₀^{3α} / (P r₀^{3α}) = 1/4`
      have hmax : max s r₀ = r₀ := max_eq_right h
      rw [hmax] at h8
      have hrd0 : 0 < r ^ d := Real.rpow_pos_of_pos hr0 d
      have hsr : s ^ (-d) ≤ r ^ (-d) :=
        Real.rpow_le_rpow_of_nonpos hr0 hrs (by linarith : -d ≤ 0)
      have h1 : r ^ (-d) ≤ (P * r₀ ^ (3 * α))⁻¹ := by
        have hPr : 0 < P * r₀ ^ (3 * α) := by positivity
        have e : r ^ (-d) = (r ^ d)⁻¹ := by
          rw [Real.rpow_neg hr0.le, inv_eq_one_div]
        rw [e]
        exact inv_anti₀ hPr hrd
      have h2 : 8 * C * r₀ ^ (3 * α) * (P * r₀ ^ (3 * α))⁻¹ = 1 / 4 := by
        have hCne : C ≠ 0 := ne_of_gt hC
        have hr₀ne : r₀ ^ (3 * α) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hr₀0 _)
        rw [hP]
        field_simp
        ring
      have hpos8 : 0 < 8 * C * r₀ ^ (3 * α) := by positivity
      have step1 : 8 * C * r₀ ^ (3 * α) * s ^ (-d)
          ≤ 8 * C * r₀ ^ (3 * α) * r ^ (-d) := by
        nlinarith [hsr, le_of_lt hpos8, Real.rpow_pos_of_pos hs0 (-d),
          Real.rpow_pos_of_pos hr0 (-d)]
      have step2 : 8 * C * r₀ ^ (3 * α) * r ^ (-d)
          ≤ 8 * C * r₀ ^ (3 * α) * (P * r₀ ^ (3 * α))⁻¹ := by
        nlinarith [h1, le_of_lt hpos8, Real.rpow_pos_of_pos hr0 (-d)]
      linarith [h8, step1, step2, h2]
  have hadm : ∀ s, r ≤ s → F s ≤ 2 * α / β * s ^ α := by
    intro s hs
    have hs1 : 1 ≤ s := le_trans hr1 hs
    have hineq : ∀ x, r ≤ x → (3 / 4 * β) * x ^ (-α - 1) * (F x) ^ 2 ≤ F' x := by
      intro x hx
      have hx1 : 1 ≤ x := le_trans hr1 hx
      have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx1
      rw [hODE x hx1]
      have hle : |e x| ≤ 1 / 4 := herr14 x hx
      have hge : (3 / 4 : ℝ) ≤ 1 - e x := by
        have := abs_le.1 hle
        linarith [this.2]
      have hxpow : 0 < x ^ (-α - 1) := Real.rpow_pos_of_pos hx0 _
      have hFsq : 0 < (F x) ^ 2 := by have := hpos x hx1; positivity
      have hnn : 0 ≤ β * x ^ (-α - 1) * (F x) ^ 2 := by positivity
      have h1 : (3 / 4) * (β * x ^ (-α - 1) * (F x) ^ 2)
          ≤ (1 - e x) * (β * x ^ (-α - 1) * (F x) ^ 2) :=
        mul_le_mul_of_nonneg_right hge hnn
      calc (3 / 4 * β) * x ^ (-α - 1) * (F x) ^ 2
          = (3 / 4) * (β * x ^ (-α - 1) * (F x) ^ 2) := by ring
        _ ≤ (1 - e x) * (β * x ^ (-α - 1) * (F x) ^ 2) := h1
        _ = (1 - e x) * β * x ^ (-α - 1) * (F x) ^ 2 := by ring
    have hmain := lemma_I_4_5_one_nocont (f := F) (f' := F') (A := 3 / 4 * β) (α := α)
      (r₀ := r) (by positivity) hα hr0
      (fun x hx => hderiv x (le_trans hr1 hx))
      (fun x hx => hpos x (le_trans hr1 hx)) hineq
    have hfin := hmain s hs
    have hcoef : α / (3 / 4 * β) = 4 * α / (3 * β) := by field_simp
    rw [hcoef] at hfin
    have hle2 : 4 * α / (3 * β) ≤ 2 * α / β := by
      rw [div_le_iff₀ (by positivity : (0:ℝ) < 3 * β)]
      have hb : 2 * α / β * (3 * β) = 6 * α := by
        field_simp
        norm_num
      rw [hb]
      linarith [hα]
    have hspos : 0 < s ^ α := Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one hs1) α
    have h3 : 4 * α / (3 * β) * s ^ α ≤ 2 * α / β * s ^ α :=
      mul_le_mul_of_nonneg_right hle2 (le_of_lt hspos)
    linarith
  have hcon2 := hmin r hr1 hadm
  linarith [hrlt]

/-! ### The general engine (covers Lemma I.4.10 as well)

Lemma I.4.10 (`d = 3α` plus the hydrodynamic condition, paper p. 38) runs the
*same* argument with the error profile `ε(r) = η(r) r^{-3α/2}` and, crucially,
with the error controlled by the power `3/2` of the volume ratio rather than the
cube: `Ē_{1,r,β} ≤ η(r) r^{-(3/2)α} (E|K|)^{3/2}` (paper (I.4.10)).  We therefore
state the engine with an arbitrary positive exponent `q`:

  `|e r| ≤ ε(r) (F r / ((α/β) r^α))^q`,

and the numerical condition at the scale `r` becomes

  `2^q ε(r) (max r r₀ / r)^{α q} ≤ 1/4`.

`q = 3` is the shape of (I.4.9)'s tree-graph error and `q = 3/2` that of
(I.4.10). -/

/-- **The general bootstrapping step.**  Let `q > 0`, let `ε` be positive and
nonincreasing on `[1,∞)`, let `F > 0` be monotone and satisfy the moment ODE
`F' = (1-e) β r^{-α-1} F²` on `[1,∞)` with `|e r| ≤ ε r (F r/((α/β)r^α))^q`, and
let `r₀ ≥ 1` be the minimal threshold with `F r ≤ (2α/β) r^α` for `r ≥ r₀`.  If
`r ≥ 1` satisfies `2^q ε(r) (max r r₀ / r)^{α q} ≤ 1/4`, then `r₀ ≤ r`. -/
theorem bootstrap_general
    {α β q : ℝ} (hα : 0 < α) (hβ : 0 < β) (hq : 0 < q)
    {F F' e ε : ℝ → ℝ}
    (hderiv : ∀ r, 1 ≤ r → HasDerivAt F (F' r) r)
    (hODE : ∀ r, 1 ≤ r → F' r = (1 - e r) * β * r ^ (-α - 1) * (F r) ^ 2)
    (hpos : ∀ r, 1 ≤ r → 0 < F r)
    (hmono : ∀ r s, 1 ≤ r → r ≤ s → F r ≤ F s)
    (hεpos : ∀ r, 1 ≤ r → 0 < ε r)
    (hεmono : ∀ r s, 1 ≤ r → r ≤ s → ε s ≤ ε r)
    (herr : ∀ r, 1 ≤ r → |e r| ≤ ε r * (F r / (α / β * r ^ α)) ^ q)
    {r₀ : ℝ} (hr₀ : 1 ≤ r₀) (hbdd : ∀ r, r₀ ≤ r → F r ≤ 2 * α / β * r ^ α)
    (hmin : ∀ b, 1 ≤ b → (∀ r, b ≤ r → F r ≤ 2 * α / β * r ^ α) → r₀ ≤ b)
    {r : ℝ} (hr1 : 1 ≤ r)
    (hsmall : (2:ℝ) ^ q * ε r * ((max r r₀ / r) ^ (α * q)) ≤ 1 / 4) :
    r₀ ≤ r := by
  -- step 1: the error is controlled by `2^q ε(s) (max s r₀ / s)^{αq}`
  have hbound : ∀ s, 1 ≤ s → |e s| ≤ (2:ℝ) ^ q * ε s * (((max s r₀) / s) ^ (α * q)) := by
    intro s hs
    have hs0 : 0 < s := lt_of_lt_of_le zero_lt_one hs
    have hmaxpos : 0 < max s r₀ := lt_of_lt_of_le hs0 (le_max_left s r₀)
    have hmaxnonneg : 0 ≤ max s r₀ := le_of_lt hmaxpos
    have hFmax : F s ≤ (2 * α / β) * ((max s r₀) ^ α) := by
      rcases le_total r₀ s with h | h
      · rw [max_eq_left h]; exact hbdd s h
      · have h1 : F s ≤ F r₀ := hmono s r₀ hs h
        have h2 : F r₀ ≤ 2 * α / β * r₀ ^ α := hbdd r₀ le_rfl
        rw [max_eq_right h]
        linarith
    have hratio : F s / (α / β * s ^ α) ≤ 2 * (((max s r₀) / s) ^ α) := by
      rw [div_le_iff₀ (by positivity)]
      calc F s ≤ (2 * α / β) * ((max s r₀) ^ α) := hFmax
        _ = 2 * (((max s r₀) / s) ^ α) * (α / β * s ^ α) := by
            rw [Real.div_rpow hmaxnonneg hs0.le]
            field_simp
    have hnonneg : 0 ≤ F s / (α / β * s ^ α) :=
      le_of_lt (div_pos (hpos s hs) (by positivity))
    have hcube : (F s / (α / β * s ^ α)) ^ q ≤ (2:ℝ) ^ q * (((max s r₀) / s) ^ (α * q)) := by
      have h1 : (F s / (α / β * s ^ α)) ^ q
          ≤ (2 * (((max s r₀) / s) ^ α)) ^ q := Real.rpow_le_rpow hnonneg hratio hq.le
      have h2 : (2 * (((max s r₀) / s) ^ α)) ^ q
          = (2:ℝ) ^ q * (((max s r₀) / s) ^ (α * q)) := by
        rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg (by positivity) α),
          ← Real.rpow_mul (by positivity), mul_comm]
      linarith
    calc |e s| ≤ ε s * (F s / (α / β * s ^ α)) ^ q := herr s hs
      _ ≤ ε s * ((2:ℝ) ^ q * (((max s r₀) / s) ^ (α * q))) :=
          mul_le_mul_of_nonneg_left hcube (le_of_lt (hεpos s hs))
      _ = (2:ℝ) ^ q * ε s * (((max s r₀) / s) ^ (α * q)) := by ring
  -- step 2: the error is `≤ 1/4` on `[r, ∞)`
  have herr14 : ∀ s, r ≤ s → |e s| ≤ 1 / 4 := by
    intro s hrs
    have hs1 : 1 ≤ s := le_trans hr1 hrs
    have hs0 : 0 < s := lt_of_lt_of_le zero_lt_one hs1
    have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr1
    have h8 := hbound s hs1
    have hεsr : ε s ≤ ε r := hεmono r s hr1 hrs
    rcases le_total r₀ s with h | h
    · -- `s ≥ r₀`: `max s r₀ = s`, so the bound is `2^q ε s ≤ 2^q ε r ≤ 1/4`
      have hmax : max s r₀ = s := max_eq_left h
      rw [hmax] at h8
      have hone : (1 : ℝ) ≤ (max r r₀ / r) ^ (α * q) := by
        have hle : (1 : ℝ) ≤ max r r₀ / r := by
          rw [le_div_iff₀ hr0]
          simpa using le_max_left r r₀
        calc (1 : ℝ) = (1 : ℝ) ^ (α * q) := by rw [Real.one_rpow]
          _ ≤ (max r r₀ / r) ^ (α * q) :=
              Real.rpow_le_rpow (by norm_num) hle (by positivity)
      have h8' : (2:ℝ) ^ q * ε s * ((s / s) ^ (α * q)) = (2:ℝ) ^ q * ε s := by
        rw [div_self (ne_of_gt hs0), Real.one_rpow, mul_one]
      rw [h8'] at h8
      have h2q : 0 < (2:ℝ) ^ q := Real.rpow_pos_of_pos (by norm_num) q
      have hε8 : (2:ℝ) ^ q * ε s ≤ 1 / 4 := by
        have h1 : (2:ℝ) ^ q * ε r ≤ (2:ℝ) ^ q * ε r * ((max r r₀ / r) ^ (α * q)) := by
          calc (2:ℝ) ^ q * ε r = (2:ℝ) ^ q * ε r * 1 := by ring
            _ ≤ (2:ℝ) ^ q * ε r * ((max r r₀ / r) ^ (α * q)) :=
                mul_le_mul_of_nonneg_left hone (le_of_lt (mul_pos h2q (hεpos r hr1)))
        have h2 : (2:ℝ) ^ q * ε s ≤ (2:ℝ) ^ q * ε r :=
          mul_le_mul_of_nonneg_left hεsr (le_of_lt h2q)
        linarith
      linarith
    · -- `s < r₀`: `max s r₀ = r₀`
      have hmax : max s r₀ = r₀ := max_eq_right h
      rw [hmax] at h8
      have hmaxr : max r r₀ = r₀ := max_eq_right (le_trans hrs h)
      rw [hmaxr] at hsmall
      have h1 : (r₀ / s) ^ (α * q) ≤ (r₀ / r) ^ (α * q) := by
        apply Real.rpow_le_rpow (by positivity) _ (by positivity)
        have hdiv : r₀ / s ≤ r₀ / r := by
          have := one_div_le_one_div_of_le hr0 hrs
          calc r₀ / s = r₀ * (1 / s) := by rw [mul_one_div]
            _ ≤ r₀ * (1 / r) := mul_le_mul_of_nonneg_left this (by linarith : (0:ℝ) ≤ r₀)
            _ = r₀ / r := by rw [mul_one_div]
        exact hdiv
      have h2q : 0 < (2:ℝ) ^ q := Real.rpow_pos_of_pos (by norm_num) q
      have h3 : (2:ℝ) ^ q * ε s ≤ (2:ℝ) ^ q * ε r :=
        mul_le_mul_of_nonneg_left hεsr (le_of_lt h2q)
      have h2 : (2:ℝ) ^ q * ε s * ((r₀ / s) ^ (α * q))
          ≤ (2:ℝ) ^ q * ε r * ((r₀ / r) ^ (α * q)) :=
        mul_le_mul h3 h1 (Real.rpow_nonneg (by positivity) _)
          (le_of_lt (mul_pos h2q (hεpos r hr1)))
      linarith
  -- step 3: apply the ODE comparison from scale `r`
  have hadm : ∀ s, r ≤ s → F s ≤ 2 * α / β * s ^ α := by
    intro s hs
    have hs1 : 1 ≤ s := le_trans hr1 hs
    have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr1
    have hineq : ∀ x, r ≤ x → (3 / 4 * β) * x ^ (-α - 1) * (F x) ^ 2 ≤ F' x := by
      intro x hx
      have hx1 : 1 ≤ x := le_trans hr1 hx
      have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx1
      rw [hODE x hx1]
      have hle : |e x| ≤ 1 / 4 := herr14 x hx
      have hge : (3 / 4 : ℝ) ≤ 1 - e x := by
        have := abs_le.1 hle
        linarith [this.2]
      have hxpow : 0 < x ^ (-α - 1) := Real.rpow_pos_of_pos hx0 _
      have hFsq : 0 < (F x) ^ 2 := by have := hpos x hx1; positivity
      have hnn : 0 ≤ β * x ^ (-α - 1) * (F x) ^ 2 := by positivity
      have h1 : (3 / 4) * (β * x ^ (-α - 1) * (F x) ^ 2)
          ≤ (1 - e x) * (β * x ^ (-α - 1) * (F x) ^ 2) :=
        mul_le_mul_of_nonneg_right hge hnn
      calc (3 / 4 * β) * x ^ (-α - 1) * (F x) ^ 2
          = (3 / 4) * (β * x ^ (-α - 1) * (F x) ^ 2) := by ring
        _ ≤ (1 - e x) * (β * x ^ (-α - 1) * (F x) ^ 2) := h1
        _ = (1 - e x) * β * x ^ (-α - 1) * (F x) ^ 2 := by ring
    have hmain := lemma_I_4_5_one_nocont (f := F) (f' := F') (A := 3 / 4 * β) (α := α)
      (r₀ := r) (by positivity) hα hr0
      (fun x hx => hderiv x (le_trans hr1 hx))
      (fun x hx => hpos x (le_trans hr1 hx)) hineq
    have hfin := hmain s hs
    have hcoef : α / (3 / 4 * β) = 4 * α / (3 * β) := by field_simp
    rw [hcoef] at hfin
    have hle2 : 4 * α / (3 * β) ≤ 2 * α / β := by
      rw [div_le_iff₀ (by positivity : (0:ℝ) < 3 * β)]
      have hb : 2 * α / β * (3 * β) = 6 * α := by
        field_simp
        norm_num
      rw [hb]
      linarith [hα]
    have hspos : 0 < s ^ α := Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one hs1) α
    have h3' : 4 * α / (3 * β) * s ^ α ≤ 2 * α / β * s ^ α :=
      mul_le_mul_of_nonneg_right hle2 (le_of_lt hspos)
    linarith
  exact hmin r hr1 hadm

end PercLib.CriticalLRP.VolumeMoments
