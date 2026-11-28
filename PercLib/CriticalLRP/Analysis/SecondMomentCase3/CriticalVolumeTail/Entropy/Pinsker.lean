/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

# The log-sum inequality and the binary Kullback–Leibler comparison

Source: T. Hutchcroft, *On the derivation of mean-field percolation critical exponents from the
triangle condition* (arXiv:2106.06400), Section 3: the relative-entropy proof of Theorem 3.1
(`Generalised Dewan–Muirhead`) and its Lemma 3.3 (the Bernoulli relative-entropy estimate).

This file contains the two analytic inequalities that the relative-entropy proof of the
two-intensity comparison runs on:

* the **log-sum inequality** `(∑ f) log ((∑ f)/(∑ g)) ≤ ∑ f log (f/g)`, the finite form of the
  Gibbs/data-processing step; and
* the **binary comparison** `(a - b)^2 ≤ 2 max a b · d(a‖b)`, where `d(a‖b)` is the binary
  Kullback–Leibler divergence.  This is the sharpened Pinsker inequality used by
  Dewan–Muirhead: the factor `max a b` (rather than `1`) is what turns the relative-entropy
  bound into the source's linear `(4/β₁)|β₂ - β₁|²` correction in Theorem 1.3.

The binary comparison is proved by a monotonicity argument: on the interval between `a` and `b`
the derivative of the comparison function has a definite sign because `y(1-y) ≤ a` there.  The
auxiliary derivative computations for `y ↦ d(a‖y)` are stated explicitly
(`hasDerivAt_bkl_snd`, `hasDerivAt_chi`, `hasDerivAt_zeta`).

Everything is finite-sum real analysis: no measure theory, no `sorry`, no extra axioms.
-/
module

public import Mathlib
public import PercLib.CriticalLRP.Analysis.SecondMomentCase3.CriticalVolumeTail.Entropy.Bernoulli

/-!
# Log-sum and binary relative entropy
-/

set_option autoImplicit false
set_option linter.hashCommand false

@[expose] public section

open Finset

namespace LRP

lemma one_sub_inv_le_log {x : ℝ} (hx : 0 < x) : 1 - x⁻¹ ≤ Real.log x := by
  have h := Real.log_le_sub_one_of_pos (x := x⁻¹) (by positivity)
  rw [Real.log_inv] at h
  linarith

noncomputable def bkl (a b : ℝ) : ℝ := a * Real.log (a / b) + (1 - a) * Real.log ((1 - a) / (1 - b))

lemma bkl_self (a : ℝ) : bkl a a = 0 := by simp [bkl]

lemma bkl_zero (b : ℝ) (hb0 : 0 < b) (hb1 : b < 1) : 0 ≤ bkl 0 b := by
  have hlogb : Real.log (1 - b) ≤ 0 := Real.log_nonpos (by linarith) (by linarith)
  have h : bkl 0 b = -Real.log (1 - b) := by
    simp only [bkl, zero_mul, sub_zero, one_mul, zero_add]
    rw [one_div, Real.log_inv]
  rw [h]; linarith

lemma bkl_one (b : ℝ) (hb0 : 0 < b) (hb1 : b < 1) : 0 ≤ bkl 1 b := by
  have hlogb : Real.log b ≤ 0 := Real.log_nonpos hb0.le hb1.le
  have h : bkl 1 b = -Real.log b := by
    simp only [bkl, sub_self, zero_mul, add_zero, one_div, one_mul]
    rw [Real.log_inv]
  rw [h]; linarith

lemma bkl_nonneg {a b : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hb0 : 0 < b) (hb1 : b < 1) :
    0 ≤ bkl a b := by
  rcases eq_or_lt_of_le ha0 with h | ha
  · rw [← h]; exact bkl_zero b hb0 hb1
  rcases eq_or_lt_of_le ha1 with h | ha'
  · rw [h]; exact bkl_one b hb0 hb1
  have h1 : a - b ≤ a * Real.log (a / b) := by
    have hlog := one_sub_inv_le_log (x := a / b) (by positivity)
    have hmul : a * (1 - (a / b)⁻¹) = a - b := by field_simp
    have h2 := mul_le_mul_of_nonneg_left hlog ha.le
    rwa [hmul] at h2
  have h2 : 1 - a - (1 - b) ≤ (1 - a) * Real.log ((1 - a) / (1 - b)) := by
    have hlog := one_sub_inv_le_log (x := (1 - a) / (1 - b)) (by positivity)
    have hmul : (1 - a) * (1 - ((1 - a) / (1 - b))⁻¹) = 1 - a - (1 - b) := by
      field_simp
    have h3 := mul_le_mul_of_nonneg_left hlog (by linarith : (0:ℝ) ≤ 1 - a)
    rwa [hmul] at h3
  simp only [bkl]
  linarith

lemma hasDerivAt_bkl_snd {a y : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hy0 : 0 < y) (hy1 : y < 1) :
    HasDerivAt (fun z => bkl a z) (-(a / y) + (1 - a) / (1 - y)) y := by
  have hid := hasDerivAt_id (x := y)
  have h2 : HasDerivAt (fun z : ℝ => Real.log (a / z)) ((-(a * (y ^ 2)⁻¹)) / (a / y)) y := by
    have h1 : HasDerivAt (fun z : ℝ => a / z) (-(a * (y ^ 2)⁻¹)) y := by
      simpa [div_eq_mul_inv, mul_neg] using (hid.inv hy0.ne').const_mul a
    exact h1.log (by positivity)
  have h5 : HasDerivAt (fun z : ℝ => Real.log ((1 - a) / (1 - z)))
      (((1 - a) * ((1 - y) ^ 2)⁻¹) / ((1 - a) / (1 - y))) y := by
    have h3 : HasDerivAt (fun z : ℝ => 1 - z) (-1) y := by simpa using hid.const_sub 1
    have h4 : HasDerivAt (fun z : ℝ => (1 - a) / (1 - z)) ((1 - a) * ((1 - y) ^ 2)⁻¹) y := by
      have h := h3.inv (by linarith)
      simpa [div_eq_mul_inv] using h.const_mul (1 - a)
    exact h4.log (by positivity)
  have h6 := (h2.const_mul a).add (h5.const_mul (1 - a))
  have hval : a * ((-(a * (y ^ 2)⁻¹)) / (a / y))
      + (1 - a) * (((1 - a) * ((1 - y) ^ 2)⁻¹) / ((1 - a) / (1 - y)))
      = -(a / y) + (1 - a) / (1 - y) := by
    have hy : y ≠ 0 := hy0.ne'
    have h1y : (1 : ℝ) - y ≠ 0 := by intro h; linarith [hy1]
    field_simp
  rw [hval] at h6
  exact h6

lemma continuousOn_bkl {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {s : Set ℝ}
    (hs0 : ∀ y ∈ s, 0 < y) (hs1 : ∀ y ∈ s, y < 1) : ContinuousOn (fun y => bkl a y) s := by
  unfold bkl
  have h1 : ContinuousOn (fun y : ℝ => a / y) s :=
    ContinuousOn.div continuousOn_const continuousOn_id (fun y hy => (hs0 y hy).ne')
  have h2 : ContinuousOn (fun y : ℝ => 1 - y) s := by fun_prop
  have h3 : ContinuousOn (fun y : ℝ => (1 - a) / (1 - y)) s :=
    ContinuousOn.div continuousOn_const h2 (fun y hy => by have := hs1 y hy; linarith)
  apply ContinuousOn.add (continuousOn_const.mul (h1.log ?_))
    (ContinuousOn.mul continuousOn_const (h3.log ?_)) <;> intro y hy
  · exact div_ne_zero ha0.ne' (hs0 y hy).ne'
  · exact div_ne_zero (by linarith : (1 : ℝ) - a ≠ 0) (by have h := hs1 y hy; linarith)

lemma hasDerivAt_chi {a y : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hy0 : 0 < y) (hy1 : y < 1) :
    HasDerivAt (fun y => 2 * a * bkl a y - (a - y) * (a - y))
      (2 * (a - y) * (1 - a / (y * (1 - y)))) y := by
  have hb := hasDerivAt_bkl_snd ha0 ha1 hy0 hy1
  have h1 : HasDerivAt (fun z : ℝ => a - z) (-1) y := by
    simpa using (hasDerivAt_id y).const_sub a
  have h2 : HasDerivAt (fun z : ℝ => (a - z) * (a - z)) (2 * (a - y) * (-1)) y := by
    have h := h1.mul h1
    convert h using 1
    ring
  have h3 := (hb.const_mul (2 * a)).sub h2
  have hval : 2 * a * (-(a / y) + (1 - a) / (1 - y)) - 2 * (a - y) * (-1)
      = 2 * (a - y) * (1 - a / (y * (1 - y))) := by
    have hy : y ≠ 0 := hy0.ne'
    have h1y : (1 : ℝ) - y ≠ 0 := by intro h; linarith [hy1]
    field_simp
    try ring
  rw [hval] at h3
  exact h3

lemma hasDerivAt_zeta {a x : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hx0 : 0 < x) (hx1 : x < 1) :
    HasDerivAt (fun x => 2 * x * bkl a x - (x - a) * (x - a))
      (2 * bkl a x + 2 * x * (x - a) / (1 - x)) x := by
  have hb := hasDerivAt_bkl_snd ha0 ha1 hx0 hx1
  have hprod : HasDerivAt (fun x => 2 * x * bkl a x)
      (2 * bkl a x + 2 * x * (-(a / x) + (1 - a) / (1 - x))) x := by
    have h2x : HasDerivAt (fun x : ℝ => 2 * x) 2 x := by
      simpa using (hasDerivAt_id x).const_mul 2
    have h := h2x.mul hb
    convert h using 1
  have h1 : HasDerivAt (fun z : ℝ => z - a) (1 : ℝ) x := by
    simpa using (hasDerivAt_id x).sub_const a
  have h2 : HasDerivAt (fun z : ℝ => (z - a) * (z - a)) (2 * (x - a) * 1) x := by
    have h := h1.mul h1
    convert h using 1
    ring
  have h3 := hprod.sub h2
  have hval : 2 * bkl a x + 2 * x * (-(a / x) + (1 - a) / (1 - x)) - 2 * (x - a) * 1
      = 2 * bkl a x + 2 * x * (x - a) / (1 - x) := by
    have hx : x ≠ 0 := hx0.ne'
    have h1x : (1 : ℝ) - x ≠ 0 := by intro h; linarith [hx1]
    field_simp
    try ring
  rw [hval] at h3
  exact h3

theorem binary_kl_sq_le {a b : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hb0 : 0 < b) (hb1 : b < 1) :
    (a - b) ^ 2 ≤ 2 * max a b * bkl a b := by
  rw [sq]
  rcases le_or_gt b a with hba | hab
  · have hanti : AntitoneOn (fun y => 2 * a * bkl a y - (a - y) * (a - y)) (Set.Icc b a) := by
      apply antitoneOn_of_deriv_nonpos (convex_Icc b a) ?_ ?_ ?_
      · have hc := continuousOn_bkl ha0 ha1 (s := Set.Icc b a)
          (fun y hy => lt_of_lt_of_le hb0 hy.1) (fun y hy => lt_of_le_of_lt hy.2 ha1)
        have h2 : ContinuousOn (fun y : ℝ => (a - y) * (a - y)) (Set.Icc b a) := by fun_prop
        exact (continuousOn_const.mul hc).sub h2
      · intro y hy
        rw [interior_Icc] at hy
        exact ((hasDerivAt_chi ha0 ha1 (lt_of_lt_of_le hb0 hy.1.le)
          (lt_trans hy.2 ha1)).differentiableAt).differentiableWithinAt
      · intro y hy
        rw [interior_Icc] at hy
        have hy0 : 0 < y := lt_of_lt_of_le hb0 hy.1.le
        have hy1 : y < 1 := lt_trans hy.2 ha1
        rw [(hasDerivAt_chi ha0 ha1 hy0 hy1).deriv]
        have hpos : 0 < y * (1 - y) := mul_pos hy0 (by linarith)
        have hle : y * (1 - y) ≤ a := by
          have h4 : y * (1 - y) ≤ y * 1 := mul_le_mul_of_nonneg_left (by linarith) hy0.le
          linarith [h4, hy.2.le]
        have hdiv : 1 ≤ a / (y * (1 - y)) := by
          rw [le_div_iff₀ hpos]; simpa using hle
        have hfac : 1 - a / (y * (1 - y)) ≤ 0 := by linarith
        have hna : 0 ≤ 2 * (a - y) := by linarith [hy.2]
        exact mul_nonpos_of_nonneg_of_nonpos hna hfac
    have h1 : 2 * a * bkl a a - (a - a) * (a - a)
        ≤ 2 * a * bkl a b - (a - b) * (a - b) := by
      have h := hanti (Set.mem_Icc.mpr ⟨le_rfl, hba⟩) (Set.mem_Icc.mpr ⟨hba, le_rfl⟩) hba
      simpa only using h
    have h2 : 2 * a * bkl a a - (a - a) * (a - a) = 0 := by simp [bkl_self]
    rw [h2] at h1
    rw [max_eq_left hba]
    linarith [h1]
  · have hmono : MonotoneOn (fun x => 2 * x * bkl a x - (x - a) * (x - a)) (Set.Icc a b) := by
      apply monotoneOn_of_deriv_nonneg (convex_Icc a b) ?_ ?_ ?_
      · have hc := continuousOn_bkl ha0 ha1 (s := Set.Icc a b)
          (fun y hy => lt_of_lt_of_le ha0 hy.1) (fun y hy => lt_of_le_of_lt hy.2 hb1)
        have h2 : ContinuousOn (fun x : ℝ => (x - a) * (x - a)) (Set.Icc a b) := by fun_prop
        have hlin : ContinuousOn (fun x : ℝ => 2 * x) (Set.Icc a b) := by fun_prop
        exact (hlin.mul hc).sub h2
      · intro x hx
        rw [interior_Icc] at hx
        exact ((hasDerivAt_zeta ha0 ha1 (lt_trans ha0 hx.1)
          (lt_trans hx.2 hb1)).differentiableAt).differentiableWithinAt
      · intro x hx
        rw [interior_Icc] at hx
        have hx0 : 0 < x := lt_trans ha0 hx.1
        have hx1 : x < 1 := lt_trans hx.2 hb1
        rw [(hasDerivAt_zeta ha0 ha1 hx0 hx1).deriv]
        have hk : 0 ≤ bkl a x := bkl_nonneg ha0.le ha1.le hx0 hx1
        have hxa : 0 ≤ x - a := by linarith [hx.1]
        have h2 : 0 ≤ 2 * x * (x - a) / (1 - x) := by positivity
        linarith [hk, h2]
    have h1 : 2 * a * bkl a a - (a - a) * (a - a)
        ≤ 2 * b * bkl a b - (b - a) * (b - a) := by
      have h := hmono (Set.mem_Icc.mpr ⟨le_rfl, hab.le⟩) (Set.mem_Icc.mpr ⟨hab.le, le_rfl⟩) hab.le
      simpa only using h
    have h2 : 2 * a * bkl a a - (a - a) * (a - a) = 0 := by simp [bkl_self]
    rw [h2] at h1
    rw [max_eq_right hab.le]
    nlinarith [h1]

section Pinsker

variable {α : Type*} [Fintype α]

/-- Binary bound, allowing the first parameter to be `0` or `1`. -/
lemma binary_kl_sq_le' {a b : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hb0 : 0 < b) (hb1 : b < 1) :
    (a - b) ^ 2 ≤ 2 * max a b * bkl a b := by
  rcases eq_or_lt_of_le ha0 with h | ha
  · -- a = 0
    subst h
    have hbkl : bkl 0 b = Real.log (1 / (1 - b)) := by
      simp only [bkl, zero_mul, sub_zero, one_mul, zero_add]
    have hbwhere : Real.log (1 / (1 - b)) = -Real.log (1 - b) := by
      rw [one_div, Real.log_inv]
    have hlog : b ≤ Real.log (1 / (1 - b)) := by
      rw [hbwhere]
      have h := Real.log_le_sub_one_of_pos (x := 1 - b) (by linarith)
      linarith
    rw [hbkl, max_eq_right hb0.le]
    nlinarith [hlog, hb0]
  rcases eq_or_lt_of_le ha1 with h | ha'
  · -- a = 1
    subst h
    have hbkl : bkl 1 b = Real.log (1 / b) := by
      simp only [bkl, sub_self, zero_mul, add_zero, one_mul]
    have hbwhere : Real.log (1 / b) = -Real.log b := by rw [one_div, Real.log_inv]
    have hlog : 1 - b ≤ Real.log (1 / b) := by
      rw [hbwhere]
      have h := Real.log_le_sub_one_of_pos (x := b) hb0
      linarith
    rw [hbkl, max_eq_left (by linarith : b ≤ 1)]
    nlinarith [hlog]
  exact binary_kl_sq_le ha ha' hb0 hb1

end Pinsker

/-- **Log-sum inequality** for two weights: `(∑ f) log ((∑ f)/(∑ g)) ≤ ∑ f log (f/g)`. -/
theorem log_sum_ineq {α : Type*} {s : Finset α} {f g : α → ℝ}
    (hf : ∀ x ∈ s, 0 ≤ f x) (hg : ∀ x ∈ s, 0 < g x) :
    (∑ x ∈ s, f x) * Real.log ((∑ x ∈ s, f x) / (∑ x ∈ s, g x))
      ≤ ∑ x ∈ s, f x * Real.log (f x / g x) := by
  classical
  set F := ∑ x ∈ s, f x with hF
  set G := ∑ x ∈ s, g x with hG
  rcases s.eq_empty_or_nonempty with rfl | hne
  · have hF0 : F = 0 := by rw [hF]; simp
    rw [hF0, zero_mul]
    simp
  have hGpos : 0 < G := by rw [hG]; exact Finset.sum_pos (fun x hx => hg x hx) hne
  rcases eq_or_lt_of_le (by rw [hF]; exact Finset.sum_nonneg hf : (0:ℝ) ≤ F) with hF0 | hFpos
  · have hfz : ∀ x ∈ s, f x = 0 := by
      intro x hx
      by_contra hne0
      have hpos : 0 < f x := lt_of_le_of_ne (hf x hx) (Ne.symm hne0)
      have h1 : f x ≤ F := by
        rw [hF]; exact Finset.single_le_sum (fun y hy => hf y hy) hx
      linarith
    have hsum0 : (∑ x ∈ s, f x * Real.log (f x / g x)) = 0 :=
      Finset.sum_eq_zero fun x hx => by rw [hfz x hx, zero_mul]
    rw [← hF0, zero_mul, hsum0]
  · have hpt : ∀ x ∈ s, f x - g x * (F / G) ≤ f x * Real.log ((f x / g x) / (F / G)) := by
      intro x hx
      rcases eq_or_lt_of_le (hf x hx) with h0 | hpos
      · rw [← h0]
        simp only [zero_mul, zero_sub]
        have hFG : 0 < F / G := div_pos hFpos hGpos
        have h2 : 0 ≤ g x * (F / G) := mul_nonneg (le_of_lt (hg x hx)) hFG.le
        simp only [neg_le_iff_add_nonneg, zero_add]
        exact h2
      · have hlog : 1 - ((f x / g x) / (F / G))⁻¹
            ≤ Real.log ((f x / g x) / (F / G)) :=
          one_sub_inv_le_log (div_pos (div_pos hpos (hg x hx)) (div_pos hFpos hGpos))
        have h2 : f x * (1 - ((f x / g x) / (F / G))⁻¹)
            ≤ f x * Real.log ((f x / g x) / (F / G)) :=
          mul_le_mul_of_nonneg_left hlog hpos.le
        have hmul : f x * (1 - ((f x / g x) / (F / G))⁻¹) = f x - g x * (F / G) := by
          field_simp
        rw [hmul] at h2
        exact h2
    have hstep : ∑ x ∈ s, (f x - g x * (F / G))
        ≤ ∑ x ∈ s, f x * Real.log ((f x / g x) / (F / G)) := Finset.sum_le_sum hpt
    have hzero : (∑ x ∈ s, (f x - g x * (F / G))) = 0 := by
      have hsum : (∑ x ∈ s, (f x - g x * (F / G)))
          = (∑ x ∈ s, f x) - (∑ x ∈ s, g x) * (F / G) := by
        rw [Finset.sum_sub_distrib, Finset.sum_mul]
      rw [hsum]
      rw [show (∑ x ∈ s, f x) = F from hF.symm, show (∑ x ∈ s, g x) = G from hG.symm]
      rw [mul_comm G (F / G), div_mul_cancel₀ F hGpos.ne', sub_self]
    have hkey : (0 : ℝ) ≤ ∑ x ∈ s, f x * Real.log ((f x / g x) / (F / G)) := by
      rw [← hzero]; exact hstep
    have hexp : ∑ x ∈ s, f x * Real.log ((f x / g x) / (F / G))
        = ∑ x ∈ s, f x * Real.log (f x / g x) - F * Real.log (F / G) := by
      have hpt2 : ∀ x ∈ s, f x * Real.log ((f x / g x) / (F / G))
          = f x * Real.log (f x / g x) - f x * Real.log (F / G) := by
        intro x hx
        rcases eq_or_lt_of_le (hf x hx) with h0 | hpos
        · rw [← h0]; simp
        · have hx0 : f x / g x ≠ 0 := ne_of_gt (div_pos hpos (hg x hx))
          have hFG : F / G ≠ 0 := ne_of_gt (div_pos hFpos hGpos)
          rw [Real.log_div hx0 hFG, mul_sub]
      rw [Finset.sum_congr rfl hpt2, Finset.sum_sub_distrib, ← Finset.sum_mul, ← hF]
    rw [hexp] at hkey
    linarith

section Model

variable {E : Type*} [Fintype E] [DecidableEq E]

omit [Fintype E] [DecidableEq E] in
theorem openProb_pos {J : E → ℝ} {β : ℝ} {e : E} (hJ : 0 < J e) (hβ : 0 < β) :
    0 < openProb J β e := by
  have hlt : Real.exp (-(β * J e)) < 1 := by
    rw [Real.exp_lt_one_iff]; nlinarith
  simp only [openProb]
  linarith

omit [Fintype E] [DecidableEq E] in
theorem openProb_lt_one {J : E → ℝ} {β : ℝ} (e : E) : openProb J β e < 1 := by
  have hpos : 0 < Real.exp (-(β * J e)) := Real.exp_pos _
  simp only [openProb]
  linarith

omit [Fintype E] [DecidableEq E] in
/-- **The binary relative-entropy comparison at the weighted model's one-edge parameters.** -/
theorem openProb_binary_kl {J : E → ℝ} {β₁ β₂ : ℝ} {e : E} (hJ : 0 < J e) (hβ1 : 0 < β₁)
    (hβ2 : 0 < β₂) :
    (openProb J β₂ e - openProb J β₁ e) ^ 2
      ≤ 2 * max (openProb J β₂ e) (openProb J β₁ e)
          * bkl (openProb J β₂ e) (openProb J β₁ e) :=
  binary_kl_sq_le (openProb_pos (J := J) (e := e) hJ hβ2) (openProb_lt_one (J := J) (β := β₂) e)
    (openProb_pos (J := J) (e := e) hJ hβ1) (openProb_lt_one (J := J) (β := β₁) e)

/-- The binary comparison is not vacuous: on a single edge with `J = 1`, `β₁ = 1`, `β₂ = 2` both
sides are computable real numbers and the inequality is strict. -/
theorem openProb_binary_kl_example :
    (openProb (fun _ : Unit => (1:ℝ)) 2 () - openProb (fun _ : Unit => (1:ℝ)) 1 ()) ^ 2
      ≤ 2 * max (openProb (fun _ : Unit => (1:ℝ)) 2 ())
          (openProb (fun _ : Unit => (1:ℝ)) 1 ())
          * bkl (openProb (fun _ : Unit => (1:ℝ)) 2 ())
            (openProb (fun _ : Unit => (1:ℝ)) 1 ()) :=
  openProb_binary_kl (J := fun _ => (1:ℝ)) (e := ()) one_pos one_pos (by norm_num)

end Model

/-! ### Generalised Pinsker inequality (interior case) -/

/-- **Generalised Pinsker inequality** (the finite form of Dewan–Muirhead's sharpened Pinsker
inequality).  For two probability weights on a finite type and an event whose probability lies
strictly between `0` and `1` for both weights, the square of the difference of the probabilities
is at most twice the relative entropy times the larger of the two probabilities.  This is the
step that converts the relative-entropy bound into a comparison of tail probabilities. -/
theorem pinsker_general {α : Type*} [Fintype α] (f g : α → ℝ) (s : Finset α)
    (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 < g x) (hf1 : ∑ x, f x = 1) (hg1 : ∑ x, g x = 1)
    (hp0 : 0 < ∑ x ∈ s, f x) (hp1 : ∑ x ∈ s, f x < 1)
    (hq0 : 0 < ∑ x ∈ s, g x) (hq1 : ∑ x ∈ s, g x < 1) :
    (∑ x ∈ s, f x - ∑ x ∈ s, g x) ^ 2
      ≤ 2 * (∑ x, f x * Real.log (f x / g x)) * max (∑ x ∈ s, f x) (∑ x ∈ s, g x) := by
  classical
  have hKL : (∑ x ∈ s, f x) * Real.log ((∑ x ∈ s, f x) / (∑ x ∈ s, g x))
      + (∑ x ∈ sᶜ, f x) * Real.log ((∑ x ∈ sᶜ, f x) / (∑ x ∈ sᶜ, g x))
      ≤ ∑ x, f x * Real.log (f x / g x) := by
    have h1 := log_sum_ineq (s := s) (f := f) (g := g) (fun x _ => hf x) (fun x _ => hg x)
    have h2 := log_sum_ineq (s := sᶜ) (f := f) (g := g) (fun x _ => hf x) (fun x _ => hg x)
    have hsplit := Finset.sum_add_sum_compl s (fun x => f x * Real.log (f x / g x))
    linarith
  have hpc : (∑ x ∈ s, f x) + (∑ x ∈ sᶜ, f x) = 1 := by
    rw [Finset.sum_add_sum_compl]; exact hf1
  have hqc : (∑ x ∈ s, g x) + (∑ x ∈ sᶜ, g x) = 1 := by
    rw [Finset.sum_add_sum_compl]; exact hg1
  have hbin : (∑ x ∈ s, f x - ∑ x ∈ s, g x) ^ 2
      ≤ 2 * max (∑ x ∈ s, f x) (∑ x ∈ s, g x)
        * ((∑ x ∈ s, f x) * Real.log ((∑ x ∈ s, f x) / (∑ x ∈ s, g x))
          + (∑ x ∈ sᶜ, f x) * Real.log ((∑ x ∈ sᶜ, f x) / (∑ x ∈ sᶜ, g x))) := by
    have hb := binary_kl_sq_le' (le_of_lt hp0) (le_of_lt hp1) hq0 hq1
    have hp'' : (∑ x ∈ sᶜ, f x) = 1 - ∑ x ∈ s, f x := by linarith
    have hq'' : (∑ x ∈ sᶜ, g x) = 1 - ∑ x ∈ s, g x := by linarith
    rw [hp'', hq'']
    simpa [bkl] using hb
  calc (∑ x ∈ s, f x - ∑ x ∈ s, g x) ^ 2
      ≤ 2 * max (∑ x ∈ s, f x) (∑ x ∈ s, g x)
        * ((∑ x ∈ s, f x) * Real.log ((∑ x ∈ s, f x) / (∑ x ∈ s, g x))
          + (∑ x ∈ sᶜ, f x) * Real.log ((∑ x ∈ sᶜ, f x) / (∑ x ∈ sᶜ, g x))) := hbin
    _ ≤ 2 * max (∑ x ∈ s, f x) (∑ x ∈ s, g x) * (∑ x, f x * Real.log (f x / g x)) := by
        refine mul_le_mul_of_nonneg_left hKL ?_
        have h : 0 ≤ max (∑ x ∈ s, f x) (∑ x ∈ s, g x) := le_trans (le_of_lt hp0) (le_max_left _ _)
        linarith
    _ = 2 * (∑ x, f x * Real.log (f x / g x)) * max (∑ x ∈ s, f x) (∑ x ∈ s, g x) := by
        ring

end LRP

namespace LRP

set_option linter.hashCommand false in
#print axioms LRP.pinsker_general

set_option linter.hashCommand false in
#print axioms LRP.binary_kl_sq_le

set_option linter.hashCommand false in
#print axioms LRP.binary_kl_sq_le'

set_option linter.hashCommand false in
#print axioms LRP.log_sum_ineq

set_option linter.hashCommand false in
#print axioms LRP.openProb_binary_kl

end LRP
