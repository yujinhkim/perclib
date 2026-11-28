/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

# Lemma 3.3 of [2106.06400]: the per-edge Bernoulli relative-entropy estimate

Source: T. Hutchcroft, *On the derivation of mean-field percolation critical exponents from the
triangle condition* (arXiv:2106.06400), Lemma 3.3, displayed there as (3.4) and used in the proof
of `thm:DM_Chi` (Theorem 3.1, the generalised Dewan–Muirhead inequality):

> For each `p ∈ [0,1]` let `Ber(p)` denote the law of a Bernoulli-`p` random variable.  The
> estimate
> `D_KL(Ber(1-e^{-a}) ‖ Ber(1-e^{-b})) = D_KL(Ber(e^{-a}) ‖ Ber(e^{-b}))`
> `≤ |a-b|²/(2 min{a,b})`
> holds for every `a, b > 0`.

The source computes `D_KL(Ber(p) ‖ Ber(q)) = ∫_q^p (p-s)/(s(1-s)) ds` and substitutes
`s = e^{-t}`, reducing the claim to the one-dimensional estimates
`e^{-a}/(1-e^{-a}) ≤ 1/a` and `1-e^{-t} ≤ t`.  This file reproduces that argument without the
integral: `t ↦ d(e^{-a} ‖ e^{-t})` is differentiated by `LRP.hasDerivAt_bkl_snd` (its derivative
is `(e^{-a}-e^{-t})/(1-e^{-t})`), the two orders `a ≤ b` and `b ≤ a` are handled separately
exactly as in the source, and in each case the derivative is compared with the slope of a
quadratic that vanishes at `t = a`, so that a monotonicity argument gives the bound.

Note the direction: this is an *upper* bound for the binary divergence, so it is not a
consequence of the sharpened Pinsker inequality `LRP.binary_kl_sq_le`, which is the opposite,
*lower* bound `(a-b)² ≤ 2 max{a,b} d(a‖b)`.  The two are complementary inputs to the
relative-entropy method, not substitutes for one another: `bkl_pos` below uses the lower bound,
and `bkl_one_sub_exp_le` is the upper bound needed per edge.
-/
module

public import PercLib.CriticalLRP.Analysis.SecondMomentCase3.CriticalVolumeTail.Entropy.Pinsker

/-!
# The per-edge relative-entropy estimate at exponential parameters
-/

set_option autoImplicit false
set_option linter.hashCommand false

@[expose] public section

namespace LRP

/-! ### Complement symmetry -/

/-- Complementing both arguments of the binary divergence leaves it unchanged:
`d(1-u ‖ 1-v) = d(u ‖ v)`.  This is the identity behind the equality in the source's (3.4)
between `D_KL(Ber(1-e^{-a}) ‖ Ber(1-e^{-b}))` and `D_KL(Ber(e^{-a}) ‖ Ber(e^{-b}))`. -/
theorem bkl_one_sub (u v : ℝ) : bkl (1 - u) (1 - v) = bkl u v := by
  simp only [bkl, sub_sub_cancel]
  exact add_comm _ _

/-- The binary divergence is strictly positive off the diagonal.  (This uses the sharpened
Pinsker inequality `binary_kl_sq_le`, in the direction in which it is available.) -/
theorem bkl_pos {p q : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hq0 : 0 < q) (hq1 : q < 1)
    (hpq : p ≠ q) : 0 < bkl p q := by
  have h := binary_kl_sq_le hp0 hp1 hq0 hq1
  have hmax : 0 < max p q := lt_of_lt_of_le hp0 (le_max_left _ _)
  have hsq : 0 < (p - q) ^ 2 := by
    rcases lt_or_gt_of_ne hpq with h' | h'
    · nlinarith
    · nlinarith
  nlinarith [h]

/-! ### Elementary exponential estimates

These are the source's two one-dimensional inequalities `1 - e^{-t} ≤ t` and
`e^{-t}/(1-e^{-t}) ≤ 1/t` (the latter from `1 + t ≤ e^t`), together with the factorisation
`e^{-a} - e^{-t} = e^{-a}(1 - e^{-(t-a)})` that arises when substituting `s = e^{-t}`. -/

/-- `1 - e^{-x} ≤ x`.  (The source uses this for `x ≥ 0`.) -/
lemma one_sub_exp_neg_le (x : ℝ) : 1 - Real.exp (-x) ≤ x := by
  have h := Real.add_one_le_exp (-x)
  linarith

/-- `x e^{-x} ≤ 1 - e^{-x}`, the source's inequality `e^{-x}(e^x - 1) ≤ x`. -/
lemma mul_exp_neg_le_one_sub_exp_neg (x : ℝ) : x * Real.exp (-x) ≤ 1 - Real.exp (-x) := by
  have h := Real.add_one_le_exp x
  have hpos : (0 : ℝ) < Real.exp (-x) := Real.exp_pos _
  have hmul : (x + 1) * Real.exp (-x) ≤ Real.exp x * Real.exp (-x) :=
    mul_le_mul_of_nonneg_right h hpos.le
  have hone : Real.exp x * Real.exp (-x) = 1 := by
    rw [← Real.exp_add]
    simp
  rw [hone] at hmul
  nlinarith

/-- `e^{-x}/(1 - e^{-x}) ≤ 1/x` for `x > 0`: the source's final estimate on
`e^{-t}/(1-e^{-t})`, applied at `t = a` (first case) and at `t = b` (second case). -/
lemma exp_neg_div_one_sub_le {x : ℝ} (hx : 0 < x) :
    Real.exp (-x) / (1 - Real.exp (-x)) ≤ 1 / x := by
  have hlt : Real.exp (-x) < 1 := by
    rw [Real.exp_lt_one_iff]
    linarith
  have hy : (0 : ℝ) < 1 - Real.exp (-x) := by linarith
  rw [div_le_div_iff₀ hy hx]
  have h := mul_exp_neg_le_one_sub_exp_neg x
  nlinarith

/-- `e^{-a} - e^{-t} = e^{-a}(1 - e^{-(t-a)})`, the numerator produced by substituting
`s = e^{-t}` in the source's integral. -/
lemma exp_neg_sub_exp_neg (a t : ℝ) :
    Real.exp (-a) - Real.exp (-t) = Real.exp (-a) * (1 - Real.exp (-(t - a))) := by
  have h : Real.exp (-t) = Real.exp (-a) * Real.exp (-(t - a)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [h]
  ring

/-! ### The derivative of `t ↦ d(p ‖ e^{-t})` and its two one-sided bounds -/

/-- `t ↦ e^{-t}` has derivative `-e^{-t}`. -/
lemma hasDerivAt_exp_neg (t : ℝ) :
    HasDerivAt (fun s : ℝ => Real.exp (-s)) (-Real.exp (-t)) t := by
  have h1 : HasDerivAt (fun s : ℝ => -s) (-1) t := hasDerivAt_neg' (x := t)
  have h2 := h1.exp
  have hval : Real.exp (-t) * (-1) = -Real.exp (-t) := by ring
  rw [hval] at h2
  exact h2

/-- The derivative of `t ↦ d(p ‖ e^{-t})` in `t`, for `0 < p < 1`: it is
`(p - e^{-t})/(1 - e^{-t})`. -/
theorem hasDerivAt_bkl_exp_neg {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => bkl p (Real.exp (-s)))
      ((p - Real.exp (-t)) / (1 - Real.exp (-t))) t := by
  have hy0 : 0 < Real.exp (-t) := Real.exp_pos _
  have hy1 : Real.exp (-t) < 1 := by
    rw [Real.exp_lt_one_iff]
    linarith
  have h := (hasDerivAt_bkl_snd hp0 hp1 hy0 hy1).comp t (hasDerivAt_exp_neg t)
  have hyne : Real.exp (-t) ≠ 0 := hy0.ne'
  have h1y : (1 : ℝ) - Real.exp (-t) ≠ 0 := by
    intro hh
    linarith
  have hval : (-(p / Real.exp (-t)) + (1 - p) / (1 - Real.exp (-t))) * (-Real.exp (-t))
      = (p - Real.exp (-t)) / (1 - Real.exp (-t)) := by
    field_simp
    ring
  rw [← hval]
  exact h

/-- Continuity of `t ↦ d(p ‖ e^{-t})` on intervals of positive numbers. -/
lemma continuousOn_bkl_exp_neg {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) {c d : ℝ} (hc : 0 < c) :
    ContinuousOn (fun t : ℝ => bkl p (Real.exp (-t))) (Set.Icc c d) := by
  have hb : ContinuousOn (fun y : ℝ => bkl p y) (Set.Ioo 0 1) :=
    continuousOn_bkl hp0 hp1 (fun y hy => hy.1) (fun y hy => hy.2)
  have hmap : Set.MapsTo (fun t : ℝ => Real.exp (-t)) (Set.Icc c d) (Set.Ioo 0 1) := by
    intro t ht
    exact ⟨Real.exp_pos _, by rw [Real.exp_lt_one_iff]; linarith [ht.1]⟩
  exact ContinuousOn.comp (g := fun y : ℝ => bkl p y) hb (by fun_prop) hmap

/-- Above `a` the derivative of `t ↦ d(e^{-a} ‖ e^{-t})` is at most `(t-a)/a`.  This is the
source's first-case bound `e^{-a}/(1-e^{-a}) · ∫_0^{b-a}(1-e^{-t})dt`, differentiated. -/
lemma bkl_exp_neg_deriv_le {a t : ℝ} (ha : 0 < a) (ht : a ≤ t) :
    (Real.exp (-a) - Real.exp (-t)) / (1 - Real.exp (-t)) ≤ (t - a) / a := by
  have hd : (0 : ℝ) < 1 - Real.exp (-t) := by
    have hlt : Real.exp (-t) < 1 := by
      rw [Real.exp_lt_one_iff]
      linarith
    linarith
  have hmono : Real.exp (-t) ≤ Real.exp (-a) := by
    rw [Real.exp_le_exp]
    linarith
  have hfac : Real.exp (-a) - Real.exp (-t) = Real.exp (-a) * (1 - Real.exp (-(t - a))) :=
    exp_neg_sub_exp_neg a t
  have h1 : 1 - Real.exp (-(t - a)) ≤ t - a := one_sub_exp_neg_le (t - a)
  have h2 : a * Real.exp (-a) ≤ 1 - Real.exp (-a) := mul_exp_neg_le_one_sub_exp_neg a
  have h4 : a * (Real.exp (-a) - Real.exp (-t)) ≤ (t - a) * (1 - Real.exp (-t)) := by
    have s1 : a * (Real.exp (-a) - Real.exp (-t))
        = a * Real.exp (-a) * (1 - Real.exp (-(t - a))) := by
      rw [hfac]
      ring
    have s2 : a * Real.exp (-a) * (1 - Real.exp (-(t - a)))
        ≤ a * Real.exp (-a) * (t - a) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    have s3 : a * Real.exp (-a) * (t - a) ≤ (1 - Real.exp (-a)) * (t - a) :=
      mul_le_mul_of_nonneg_right h2 (by linarith)
    have s4 : (1 - Real.exp (-a)) * (t - a) ≤ (1 - Real.exp (-t)) * (t - a) :=
      mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    nlinarith [s1, s2, s3, s4]
  rw [div_le_div_iff₀ hd ha]
  nlinarith [h4]

/-- Below `a` (and above `b`) the derivative of `t ↦ d(e^{-a} ‖ e^{-t})` is at least
`-(a-t)/b`.  This is the source's second-case bound. -/
lemma bkl_exp_neg_deriv_ge {a b t : ℝ} (hb : 0 < b) (hbt : b ≤ t) (hta : t ≤ a) :
    -((a - t) / b) ≤ (Real.exp (-a) - Real.exp (-t)) / (1 - Real.exp (-t)) := by
  have hd : (0 : ℝ) < 1 - Real.exp (-t) := by
    have hlt : Real.exp (-t) < 1 := by
      rw [Real.exp_lt_one_iff]
      linarith
    linarith
  have hmono : Real.exp (-t) ≤ Real.exp (-b) := by
    rw [Real.exp_le_exp]
    linarith
  have hfac : Real.exp (-t) - Real.exp (-a) = Real.exp (-t) * (1 - Real.exp (-(a - t))) :=
    exp_neg_sub_exp_neg t a
  have h1 : 1 - Real.exp (-(a - t)) ≤ a - t := one_sub_exp_neg_le (a - t)
  have h2 : b * Real.exp (-b) ≤ 1 - Real.exp (-b) := mul_exp_neg_le_one_sub_exp_neg b
  have hkey : (Real.exp (-t) - Real.exp (-a)) / (1 - Real.exp (-t)) ≤ (a - t) / b := by
    rw [div_le_div_iff₀ hd hb]
    have s1 : (Real.exp (-t) - Real.exp (-a)) * b
        = b * Real.exp (-t) * (1 - Real.exp (-(a - t))) := by
      rw [hfac]
      ring
    have s2 : b * Real.exp (-t) * (1 - Real.exp (-(a - t)))
        ≤ b * Real.exp (-t) * (a - t) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    have s3 : b * Real.exp (-t) * (a - t) ≤ b * Real.exp (-b) * (a - t) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hmono hb.le) (by linarith)
    have s4 : b * Real.exp (-b) * (a - t) ≤ (1 - Real.exp (-b)) * (a - t) :=
      mul_le_mul_of_nonneg_right h2 (by linarith)
    have s5 : (1 - Real.exp (-b)) * (a - t) ≤ (1 - Real.exp (-t)) * (a - t) :=
      mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    nlinarith [s1, s2, s3, s4, s5]
  have hneg : -((a - t) / b)
      ≤ -((Real.exp (-t) - Real.exp (-a)) / (1 - Real.exp (-t))) := neg_le_neg hkey
  have heq : -((Real.exp (-t) - Real.exp (-a)) / (1 - Real.exp (-t)))
      = (Real.exp (-a) - Real.exp (-t)) / (1 - Real.exp (-t)) := by
    ring
  rwa [heq] at hneg

/-! ### The two cases of the proof -/

/-- **First case of the source's proof** (`a ≤ b`): on `[a,b]` the function
`t ↦ d(e^{-a} ‖ e^{-t}) - (t-a)²/(2a)` is antitone, by the derivative bound
`bkl_exp_neg_deriv_le`; it vanishes at `t = a`. -/
theorem bkl_exp_neg_le_of_le {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    bkl (Real.exp (-a)) (Real.exp (-b)) ≤ (b - a) ^ 2 / (2 * a) := by
  have hp0 : 0 < Real.exp (-a) := Real.exp_pos _
  have hp1 : Real.exp (-a) < 1 := by
    rw [Real.exp_lt_one_iff]
    linarith
  have hpt : ∀ t ∈ Set.Ioo a b, HasDerivAt
      (fun s : ℝ => bkl (Real.exp (-a)) (Real.exp (-s)) - (s - a) * (s - a) / (2 * a))
      ((Real.exp (-a) - Real.exp (-t)) / (1 - Real.exp (-t)) - (t - a) / a) t := by
    intro t ht
    have ht0 : 0 < t := lt_trans ha ht.1
    have hb := hasDerivAt_bkl_exp_neg (p := Real.exp (-a)) hp0 hp1 ht0
    have hp : HasDerivAt (fun s : ℝ => (s - a) * (s - a) / (2 * a))
        ((t - a) / a) t := by
      have h1 : HasDerivAt (fun s : ℝ => s - a) 1 t := by
        simpa using (hasDerivAt_id t).sub_const a
      have hmul : HasDerivAt (fun s : ℝ => (s - a) * (s - a))
          ((t - a) + (t - a)) t := by
        have h := h1.mul h1
        convert h using 1
        ring
      have h3 := hmul.div_const (2 * a)
      have hval : ((t - a) + (t - a)) / (2 * a) = (t - a) / a := by
        field_simp
        ring
      rw [← hval]
      exact h3
    exact hb.sub hp
  have hanti : AntitoneOn
      (fun s : ℝ => bkl (Real.exp (-a)) (Real.exp (-s)) - (s - a) * (s - a) / (2 * a))
      (Set.Icc a b) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc a b) ?_ ?_ ?_
    · exact (continuousOn_bkl_exp_neg hp0 hp1 ha).sub (by fun_prop)
    · intro t ht
      rw [interior_Icc] at ht
      exact ((hpt t ht).differentiableAt).differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      rw [(hpt t ht).deriv]
      have h := bkl_exp_neg_deriv_le ha ht.1.le
      linarith
  have h := hanti (Set.mem_Icc.mpr ⟨le_rfl, hab⟩) (Set.mem_Icc.mpr ⟨hab, le_rfl⟩) hab
  have h' : bkl (Real.exp (-a)) (Real.exp (-b)) - (b - a) * (b - a) / (2 * a)
      ≤ bkl (Real.exp (-a)) (Real.exp (-a)) - (a - a) * (a - a) / (2 * a) := h
  have h0 : bkl (Real.exp (-a)) (Real.exp (-a)) - (a - a) * (a - a) / (2 * a) = 0 := by
    simp [bkl_self]
  rw [pow_two]
  nlinarith [h', h0]

/-- **Second case of the source's proof** (`b ≤ a`): on `[b,a]` the function
`t ↦ d(e^{-a} ‖ e^{-t}) + (a-t)²/(2b)` is monotone, by the derivative bound
`bkl_exp_neg_deriv_ge`; it vanishes at `t = a`. -/
theorem bkl_exp_neg_le_of_ge {a b : ℝ} (hb : 0 < b) (hba : b ≤ a) :
    bkl (Real.exp (-a)) (Real.exp (-b)) ≤ (a - b) ^ 2 / (2 * b) := by
  have hp0 : 0 < Real.exp (-a) := Real.exp_pos _
  have hp1 : Real.exp (-a) < 1 := by
    rw [Real.exp_lt_one_iff]
    linarith
  have hpt : ∀ t ∈ Set.Ioo b a, HasDerivAt
      (fun s : ℝ => bkl (Real.exp (-a)) (Real.exp (-s)) - (a - s) * (a - s) / (2 * b))
      ((Real.exp (-a) - Real.exp (-t)) / (1 - Real.exp (-t)) + (a - t) / b) t := by
    intro t ht
    have ht0 : 0 < t := lt_trans hb ht.1
    have hd := hasDerivAt_bkl_exp_neg (p := Real.exp (-a)) hp0 hp1 ht0
    have hp : HasDerivAt (fun s : ℝ => (a - s) * (a - s) / (2 * b))
        (-((a - t) / b)) t := by
      have h1 : HasDerivAt (fun s : ℝ => a - s) (-1) t := by
        simpa using (hasDerivAt_id t).const_sub a
      have hmul : HasDerivAt (fun s : ℝ => (a - s) * (a - s))
          (2 * (a - t) * (-1)) t := by
        have h := h1.mul h1
        convert h using 1
        ring
      have h3 := hmul.div_const (2 * b)
      have hval : 2 * (a - t) * (-1) / (2 * b) = -((a - t) / b) := by
        field_simp
      rw [← hval]
      exact h3
    have hsub := hd.sub hp
    have hval : (Real.exp (-a) - Real.exp (-t)) / (1 - Real.exp (-t)) - -((a - t) / b)
        = (Real.exp (-a) - Real.exp (-t)) / (1 - Real.exp (-t)) + (a - t) / b := by
      ring
    rw [hval] at hsub
    exact hsub
  have hmono : MonotoneOn
      (fun s : ℝ => bkl (Real.exp (-a)) (Real.exp (-s)) - (a - s) * (a - s) / (2 * b))
      (Set.Icc b a) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc b a) ?_ ?_ ?_
    · exact (continuousOn_bkl_exp_neg hp0 hp1 hb).sub (by fun_prop)
    · intro t ht
      rw [interior_Icc] at ht
      exact ((hpt t ht).differentiableAt).differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      rw [(hpt t ht).deriv]
      have h := bkl_exp_neg_deriv_ge hb ht.1.le ht.2.le
      linarith
  have h := hmono (Set.mem_Icc.mpr ⟨le_rfl, hba⟩) (Set.mem_Icc.mpr ⟨hba, le_rfl⟩) hba
  have h' : bkl (Real.exp (-a)) (Real.exp (-b)) - (a - b) * (a - b) / (2 * b)
      ≤ bkl (Real.exp (-a)) (Real.exp (-a)) - (a - a) * (a - a) / (2 * b) := h
  have h0 : bkl (Real.exp (-a)) (Real.exp (-a)) - (a - a) * (a - a) / (2 * b) = 0 := by
    simp [bkl_self]
  rw [pow_two]
  nlinarith [h', h0]

/-! ### Lemma 3.3 -/

/-- **The one-dimensional estimate behind Lemma 3.3**:
`d(e^{-a} ‖ e^{-b}) ≤ (a-b)²/(2 min{a,b})` for `a, b > 0`. -/
theorem bkl_exp_le {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    bkl (Real.exp (-a)) (Real.exp (-b)) ≤ (b - a) ^ 2 / (2 * min a b) := by
  rcases le_total a b with h | h
  · rw [min_eq_left h]
    exact bkl_exp_neg_le_of_le ha h
  · rw [min_eq_right h]
    have h1 := bkl_exp_neg_le_of_ge hb h
    have h2 : (a - b) ^ 2 = (b - a) ^ 2 := by ring
    rw [h2] at h1
    exact h1

/-- **Lemma 3.3 of [2106.06400]**, equation (3.4): for all `a, b > 0`,
`D_KL(Ber(1-e^{-a}) ‖ Ber(1-e^{-b})) = D_KL(Ber(e^{-a}) ‖ Ber(e^{-b}))`
`≤ |a-b|²/(2 min{a,b})`, the *upper* bound for the binary relative entropy at exponential
parameters that the relative-entropy proof of `thm:DM_Chi` runs on. -/
theorem bkl_one_sub_exp_le {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    bkl (1 - Real.exp (-a)) (1 - Real.exp (-b)) ≤ (b - a) ^ 2 / (2 * min a b) := by
  rw [bkl_one_sub]
  exact bkl_exp_le ha hb

/-! ### The per-edge form used by the model -/

section Model

variable {E : Type*} [Fintype E] [DecidableEq E]

omit [Fintype E] [DecidableEq E] in
/-- **Lemma 3.3 at the weighted model's one-edge parameters.**  For an edge of weight
`J e > 0` and intensities `0 < β₁ ≤ β₂`, the binary divergence of the open probabilities is
at most `(β₂-β₁)² J e/(2 β₁)`; this is the per-edge input of the finite relative-entropy
chain rule. -/
theorem bkl_openProb_le {J : E → ℝ} {β₁ β₂ : ℝ} {e : E} (hJ : 0 < J e)
    (hβ1 : 0 < β₁) (hβ12 : β₁ ≤ β₂) :
    bkl (openProb J β₂ e) (openProb J β₁ e) ≤ (β₂ - β₁) ^ 2 * J e / (2 * β₁) := by
  have hβ2 : 0 < β₂ := lt_of_lt_of_le hβ1 hβ12
  have h := bkl_one_sub_exp_le (a := β₂ * J e) (b := β₁ * J e)
    (by positivity) (by positivity)
  have hmin : min (β₂ * J e) (β₁ * J e) = β₁ * J e := by
    rw [min_eq_right]
    exact mul_le_mul_of_nonneg_right hβ12 hJ.le
  rw [hmin] at h
  have hval : (β₁ * J e - β₂ * J e) ^ 2 / (2 * (β₁ * J e))
      = (β₂ - β₁) ^ 2 * J e / (2 * β₁) := by
    field_simp
    ring
  simp only [openProb]
  rw [← hval]
  exact h

omit [Fintype E] [DecidableEq E] in
/-- The same per-edge estimate with the two intensities in the other order.  Because the bound
of Lemma 3.3 involves `min{a,b}`, it is symmetric in `a` and `b`, so both orientations of the
edge divergence (whichever one a transcript chain rule produces) are covered. -/
theorem bkl_openProb_le' {J : E → ℝ} {β₁ β₂ : ℝ} {e : E} (hJ : 0 < J e)
    (hβ2 : 0 < β₂) (hβ21 : β₂ ≤ β₁) :
    bkl (openProb J β₁ e) (openProb J β₂ e) ≤ (β₂ - β₁) ^ 2 * J e / (2 * β₂) := by
  have h := bkl_openProb_le (J := J) (β₁ := β₂) (β₂ := β₁) (e := e) hJ hβ2 hβ21
  have hsq : (β₁ - β₂) ^ 2 = (β₂ - β₁) ^ 2 := by ring
  rwa [hsq] at h

end Model

/-! ### A worked witness

At `a = log 2` and `b = log 4` the exponentials are `e^{-a} = 1/2` and `e^{-b} = 1/4`, so both
sides are explicit: the divergence is `½ log(4/3)`, and the bound is `½ log 2`, which is
strictly larger.  This shows that the statement is not vacuous and that its constant is not
oversized by a factor two at this point. -/

/-- `d(1/2 ‖ 3/4) = ½ log(4/3)`. -/
lemma bkl_half_three_quarters : bkl (1 / 2) (3 / 4) = Real.log (4 / 3) / 2 := by
  have h1 : (1 : ℝ) / 2 / (3 / 4) = 2 / 3 := by norm_num
  have h2 : (1 - (1 : ℝ) / 2) / (1 - 3 / 4) = 2 := by norm_num
  have h3 : Real.log ((2 : ℝ) / 3) + Real.log 2 = Real.log (4 / 3) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]
    norm_num
  simp only [bkl, h1, h2]
  linarith

/-- The instance of Lemma 3.3 at `a = log 2`, `b = log 4`. -/
theorem bkl_one_sub_exp_example_le :
    bkl (1 - Real.exp (-Real.log 2)) (1 - Real.exp (-Real.log 4))
      ≤ (Real.log 4 - Real.log 2) ^ 2 / (2 * min (Real.log 2) (Real.log 4)) :=
  bkl_one_sub_exp_le (Real.log_pos one_lt_two) (Real.log_pos (by norm_num))

/-- **The witness is strict**: at `a = log 2`, `b = log 4` the left-hand side is
`½ log(4/3)`, which is strictly less than the bound `½ log 2`. -/
theorem bkl_one_sub_exp_example_lt :
    bkl (1 - Real.exp (-Real.log 2)) (1 - Real.exp (-Real.log 4)) < Real.log 2 / 2 := by
  have h2 : Real.exp (-Real.log 2) = 1 / 2 := by
    rw [Real.exp_neg, Real.exp_log (by norm_num)]
    norm_num
  have h4 : Real.exp (-Real.log 4) = 1 / 4 := by
    rw [Real.exp_neg, Real.exp_log (by norm_num)]
    norm_num
  have hh : (1 : ℝ) - 1 / 2 = 1 / 2 := by norm_num
  have hq : (1 : ℝ) - 1 / 4 = 3 / 4 := by norm_num
  rw [h2, h4, hh, hq, bkl_half_three_quarters]
  have hlt : Real.log (4 / 3) < Real.log 2 := Real.log_lt_log (by norm_num) (by norm_num)
  linarith

/-- At the witness point the right-hand side of Lemma 3.3 is exactly `½ log 2`, matching
`bkl_one_sub_exp_example_lt`. -/
theorem bkl_one_sub_exp_example_rhs :
    (Real.log 4 - Real.log 2) ^ 2 / (2 * min (Real.log 2) (Real.log 4))
      = Real.log 2 / 2 := by
  have h2 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
    ring
  have hmin : min (Real.log 2) (Real.log 4) = Real.log 2 := by
    rw [min_eq_left]
    rw [h2]
    have := Real.log_pos one_lt_two
    linarith
  rw [hmin, h2]
  field_simp
  ring

/-- The divergence at the witness point is positive, so the inequality there is a genuine
comparison and not a degenerate `0 ≤ 0`. -/
theorem bkl_one_sub_exp_example_pos :
    0 < bkl (1 - Real.exp (-Real.log 2)) (1 - Real.exp (-Real.log 4)) := by
  have h2 : Real.exp (-Real.log 2) = 1 / 2 := by
    rw [Real.exp_neg, Real.exp_log (by norm_num)]
    norm_num
  have h4 : Real.exp (-Real.log 4) = 1 / 4 := by
    rw [Real.exp_neg, Real.exp_log (by norm_num)]
    norm_num
  have hh : (1 : ℝ) - 1 / 2 = 1 / 2 := by norm_num
  have hq : (1 : ℝ) - 1 / 4 = 3 / 4 := by norm_num
  rw [h2, h4, hh, hq, bkl_half_three_quarters]
  have := Real.log_pos (by norm_num : (1 : ℝ) < 4 / 3)
  linarith

end LRP

namespace LRP

set_option linter.hashCommand false in
#print axioms LRP.bkl_one_sub

set_option linter.hashCommand false in
#print axioms LRP.bkl_pos

set_option linter.hashCommand false in
#print axioms LRP.one_sub_exp_neg_le

set_option linter.hashCommand false in
#print axioms LRP.mul_exp_neg_le_one_sub_exp_neg

set_option linter.hashCommand false in
#print axioms LRP.exp_neg_div_one_sub_le

set_option linter.hashCommand false in
#print axioms LRP.exp_neg_sub_exp_neg

set_option linter.hashCommand false in
#print axioms LRP.hasDerivAt_exp_neg

set_option linter.hashCommand false in
#print axioms LRP.hasDerivAt_bkl_exp_neg

set_option linter.hashCommand false in
#print axioms LRP.continuousOn_bkl_exp_neg

set_option linter.hashCommand false in
#print axioms LRP.bkl_exp_neg_deriv_le

set_option linter.hashCommand false in
#print axioms LRP.bkl_exp_neg_deriv_ge

set_option linter.hashCommand false in
#print axioms LRP.bkl_exp_neg_le_of_le

set_option linter.hashCommand false in
#print axioms LRP.bkl_exp_neg_le_of_ge

set_option linter.hashCommand false in
#print axioms LRP.bkl_exp_le

set_option linter.hashCommand false in
#print axioms LRP.bkl_one_sub_exp_le

set_option linter.hashCommand false in
#print axioms LRP.bkl_openProb_le

set_option linter.hashCommand false in
#print axioms LRP.bkl_openProb_le'

set_option linter.hashCommand false in
#print axioms LRP.bkl_half_three_quarters

set_option linter.hashCommand false in
#print axioms LRP.bkl_one_sub_exp_example_le

set_option linter.hashCommand false in
#print axioms LRP.bkl_one_sub_exp_example_lt

set_option linter.hashCommand false in
#print axioms LRP.bkl_one_sub_exp_example_rhs

set_option linter.hashCommand false in
#print axioms LRP.bkl_one_sub_exp_example_pos

end LRP
