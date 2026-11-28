/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

# The marginal case of the source convolution (I.4.12) needs the logarithm

Source: Hutchcroft, *Critical long-range percolation I*, arXiv:2508.18807v1, proof of Lemma I.4.3,
p. 41.  The paper convolves two pointwise profiles: for `a, b > 0`, `â, b̂ ≥ 0` with
`|f x| ⪯ (1 + ‖x‖)^{-d+a} (log (2 + ‖x‖))^{-â}` and
`|g x| ⪯ (1 + ‖x‖)^{-d+b} (log (2 + ‖x‖))^{-b̂}` it proves
`|f * g (x)| ⪯ (1 + ‖x‖)^{-d+a+b} (log (2 + ‖x‖))^{-â-b̂}` when `a + b < d`, and
`|f * g (x)| ⪯ (log (2 + ‖x‖))^{-â-b̂+1}` when `a + b = d` **and `â + b̂ > 1`**.

The marginal alternative therefore carries the side condition `â + b̂ > 1`.  This file proves that
this side condition is not an artefact of the paper's region decomposition: in the log-free
marginal case `â = b̂ = 0`, `a + b = d`, the convolution of the two printed profiles does not
decay at all along the window `‖z‖ ≤ ‖x‖/2`, because that window already carries `≍ ‖x‖^d`
lattice points on which both profiles are `≍ ‖x‖^{-d}`.

The percolation reading is the Case-3 pair at the doubly marginal point `d = 6`, `α = 2`.  There
`τ(x) ⪯ (1 + ‖x‖)^{-4} (log (2 + ‖x‖))^{-1}` is the printed display of (HD)(3),
i.e. `a = 2`,
`â = 1`.  The second fold `τ * τ` has `a + b = 4 < d` and is covered by the *strict* alternative.
The third fold `∇ = τ * τ * τ` is exactly marginal, `a + b = 6 = d`, and there `τ * τ`
contributes
`â = 2` while `τ` contributes `b̂ = 1`, so `â + b̂ = 3 > 1` and the paper's rule returns the
`(log)^{-2}` of (I.4.13).  If instead only the log-free display of Case 2 at the same exponents is
available, then the marginal pair carries `â = b̂ = 0`, and by the theorem below the third fold
does not decay at all: the `(log)^{-2}` of (I.4.13) is then unreachable, not merely unproved.  The
printed `(log)^{-1}` of (HD)(3) is therefore exactly what makes the marginal stage applicable.

This does not refute (I.4.12): in the marginal case with `â + b̂ = 0` the paper's own conclusion
is `(log)^{+1}`, i.e. no decay, and the lower bound below is consistent with it.  What is proved is
that the side condition `â + b̂ > 1` cannot be weakened: no argument within this profile class can
recover a decaying bound at `â + b̂ = 0`.

Nothing here is a percolation estimate.  The statements concern the printed profiles on the
model's own normalized lattice `M.V = ℤ^d` with the source norm `M.S.ρ`, and they use only the
normalization `(∗)` through `SourceModelData.ball_count` (Lemma I.4.6).  No bound on `τ` is
assumed and no lace-expansion input is used.
-/
module

public import PercLib.CriticalLRP.Analysis.SecondMomentCase3.TriangleFromHD.Pointwise
public import PercLib.CriticalLRP.Analysis.BallRatioLogError

/-! Explicit normalized-lattice profiles and a sharp non-decay example at the
log-free marginal exponent; no percolation two-point estimate is supplied. -/

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.hashCommand false

@[expose] public section

noncomputable section

open Filter Set Asymptotics
open scoped BigOperators NNReal ENNReal Topology

namespace PercLib.CriticalLRP
namespace Orchestration

namespace SourceModelData

variable (M : SourceModelData)

/-! ## §1 The two printed log-free marginal profiles and their windowed convolution -/

/-- The source profile `(1 + ‖z‖)^{-d+a}` with `a = 2`, written as the reciprocal power
`1 / (1 + ‖z‖)^(d - 2)`. -/
def logFreeMarginalF (z : M.V) : ℝ := ((1 + M.S.ρ (toVec z)) ^ (M.d - 2))⁻¹

/-- The source profile `(1 + ‖z‖)^{-d+b}` with `b = d - 2`, written as `1 / (1 + ‖z‖)^2`. -/
def logFreeMarginalG (z : M.V) : ℝ := ((1 + M.S.ρ (toVec z)) ^ 2)⁻¹

/-- The windowed convolution `f * g` of the two log-free marginal profiles, restricted to
`{z : ‖z‖ ≤ ‖x‖ / 2}`. -/
def logFreeMarginalConv (x : M.V) : ℝ :=
  ∑ z ∈ (M.finite_ball (M.S.ρ (toVec x) / 2)).toFinset,
    M.logFreeMarginalF z * M.logFreeMarginalG (x - z)

theorem logFreeMarginalF_nonneg (z : M.V) : 0 ≤ M.logFreeMarginalF z :=
  inv_nonneg.mpr (pow_nonneg (by have h := M.sρ_nonneg z; linarith) _)

theorem logFreeMarginalG_nonneg (z : M.V) : 0 ≤ M.logFreeMarginalG z :=
  inv_nonneg.mpr (pow_nonneg (by have h := M.sρ_nonneg z; linarith) _)

/-- `logFreeMarginalF` is the paper's profile `(1 + ‖z‖)^{-d+a}` with `a = 2`. -/
theorem logFreeMarginalF_eq_rpow (hd2 : 2 ≤ M.d) (z : M.V) :
    M.logFreeMarginalF z = (1 + M.S.ρ (toVec z)) ^ (-((M.d : ℝ) - 2)) := by
  have h0 : (0 : ℝ) < 1 + M.S.ρ (toVec z) := by
    have h := M.sρ_nonneg z
    linarith
  have hcast : ((M.d - 2 : ℕ) : ℝ) = (M.d : ℝ) - 2 := by
    rw [Nat.cast_sub hd2]
    norm_num
  rw [logFreeMarginalF, ← Real.rpow_natCast (1 + M.S.ρ (toVec z)) (M.d - 2),
    Real.rpow_neg h0.le, hcast]

/-- `logFreeMarginalG` is the paper's log-free profile `(1 + ‖z‖)^{-2}`, i.e. `b = d - 2`. -/
theorem logFreeMarginalG_eq_rpow (z : M.V) :
    M.logFreeMarginalG z = (1 + M.S.ρ (toVec z)) ^ (-(2 : ℝ)) := by
  have h0 : (0 : ℝ) < 1 + M.S.ρ (toVec z) := by
    have h := M.sρ_nonneg z
    linarith
  rw [logFreeMarginalG, ← Real.rpow_natCast (1 + M.S.ρ (toVec z)) 2, Real.rpow_neg h0.le]
  norm_num

/-- **The exponents are the marginal ones**: `a = 2` and `b = d - 2` add up to `d`. -/
theorem logFreeMarginal_exponents (hd2 : 2 ≤ M.d) : 2 + (M.d - 2) = M.d :=
  Nat.add_sub_cancel' hd2

/-! ## §2 The lattice is unbounded in the source norm -/

/-- For every radius there is a lattice point outside it. -/
theorem exists_sρ_ge (R : ℝ) : ∃ x : M.V, R ≤ M.S.ρ (toVec x) := by
  classical
  set i₀ : Fin M.d := ⟨0, M.hd⟩ with hi₀
  set e : M.V := fun i => if i = i₀ then (1 : ℤ) else 0 with he
  have hene : e ≠ 0 := by
    intro h
    have h0 : e i₀ = (0 : ℤ) := by rw [h]; rfl
    simp [he] at h0
  have hpos : 0 < M.S.ρ (toVec e) := M.S.ρ_pos _ (by
    intro hc
    refine hene (funext fun i => ?_)
    have hi : ((e i : ℤ) : ℝ) = 0 := by
      have := congrFun hc i
      simpa [toVec] using this
    exact_mod_cast hi)
  obtain ⟨N, hN⟩ := exists_nat_gt (R / M.S.ρ (toVec e))
  refine ⟨fun i => (N : ℤ) * e i, ?_⟩
  have hvec : toVec (fun i => (N : ℤ) * e i) = (N : ℝ) • toVec e := by
    funext i
    simp [toVec]
  rw [hvec, M.S.ρ_smul]
  have hNR : R / M.S.ρ (toVec e) ≤ (N : ℝ) := le_of_lt hN
  have hNR' : R ≤ (N : ℝ) * M.S.ρ (toVec e) := by
    rw [div_le_iff₀ hpos] at hNR
    linarith
  calc R ≤ (N : ℝ) * M.S.ρ (toVec e) := hNR'
    _ = |(N : ℝ)| * M.S.ρ (toVec e) := by rw [Nat.abs_cast]

/-! ## §3 The normalized ball count gives a positive lower comparison (Lemma I.4.6) -/

/-- **A positive lower comparison for the normalized ball count.**  From
`SourceModelData.ball_count` (Lemma I.4.6), eventually `#B_r ≥ c r^d`. -/
theorem exists_ball_ncard_lower :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∀ r : ℝ, R₀ ≤ r →
      c₀ * r ^ M.d ≤ ((M.ball r).ncard : ℝ) := by
  obtain ⟨C₁, hC₁⟩ := M.ball_count.symm.isBigO.bound
  obtain ⟨r₀, hr₀⟩ := Filter.eventually_atTop.1 hC₁
  have hCpos : (0 : ℝ) < max C₁ 0 + 1 := by linarith [le_max_right C₁ 0]
  refine ⟨(max C₁ 0 + 1)⁻¹, inv_pos.mpr hCpos, max r₀ 1, le_max_right _ _,
    fun r hr => ?_⟩
  have hr₀r : r₀ ≤ r := le_trans (le_max_left _ _) hr
  have hr0 : (0 : ℝ) ≤ r :=
    le_trans (le_trans (by norm_num : (0 : ℝ) ≤ 1) (le_max_right _ _)) hr
  have hle := hr₀ r hr₀r
  rw [Real.norm_of_nonneg (pow_nonneg hr0 _), Real.norm_of_nonneg (Nat.cast_nonneg _)] at hle
  have hbig : r ^ M.d ≤ (max C₁ 0 + 1) * ((M.ball r).ncard : ℝ) := by
    refine le_trans hle (mul_le_mul_of_nonneg_right ?_ (by positivity))
    linarith [le_max_left C₁ 0]
  have hstep : (max C₁ 0 + 1)⁻¹ * r ^ M.d
      ≤ (max C₁ 0 + 1)⁻¹ * ((max C₁ 0 + 1) * ((M.ball r).ncard : ℝ)) :=
    mul_le_mul_of_nonneg_left hbig (by positivity)
  have hcancel : (max C₁ 0 + 1)⁻¹ * ((max C₁ 0 + 1) * ((M.ball r).ncard : ℝ))
      = ((M.ball r).ncard : ℝ) := by
    field_simp
  rw [hcancel] at hstep
  exact hstep

/-! ## §4 The termwise bound on the window `‖z‖ ≤ ‖x‖ / 2` -/

/-- **The marginal term bound.**  On the window `‖z‖ ≤ ‖x‖/2` with `‖x‖ = s ≥ 2`, the product
of the two log-free profiles is at least `(9 s^d)⁻¹`. -/
theorem logFreeMarginal_term_ge (hd2 : 2 ≤ M.d) {x z : M.V}
    (hs : 2 ≤ M.S.ρ (toVec x)) (hz : M.S.ρ (toVec z) ≤ M.S.ρ (toVec x) / 2) :
    (9 * (M.S.ρ (toVec x)) ^ M.d)⁻¹ ≤ M.logFreeMarginalF z * M.logFreeMarginalG (x - z) := by
  set s : ℝ := M.S.ρ (toVec x) with hsd
  set a : ℝ := M.S.ρ (toVec z) with had
  have hs0 : 0 < s := by linarith
  have ha0 : 0 ≤ a := M.sρ_nonneg z
  have hb0 : 0 ≤ M.S.ρ (toVec (x - z)) := M.sρ_nonneg (x - z)
  have hb : M.S.ρ (toVec (x - z)) ≤ s + a := by
    have hsub : toVec (x - z) = toVec x - toVec z := toVec_sub x z
    rw [hsub, sub_eq_add_neg]
    have h := M.S.ρ_add_le (toVec x) (-(toVec z))
    rw [M.S.ρ_neg] at h
    exact h
  have h1le : 1 + a ≤ s := by
    have : a ≤ s / 2 := hz
    linarith
  have h1pos : (0 : ℝ) < (1 + a) ^ (M.d - 2) := pow_pos (by linarith) _
  have h1 : (s ^ (M.d - 2))⁻¹ ≤ ((1 + a) ^ (M.d - 2))⁻¹ := by
    rw [← one_div, ← one_div]
    exact one_div_le_one_div_of_le h1pos (pow_le_pow_left₀ (by linarith) h1le _)
  have h2le : 1 + M.S.ρ (toVec (x - z)) ≤ 3 * s := by linarith
  have h2pos : (0 : ℝ) < (1 + M.S.ρ (toVec (x - z))) ^ 2 := pow_pos (by linarith) 2
  have h2 : ((3 * s) ^ 2)⁻¹ ≤ ((1 + M.S.ρ (toVec (x - z))) ^ 2)⁻¹ := by
    rw [← one_div, ← one_div]
    exact one_div_le_one_div_of_le h2pos (pow_le_pow_left₀ (by linarith) h2le 2)
  have hkey : (s ^ (M.d - 2))⁻¹ * ((3 * s) ^ 2)⁻¹
      ≤ M.logFreeMarginalF z * M.logFreeMarginalG (x - z) :=
    mul_le_mul h1 h2 (by positivity) (inv_nonneg.mpr (pow_nonneg (by linarith) _))
  have hpow : s ^ (M.d - 2) * s ^ 2 = s ^ M.d := by
    rw [← pow_add, Nat.sub_add_cancel hd2]
  have hval : (s ^ (M.d - 2))⁻¹ * ((3 * s) ^ 2)⁻¹ = (9 * s ^ M.d)⁻¹ := by
    rw [← mul_inv]
    congr 1
    have h3 : (3 * s) ^ 2 = 9 * s ^ 2 := by ring
    rw [h3, ← hpow]
    ring
  rw [hval] at hkey
  exact hkey

/-! ## §5 The windowed convolution does not decay -/

/-- **The windowed marginal convolution is bounded below by a positive constant.** -/
theorem logFreeMarginalConv_ge (hd2 : 2 ≤ M.d) {c₀ R₀ : ℝ} (hc₀ : 0 < c₀)
    (hR₀ : 1 ≤ R₀)
    (hcard : ∀ r : ℝ, R₀ ≤ r → c₀ * r ^ M.d ≤ ((M.ball r).ncard : ℝ))
    {x : M.V} (hs : 2 * R₀ + 2 ≤ M.S.ρ (toVec x)) :
    c₀ * (9 * (2 : ℝ) ^ M.d)⁻¹ ≤ M.logFreeMarginalConv x := by
  set s : ℝ := M.S.ρ (toVec x) with hsd
  have hR₀pos : 0 < R₀ := by linarith
  have hs0 : 0 < s := by linarith
  have hs2 : 2 ≤ s := by linarith
  have hhalf : R₀ ≤ s / 2 := by linarith
  have hcard' : c₀ * (s / 2) ^ M.d
      ≤ (((M.finite_ball (s / 2)).toFinset.card : ℕ) : ℝ) := by
    have h := hcard (s / 2) hhalf
    rwa [Set.ncard_eq_toFinset_card (M.ball (s / 2)) (M.finite_ball (s / 2))] at h
  have hterm : ∀ z ∈ (M.finite_ball (s / 2)).toFinset,
      (9 * s ^ M.d)⁻¹ ≤ M.logFreeMarginalF z * M.logFreeMarginalG (x - z) := by
    intro z hz
    have hz' : M.S.ρ (toVec z) ≤ s / 2 := by
      have hmem := (M.finite_ball (s / 2)).mem_toFinset.mp hz
      simpa [ball, hsd] using hmem
    exact logFreeMarginal_term_ge M hd2 (by simpa [hsd] using hs2) hz'
  have hsum : (((M.finite_ball (s / 2)).toFinset.card : ℕ) : ℝ) * (9 * s ^ M.d)⁻¹
      ≤ M.logFreeMarginalConv x := by
    have h1 : ∑ z ∈ (M.finite_ball (s / 2)).toFinset, (9 * s ^ M.d)⁻¹
        ≤ M.logFreeMarginalConv x := by
      rw [logFreeMarginalConv]
      exact Finset.sum_le_sum fun z hz => hterm z hz
    have h2 : ∑ z ∈ (M.finite_ball (s / 2)).toFinset, (9 * s ^ M.d)⁻¹
        = (((M.finite_ball (s / 2)).toFinset.card : ℕ) : ℝ) * (9 * s ^ M.d)⁻¹ := by
      rw [Finset.sum_const, nsmul_eq_mul]
    rw [h2] at h1
    exact h1
  refine le_trans ?_ hsum
  have hstep : c₀ * (9 * (2 : ℝ) ^ M.d)⁻¹
      = (c₀ * (s / 2) ^ M.d) * (9 * s ^ M.d)⁻¹ := by
    have hsp : s ^ M.d ≠ 0 := by positivity
    rw [div_pow]
    field_simp
  rw [hstep]
  exact mul_le_mul_of_nonneg_right hcard' (by positivity)

/-- **Existence form: the windowed log-free marginal convolution stays bounded away from zero
along the lattice.** -/
theorem exists_pos_le_logFreeMarginalConv (hd2 : 2 ≤ M.d) :
    ∃ c : ℝ, 0 < c ∧ ∀ R : ℝ, ∃ x : M.V,
      R ≤ M.S.ρ (toVec x) ∧ c ≤ M.logFreeMarginalConv x := by
  obtain ⟨c₀, hc₀, R₀, hR₀, hcard⟩ := M.exists_ball_ncard_lower
  refine ⟨c₀ * (9 * (2 : ℝ) ^ M.d)⁻¹, by positivity, fun R => ?_⟩
  obtain ⟨x, hx⟩ := M.exists_sρ_ge (max R (2 * R₀ + 2))
  exact ⟨x, le_trans (le_max_left _ _) hx,
    M.logFreeMarginalConv_ge hd2 hc₀ hR₀ hcard (le_trans (le_max_right _ _) hx)⟩

/-- **The log-free marginal convolution cannot be bounded by the decaying profile
`(1 + ‖x‖)^{-d}`.** -/
theorem not_bdd_by_logFreeMarginal_decay (hd2 : 2 ≤ M.d) :
    ¬ ∃ C : ℝ, 0 < C ∧ ∀ x : M.V,
      M.logFreeMarginalConv x ≤ C * ((1 + M.S.ρ (toVec x)) ^ M.d)⁻¹ := by
  intro ⟨C, hC, hbound⟩
  obtain ⟨c, hc, hconv⟩ := M.exists_pos_le_logFreeMarginalConv hd2
  obtain ⟨x, hx, hconvx⟩ := hconv (max 2 (2 * C / c + 1))
  have hs2 : 2 ≤ M.S.ρ (toVec x) := le_trans (le_max_left _ _) hx
  have hbig : 2 * C / c ≤ M.S.ρ (toVec x) := by
    have := le_trans (le_max_right _ _) hx
    linarith
  have hboundx := hbound x
  have h1s : 1 + M.S.ρ (toVec x) ≤ (1 + M.S.ρ (toVec x)) ^ M.d := by
    calc 1 + M.S.ρ (toVec x) = (1 + M.S.ρ (toVec x)) ^ 1 := (pow_one _).symm
      _ ≤ (1 + M.S.ρ (toVec x)) ^ M.d := pow_le_pow_right₀ (by linarith) M.hd
  have hge : 2 * C / c ≤ (1 + M.S.ρ (toVec x)) ^ M.d := le_trans hbig (by linarith)
  have hinv : ((1 + M.S.ρ (toVec x)) ^ M.d)⁻¹ ≤ c / (2 * C) := by
    have hp : (0 : ℝ) < (1 + M.S.ρ (toVec x)) ^ M.d :=
      pow_pos (by have h := M.sρ_nonneg x; linarith) _
    have h2C : (0 : ℝ) < 2 * C := by linarith
    have hge' : 2 * C ≤ c * (1 + M.S.ρ (toVec x)) ^ M.d := by
      have h := mul_le_mul_of_nonneg_left hge hc.le
      rwa [mul_div_cancel₀ _ (ne_of_gt hc)] at h
    rw [le_div_iff₀ h2C]
    calc ((1 + M.S.ρ (toVec x)) ^ M.d)⁻¹ * (2 * C)
        = 2 * C / (1 + M.S.ρ (toVec x)) ^ M.d := by
          rw [div_eq_mul_inv]; ring
      _ ≤ c := by
          rw [div_le_iff₀ hp]
          exact hge'
  have hfin : C * ((1 + M.S.ρ (toVec x)) ^ M.d)⁻¹ ≤ c / 2 := by
    calc C * ((1 + M.S.ρ (toVec x)) ^ M.d)⁻¹ ≤ C * (c / (2 * C)) :=
          mul_le_mul_of_nonneg_left hinv hC.le
      _ = c / 2 := by field_simp
  linarith [hconvx, hboundx]

/-- **The unrestricted lattice convolution does not decay either.**  The windowed lower bound is a
lower bound for the full `ℝ≥0∞` lattice sum, so the two-point convolution of the two log-free
marginal profiles stays at least `c` at arbitrarily large `‖x‖`. -/
theorem exists_pos_le_tsum_logFreeMarginal (hd2 : 2 ≤ M.d) :
    ∃ c : ℝ, 0 < c ∧ ∀ R : ℝ, ∃ x : M.V, R ≤ M.S.ρ (toVec x) ∧
      ENNReal.ofReal c ≤
        ∑' z : M.V, ENNReal.ofReal (M.logFreeMarginalF z * M.logFreeMarginalG (x - z)) := by
  obtain ⟨c, hc, hconv⟩ := M.exists_pos_le_logFreeMarginalConv hd2
  refine ⟨c, hc, fun R => ?_⟩
  obtain ⟨x, hxR, hcx⟩ := hconv R
  refine ⟨x, hxR, ?_⟩
  have hwin : ENNReal.ofReal c ≤
      ∑ z ∈ (M.finite_ball (M.S.ρ (toVec x) / 2)).toFinset,
        ENNReal.ofReal (M.logFreeMarginalF z * M.logFreeMarginalG (x - z)) := by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun z _ =>
      mul_nonneg (M.logFreeMarginalF_nonneg z) (M.logFreeMarginalG_nonneg (x - z)))]
    exact ENNReal.ofReal_le_ofReal hcx
  exact le_trans hwin (ENNReal.sum_le_tsum _)

/-- **At the doubly marginal dimension `d = 6` the log-free marginal pair has no
`(1 + ‖x‖)^{-6}` majorant**, matching the printed power of (HD)(3) at `d = 6`. -/
theorem not_bdd_by_six_rpow (hd6 : M.d = 6) :
    ¬ ∃ C : ℝ, 0 < C ∧ ∀ x : M.V,
      M.logFreeMarginalConv x ≤ C * (1 + M.S.ρ (toVec x)) ^ (-(6 : ℝ)) := by
  intro ⟨C, hC, hbound⟩
  have hd2 : 2 ≤ M.d := by omega
  refine M.not_bdd_by_logFreeMarginal_decay hd2 ⟨C, hC, fun x => ?_⟩
  have h0 : (0 : ℝ) < 1 + M.S.ρ (toVec x) := by
    have h := M.sρ_nonneg x
    linarith
  have hd6R : (M.d : ℝ) = 6 := by exact_mod_cast hd6
  have hpow : ((1 + M.S.ρ (toVec x)) ^ M.d)⁻¹ = (1 + M.S.ρ (toVec x)) ^ (-(6 : ℝ)) := by
    rw [← Real.rpow_natCast (1 + M.S.ρ (toVec x)) M.d, ← Real.rpow_neg h0.le, hd6R]
  rw [hpow]
  exact hbound x

end SourceModelData

/-! ## Axiom audit -/

#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.logFreeMarginal_term_ge
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.logFreeMarginalConv_ge
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.exists_pos_le_logFreeMarginalConv
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.not_bdd_by_logFreeMarginal_decay
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.exists_pos_le_tsum_logFreeMarginal
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.not_bdd_by_six_rpow

end Orchestration
end PercLib.CriticalLRP
