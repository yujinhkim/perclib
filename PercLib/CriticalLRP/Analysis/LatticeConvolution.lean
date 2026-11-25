/-
Lemma I.4.3, analytic core: convolution tail bounds with logarithmic corrections.

Source: arXiv:2508.18807v1, Lemma I.4.3 (p. 35) and its proof: the two convolution
estimates (I.4.11) and (I.4.12) obtained from the `A1/A2/A3` region split.

This file is self-contained (`module

public import PercLib.CriticalLRP.Analysis.LatticeConvolution.Defs`) and is a candidate for
`PercLib/CriticalLRP/Analysis/LatticeConvolution.lean`.
-/
module

public import PercLib.CriticalLRP.Analysis.LatticeConvolution.Defs

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section

namespace CriticalLRPConv

open scoped Topology
open Filter

/-! ## §1 The logarithmic profile `Λ x = log (2 + ρ x)` -/

variable {G : Type*} [AddCommGroup G] {ρ : G → ℝ}

lemma Lam_def {x : G} : Lam ρ x = Real.log (2 + ρ x) := rfl

lemma two_add_pos (hρnn : ∀ x, 0 ≤ ρ x) (x : G) : (0 : ℝ) < 2 + ρ x := by
  have := hρnn x; linarith

lemma Lam_pos (hρnn : ∀ x, 0 ≤ ρ x) (x : G) : 0 < Lam ρ x := by
  have h3 : (1 : ℝ) < 2 + ρ x := by linarith [hρnn x]
  exact Real.log_pos h3

lemma Lam_mono (hρnn : ∀ x, 0 ≤ ρ x) {x y : G} (h : ρ x ≤ ρ y) : Lam ρ x ≤ Lam ρ y := by
  exact Real.log_le_log (two_add_pos hρnn x) (by linarith)

/-- A comparison of logarithmic profiles at radii that differ by at most a factor `2`. -/
lemma Lam_le_two_mul (hρnn : ∀ x, 0 ≤ ρ x) {x y : G} (h : ρ x ≤ 2 * ρ y) :
    Lam ρ x ≤ 2 * Lam ρ y := by
  have hy : (0 : ℝ) < 2 + ρ y := two_add_pos hρnn y
  have hy' : (0:ℝ) ≤ ρ y := hρnn y
  have h1 : Lam ρ x ≤ Real.log (2 * (2 + ρ y)) := by
    rw [Lam_def]
    apply Real.log_le_log (two_add_pos hρnn x)
    linarith
  have h2 : Real.log (2 * (2 + ρ y)) = Real.log 2 + Real.log (2 + ρ y) := by
    rw [Real.log_mul (by norm_num) (ne_of_gt hy)]
  have hlog2 : Real.log 2 ≤ Real.log (2 + ρ y) :=
    Real.log_le_log (by norm_num) (by linarith)
  rw [h2] at h1
  simp only [Lam_def] at h1 ⊢
  linarith

/-- For `z ≤ 0`, the profile `s ↦ (1+s)^z` is antitone. -/
lemma rpow_one_add_le_of_le (hρnn : ∀ x, 0 ≤ ρ x) {e : ℝ} (he : e ≤ 0) {x y : G}
    (h : ρ x ≤ ρ y) : (1 + ρ y) ^ e ≤ (1 + ρ x) ^ e := by
  have hx : (0 : ℝ) < 1 + ρ x := by linarith [hρnn x]
  exact Real.rpow_le_rpow_of_nonpos hx (by linarith) he

/-- The doubled-radius loss in the power profile: if `ρ x ≤ 2 ρ y` then the profile at `y`
dominates (up to `2^{-e}`) the profile at `x`. -/
lemma rpow_one_add_le_mul (hρnn : ∀ x, 0 ≤ ρ x) {e : ℝ} (he : e ≤ 0) {x y : G}
    (h : ρ x ≤ 2 * ρ y) : (1 + ρ y) ^ e ≤ 2 ^ (-e) * (1 + ρ x) ^ e := by
  have hx : (0 : ℝ) < 1 + ρ x := by linarith [hρnn x]
  have hstep : (1 + ρ y) ^ e ≤ (1 + ρ x / 2) ^ e := by
    have hx2 : (0 : ℝ) < 1 + ρ x / 2 := by linarith [hρnn x]
    exact Real.rpow_le_rpow_of_nonpos hx2 (by linarith) he
  have hhalf : (1 + ρ x / 2) ^ e ≤ 2 ^ (-e) * (1 + ρ x) ^ e := by
    have h2 : (1 + ρ x / 2) ^ e ≤ ((1 + ρ x) / 2) ^ e := by
      have hpos : (0 : ℝ) < (1 + ρ x) / 2 := by linarith
      exact Real.rpow_le_rpow_of_nonpos hpos (by linarith) he
    have h3 : ((1 + ρ x) / 2) ^ e = 2 ^ (-e) * (1 + ρ x) ^ e := by
      rw [Real.div_rpow (le_of_lt hx) (by norm_num : (0:ℝ) ≤ 2),
        Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
      ring
    rw [h3] at h2
    exact h2
  exact hstep.trans hhalf

/-! ## §2 Gap inequalities for real powers, via the mean value theorem -/

/-- Mean value form of the derivative of `x ↦ x ^ θ` on a positive interval. -/
lemma exists_rpow_slope {θ : ℝ} (_hθ : θ ≠ 0) {x y : ℝ} (hx : 0 < x) (hxy : x < y) :
    ∃ c ∈ Set.Ioo x y, y ^ θ - x ^ θ = θ * c ^ (θ - 1) * (y - x) := by
  have hcont : ContinuousOn (fun t : ℝ => t ^ θ) (Set.Icc x y) := by
    intro t ht
    exact (Real.hasDerivAt_rpow_const
      (Or.inl (ne_of_gt (lt_of_lt_of_le hx ht.1)))).continuousAt.continuousWithinAt
  have hderiv : ∀ t ∈ Set.Ioo x y,
      HasDerivAt (fun t : ℝ => t ^ θ) (θ * t ^ (θ - 1)) t := by
    intro t ht
    exact Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt (lt_trans hx (Set.mem_Ioo.mp ht).1)))
  obtain ⟨c, hc, hslope⟩ :=
    exists_hasDerivAt_eq_slope (fun t : ℝ => t ^ θ) (fun t => θ * t ^ (θ - 1)) hxy hcont hderiv
  refine ⟨c, hc, ?_⟩
  have h := (eq_div_iff (by linarith : (y - x) ≠ 0)).mp hslope
  exact h.symm

/-- For `θ > 0`, `0 < x < y`: `y^θ - x^θ` is at least `θ · y^{θ-1} · (y-x)` when `θ ≤ 1`. -/
lemma rpow_sub_ge_of_small {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1) {x y : ℝ} (hx : 0 < x) (hxy : x < y) :
    θ * y ^ (θ - 1) * (y - x) ≤ y ^ θ - x ^ θ := by
  obtain ⟨c, hc, heq⟩ := exists_rpow_slope (ne_of_gt hθ) hx hxy
  have hcx : 0 < c := lt_trans hx hc.1
  have hcy : c < y := hc.2
  have h1 : c ^ (θ - 1) ≥ y ^ (θ - 1) := by
    refine Real.rpow_le_rpow_of_nonpos hcx (le_of_lt hcy) ?_
    linarith
  have : θ * c ^ (θ - 1) * (y - x) ≥ θ * y ^ (θ - 1) * (y - x) := by
    have hyx : (0:ℝ) ≤ y - x := by linarith
    have hle : θ * y ^ (θ - 1) ≤ θ * c ^ (θ - 1) := by
      exact mul_le_mul_of_nonneg_left h1 (le_of_lt hθ)
    exact mul_le_mul_of_nonneg_right hle hyx
  linarith [heq]

/-- For `θ ≥ 1`, `0 < x < y`: `y^θ - x^θ ≥ θ · x^{θ-1} · (y-x)`. -/
lemma rpow_sub_ge_of_large {θ : ℝ} (hθ : 1 ≤ θ) {x y : ℝ} (hx : 0 < x) (hxy : x < y) :
    θ * x ^ (θ - 1) * (y - x) ≤ y ^ θ - x ^ θ := by
  obtain ⟨c, hc, heq⟩ := exists_rpow_slope (by linarith : θ ≠ 0) hx hxy
  have hcx : 0 < c := lt_trans hx hc.1
  have hcxy : x < c := hc.1
  have h1 : c ^ (θ - 1) ≥ x ^ (θ - 1) := by
    have h0 : (0:ℝ) ≤ θ - 1 := by linarith
    exact Real.rpow_le_rpow (le_of_lt hx) (le_of_lt hcxy) h0
  have : θ * c ^ (θ - 1) * (y - x) ≥ θ * x ^ (θ - 1) * (y - x) := by
    have hyx : (0:ℝ) ≤ y - x := by linarith
    have hle : θ * x ^ (θ - 1) ≤ θ * c ^ (θ - 1) := by
      exact mul_le_mul_of_nonneg_left h1 (by linarith)
    exact mul_le_mul_of_nonneg_right hle hyx
  linarith [heq]

/-- For `θ < 0`, `0 < x < y`: `x^θ - y^θ ≥ (-θ) · y^{θ-1} · (y-x)`. -/
lemma rpow_sub_ge_of_neg {θ : ℝ} (hθ : θ < 0) {x y : ℝ} (hx : 0 < x) (hxy : x < y) :
    (-θ) * y ^ (θ - 1) * (y - x) ≤ x ^ θ - y ^ θ := by
  obtain ⟨c, hc, heq⟩ := exists_rpow_slope (ne_of_lt hθ) hx hxy
  have hcx : 0 < c := lt_trans hx hc.1
  have h1 : c ^ (θ - 1) ≥ y ^ (θ - 1) := by
    refine Real.rpow_le_rpow_of_nonpos hcx (le_of_lt hc.2) ?_
    linarith
  have h2 : θ * y ^ (θ - 1) * (y - x) ≥ θ * c ^ (θ - 1) * (y - x) := by
    have hyx : (0:ℝ) ≤ y - x := by linarith
    have hle : θ * c ^ (θ - 1) ≤ θ * y ^ (θ - 1) := by
      have := mul_le_mul_of_nonneg_left h1 (le_of_lt hcx)
      nlinarith
    exact mul_le_mul_of_nonneg_right hle hyx
  have : y ^ θ - x ^ θ ≤ θ * y ^ (θ - 1) * (y - x) := by linarith [heq]
  linarith

/-- For `θ < 0`, `0 < x < y`: `x^θ - y^θ ≤ (-θ) · x^{θ-1} · (y-x)`. -/
lemma rpow_sub_le_of_neg {θ : ℝ} (hθ : θ < 0) {x y : ℝ} (hx : 0 < x) (hxy : x < y) :
    x ^ θ - y ^ θ ≤ (-θ) * x ^ (θ - 1) * (y - x) := by
  obtain ⟨c, hc, heq⟩ := exists_rpow_slope (ne_of_lt hθ) hx hxy
  have hcx : 0 < c := lt_trans hx hc.1
  have h1 : c ^ (θ - 1) ≤ x ^ (θ - 1) := by
    refine Real.rpow_le_rpow_of_nonpos hx (le_of_lt hc.1) ?_
    linarith
  have h2 : θ * x ^ (θ - 1) ≤ θ * c ^ (θ - 1) := mul_le_mul_of_nonpos_left h1 (le_of_lt hθ)
  have hyx : (0:ℝ) ≤ y - x := by linarith
  have h3 : θ * x ^ (θ - 1) * (y - x) ≤ θ * c ^ (θ - 1) * (y - x) :=
    mul_le_mul_of_nonneg_right h2 hyx
  have h4 : y ^ θ - x ^ θ ≥ θ * x ^ (θ - 1) * (y - x) := by linarith [heq]
  linarith



/-! ## §3 Real-variable logarithmic profile and its discrete increments -/

lemma LamR_def (s : ℝ) : LamR s = Real.log (2 + s) := rfl

lemma LamR_eq (x : G) : Lam ρ x = LamR (ρ x) := rfl

lemma LamR_pos {s : ℝ} (hs : 0 ≤ s) : 0 < LamR s := by
  rw [LamR_def]; exact Real.log_pos (by linarith)

lemma LamR_nonneg {s : ℝ} (hs : 0 ≤ s) : 0 ≤ LamR s := (LamR_pos hs).le

lemma LamR_mono {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) : LamR a ≤ LamR b := by
  rw [LamR_def, LamR_def]
  exact Real.log_le_log (by linarith) (by linarith)

lemma LamR_lt {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) : LamR a < LamR b := by
  rw [LamR_def, LamR_def]
  exact Real.log_lt_log (by linarith) (by linarith)

/-- `Λ (2s) ≤ 2 Λ s` — doubling the radius at most doubles the logarithmic profile. -/
lemma LamR_two_mul (s : ℝ) (hs : 0 ≤ s) : LamR (2 * s) ≤ 2 * LamR s := by
  have h1 : LamR (2 * s) ≤ Real.log (2 * (2 + s)) := by
    rw [LamR_def]
    apply Real.log_le_log (by linarith)
    linarith
  have h2 : Real.log (2 * (2 + s)) = Real.log 2 + LamR s := by
    rw [Real.log_mul (by norm_num) (by linarith), LamR_def]
  have h3 : Real.log 2 ≤ LamR s := by
    rw [LamR_def]; exact Real.log_le_log (by norm_num) (by linarith)
  rw [h2] at h1
  linarith

/-- Upper bound for the discrete increment of `Λ`: `Λ(n+1) - Λ(n) ≤ 1/(2+n)`. -/
lemma LamR_gap_upper (n : ℕ) :
    LamR ((n : ℝ) + 1) - LamR (n : ℝ) ≤ 1 / (2 + (n : ℝ)) := by
  have hlt : (0:ℝ) < 2 + (n:ℝ) := by positivity
  have h1 : LamR ((n:ℝ) + 1) - LamR (n:ℝ) = Real.log ((2 + ((n:ℝ) + 1)) / (2 + (n:ℝ))) := by
    rw [LamR_def, LamR_def, ← Real.log_div (by positivity) (by positivity)]
  rw [h1]
  have h2 : (2 + ((n:ℝ) + 1)) / (2 + (n:ℝ)) = 1 + 1 / (2 + (n:ℝ)) := by
    field_simp; ring
  rw [h2]
  have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 1 + 1 / (2 + (n:ℝ)) by positivity)
  have h3 : 1 + 1 / (2 + (n:ℝ)) - 1 = 1 / (2 + (n:ℝ)) := by ring
  linarith [this, h3]

/-- The elementary lower bound `log x ≥ 1 - 1/x` for `x > 0`. -/
lemma log_ge_one_sub_inv {x : ℝ} (hx : 0 < x) : 1 - 1 / x ≤ Real.log x := by
  have h := Real.log_le_sub_one_of_pos (show (0:ℝ) < 1 / x by positivity)
  have hinv : Real.log (1 / x) = -Real.log x := by
    rw [one_div, Real.log_inv]
  rw [hinv] at h
  linarith

/-- Lower bound for the discrete increment of `Λ`: `1/(4(1+n)) ≤ Λ(n+1) - Λ(n)`. -/
lemma LamR_gap_lower (n : ℕ) :
    1 / (4 * ((n : ℝ) + 1)) ≤ LamR ((n : ℝ) + 1) - LamR (n : ℝ) := by
  have hn : (0:ℝ) < 2 + (n:ℝ) := by positivity
  have h1 : LamR ((n:ℝ) + 1) - LamR (n:ℝ) = Real.log ((2 + ((n:ℝ) + 1)) / (2 + (n:ℝ))) := by
    rw [LamR_def, LamR_def, ← Real.log_div (by positivity) (by positivity)]
  rw [h1]
  have h2 : (2 + ((n:ℝ) + 1)) / (2 + (n:ℝ)) = 1 + 1 / (2 + (n:ℝ)) := by
    field_simp; ring
  rw [h2]
  have hx : (0:ℝ) < 1 + 1 / (2 + (n:ℝ)) := by positivity
  have hlog := log_ge_one_sub_inv hx
  have h3 : 1 - 1 / (1 + 1 / (2 + (n:ℝ))) = 1 / (3 + (n:ℝ)) := by
    field_simp; ring
  have h4 : 1 / (3 + (n:ℝ)) ≥ 1 / (4 * ((n:ℝ) + 1)) := by
    apply one_div_le_one_div_of_le (by positivity)
    linarith
  linarith [hlog, h3, h4]

/-- `Λ(n+1) ≤ 2 Λ(n)` for all `n`. -/
lemma LamR_succ_le_two (n : ℕ) : LamR ((n : ℝ) + 1) ≤ 2 * LamR (n : ℝ) := by
  have h1 : LamR ((n:ℝ) + 1) ≤ Real.log (2 * (2 + (n:ℝ))) := by
    rw [LamR_def]
    apply Real.log_le_log (by positivity)
    linarith
  have h2 : Real.log (2 * (2 + (n:ℝ))) = Real.log 2 + LamR (n:ℝ) := by
    rw [Real.log_mul (by norm_num) (by positivity), LamR_def]
  have h3 : Real.log 2 ≤ LamR (n:ℝ) := by
    rw [LamR_def]
    exact Real.log_le_log (by norm_num) (by linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ (n:ℝ))])
  rw [h2] at h1
  linarith

/-- `Λ(n) ≤ 2 Λ(m)` when `n ≤ 2m`. -/
lemma LamR_le_two_of_le_two_mul {n m : ℝ} (hn : 0 ≤ n) (h : n ≤ 2 * m) :
    LamR n ≤ 2 * LamR m := by
  have hm : (0:ℝ) ≤ m := by nlinarith
  have h1 : LamR n ≤ Real.log (2 * (2 + m)) := by
    rw [LamR_def]
    apply Real.log_le_log (by linarith)
    linarith
  have h2 : Real.log (2 * (2 + m)) = Real.log 2 + LamR m := by
    rw [Real.log_mul (by norm_num) (by linarith), LamR_def]
  have h3 : Real.log 2 ≤ LamR m := by
    rw [LamR_def]; exact Real.log_le_log (by norm_num) (by linarith)
  rw [h2] at h1
  linarith



/-! ## §4 Layer cake (Abel) summation on a lattice -/

/-- **Layer cake / Abel summation bound.** For a finite set `F`, a nonnegative antitone weight `w`
and any integer `M` dominating all the floors `⌊ρ y⌋` for `y ∈ F`, the total `ρ`-weight of `F` is
controlled by the discrete increments of `w` against the counting function of `ρ`. -/
lemma finset_layer_cake {w : ℝ → ℝ} {F : Finset G} {M : ℕ}
    (hwmono : ∀ r s, r ≤ s → w s ≤ w r)
    (hρnn : ∀ x, 0 ≤ ρ x)
    (hM : ∀ y ∈ F, ⌊ρ y⌋₊ ≤ M) :
    ∑ y ∈ F, w (ρ y) ≤
      ∑ n ∈ Finset.range M,
          (w (n : ℝ) - w ((n : ℝ) + 1)) * ((F.filter (fun y => ⌊ρ y⌋₊ ≤ n)).card : ℝ)
        + w (M : ℝ) * (F.card : ℝ) := by
  classical
  have hstep1 : ∑ y ∈ F, w (ρ y) ≤ ∑ y ∈ F, w ((⌊ρ y⌋₊ : ℝ)) := by
    refine Finset.sum_le_sum fun y _ => hwmono _ _ (Nat.floor_le (hρnn y))
  have hkey : ∀ y ∈ F, w ((⌊ρ y⌋₊ : ℝ)) =
      (∑ n ∈ Finset.range M, (if ⌊ρ y⌋₊ ≤ n then (w (n : ℝ) - w ((n : ℝ) + 1)) else 0))
        + w (M : ℝ) := by
    intro y hy
    have hkM := hM y hy
    have hfilter : (Finset.range M).filter (fun n => ⌊ρ y⌋₊ ≤ n) = Finset.Ico ⌊ρ y⌋₊ M := by
      ext n
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
      omega
    have h1 : ∑ n ∈ Finset.range M, (if ⌊ρ y⌋₊ ≤ n then (w (n : ℝ) - w ((n : ℝ) + 1)) else 0)
        = ∑ n ∈ Finset.Ico ⌊ρ y⌋₊ M, (w (n : ℝ) - w ((n : ℝ) + 1)) := by
      rw [← Finset.sum_filter, hfilter]
    have h2 : ∑ n ∈ Finset.Ico ⌊ρ y⌋₊ M, (w (n : ℝ) - w ((n : ℝ) + 1))
        = w ((⌊ρ y⌋₊ : ℝ)) - w (M : ℝ) := by
      have hsub := Finset.sum_Ico_sub (f := fun n : ℕ => w (n : ℝ)) (m := ⌊ρ y⌋₊) (n := M) hkM
      have hneg : ∑ n ∈ Finset.Ico ⌊ρ y⌋₊ M, (w (n : ℝ) - w ((n : ℝ) + 1))
          = -∑ n ∈ Finset.Ico ⌊ρ y⌋₊ M, (w ((n : ℝ) + 1) - w (n : ℝ)) := by
        rw [← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl fun n _ => by ring
      have hsub' : ∑ n ∈ Finset.Ico ⌊ρ y⌋₊ M, (w ((n : ℝ) + 1) - w (n : ℝ))
          = w (M : ℝ) - w ((⌊ρ y⌋₊ : ℕ) : ℝ) := by
        simpa using hsub
      rw [hneg, hsub']
      ring
    rw [h1, h2]
    ring
  have hinner : ∀ n ∈ Finset.range M,
      ∑ y ∈ F, (if ⌊ρ y⌋₊ ≤ n then (w (n : ℝ) - w ((n : ℝ) + 1)) else 0)
        = (w (n : ℝ) - w ((n : ℝ) + 1)) * ((F.filter (fun y => ⌊ρ y⌋₊ ≤ n)).card : ℝ) := by
    intro n _
    rw [← Finset.sum_filter]
    rw [Finset.sum_const, nsmul_eq_mul]
    ring
  calc ∑ y ∈ F, w (ρ y) ≤ ∑ y ∈ F, w ((⌊ρ y⌋₊ : ℝ)) := hstep1
    _ = ∑ y ∈ F, ((∑ n ∈ Finset.range M,
            (if ⌊ρ y⌋₊ ≤ n then (w (n : ℝ) - w ((n : ℝ) + 1)) else 0)) + w (M : ℝ)) :=
        Finset.sum_congr rfl hkey
    _ = (∑ y ∈ F, ∑ n ∈ Finset.range M,
            (if ⌊ρ y⌋₊ ≤ n then (w (n : ℝ) - w ((n : ℝ) + 1)) else 0))
          + ∑ _y ∈ F, w (M : ℝ) := Finset.sum_add_distrib
    _ = (∑ n ∈ Finset.range M, ∑ y ∈ F,
            (if ⌊ρ y⌋₊ ≤ n then (w (n : ℝ) - w ((n : ℝ) + 1)) else 0))
          + w (M : ℝ) * (F.card : ℝ) := by
        rw [Finset.sum_comm, Finset.sum_const, nsmul_eq_mul, mul_comm]
    _ = _ := by
        rw [Finset.sum_congr rfl hinner]



/-! ## §5 The weight profile and its discrete increments -/

lemma Wt_pos {e c r : ℝ} (hr : 0 ≤ r) : 0 < Wt e c r :=
  mul_pos (Real.rpow_pos_of_pos (by linarith) _) (Real.rpow_pos_of_pos (LamR_pos hr) _)

lemma Wt_nonneg {e c r : ℝ} (hr : 0 ≤ r) : 0 ≤ Wt e c r := (Wt_pos hr).le

lemma Wt_antitone {e c : ℝ} (he : 0 < e) (hc : 0 ≤ c) {r s : ℝ} (hr : 0 ≤ r) (hrs : r ≤ s) :
    Wt e c s ≤ Wt e c r := by
  have hs : (0:ℝ) ≤ s := le_trans hr hrs
  have h1 : (1 + s) ^ (-e) ≤ (1 + r) ^ (-e) :=
    Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) (by linarith)
  have h2 : LamR s ^ (-c) ≤ LamR r ^ (-c) :=
    Real.rpow_le_rpow_of_nonpos (LamR_pos hr) (LamR_mono hr hrs) (by linarith)
  have h3 : (0:ℝ) ≤ (1 + r) ^ (-e) := Real.rpow_nonneg (by linarith) _
  have h4 : (0:ℝ) ≤ LamR s ^ (-c) := Real.rpow_nonneg (LamR_nonneg hs) _
  exact mul_le_mul h1 h2 h4 h3

/-- Power gap at consecutive integers. -/
lemma rpow_pow_sub_le {e : ℝ} (he : 0 < e) (n : ℕ) :
    (1 + (n:ℝ)) ^ (-e) - (1 + ((n:ℝ)+1)) ^ (-e) ≤ e * (1+(n:ℝ)) ^ (-e-1) := by
  have hx : (0:ℝ) < 1 + (n:ℝ) := by linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ (n:ℝ))]
  have hxy : (1 + (n:ℝ)) < (1 + ((n:ℝ)+1)) := by linarith
  have h := rpow_sub_le_of_neg (θ := -e) (by linarith) hx hxy
  have hd : (1+((n:ℝ)+1)) - (1+(n:ℝ)) = 1 := by ring
  calc (1 + (n:ℝ)) ^ (-e) - (1 + ((n:ℝ)+1)) ^ (-e)
      ≤ (-(-e)) * (1 + (n:ℝ)) ^ (-e-1) * ((1+((n:ℝ)+1)) - (1+(n:ℝ))) := h
    _ = e * (1+(n:ℝ)) ^ (-e-1) := by rw [hd]; ring

/-- `x^{-e} · x⁻¹ = x^{-e-1}`. -/
lemma rpow_mul_inv {e : ℝ} {x : ℝ} (hx : 0 < x) : x ^ (-e) * x⁻¹ = x ^ (-e-1) := by
  have h1 : x⁻¹ = x ^ (-1:ℝ) := by
    rw [Real.rpow_neg (le_of_lt hx), Real.rpow_one]
  rw [h1, ← Real.rpow_add hx]
  ring_nf

/-- For `x ≥ log 2 ≥ 1/2`, decay by one more logarithm costs at most a factor `2`. -/
lemma rpow_decay_step {c x : ℝ} (hx0 : 0 ≤ x) (hx : Real.log 2 ≤ x) :
    x ^ (-c-1) ≤ 2 * x ^ (-c) := by
  have hxpos : 0 < x := lt_of_lt_of_le (Real.log_pos (by norm_num)) hx
  have hid : x ^ (-c-1) = x ^ (-c) * x⁻¹ := (rpow_mul_inv hxpos).symm
  rw [hid]
  have hle : x⁻¹ ≤ 2 := by
    rw [inv_le_iff_one_le_mul₀ hxpos]
    nlinarith [Real.log_two_gt_d9]
  calc x ^ (-c) * x⁻¹ ≤ x ^ (-c) * 2 := mul_le_mul_of_nonneg_left hle (Real.rpow_nonneg hx0 _)
    _ = 2 * x ^ (-c) := by ring

/-- Logarithmic gap of the weight's log factor. -/
lemma LamR_rpow_sub_le {c : ℝ} (hc : 0 < c) (n : ℕ) :
    LamR (n:ℝ) ^ (-c) - LamR ((n:ℝ)+1) ^ (-c)
      ≤ 2 * (c + 1) * (LamR (n:ℝ) ^ (-c) * (1/(1+(n:ℝ)))) := by
  have hn : (0:ℝ) ≤ (n:ℝ) := (Nat.cast_nonneg n : _)
  have hL : (0:ℝ) < LamR (n:ℝ) := LamR_pos hn
  have hLge : Real.log 2 ≤ LamR (n:ℝ) := by
    rw [LamR_def]; exact Real.log_le_log (by norm_num) (by linarith)
  have hlt : LamR (n:ℝ) < LamR ((n:ℝ)+1) := LamR_lt hn (by linarith)
  have h := rpow_sub_le_of_neg (θ := -c) (by linarith) hL hlt
  have hgap : LamR ((n:ℝ)+1) - LamR (n:ℝ) ≤ 1/(2+(n:ℝ)) := LamR_gap_upper n
  set x := LamR (n:ℝ)
  have hx0 : (0:ℝ) ≤ x := hL.le
  have hdec : x ^ (-c-1) ≤ 2 * x ^ (-c) := rpow_decay_step hx0 hLge
  have hS : (1/(2+(n:ℝ))) ≤ (1/(1+(n:ℝ))) := by
    apply one_div_le_one_div_of_le (by linarith); linarith
  have hstep : x ^ (-c-1) * (LamR ((n:ℝ)+1) - x) ≤ 2 * (x ^ (-c) * (1/(1+(n:ℝ)))) := by
    have h1 : x ^ (-c-1) * (LamR ((n:ℝ)+1) - x) ≤ x ^ (-c-1) * (1/(1+(n:ℝ))) := by
      refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hx0 _)
      exact le_trans hgap hS
    have h2 : (0:ℝ) ≤ (1/(1+(n:ℝ))) := by positivity
    calc x ^ (-c-1) * (LamR ((n:ℝ)+1) - x)
        ≤ x ^ (-c-1) * (1/(1+(n:ℝ))) := h1
      _ ≤ (2 * x ^ (-c)) * (1/(1+(n:ℝ))) := mul_le_mul_of_nonneg_right hdec h2
      _ = 2 * (x ^ (-c) * (1/(1+(n:ℝ)))) := by ring
  have hfinal : x ^ (-c) - LamR ((n:ℝ)+1) ^ (-c)
      ≤ c * (x ^ (-c-1) * (LamR ((n:ℝ)+1) - x)) := by
    have := h
    calc x ^ (-c) - LamR ((n:ℝ)+1) ^ (-c)
        ≤ (-(-c)) * x ^ (-c-1) * (LamR ((n:ℝ)+1) - x) := this
      _ = c * (x ^ (-c-1) * (LamR ((n:ℝ)+1) - x)) := by ring
  calc x ^ (-c) - LamR ((n:ℝ)+1) ^ (-c)
      ≤ c * (x ^ (-c-1) * (LamR ((n:ℝ)+1) - x)) := hfinal
    _ ≤ c * (2 * (x ^ (-c) * (1/(1+(n:ℝ))))) := mul_le_mul_of_nonneg_left hstep hc.le
    _ = 2 * (c + 1) * (LamR (n:ℝ) ^ (-c) * (1/(1+(n:ℝ))))
          - 2 * (LamR (n:ℝ) ^ (-c) * (1/(1+(n:ℝ)))) := by
        ring
    _ ≤ 2 * (c + 1) * (LamR (n:ℝ) ^ (-c) * (1/(1+(n:ℝ)))) := by
        have h2 : (0:ℝ) ≤ 2 * (x ^ (-c) * (1/(1+(n:ℝ)))) := by positivity
        linarith

/-- The discrete increment of the weight profile, bounded by a power profile. -/
lemma Wt_incr_le {e c : ℝ} (he : 0 < e) (hc : 0 ≤ c) (n : ℕ) :
    Wt e c (n : ℝ) - Wt e c ((n : ℝ) + 1)
      ≤ (e + 2 * (c + 1)) * (1 + (n : ℝ)) ^ (-e - 1) * LamR (n : ℝ) ^ (-c) := by
  have hn : (0:ℝ) ≤ (n:ℝ) := (Nat.cast_nonneg n : _)
  have hA : (0:ℝ) < 1 + (n:ℝ) := by linarith
  have hB : (0:ℝ) < 1 + ((n:ℝ)+1) := by linarith
  have hL : (0:ℝ) < LamR (n:ℝ) := LamR_pos hn
  have hL2 : (0:ℝ) < LamR ((n:ℝ)+1) := LamR_pos (by linarith)
  have hdec : Wt e c (n:ℝ) - Wt e c ((n:ℝ)+1)
      = (1+(n:ℝ)) ^ (-e) * (LamR (n:ℝ) ^ (-c) - LamR ((n:ℝ)+1) ^ (-c))
        + LamR ((n:ℝ)+1) ^ (-c)
            * ((1+(n:ℝ)) ^ (-e) - (1+((n:ℝ)+1)) ^ (-e)) := by
    simp only [Wt]; ring
  have hpow := rpow_pow_sub_le (e := e) he n
  have hpow0 : (0:ℝ) ≤ (1+(n:ℝ)) ^ (-e) - (1+((n:ℝ)+1)) ^ (-e) := by
    have h := Real.rpow_le_rpow_of_nonpos (x := 1+(n:ℝ)) (y := 1+((n:ℝ)+1)) (z := -e) hA
      (by linarith) (show -e ≤ 0 by linarith)
    linarith
  have hterm2 : LamR ((n:ℝ)+1) ^ (-c)
        * ((1+(n:ℝ)) ^ (-e) - (1+((n:ℝ)+1)) ^ (-e))
      ≤ e * (1+(n:ℝ)) ^ (-e-1) * LamR (n:ℝ) ^ (-c) := by
    have h1 : LamR ((n:ℝ)+1) ^ (-c) ≤ LamR (n:ℝ) ^ (-c) := by
      refine Real.rpow_le_rpow_of_nonpos hL (LamR_mono hn (by linarith)) ?_
      linarith
    calc LamR ((n:ℝ)+1) ^ (-c)
          * ((1+(n:ℝ)) ^ (-e) - (1+((n:ℝ)+1)) ^ (-e))
        ≤ LamR (n:ℝ) ^ (-c) * (e * (1+(n:ℝ)) ^ (-e-1)) :=
          mul_le_mul h1 hpow hpow0 (Real.rpow_nonneg hL.le _)
      _ = e * (1+(n:ℝ)) ^ (-e-1) * LamR (n:ℝ) ^ (-c) := by ring
  have hid : (1+(n:ℝ)) ^ (-e) * (1/(1+(n:ℝ))) = (1+(n:ℝ)) ^ (-e-1) := by
    have h1 : (1/(1+(n:ℝ))) = (1+(n:ℝ))⁻¹ := by ring
    rw [h1, rpow_mul_inv hA]
  rcases eq_or_lt_of_le hc with hc0 | hcpos
  · subst hc0
    have hLHS : Wt e 0 (n:ℝ) - Wt e 0 ((n:ℝ)+1)
        = (1+(n:ℝ)) ^ (-e) - (1+((n:ℝ)+1)) ^ (-e) := by
      simp only [Wt, neg_zero, Real.rpow_zero, mul_one]
    rw [hLHS]
    have hRHS : (e + 2 * ((0:ℝ) + 1)) * (1 + (n : ℝ)) ^ (-e - 1) * LamR (n : ℝ) ^ (-(0:ℝ))
        = (e+2) * (1+(n:ℝ)) ^ (-e-1) := by
      rw [neg_zero, Real.rpow_zero, mul_one]
      ring
    rw [hRHS]
    have h7 : (0:ℝ) ≤ (1+(n:ℝ)) ^ (-e-1) := Real.rpow_nonneg hA.le _
    linarith [hpow]
  · have hlog := LamR_rpow_sub_le (c := c) hcpos n
    have hterm1 : (1+(n:ℝ)) ^ (-e) * (LamR (n:ℝ) ^ (-c) - LamR ((n:ℝ)+1) ^ (-c))
        ≤ 2 * (c + 1) * (1+(n:ℝ)) ^ (-e-1) * LamR (n:ℝ) ^ (-c) := by
      have hA0 : (0:ℝ) ≤ (1+(n:ℝ)) ^ (-e) := Real.rpow_nonneg hA.le _
      have h1 : (1+(n:ℝ)) ^ (-e) * (LamR (n:ℝ) ^ (-c) - LamR ((n:ℝ)+1) ^ (-c))
          ≤ (1+(n:ℝ)) ^ (-e)
            * (2 * (c + 1) * (LamR (n:ℝ) ^ (-c) * (1/(1+(n:ℝ))))) :=
        mul_le_mul_of_nonneg_left hlog hA0
      have h2 : (1+(n:ℝ)) ^ (-e)
            * (2 * (c + 1) * (LamR (n:ℝ) ^ (-c) * (1/(1+(n:ℝ)))))
          = 2 * (c + 1) * ((1+(n:ℝ)) ^ (-e) * (1/(1+(n:ℝ)))) * LamR (n:ℝ) ^ (-c) := by ring
      rw [h2, hid] at h1
      exact h1
    rw [hdec]
    have hsum : (1+(n:ℝ)) ^ (-e) * (LamR (n:ℝ) ^ (-c) - LamR ((n:ℝ)+1) ^ (-c))
          + LamR ((n:ℝ)+1) ^ (-c) * ((1+(n:ℝ)) ^ (-e) - (1+((n:ℝ)+1)) ^ (-e))
        ≤ 2 * (c + 1) * (1+(n:ℝ)) ^ (-e-1) * LamR (n:ℝ) ^ (-c)
          + e * (1+(n:ℝ)) ^ (-e-1) * LamR (n:ℝ) ^ (-c) := by linarith
    have hcomb : 2 * (c + 1) * (1+(n:ℝ)) ^ (-e-1) * LamR (n:ℝ) ^ (-c)
          + e * (1+(n:ℝ)) ^ (-e-1) * LamR (n:ℝ) ^ (-c)
        = (e + 2 * (c + 1)) * (1+(n:ℝ)) ^ (-e-1) * LamR (n:ℝ) ^ (-c) := by ring
    linarith [hsum, hcomb]


set_option linter.hashCommand false

/-! ## §7 Axiom audit (no `sorry`, no custom axioms, no `native_decide`) -/

#print axioms CriticalLRPConv.Lam_pos
#print axioms CriticalLRPConv.Lam_mono
#print axioms CriticalLRPConv.Lam_le_two_mul
#print axioms CriticalLRPConv.rpow_one_add_le_of_le
#print axioms CriticalLRPConv.rpow_one_add_le_mul
#print axioms CriticalLRPConv.exists_rpow_slope
#print axioms CriticalLRPConv.rpow_sub_ge_of_small
#print axioms CriticalLRPConv.rpow_sub_ge_of_large
#print axioms CriticalLRPConv.rpow_sub_ge_of_neg
#print axioms CriticalLRPConv.rpow_sub_le_of_neg
#print axioms CriticalLRPConv.LamR_pos
#print axioms CriticalLRPConv.LamR_mono
#print axioms CriticalLRPConv.LamR_lt
#print axioms CriticalLRPConv.LamR_two_mul
#print axioms CriticalLRPConv.LamR_gap_upper
#print axioms CriticalLRPConv.log_ge_one_sub_inv
#print axioms CriticalLRPConv.LamR_gap_lower
#print axioms CriticalLRPConv.LamR_succ_le_two
#print axioms CriticalLRPConv.LamR_le_two_of_le_two_mul
#print axioms CriticalLRPConv.finset_layer_cake
#print axioms CriticalLRPConv.Wt_pos
#print axioms CriticalLRPConv.Wt_nonneg
#print axioms CriticalLRPConv.Wt_antitone
#print axioms CriticalLRPConv.rpow_pow_sub_le
#print axioms CriticalLRPConv.rpow_mul_inv
#print axioms CriticalLRPConv.rpow_decay_step
#print axioms CriticalLRPConv.LamR_rpow_sub_le
#print axioms CriticalLRPConv.Wt_incr_le

end CriticalLRPConv
