/-
# Weighted ball shell estimate for the lattice convolution (A1/A2 of Lemma I.4.3)

Source: arXiv:2508.18807v1, proof of Lemma I.4.3, estimate (I.4.12): the two
"ball" sums

  `A1 = ⟨x⟩^{-d+a} (log⟨x⟩)^{-â} Σ_{r ≼ ⟨x⟩} r^{-(d-a)} (log r)^{-â}`,
  `A2 = ⟨x⟩^{-d+a} (log⟨x⟩)^{-â} Σ_{r ≼ ⟨x⟩} r^{-(d-b)} (log r)^{-b̂}`

are controlled by the one-dimensional comparison

  `Σ_{r ≤ S} r^{-(d-a)} (log r)^{-c} ⪯_a S^a (log S)^{-c}`  (0 < a < d, c ≥ 0).

This file proves exactly that comparison, at the level of a finite set of lattice
points with an explicit counting function, and then feeds it through the already
proved finite layer-cake identity.  No model input (kernel, cutoff, percolation
measure) is used: the counting function stays an explicit hypothesis, matching
the design of `Analysis/LatticeConvolution.lean`.
-/
module

public import PercLib.CriticalLRP.Analysis.LatticeConvolution.BallShell.Defs
public import PercLib.Models.LongRange.PowerLaw

/-!
Weighted ball-shell estimates and their normalized A1/A2 contribution.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

@[expose] public section

namespace CriticalLRPConv

open scoped Topology

/-! ## §1 The one-dimensional power–log core -/

lemma Sfun_nonneg (a c : ℝ) (M : ℕ) : 0 ≤ Sfun a c M := by
  unfold Sfun
  exact mul_nonneg (Real.rpow_nonneg (by positivity) _)
    (Real.rpow_nonneg (LamR_pos (Nat.cast_nonneg M)).le _)

lemma Tfun_nonneg (a c : ℝ) (M : ℕ) : 0 ≤ Tfun a c M := by
  unfold Tfun
  exact mul_nonneg (Real.rpow_nonneg (by positivity) _)
    (Real.rpow_nonneg (LamR_pos (Nat.cast_nonneg M)).le _)

lemma Sfun_pos {a c : ℝ} (ha : 0 < a) (M : ℕ) : 0 < Sfun a c M := by
  unfold Sfun
  exact mul_pos (Real.rpow_pos_of_pos (by positivity) _)
    (Real.rpow_pos_of_pos (LamR_pos (Nat.cast_nonneg M)) _)

lemma Sfun_succ (a c : ℝ) (M : ℕ) :
    Sfun a c (M + 1) = (2 + (M : ℝ)) ^ a * LamR ((M : ℝ) + 1) ^ (-c) := by
  unfold Sfun
  have h1 : ((M + 1 : ℕ) : ℝ) = (M : ℝ) + 1 := by push_cast; ring
  rw [h1]
  have h2 : 1 + ((M : ℝ) + 1) = 2 + (M : ℝ) := by ring
  rw [h2]

lemma Tfun_eq_Sfun_div {a c : ℝ} {M : ℕ} :
    Tfun a c M = Sfun a c M / (1 + (M : ℝ)) := by
  unfold Tfun Sfun
  have hu : (0:ℝ) < 1 + (M : ℝ) := by positivity
  rw [eq_div_iff (ne_of_gt hu)]
  have h : (1 + (M : ℝ)) ^ (a - 1) * (1 + (M : ℝ)) = (1 + (M : ℝ)) ^ a := by
    nth_rewrite 2 [← Real.rpow_one (1 + (M : ℝ))]
    rw [← Real.rpow_add hu]
    norm_num
  calc (1 + (M : ℝ)) ^ (a - 1) * LamR (M : ℝ) ^ (-c) * (1 + (M : ℝ))
      = ((1 + (M : ℝ)) ^ (a - 1) * (1 + (M : ℝ))) * LamR (M : ℝ) ^ (-c) := by ring
    _ = (1 + (M : ℝ)) ^ a * LamR (M : ℝ) ^ (-c) := by rw [h]

/-- Pointwise lower estimate for the logarithmic profile increment. -/
lemma one_div_two_mul_le_log_one_add_inv {u : ℝ} (hu : 1 ≤ u) :
    1 / (2 * u) ≤ Real.log (1 + 1 / u) := by
  have hu0 : (0:ℝ) < u := lt_of_lt_of_le one_pos hu
  have hx : (0:ℝ) ≤ 1 / u := by positivity
  have h := Real.le_log_one_add_of_nonneg hx
  have h2 : 2 * (1 / u) / (1 / u + 2) = 2 / (1 + 2 * u) := by
    field_simp
  have h3 : 1 / (2 * u) ≤ 2 / (1 + 2 * u) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    linarith
  rw [h2] at h
  linarith

/-- The `exp`-form core inequality of the doubling step.  If `b ≤ b'` are two positive
logarithmic profiles whose gap is at most `1/(u+1)`, and `4c ≤ b a`, then the product
`(1+1/u)^a (b/b')^c` dominates `1 + a/(4u)`. -/
lemma exp_step_aux {u b b' a c : ℝ} (hu : 1 ≤ u) (hb : 0 < b) (hbb' : b ≤ b')
    (ha : 0 < a) (hc : 0 ≤ c) (hthr : 4 * c ≤ b * a) (hδ : b' - b ≤ 1 / (u + 1)) :
    1 + a / (4 * u) ≤ (1 + 1 / u) ^ a * (b / b') ^ c := by
  have hu0 : (0:ℝ) < u := lt_of_lt_of_le one_pos hu
  have hb'0 : (0:ℝ) < b' := lt_of_lt_of_le hb hbb'
  -- lower bound for the power factor
  have hlog1 : 1 / (2 * u) ≤ Real.log (1 + 1 / u) := one_div_two_mul_le_log_one_add_inv hu
  have hP : Real.exp (a / (2 * u)) ≤ (1 + 1 / u) ^ a := by
    rw [Real.rpow_def_of_pos (by positivity : (0:ℝ) < 1 + 1 / u)]
    apply Real.exp_le_exp_of_le
    have hmul := mul_le_mul_of_nonneg_left hlog1 (le_of_lt ha)
    calc a / (2 * u) = a * (1 / (2 * u)) := by ring
      _ ≤ a * Real.log (1 + 1 / u) := hmul
      _ = Real.log (1 + 1 / u) * a := by ring
  -- upper bound for the log factor
  have hlogle : Real.log (1 + (b' - b) / b) ≤ (b' - b) / b := by
    have hpos : (0:ℝ) < 1 + (b' - b) / b := by positivity
    have := Real.log_le_sub_one_of_pos hpos
    linarith
  have hQ : Real.exp (-(c * ((b' - b) / b))) ≤ (b / b') ^ c := by
    rw [Real.rpow_def_of_pos (by positivity : (0:ℝ) < b / b')]
    apply Real.exp_le_exp_of_le
    have hratio : b' / b = 1 + (b' - b) / b := by field_simp; ring
    have hinv : Real.log (b / b') = - Real.log (b' / b) := by
      rw [← Real.log_inv]
      congr 1
      field_simp
    rw [hinv, hratio]
    nlinarith [hlogle, hc]
  -- the threshold converts the log gap into the power budget
  have hbudget : c * ((b' - b) / b) ≤ a / (4 * u) := by
    have h1 : (b' - b) / b ≤ (1 / (u + 1)) / b :=
      (div_le_div_iff_of_pos_right hb).mpr hδ
    have h2 : c * ((b' - b) / b) ≤ c * ((1 / (u + 1)) / b) :=
      mul_le_mul_of_nonneg_left h1 hc
    have h3 : c * ((1 / (u + 1)) / b) ≤ a / (4 * u) := by
      have hL : c * ((1 / (u + 1)) / b) = c / ((u + 1) * b) := by field_simp
      rw [hL, div_le_div_iff₀ (by positivity) (by positivity)]
      have h4 : 4 * c * u ≤ b * a * u := by nlinarith [hthr, hu0]
      have h5 : b * a * u ≤ b * a * (u + 1) := by nlinarith [hb, ha]
      nlinarith [h4, h5]
    linarith
  have hmain : Real.exp (a / (4 * u)) ≤ (1 + 1 / u) ^ a * (b / b') ^ c := by
    have hsplit : a / (2 * u) - a / (4 * u) = a / (4 * u) := by
      field_simp
      ring
    have h1 : Real.exp (a / (4 * u)) ≤ Real.exp (a / (2 * u) - c * ((b' - b) / b)) := by
      apply Real.exp_le_exp_of_le
      linarith
    have h2 : Real.exp (a / (2 * u) - c * ((b' - b) / b))
        = Real.exp (a / (2 * u)) * Real.exp (-(c * ((b' - b) / b))) := by
      rw [← Real.exp_add]
      ring_nf
    rw [h2] at h1
    exact h1.trans (mul_le_mul hP hQ (Real.exp_pos _).le (Real.rpow_nonneg (by positivity) _))
  have hexp : 1 + a / (4 * u) ≤ Real.exp (a / (4 * u)) := by
    have := Real.add_one_le_exp (a / (4 * u))
    linarith
  exact hexp.trans hmain



/-! ## §2 The one-step inequality for `Sfun` -/

/-- **The doubling step.**  If the logarithmic profile at radius `M` dominates `4c/a` then
the shell weight at `M` is at most `4/a` times the increment of the target profile. -/
lemma Sfun_step {a c : ℝ} (ha : 0 < a) (hc : 0 ≤ c) {M : ℕ}
    (hM : 4 * c ≤ LamR (M : ℝ) * a) :
    Sfun a c M + (a / 4) * Tfun a c M ≤ Sfun a c (M + 1) := by
  have hu : (1:ℝ) ≤ 1 + (M : ℝ) := by
    have h : (0:ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
    linarith
  have hu0 : (0:ℝ) < 1 + (M : ℝ) := by positivity
  have hb : 0 < LamR (M : ℝ) := LamR_pos (Nat.cast_nonneg M)
  have hbb' : LamR (M : ℝ) ≤ LamR ((M : ℝ) + 1) :=
    LamR_mono (Nat.cast_nonneg M) (by linarith)
  have hδ : LamR ((M : ℝ) + 1) - LamR (M : ℝ) ≤ 1 / ((1 + (M : ℝ)) + 1) := by
    have h := LamR_gap_upper M
    have h2 : (1 + (M : ℝ)) + 1 = 2 + (M : ℝ) := by ring
    rw [h2]
    exact h
  have hkey := exp_step_aux hu hb hbb' ha hc hM hδ
  have hb' : (0:ℝ) < LamR ((M : ℝ) + 1) := LamR_pos (by positivity)
  have hinv : (LamR ((M : ℝ) + 1) / LamR (M : ℝ)) ^ (-c)
      = (LamR (M : ℝ) / LamR ((M : ℝ) + 1)) ^ c := by
    have hx0 : (0:ℝ) < LamR ((M : ℝ) + 1) / LamR (M : ℝ) := by positivity
    conv_lhs => rw [Real.rpow_neg hx0.le, Real.div_rpow hb'.le hb.le, inv_div]
    rw [Real.div_rpow hb.le hb'.le]
  have hbase : (2 + (M : ℝ)) = (1 + (M : ℝ)) * (1 + 1 / (1 + (M : ℝ))) := by
    field_simp
    ring
  have hlog : LamR ((M : ℝ) + 1) = LamR (M : ℝ) * (LamR ((M : ℝ) + 1) / LamR (M : ℝ)) := by
    field_simp
  have h1 : (2 + (M : ℝ)) ^ a
      = (1 + (M : ℝ)) ^ a * (1 + 1 / (1 + (M : ℝ))) ^ a := by
    rw [hbase, Real.mul_rpow hu0.le (by positivity)]
  have h2 : LamR ((M : ℝ) + 1) ^ (-c)
      = LamR (M : ℝ) ^ (-c) * (LamR ((M : ℝ) + 1) / LamR (M : ℝ)) ^ (-c) := by
    conv_lhs => rw [hlog, Real.mul_rpow hb.le (by positivity)]
  have hfac : Sfun a c (M + 1)
      = Sfun a c M * ((1 + 1 / (1 + (M : ℝ))) ^ a
          * (LamR (M : ℝ) / LamR ((M : ℝ) + 1)) ^ c) := by
    calc Sfun a c (M + 1)
        = (2 + (M : ℝ)) ^ a * LamR ((M : ℝ) + 1) ^ (-c) := Sfun_succ a c M
      _ = ((1 + (M : ℝ)) ^ a * (1 + 1 / (1 + (M : ℝ))) ^ a)
            * (LamR (M : ℝ) ^ (-c) * (LamR ((M : ℝ) + 1) / LamR (M : ℝ)) ^ (-c)) := by
          rw [h1, h2]
      _ = (1 + (M : ℝ)) ^ a * LamR (M : ℝ) ^ (-c)
            * ((1 + 1 / (1 + (M : ℝ))) ^ a
              * (LamR (M : ℝ) / LamR ((M : ℝ) + 1)) ^ c) := by
          rw [hinv]
          ring
      _ = Sfun a c M * ((1 + 1 / (1 + (M : ℝ))) ^ a
            * (LamR (M : ℝ) / LamR ((M : ℝ) + 1)) ^ c) := rfl
  have hT : Tfun a c M = Sfun a c M / (1 + (M : ℝ)) := Tfun_eq_Sfun_div
  have hS : (0:ℝ) ≤ Sfun a c M := Sfun_nonneg a c M
  calc Sfun a c M + (a / 4) * Tfun a c M
      = Sfun a c M * (1 + a / (4 * (1 + (M : ℝ)))) := by
        rw [hT]
        field_simp
    _ ≤ Sfun a c M * ((1 + 1 / (1 + (M : ℝ))) ^ a
          * (LamR (M : ℝ) / LamR ((M : ℝ) + 1)) ^ c) :=
        mul_le_mul_of_nonneg_left hkey hS
    _ = Sfun a c (M + 1) := hfac.symm

/-! ## §3 The threshold and the constant of the core bound -/

lemma LamR_coreThresh {a c : ℝ} (ha : 0 < a) :
    4 * c ≤ LamR ((coreThresh a c : ℕ) : ℝ) * a := by
  have hexp : Real.exp (4 * c / a) ≤ ((coreThresh a c : ℕ) : ℝ) := Nat.le_ceil _
  have hlog : Real.log (Real.exp (4 * c / a))
      ≤ Real.log (2 + ((coreThresh a c : ℕ) : ℝ)) := by
    apply Real.log_le_log (Real.exp_pos _)
    linarith
  rw [Real.log_exp] at hlog
  unfold LamR
  have h4 : 4 * c / a ≤ Real.log (2 + ((coreThresh a c : ℕ) : ℝ)) := hlog
  rw [div_le_iff₀ ha] at h4
  linarith

lemma one_le_coreThresh {a c : ℝ} (ha : 0 < a) (hc : 0 ≤ c) : 1 ≤ coreThresh a c := by
  unfold coreThresh
  have h1 : (1:ℝ) ≤ Real.exp (4 * c / a) := by
    rw [← Real.exp_zero]
    apply Real.exp_le_exp_of_le
    have : (0:ℝ) ≤ 4 * c / a := by positivity
    linarith
  calc (1:ℕ) = ⌈(1:ℝ)⌉₊ := by simp
    _ ≤ ⌈Real.exp (4 * c / a)⌉₊ := Nat.ceil_mono h1

lemma le_coreConst_max (a c : ℝ) : 4 / a ≤ coreConst a c := by
  unfold coreConst
  linarith [le_max_left (4 / a)
    ((coreThresh a c : ℝ) * (max 1 (((coreThresh a c : ℕ) : ℝ) ^ (a - 1))) *
      LamR ((0:ℕ) : ℝ) ^ (-c) * LamR ((coreThresh a c : ℕ) : ℝ) ^ c)]

lemma coreConst_pos (a c : ℝ) : 0 < coreConst a c := by
  unfold coreConst
  have h1 : (0:ℝ) ≤ (coreThresh a c : ℝ) := by positivity
  have h2 : (1:ℝ) ≤ max 1 (((coreThresh a c : ℕ) : ℝ) ^ (a - 1)) := le_max_left _ _
  have h3 : (0:ℝ) ≤ LamR ((0:ℕ) : ℝ) ^ (-c) :=
    Real.rpow_nonneg (LamR_pos (Nat.cast_nonneg 0)).le _
  have h4 : (0:ℝ) ≤ LamR ((coreThresh a c : ℕ) : ℝ) ^ c :=
    Real.rpow_nonneg (LamR_pos (Nat.cast_nonneg _)).le _
  have h5 : (0:ℝ) ≤ (coreThresh a c : ℝ) * (max 1 (((coreThresh a c : ℕ) : ℝ) ^ (a - 1))) *
      LamR ((0:ℕ) : ℝ) ^ (-c) * LamR ((coreThresh a c : ℕ) : ℝ) ^ c :=
    mul_nonneg (mul_nonneg (mul_nonneg h1 (by linarith)) h3) h4
  have : (0:ℝ) ≤ max (4 / a)
      ((coreThresh a c : ℝ) * (max 1 (((coreThresh a c : ℕ) : ℝ) ^ (a - 1))) *
        LamR ((0:ℕ) : ℝ) ^ (-c) * LamR ((coreThresh a c : ℕ) : ℝ) ^ c) :=
    le_trans h5 (le_max_right _ _)
  linarith



/-! ## §4 The one-dimensional power–log core bound -/

lemma Tfun_le_of_lt_thresh {a c : ℝ} (ha : 0 < a) (hc : 0 ≤ c) {n : ℕ}
    (hn : n < coreThresh a c) :
    Tfun a c n ≤
      max 1 (((coreThresh a c : ℕ) : ℝ) ^ (a - 1)) * LamR ((0:ℕ) : ℝ) ^ (-c) := by
  have hN1 : (1:ℝ) ≤ ((coreThresh a c : ℕ) : ℝ) := by
    have := one_le_coreThresh ha hc
    exact_mod_cast this
  have hn1 : (1:ℝ) ≤ 1 + (n : ℝ) := by
    have h : (0:ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hle : (1:ℝ) + (n : ℝ) ≤ ((coreThresh a c : ℕ) : ℝ) := by
    have h : (n : ℝ) + 1 ≤ ((coreThresh a c : ℕ) : ℝ) := by exact_mod_cast hn
    linarith
  have hpow : (1 + (n : ℝ)) ^ (a - 1) ≤ max 1 (((coreThresh a c : ℕ) : ℝ) ^ (a - 1)) := by
    by_cases h : 0 ≤ a - 1
    · exact le_trans (Real.rpow_le_rpow (by linarith) hle h) (le_max_right _ _)
    · have hlt : a - 1 < 0 := not_le.mp h
      have hstep : (1 + (n : ℝ)) ^ (a - 1) ≤ (1:ℝ) ^ (a - 1) :=
        Real.rpow_le_rpow_of_nonpos (by norm_num) hn1 hlt.le
      rw [Real.one_rpow] at hstep
      exact le_trans hstep (le_max_left _ _)
  have hlog : LamR ((n:ℕ) : ℝ) ^ (-c) ≤ LamR ((0:ℕ) : ℝ) ^ (-c) := by
    have h0 : (0:ℝ) ≤ ((0:ℕ) : ℝ) := by norm_num
    have hn' : ((0:ℕ) : ℝ) ≤ ((n:ℕ) : ℝ) := by exact_mod_cast Nat.zero_le n
    have hmono : LamR ((0:ℕ) : ℝ) ≤ LamR ((n:ℕ) : ℝ) := LamR_mono h0 hn'
    exact Real.rpow_le_rpow_of_nonpos (LamR_pos h0) hmono (by linarith)
  have hMpos : (0:ℝ) ≤ max 1 (((coreThresh a c : ℕ) : ℝ) ^ (a - 1)) := by
    linarith [le_max_left (1:ℝ) (((coreThresh a c : ℕ) : ℝ) ^ (a - 1))]
  have hlogpos : (0:ℝ) ≤ LamR ((n:ℕ) : ℝ) ^ (-c) :=
    Real.rpow_nonneg (LamR_pos (Nat.cast_nonneg n)).le (-c)
  calc Tfun a c n = (1 + (n : ℝ)) ^ (a - 1) * LamR ((n:ℕ) : ℝ) ^ (-c) := rfl
    _ ≤ max 1 (((coreThresh a c : ℕ) : ℝ) ^ (a - 1)) * LamR ((0:ℕ) : ℝ) ^ (-c) :=
        mul_le_mul hpow hlog hlogpos hMpos

lemma core_sum_le_thresh {a c : ℝ} (ha : 0 < a) (hc : 0 ≤ c) :
    ∑ n ∈ Finset.range (coreThresh a c), Tfun a c n
      ≤ (coreThresh a c : ℝ) *
        (max 1 (((coreThresh a c : ℕ) : ℝ) ^ (a - 1)) * LamR ((0:ℕ) : ℝ) ^ (-c)) := by
  have h := Finset.sum_le_sum
    (fun n hn => Tfun_le_of_lt_thresh ha hc (Finset.mem_range.mp hn))
  calc ∑ n ∈ Finset.range (coreThresh a c), Tfun a c n
      ≤ ∑ _n ∈ Finset.range (coreThresh a c),
          (max 1 (((coreThresh a c : ℕ) : ℝ) ^ (a - 1)) * LamR ((0:ℕ) : ℝ) ^ (-c)) := h
    _ = (coreThresh a c : ℝ) *
          (max 1 (((coreThresh a c : ℕ) : ℝ) ^ (a - 1)) * LamR ((0:ℕ) : ℝ) ^ (-c)) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

lemma thresh_bound_le_coreConst {a c : ℝ} (ha : 0 < a) (hc : 0 ≤ c) :
    (coreThresh a c : ℝ) *
        (max 1 (((coreThresh a c : ℕ) : ℝ) ^ (a - 1)) * LamR ((0:ℕ) : ℝ) ^ (-c))
      ≤ coreConst a c * LamR ((coreThresh a c : ℕ) : ℝ) ^ (-c) := by
  have hNpos : (0:ℝ) < LamR ((coreThresh a c : ℕ) : ℝ) :=
    LamR_pos (Nat.cast_nonneg _)
  have hge : (coreThresh a c : ℝ) * (max 1 (((coreThresh a c : ℕ) : ℝ) ^ (a - 1)))
      * LamR ((0:ℕ) : ℝ) ^ (-c) * LamR ((coreThresh a c : ℕ) : ℝ) ^ c ≤ coreConst a c := by
    unfold coreConst
    linarith [le_max_right (4 / a) ((coreThresh a c : ℝ) *
      (max 1 (((coreThresh a c : ℕ) : ℝ) ^ (a - 1))) * LamR ((0:ℕ) : ℝ) ^ (-c) *
      LamR ((coreThresh a c : ℕ) : ℝ) ^ c)]
  have hmul := mul_le_mul_of_nonneg_right hge (Real.rpow_nonneg hNpos.le (-c))
  have hcancel : LamR ((coreThresh a c : ℕ) : ℝ) ^ c
      * LamR ((coreThresh a c : ℕ) : ℝ) ^ (-c) = 1 := by
    rw [← Real.rpow_add hNpos]
    norm_num
  calc (coreThresh a c : ℝ) *
        (max 1 (((coreThresh a c : ℕ) : ℝ) ^ (a - 1)) * LamR ((0:ℕ) : ℝ) ^ (-c))
      = (coreThresh a c : ℝ) * (max 1 (((coreThresh a c : ℕ) : ℝ) ^ (a - 1)))
          * LamR ((0:ℕ) : ℝ) ^ (-c) * (LamR ((coreThresh a c : ℕ) : ℝ) ^ c
          * LamR ((coreThresh a c : ℕ) : ℝ) ^ (-c)) := by rw [hcancel]; ring
    _ = ((coreThresh a c : ℝ) * (max 1 (((coreThresh a c : ℕ) : ℝ) ^ (a - 1)))
          * LamR ((0:ℕ) : ℝ) ^ (-c) * LamR ((coreThresh a c : ℕ) : ℝ) ^ c)
          * LamR ((coreThresh a c : ℕ) : ℝ) ^ (-c) := by ring
    _ ≤ coreConst a c * LamR ((coreThresh a c : ℕ) : ℝ) ^ (-c) := hmul

/-- `Sfun` dominates the bare logarithmic factor. -/
lemma LamR_rpow_le_Sfun {a c : ℝ} (ha : 0 < a) (M : ℕ) :
    LamR ((M:ℕ) : ℝ) ^ (-c) ≤ Sfun a c M := by
  have h1 : (1:ℝ) ≤ 1 + (M : ℝ) := by
    have h : (0:ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
    linarith
  have h2 : (1:ℝ) ≤ (1 + (M : ℝ)) ^ a := Real.one_le_rpow h1 ha.le
  have h3 : (0:ℝ) ≤ LamR ((M:ℕ) : ℝ) ^ (-c) :=
    Real.rpow_nonneg (LamR_pos (Nat.cast_nonneg M)).le _
  calc LamR ((M:ℕ) : ℝ) ^ (-c) = 1 * LamR ((M:ℕ) : ℝ) ^ (-c) := by rw [one_mul]
    _ ≤ (1 + (M : ℝ)) ^ a * LamR ((M:ℕ) : ℝ) ^ (-c) :=
        mul_le_mul_of_nonneg_right h2 h3

/-- **The one-dimensional power–log core bound.**  For `a > 0`, `c ≥ 0` and every `M`,
`Σ_{n < M} (1+n)^{a-1} (log (2+n))^{-c} ≤ coreConst a c · (1+M)^a (log (2+M))^{-c}`,
with `coreConst a c` independent of `M`. -/
theorem core_sum_bound {a c : ℝ} (ha : 0 < a) (hc : 0 ≤ c) (M : ℕ) :
    ∑ n ∈ Finset.range M, Tfun a c n ≤ coreConst a c * Sfun a c M := by
  have hstep : ∀ k : ℕ, coreThresh a c ≤ k →
      Sfun a c k + (a / 4) * Tfun a c k ≤ Sfun a c (k + 1) := by
    intro k hk
    refine Sfun_step ha hc ?_
    have hmono : LamR ((coreThresh a c : ℕ) : ℝ) ≤ LamR (k : ℝ) := by
      apply LamR_mono (Nat.cast_nonneg _)
      exact_mod_cast hk
    have hmul : LamR ((coreThresh a c : ℕ) : ℝ) * a ≤ LamR (k : ℝ) * a :=
      mul_le_mul_of_nonneg_right hmono ha.le
    linarith [LamR_coreThresh (a := a) (c := c) ha]
  have hmain : ∀ M : ℕ, coreThresh a c ≤ M →
      ∑ n ∈ Finset.range M, Tfun a c n ≤ coreConst a c * Sfun a c M := by
    intro M hM
    induction M, hM using Nat.le_induction with
    | base =>
        have h1 := core_sum_le_thresh (a := a) (c := c) ha hc
        have h2 := thresh_bound_le_coreConst (a := a) (c := c) ha hc
        have h3 := LamR_rpow_le_Sfun (a := a) (c := c) ha (coreThresh a c)
        have h4 := coreConst_pos (a := a) (c := c)
        calc ∑ n ∈ Finset.range (coreThresh a c), Tfun a c n
            ≤ (coreThresh a c : ℝ) *
                (max 1 (((coreThresh a c : ℕ) : ℝ) ^ (a - 1)) * LamR ((0:ℕ) : ℝ) ^ (-c)) := h1
          _ ≤ coreConst a c * LamR ((coreThresh a c : ℕ) : ℝ) ^ (-c) := h2
          _ ≤ coreConst a c * Sfun a c (coreThresh a c) :=
              mul_le_mul_of_nonneg_left h3 h4.le
    | succ k hk ih =>
        have hk' : coreThresh a c ≤ k := hk
        have hstepk := hstep k hk'
        have hTk : Tfun a c k ≤ coreConst a c * (Sfun a c (k + 1) - Sfun a c k) := by
          have h1 : (a / 4) * Tfun a c k ≤ Sfun a c (k + 1) - Sfun a c k := by linarith
          have h2 : (0:ℝ) < a / 4 := by positivity
          have h3 : Tfun a c k ≤ (Sfun a c (k + 1) - Sfun a c k) / (a / 4) := by
            rw [le_div_iff₀ h2]
            linarith
          have h4 : (Sfun a c (k + 1) - Sfun a c k) / (a / 4)
              ≤ coreConst a c * (Sfun a c (k + 1) - Sfun a c k) := by
            rw [div_le_iff₀ h2]
            have hK := le_coreConst_max (a := a) (c := c)
            have hnn : (0:ℝ) ≤ Sfun a c (k + 1) - Sfun a c k :=
              le_trans (mul_nonneg h2.le (Tfun_nonneg a c k)) h1
            have hone : (1:ℝ) ≤ coreConst a c * (a / 4) := by
              have h4a : (4 / a) * (a / 4) = (1:ℝ) := by field_simp
              calc (1:ℝ) = (4 / a) * (a / 4) := h4a.symm
                _ ≤ coreConst a c * (a / 4) := mul_le_mul_of_nonneg_right hK h2.le
            calc Sfun a c (k + 1) - Sfun a c k
                = 1 * (Sfun a c (k + 1) - Sfun a c k) := (one_mul _).symm
              _ ≤ (coreConst a c * (a / 4)) * (Sfun a c (k + 1) - Sfun a c k) :=
                  mul_le_mul_of_nonneg_right hone hnn
              _ = coreConst a c * (Sfun a c (k + 1) - Sfun a c k) * (a / 4) := by ring
          linarith
        have hsum : ∑ n ∈ Finset.range (k + 1), Tfun a c n
            = (∑ n ∈ Finset.range k, Tfun a c n) + Tfun a c k := Finset.sum_range_succ _ _
        rw [hsum]
        calc (∑ n ∈ Finset.range k, Tfun a c n) + Tfun a c k
            ≤ coreConst a c * Sfun a c k
                + coreConst a c * (Sfun a c (k + 1) - Sfun a c k) := by linarith
          _ = coreConst a c * Sfun a c (k + 1) := by ring
  by_cases hM : coreThresh a c ≤ M
  · exact hmain M hM
  · have hMle : M ≤ coreThresh a c := le_of_lt (not_le.mp hM)
    have h1 : ∑ n ∈ Finset.range M, Tfun a c n
        ≤ ∑ n ∈ Finset.range (coreThresh a c), Tfun a c n := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr hMle)
      intro x _ _
      exact Tfun_nonneg a c x
    have h2 := core_sum_le_thresh (a := a) (c := c) ha hc
    have h3 := thresh_bound_le_coreConst (a := a) (c := c) ha hc
    have h4 : LamR ((coreThresh a c : ℕ) : ℝ) ^ (-c) ≤ Sfun a c M := by
      have hmono : LamR ((M:ℕ) : ℝ) ≤ LamR ((coreThresh a c : ℕ) : ℝ) := by
        apply LamR_mono (Nat.cast_nonneg _)
        exact_mod_cast hMle
      have hle : LamR ((coreThresh a c : ℕ) : ℝ) ^ (-c) ≤ LamR ((M:ℕ) : ℝ) ^ (-c) :=
        Real.rpow_le_rpow_of_nonpos (LamR_pos (Nat.cast_nonneg M)) hmono (by linarith)
      exact le_trans hle (LamR_rpow_le_Sfun ha M)
    have h5 := coreConst_pos (a := a) (c := c)
    calc ∑ n ∈ Finset.range M, Tfun a c n
        ≤ ∑ n ∈ Finset.range (coreThresh a c), Tfun a c n := h1
      _ ≤ (coreThresh a c : ℝ) *
            (max 1 (((coreThresh a c : ℕ) : ℝ) ^ (a - 1)) * LamR ((0:ℕ) : ℝ) ^ (-c)) := h2
      _ ≤ coreConst a c * LamR ((coreThresh a c : ℕ) : ℝ) ^ (-c) := h3
      _ ≤ coreConst a c * Sfun a c M := mul_le_mul_of_nonneg_left h4 h5.le



/-! ## §5 The weight `Wt` and its interaction with the power profile -/

/-- `Wt (d-a) c` is antitone on `[0,∞)`, so the clamped weight `r ↦ Wt (d-a) c (max r 0)`
is antitone on `ℝ` (the finite layer-cake lemma asks for a weight on all of `ℝ`). -/
lemma Wt_max_antitone {d a c : ℝ} (had : a < d) (hc : 0 ≤ c) {r s : ℝ} (hrs : r ≤ s) :
    Wt (d - a) c (max s 0) ≤ Wt (d - a) c (max r 0) := by
  have he : 0 < d - a := by linarith
  by_cases h : 0 ≤ r
  · rw [max_eq_left h, max_eq_left (le_trans h hrs)]
    exact Wt_antitone he hc h hrs
  · rw [max_eq_right (not_le.mp h).le]
    by_cases hs : 0 ≤ s
    · rw [max_eq_left hs]
      exact Wt_antitone he hc le_rfl hs
    · rw [max_eq_right (not_le.mp hs).le]

lemma Wt_max_of_nonneg {e c : ℝ} {r : ℝ} (hr : 0 ≤ r) : Wt e c (max r 0) = Wt e c r := by
  rw [max_eq_left hr]

@[simp] lemma Wt_max_natCast (e c : ℝ) (n : ℕ) :
    Wt e c (max (n:ℝ) 0) = Wt e c (n:ℝ) := Wt_max_of_nonneg (Nat.cast_nonneg n)

@[simp] lemma Wt_max_natCast_succ (e c : ℝ) (n : ℕ) :
    Wt e c (max ((n:ℝ) + 1) 0) = Wt e c ((n:ℝ) + 1) := Wt_max_of_nonneg (by positivity)

/-- The layer-cake weight decrement, integrated against the ball counting profile. -/
lemma Wt_incr_mul_pow_le {d a c : ℝ} (had : a < d) (hc : 0 ≤ c) (n : ℕ) :
    (Wt (d - a) c (n : ℝ) - Wt (d - a) c ((n : ℝ) + 1)) * (1 + (n : ℝ)) ^ d
      ≤ (d - a + 2 * (c + 1)) * Tfun a c n := by
  have he : 0 < d - a := by linarith
  have hbase : (0:ℝ) < 1 + (n:ℝ) := by positivity
  have hincr := Wt_incr_le (e := d - a) (c := c) he hc n
  have hpow0 : (0:ℝ) ≤ (1 + (n:ℝ)) ^ d := Real.rpow_nonneg hbase.le d
  have h1 : (Wt (d - a) c (n : ℝ) - Wt (d - a) c ((n : ℝ) + 1)) * (1 + (n : ℝ)) ^ d
      ≤ ((d - a + 2 * (c + 1)) * (1 + (n:ℝ)) ^ (-(d - a) - 1) * LamR (n:ℝ) ^ (-c))
        * (1 + (n : ℝ)) ^ d :=
    mul_le_mul_of_nonneg_right hincr hpow0
  have hpowid : (1 + (n:ℝ)) ^ (-(d - a) - 1) * (1 + (n:ℝ)) ^ d = (1 + (n:ℝ)) ^ (a - 1) := by
    rw [← Real.rpow_add hbase]
    congr 1
    ring
  have hL : ((d - a + 2 * (c + 1)) * (1 + (n:ℝ)) ^ (-(d - a) - 1) * LamR (n:ℝ) ^ (-c))
        * (1 + (n : ℝ)) ^ d
      = (d - a + 2 * (c + 1)) * (((1 + (n:ℝ)) ^ (-(d - a) - 1) * (1 + (n:ℝ)) ^ d)
        * LamR (n:ℝ) ^ (-c)) := by ring
  rw [hL, hpowid] at h1
  unfold Tfun
  calc (Wt (d - a) c (n : ℝ) - Wt (d - a) c ((n : ℝ) + 1)) * (1 + (n : ℝ)) ^ d
      ≤ (d - a + 2 * (c + 1)) * ((1 + (n:ℝ)) ^ (a - 1) * LamR (n:ℝ) ^ (-c)) := h1
    _ = (d - a + 2 * (c + 1)) * ((1 + (n : ℝ)) ^ (a - 1) * LamR (n : ℝ) ^ (-c)) := by ring

/-- The layer-cake boundary term, integrated against the ball counting profile. -/
lemma Wt_mul_pow_le {d a c : ℝ} (had : a < d) (M : ℕ) :
    Wt (d - a) c (M : ℝ) * (1 + (M:ℝ)) ^ d ≤ Sfun a c M := by
  unfold Wt Sfun
  have hbase : (0:ℝ) < 1 + (M:ℝ) := by positivity
  have hpowid : (1 + (M:ℝ)) ^ (-(d - a)) * (1 + (M:ℝ)) ^ d = (1 + (M:ℝ)) ^ a := by
    rw [← Real.rpow_add hbase]
    congr 1
    ring
  have h2 : (1 + (M:ℝ)) ^ (-(d - a)) * LamR (M:ℝ) ^ (-c) * (1 + (M:ℝ)) ^ d
      = (1 + (M:ℝ)) ^ a * LamR (M:ℝ) ^ (-c) := by
    rw [show (1 + (M:ℝ)) ^ (-(d - a)) * LamR (M:ℝ) ^ (-c) * (1 + (M:ℝ)) ^ d
        = ((1 + (M:ℝ)) ^ (-(d - a)) * (1 + (M:ℝ)) ^ d) * LamR (M:ℝ) ^ (-c) from by ring,
      hpowid]
  exact le_of_eq h2



/-! ## §6 The weighted ball shell bound (A1/A2 of (I.4.12)) -/

/-- **Weighted ball shell bound.**  For a finite set `F` of lattice points with
`ρ y ≤ S`, whose ball counting function is dominated by `Ce · (1+n)^d`, the total
weight `Σ_y (1+ρ y)^{-(d-a)} (log (2+ρ y))^{-c}` is bounded by
`K · (1+S)^a (log (2+S))^{-c}` with `K` independent of `S` (it depends only on
`a, c, d` and the counting constant `Ce`).

This is the ball (A1/A2) part of estimate (I.4.12) in the proof of Lemma I.4.3. -/
theorem ball_shell_bound
    {G : Type*} [AddCommGroup G] {ρ : G → ℝ} (hρnn : ∀ x, 0 ≤ ρ x)
    {d a c Ce S : ℝ} (ha : 0 < a) (had : a < d) (hc : 0 ≤ c) (hS : 0 ≤ S) (hCe : 0 ≤ Ce)
    {F : Finset G} (hrad : ∀ y ∈ F, ρ y ≤ S)
    (hcnt : ∀ n : ℕ, ((F.filter (fun y => ⌊ρ y⌋₊ ≤ n)).card : ℝ) ≤ Ce * (1 + (n:ℝ)) ^ d) :
    ∑ y ∈ F, Wt (d - a) c (ρ y) ≤ 2 ^ a * (Ce * (1 + (d - a + 2 * (c + 1)) * coreConst a c)) *
      ((1 + S) ^ a * LamR S ^ (-c)) := by
  classical
  have he : 0 < d - a := by linarith
  set M : ℕ := ⌊S⌋₊ + 1
  have hSM : S ≤ (M:ℝ) := by
    have h1 : S < (⌊S⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one S
    have h2 : ((M:ℕ) : ℝ) = (⌊S⌋₊ : ℝ) + 1 := by simp [M]
    linarith
  have hradM : ∀ y ∈ F, ⌊ρ y⌋₊ ≤ M := by
    intro y hy
    have h1 : ⌊ρ y⌋₊ ≤ ⌊S⌋₊ := Nat.floor_mono (hrad y hy)
    have h2 : ⌊S⌋₊ < M := by simp [M]
    omega
  -- the finite layer-cake identity for the clamped weight
  have hcake := finset_layer_cake (ρ := ρ) (w := fun r => Wt (d - a) c (max r 0))
    (F := F) (M := M) (fun r s hrs => Wt_max_antitone had hc hrs) hρnn hradM
  rw [Finset.sum_congr rfl (fun y hy => Wt_max_of_nonneg (hρnn y))] at hcake
  simp only [Wt_max_natCast, Wt_max_natCast_succ] at hcake
  -- termwise bound against the shell profile
  have hterm : ∀ n ∈ Finset.range M,
      (Wt (d - a) c (n : ℝ) - Wt (d - a) c ((n : ℝ) + 1)) *
        ((F.filter (fun y => ⌊ρ y⌋₊ ≤ n)).card : ℝ)
      ≤ Ce * (d - a + 2 * (c + 1)) * Tfun a c n := by
    intro n _
    have hcntn := hcnt n
    have hmono : Wt (d - a) c ((n:ℝ) + 1) ≤ Wt (d - a) c (n:ℝ) :=
      Wt_antitone he hc (Nat.cast_nonneg n) (by linarith)
    have hWnn : (0:ℝ) ≤ Wt (d - a) c (n : ℝ) - Wt (d - a) c ((n : ℝ) + 1) := by linarith
    calc (Wt (d - a) c (n : ℝ) - Wt (d - a) c ((n : ℝ) + 1)) *
          ((F.filter (fun y => ⌊ρ y⌋₊ ≤ n)).card : ℝ)
        ≤ (Wt (d - a) c (n : ℝ) - Wt (d - a) c ((n : ℝ) + 1)) * (Ce * (1 + (n:ℝ)) ^ d) :=
          mul_le_mul_of_nonneg_left hcntn hWnn
      _ = Ce * ((Wt (d - a) c (n : ℝ) - Wt (d - a) c ((n : ℝ) + 1)) * (1 + (n:ℝ)) ^ d) := by
          ring
      _ ≤ Ce * ((d - a + 2 * (c + 1)) * Tfun a c n) :=
          mul_le_mul_of_nonneg_left (Wt_incr_mul_pow_le had hc n) hCe
      _ = Ce * (d - a + 2 * (c + 1)) * Tfun a c n := by ring
  -- the boundary term
  have hcard : (F.card : ℝ) ≤ Ce * (1 + (M:ℝ)) ^ d := by
    have h1 : F.filter (fun y => ⌊ρ y⌋₊ ≤ M) = F := Finset.filter_true_of_mem hradM
    have h2 := hcnt M
    rwa [h1] at h2
  have hWnn2 : (0:ℝ) ≤ Wt (d - a) c (M : ℝ) := Wt_nonneg (Nat.cast_nonneg M)
  have hbound : Wt (d - a) c (M : ℝ) * (F.card : ℝ) ≤ Ce * Sfun a c M := by
    calc Wt (d - a) c (M : ℝ) * (F.card : ℝ)
        ≤ Wt (d - a) c (M : ℝ) * (Ce * (1 + (M:ℝ)) ^ d) :=
          mul_le_mul_of_nonneg_left hcard hWnn2
      _ = Ce * (Wt (d - a) c (M : ℝ) * (1 + (M:ℝ)) ^ d) := by ring
      _ ≤ Ce * Sfun a c M := mul_le_mul_of_nonneg_left (Wt_mul_pow_le had M) hCe
  have hK0 : (0:ℝ) ≤ Ce * (d - a + 2 * (c + 1)) := by
    have h : (0:ℝ) ≤ d - a + 2 * (c + 1) := by linarith
    exact mul_nonneg hCe h
  have hsum : ∑ y ∈ F, Wt (d - a) c (ρ y)
      ≤ Ce * (d - a + 2 * (c + 1)) * (∑ n ∈ Finset.range M, Tfun a c n) + Ce * Sfun a c M := by
    have hsum1 : ∑ n ∈ Finset.range M,
          (Wt (d - a) c (n : ℝ) - Wt (d - a) c ((n : ℝ) + 1)) *
            ((F.filter (fun y => ⌊ρ y⌋₊ ≤ n)).card : ℝ)
        ≤ ∑ n ∈ Finset.range M, (Ce * (d - a + 2 * (c + 1)) * Tfun a c n) :=
      Finset.sum_le_sum hterm
    have hsum2 : ∑ n ∈ Finset.range M, (Ce * (d - a + 2 * (c + 1)) * Tfun a c n)
        = Ce * (d - a + 2 * (c + 1)) * (∑ n ∈ Finset.range M, Tfun a c n) := by
      rw [Finset.mul_sum]
    linarith [hcake, hsum1, hbound]
  -- the shell sum is bounded by the core constant times `Sfun a c M`
  have hcore := core_sum_bound ha hc M
  have hMle : Ce * (d - a + 2 * (c + 1)) * (∑ n ∈ Finset.range M, Tfun a c n)
      ≤ Ce * (d - a + 2 * (c + 1)) * (coreConst a c * Sfun a c M) :=
    mul_le_mul_of_nonneg_left hcore hK0
  have hcoef : (0:ℝ) ≤ Ce * (1 + (d - a + 2 * (c + 1)) * coreConst a c) := by
    have hcpos := coreConst_pos (a := a) (c := c)
    have h2 : (0:ℝ) ≤ d - a + 2 * (c + 1) := by linarith
    have h3 : (0:ℝ) ≤ (d - a + 2 * (c + 1)) * coreConst a c := mul_nonneg h2 hcpos.le
    have h4 : (0:ℝ) ≤ 1 + (d - a + 2 * (c + 1)) * coreConst a c := by linarith
    exact mul_nonneg hCe h4
  -- comparison of the target profile at `M` with the target profile at `S`
  have hbase_le : (1 + (M:ℝ)) ≤ 2 * (1 + S) := by
    have h1 : ((M:ℕ) : ℝ) = (⌊S⌋₊ : ℝ) + 1 := by simp [M]
    have h2 : (⌊S⌋₊ : ℝ) ≤ S := Nat.floor_le hS
    linarith
  have hΛle : LamR (M:ℝ) ^ (-c) ≤ LamR S ^ (-c) := by
    have hmono : LamR S ≤ LamR (M:ℝ) := LamR_mono hS hSM
    exact Real.rpow_le_rpow_of_nonpos (LamR_pos hS) hmono (by linarith)
  have hSfun_le : Sfun a c M ≤ 2 ^ a * ((1 + S) ^ a * LamR S ^ (-c)) := by
    have h0 : (0:ℝ) ≤ (M:ℝ) := Nat.cast_nonneg M
    have hpow : (1 + (M:ℝ)) ^ a ≤ (2 * (1 + S)) ^ a :=
      Real.rpow_le_rpow (by positivity) hbase_le ha.le
    calc Sfun a c M = (1 + (M:ℝ)) ^ a * LamR (M:ℝ) ^ (-c) := rfl
      _ ≤ (2 * (1 + S)) ^ a * LamR S ^ (-c) :=
          mul_le_mul hpow hΛle (Real.rpow_nonneg (LamR_pos h0).le _)
            (Real.rpow_nonneg (by positivity) _)
      _ = 2 ^ a * ((1 + S) ^ a * LamR S ^ (-c)) := by
          rw [Real.mul_rpow (by norm_num) (by linarith : (0:ℝ) ≤ 1 + S)]
          ring
  have hstep : Ce * (d - a + 2 * (c + 1)) * (coreConst a c * Sfun a c M) + Ce * Sfun a c M
      ≤ Ce * (1 + (d - a + 2 * (c + 1)) * coreConst a c) * Sfun a c M := by
    have h : Ce * (d - a + 2 * (c + 1)) * (coreConst a c * Sfun a c M) + Ce * Sfun a c M
        = (Ce * (1 + (d - a + 2 * (c + 1)) * coreConst a c)) * Sfun a c M := by ring
    rw [h]
  calc ∑ y ∈ F, Wt (d - a) c (ρ y)
      ≤ Ce * (d - a + 2 * (c + 1)) * (∑ n ∈ Finset.range M, Tfun a c n) + Ce * Sfun a c M :=
        hsum
    _ ≤ Ce * (d - a + 2 * (c + 1)) * (coreConst a c * Sfun a c M) + Ce * Sfun a c M := by
        linarith [hMle]
    _ ≤ Ce * (1 + (d - a + 2 * (c + 1)) * coreConst a c) * Sfun a c M := hstep
    _ ≤ Ce * (1 + (d - a + 2 * (c + 1)) * coreConst a c)
          * (2 ^ a * ((1 + S) ^ a * LamR S ^ (-c))) :=
        mul_le_mul_of_nonneg_left hSfun_le hcoef
    _ = 2 ^ a * (Ce * (1 + (d - a + 2 * (c + 1)) * coreConst a c)) *
          ((1 + S) ^ a * LamR S ^ (-c)) := by ring



/-! ## §7 The concrete `ℤ^D` lattice instance -/

/-- **The ball shell bound on the actual lattice `ℤ^D`** (sup-norm radius `‖y‖`): for a
finite set `F` contained in the ball of radius `S`, the weighted ball sum of
`(1+‖y‖)^{-(D-a)} (log (2+‖y‖))^{-c}` is bounded by `K (1+S)^a (log (2+S))^{-c}` with
`K` depending only on `D, a, c`.

The counting hypothesis of `ball_shell_bound` is discharged here by the proved lattice
ball cardinality `#{‖y‖ ≤ n} = (2n+1)^D`. -/
theorem ball_shell_bound_latticeInt (D : ℕ) {a c S : ℝ} (ha : 0 < a) (haD : a < (D : ℝ))
    (hc : 0 ≤ c) (hS : 0 ≤ S) {F : Finset (Fin D → ℤ)} (hrad : ∀ y ∈ F, ‖y‖ ≤ S) :
    ∑ y ∈ F, Wt ((D : ℝ) - a) c ‖y‖ ≤
      2 ^ a * (2 ^ (D : ℝ) * (1 + ((D:ℝ) - a + 2 * (c + 1)) * coreConst a c)) *
        ((1 + S) ^ a * LamR S ^ (-c)) := by
  refine ball_shell_bound (ρ := fun y : Fin D → ℤ => ‖y‖) (fun y => norm_nonneg y) ha haD hc
    hS (by positivity) hrad ?_
  intro n
  have hsub : F.filter (fun y => ⌊‖y‖⌋₊ ≤ n) ⊆
      Finset.Icc (fun _ : Fin D => -(n:ℤ)) (fun _ => (n:ℤ)) := by
    intro y hy
    rw [Finset.mem_filter] at hy
    rw [PercLib.Models.LongRange.mem_Icc_iff_norm_le]
    have h1 : ‖y‖ = ((⌊‖y‖⌋₊ : ℕ) : ℝ) := (PercLib.Models.LongRange.natCast_floor_norm y).symm
    rw [h1]
    exact_mod_cast hy.2
  have h2 : ((F.filter (fun y => ⌊‖y‖⌋₊ ≤ n)).card : ℝ) ≤ ((2 * n + 1) ^ D : ℕ) := by
    have h3 : (F.filter (fun y => ⌊‖y‖⌋₊ ≤ n)).card
        ≤ (Finset.Icc (fun _ : Fin D => -(n:ℤ)) (fun _ => (n:ℤ))).card :=
      Finset.card_le_card hsub
    rw [PercLib.Models.LongRange.card_Icc_ball n] at h3
    exact_mod_cast h3
  have h4 : (((2 * n + 1) ^ D : ℕ) : ℝ) ≤ 2 ^ (D : ℝ) * (1 + (n:ℝ)) ^ (D:ℝ) := by
    have h5 : ((2 * n + 1 : ℕ) : ℝ) = 2 * (n:ℝ) + 1 := by push_cast; ring
    have h9 : (((2 * n + 1) ^ D : ℕ) : ℝ) = ((2 * n + 1 : ℕ) : ℝ) ^ (D:ℝ) := by
      rw [Nat.cast_pow, Real.rpow_natCast]
    rw [h9, h5]
    have h6 : (0:ℝ) ≤ 2 * (n:ℝ) + 1 := by positivity
    have h7 : (2 * (n:ℝ) + 1) ^ (D:ℝ) ≤ (2 * ((n:ℝ) + 1)) ^ (D:ℝ) :=
      Real.rpow_le_rpow h6 (by linarith) (Nat.cast_nonneg D)
    have h8 : (2 * ((n:ℝ) + 1)) ^ (D:ℝ) = 2 ^ (D : ℝ) * (1 + (n:ℝ)) ^ (D:ℝ) := by
      rw [Real.mul_rpow (by norm_num) (by positivity)]
      ring_nf
    rw [h8] at h7
    exact h7
  exact h2.trans h4

/-! ## §8 The source-level `A1` contribution -/

/-- **The `A1`/`A2` contribution of (I.4.12), in the paper's normalisation.**  Multiplying
the ball shell bound by the outer factor `⟨S⟩^{-d+b}(log⟨S⟩)^{-b̂}` gives exactly the
source's displayed contribution
`⟨S⟩^{-d+a+b}(log⟨S⟩)^{-b̂-c}` — no further analytic content, but stated so that the
correspondence with (I.4.12) is machine-checked rather than verbal. -/
theorem A1_contribution_bound
    {G : Type*} [AddCommGroup G] {ρ : G → ℝ} (hρnn : ∀ x, 0 ≤ ρ x)
    {d a c bh Ce S : ℝ} (ha : 0 < a) (had : a < d) (hc : 0 ≤ c) (hbh : 0 ≤ bh)
    (hS : 0 ≤ S) (hCe : 0 ≤ Ce)
    {F : Finset G} (hrad : ∀ y ∈ F, ρ y ≤ S)
    (hcnt : ∀ n : ℕ, ((F.filter (fun y => ⌊ρ y⌋₊ ≤ n)).card : ℝ) ≤ Ce * (1 + (n:ℝ)) ^ d) :
    (1 + S) ^ (-d + bh) * LamR S ^ (-bh) * (∑ y ∈ F, Wt (d - a) c (ρ y))
      ≤ 2 ^ a * (Ce * (1 + (d - a + 2 * (c + 1)) * coreConst a c)) *
          ((1 + S) ^ (-d + a + bh) * LamR S ^ (-(bh + c))) := by
  have hb := ball_shell_bound hρnn ha had hc hS hCe hrad hcnt
  have hbase : (0:ℝ) < 1 + S := by linarith
  have hΛ : (0:ℝ) < LamR S := LamR_pos hS
  have hcoef : (0:ℝ) ≤ (1 + S) ^ (-d + bh) * LamR S ^ (-bh) :=
    mul_nonneg (Real.rpow_nonneg hbase.le _) (Real.rpow_nonneg hΛ.le _)
  have hmul := mul_le_mul_of_nonneg_left hb hcoef
  refine hmul.trans_eq ?_
  have e1 : (1 + S) ^ (-d + bh) * (1 + S) ^ a = (1 + S) ^ (-d + a + bh) := by
    rw [← Real.rpow_add hbase]
    congr 1
    ring
  have e2 : LamR S ^ (-bh) * LamR S ^ (-c) = LamR S ^ (-(bh + c)) := by
    rw [← Real.rpow_add hΛ]
    congr 1
    ring
  calc (1 + S) ^ (-d + bh) * LamR S ^ (-bh)
        * (2 ^ a * (Ce * (1 + (d - a + 2 * (c + 1)) * coreConst a c))
          * ((1 + S) ^ a * LamR S ^ (-c)))
      = 2 ^ a * (Ce * (1 + (d - a + 2 * (c + 1)) * coreConst a c))
          * ((1 + S) ^ (-d + bh) * (1 + S) ^ a) * (LamR S ^ (-bh) * LamR S ^ (-c)) := by
        ring
    _ = 2 ^ a * (Ce * (1 + (d - a + 2 * (c + 1)) * coreConst a c))
          * ((1 + S) ^ (-d + a + bh) * LamR S ^ (-(bh + c))) := by
        rw [e1, e2]
        ring

end CriticalLRPConv

set_option linter.hashCommand false

/-! ## §9 Axiom audit -/

#print axioms CriticalLRPConv.exp_step_aux
#print axioms CriticalLRPConv.one_div_two_mul_le_log_one_add_inv
#print axioms CriticalLRPConv.Sfun_succ
#print axioms CriticalLRPConv.Tfun_eq_Sfun_div
#print axioms CriticalLRPConv.Sfun_step
#print axioms CriticalLRPConv.LamR_coreThresh
#print axioms CriticalLRPConv.one_le_coreThresh
#print axioms CriticalLRPConv.le_coreConst_max
#print axioms CriticalLRPConv.coreConst_pos
#print axioms CriticalLRPConv.Tfun_le_of_lt_thresh
#print axioms CriticalLRPConv.core_sum_le_thresh
#print axioms CriticalLRPConv.thresh_bound_le_coreConst
#print axioms CriticalLRPConv.LamR_rpow_le_Sfun
#print axioms CriticalLRPConv.core_sum_bound
#print axioms CriticalLRPConv.Wt_max_antitone
#print axioms CriticalLRPConv.Wt_incr_mul_pow_le
#print axioms CriticalLRPConv.Wt_mul_pow_le
#print axioms CriticalLRPConv.ball_shell_bound
#print axioms CriticalLRPConv.ball_shell_bound_latticeInt
#print axioms CriticalLRPConv.A1_contribution_bound
