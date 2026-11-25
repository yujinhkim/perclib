/-
# `ℓ^p` membership of the campaign's power–log radial weight

Swarm `smwtxo95t`, member `m3`, direction d6.

The campaign weights are `Wt e c r = (1 + r)^{-e} (log (2 + r))^{-c}` evaluated at the
sup-norm radius `‖y‖_∞` of a lattice point `y : Fin d → ℤ`.  This file decides for which
`p` the weight `Wt γ ĉ` belongs to `ℓ^p` of the lattice, i.e. for which parameters the
lattice series `∑'_y |Wt γ ĉ ‖y‖|^p` converges.

Convergence side (this file): for `p > 0` the identity `|Wt γ ĉ r|^p = Wt (p γ) (p ĉ) r`
reduces `ℓ^p` membership to summability of a power–log weight.  The finite lattice box is
handled separately (it is a single point at radius `0`), and everything outside it is the
`A3` far region covered by `TailShell`.

* `summable_Wt_of_lt` : radius exponent `> d` (the `γ > 0` case of `tailShellConst`);
* `summable_Wt_marginal` : critical radius exponent `= d` with log exponent `> 1`
  (the pure-log `c - 1` case of `tailShellConstLog`).

No new definition is introduced; the imported `Wt` is used unchanged.
-/
module

public import PercLib.CriticalLRP.Analysis.LatticeConvolution.TailShell
public import PercLib.CriticalLRP.LatticeGeometry

/-!
Sharp convergence and divergence criteria for the power–log radial lattice weight, with exact
log-critical and square-column thresholds.
-/

set_option autoImplicit false

@[expose] public section

open Finset Filter

namespace CriticalLRPConv

open PercLib.CriticalLRP.FiniteVolume (box card_box linfNorm mem_box_iff sum_box_eq)

/-! ## §1 The value at the origin -/

lemma Wt_zero (e c : ℝ) : Wt e c 0 = LamR 0 ^ (-c) := by
  unfold Wt
  simp

/-! ## §2 Summability from a far-region bound

The lattice splits into the single origin (radius `0`) and the far region `‖y‖ > 0`, so a
uniform bound on finite subsets of the far region gives summability with constant
`Wt e c 0 + K`.  This is the shape in which both `TailShell` estimates are available. -/

theorem summable_Wt_of_tail_bound {d : ℕ} {e c : ℝ} {K : ℝ}
    (htail : ∀ F : Finset (Fin d → ℤ), (∀ y ∈ F, 0 < (linfNorm y : ℝ)) →
      ∑ y ∈ F, Wt e c (linfNorm y : ℝ) ≤ K) :
    Summable (fun y : Fin d → ℤ => Wt e c (linfNorm y : ℝ)) := by
  classical
  have hbdd : ∀ u : Finset (Fin d → ℤ),
      ∑ y ∈ u, Wt e c (linfNorm y : ℝ) ≤ Wt e c 0 + K := by
    intro u
    have hsplit := Finset.sum_filter_add_sum_filter_not (s := u)
      (p := fun y : Fin d → ℤ => linfNorm y = 0)
      (f := fun y => Wt e c (linfNorm y : ℝ))
    rw [← hsplit]
    have hzero : ∑ y ∈ u.filter (fun y : Fin d → ℤ => linfNorm y = 0),
        Wt e c (linfNorm y : ℝ) ≤ Wt e c 0 := by
      have hterm : ∀ y ∈ u.filter (fun y : Fin d → ℤ => linfNorm y = 0),
          Wt e c (linfNorm y : ℝ) = Wt e c 0 := by
        intro y hy
        rw [Finset.mem_filter] at hy
        rw [hy.2, Nat.cast_zero]
      have hcard : (u.filter (fun y : Fin d → ℤ => linfNorm y = 0)).card ≤ 1 := by
        have hsub : u.filter (fun y : Fin d → ℤ => linfNorm y = 0) ⊆
            PercLib.CriticalLRP.FiniteVolume.box d 0 := by
          intro y hy
          rw [Finset.mem_filter] at hy
          rw [PercLib.CriticalLRP.FiniteVolume.mem_box_iff]
          omega
        calc (u.filter (fun y : Fin d → ℤ => linfNorm y = 0)).card
            ≤ (PercLib.CriticalLRP.FiniteVolume.box d 0).card := Finset.card_le_card hsub
          _ = 1 := by rw [card_box]; norm_num
      calc ∑ y ∈ u.filter (fun y : Fin d → ℤ => linfNorm y = 0),
            Wt e c (linfNorm y : ℝ)
          = ((u.filter (fun y : Fin d → ℤ => linfNorm y = 0)).card : ℝ) * Wt e c 0 := by
            rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul]
        _ ≤ Wt e c 0 := by
            have hcard1 : ((u.filter (fun y : Fin d → ℤ => linfNorm y = 0)).card : ℝ)
                ≤ 1 := by
              exact_mod_cast hcard
            calc ((u.filter (fun y : Fin d → ℤ => linfNorm y = 0)).card : ℝ) * Wt e c 0
                ≤ 1 * Wt e c 0 := by
                  refine mul_le_mul_of_nonneg_right hcard1 (Wt_nonneg (le_refl (0 : ℝ)))
              _ = Wt e c 0 := one_mul _
    have hfar : ∑ y ∈ u.filter (fun y : Fin d → ℤ => ¬ (linfNorm y = 0)),
        Wt e c (linfNorm y : ℝ) ≤ K := by
      refine htail _ ?_
      intro y hy
      rw [Finset.mem_filter] at hy
      have hpos : 0 < linfNorm y := Nat.pos_of_ne_zero hy.2
      exact_mod_cast hpos
    linarith
  exact summable_of_sum_le (fun y => Wt_nonneg (by positivity)) hbdd

/-! ## §3 The two convergent regimes -/

/-- **Subcritical radius exponent.** For `d < e` and `c ≥ 0` the weight is summable: the
far region is the `γ = e - d > 0` case of `sum_Wt_tail_le`. -/
theorem summable_Wt_of_lt {d : ℕ} (hd : 0 < d) {e c : ℝ} (he : (d : ℝ) < e) (hc : 0 ≤ c) :
    Summable (fun y : Fin d → ℤ => Wt e c (linfNorm y : ℝ)) := by
  have he0 : 0 < e := lt_of_le_of_lt (Nat.cast_nonneg d) he
  have hγ : 0 < e - (d : ℝ) := by linarith
  have heq : (d : ℝ) + (e - (d : ℝ)) = e := by ring
  refine summable_Wt_of_tail_bound
    (K := tailShellConst d (e - (d : ℝ)) * Wt (e - (d : ℝ)) c 0) ?_
  intro F hF
  have h := sum_Wt_tail_le (d := d) hd (γ := e - (d : ℝ)) (c := c) hγ hc
    (S := 0) (by norm_num) F hF
  simpa [heq] using h

/-- **Critical radius exponent.** For `e = d` and log exponent `c > 1` the weight is
summable: the far region is the pure-log `c - 1` case `sum_Wt_tail_le_pureLog`. -/
theorem summable_Wt_marginal {d : ℕ} (hd : 0 < d) {c : ℝ} (hc : 1 < c) :
    Summable (fun y : Fin d → ℤ => Wt (d : ℝ) c (linfNorm y : ℝ)) := by
  have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hc0 : 0 ≤ c := by linarith
  refine summable_Wt_of_tail_bound
    (K := tailShellConstLog d c * Wt 0 (c - 1) 0) ?_
  intro F hF
  exact sum_Wt_tail_le_pureLog hd hc (S := 0) (by norm_num) F hF

/-! ## §4 The `ℓ^p` transfer -/

/-- The `p`-th power of the weight is the weight with both exponents multiplied by `p`. -/
lemma Wt_rpow {e c r p : ℝ} (hr : 0 ≤ r) :
    Wt e c r ^ p = Wt (p * e) (p * c) r := by
  unfold Wt
  rw [Real.mul_rpow (Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ 1 + r) _)
    (Real.rpow_nonneg (LamR_nonneg hr) _)]
  rw [← Real.rpow_mul (by linarith : (0 : ℝ) ≤ 1 + r),
    ← Real.rpow_mul (LamR_nonneg hr)]
  have h1 : -e * p = -(p * e) := by ring
  have h2 : -c * p = -(p * c) := by ring
  rw [h1, h2]

/-- **`ℓ^p` membership, convergent cases.** For `p > 0` the weight `Wt γ ĉ` is `p`-summable
as soon as `p γ > d`, or `p γ = d` with `p ĉ > 1`. -/
theorem summable_abs_rpow_Wt {d : ℕ} (hd : 0 < d) {γ ĉ p : ℝ} (hĉ : 0 ≤ ĉ) (hp : 0 < p)
    (h : (d : ℝ) < p * γ ∨ (p * γ = d ∧ 1 < p * ĉ)) :
    Summable (fun y : Fin d → ℤ => |Wt γ ĉ (linfNorm y : ℝ)| ^ p) := by
  have hfun : (fun y : Fin d → ℤ => |Wt γ ĉ (linfNorm y : ℝ)| ^ p)
      = fun y => Wt (p * γ) (p * ĉ) (linfNorm y : ℝ) := by
    funext y
    rw [abs_of_pos (Wt_pos (by positivity)), Wt_rpow (by positivity)]
  rw [hfun]
  rcases h with h | ⟨h1, h2⟩
  · exact summable_Wt_of_lt (d := d) (e := p * γ) (c := p * ĉ) hd h (by positivity)
  · rw [h1]
    exact summable_Wt_marginal hd h2

/-! ## §5 Divergence at the critical exponent -/

/-- `x ^ (-1) = x⁻¹` for `x ≥ 0`. -/
lemma rpow_neg_one_eq_inv {x : ℝ} (hx : 0 ≤ x) : x ^ (-1 : ℝ) = x⁻¹ := by
  rw [Real.rpow_neg hx, Real.rpow_one]

/-- The shifted harmonic series diverges: `∑_{k<K} (k+3)⁻¹ → ∞`. -/
lemma tendsto_sum_range_inv_add_three :
    Tendsto (fun K : ℕ => ∑ k ∈ range K, (((k + 3 : ℕ)) : ℝ)⁻¹) atTop atTop := by
  have hshift : ¬ Summable (fun k : ℕ => (((k + 3 : ℕ)) : ℝ)⁻¹) := by
    intro hs
    refine Real.not_summable_one_div_natCast ?_
    have h := (summable_nat_add_iff 3 (f := fun n : ℕ => ((n : ℝ))⁻¹)).mp ?_
    · simpa [one_div] using h
    · simpa using hs
  exact (not_summable_iff_tendsto_nat_atTop_of_nonneg
    (f := fun k : ℕ => (((k + 3 : ℕ)) : ℝ)⁻¹) (fun k => by positivity)).mp hshift

/-- **Logarithmic divergence at the critical exponent.**
For `0 ≤ c ≤ 1` the series `∑_m m⁻¹ (log (2+m))^{-c}` diverges.  The proof is Cauchy
condensation: the condensed term is `(log (2+2^k))^{-c} ≳ (k+3)^{-c} ≥ (k+3)^{-1}`, and the
shifted harmonic series diverges. -/
lemma not_summable_inv_mul_LamR {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    ¬ Summable (fun m : ℕ => ((m : ℝ))⁻¹ * (LamR (m : ℝ)) ^ (-c)) := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  intro hS
  have hnonneg : ∀ n : ℕ, 0 ≤ ((n : ℝ))⁻¹ * (LamR (n : ℝ)) ^ (-c) := by
    intro n
    exact mul_nonneg (by positivity) (Real.rpow_nonneg (LamR_nonneg (by positivity)) _)
  have hmono : ∀ ⦃m n : ℕ⦄, 0 < m → m ≤ n →
      ((n : ℝ))⁻¹ * (LamR (n : ℝ)) ^ (-c)
        ≤ ((m : ℝ))⁻¹ * (LamR (m : ℝ)) ^ (-c) := by
    intro m n hm hmn
    have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
    have hmn' : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
    have hinv : ((n : ℝ))⁻¹ ≤ ((m : ℝ))⁻¹ := by
      simpa [one_div] using one_div_le_one_div_of_le hm0 hmn'
    have hLam : LamR ((m : ℝ)) ≤ LamR ((n : ℝ)) := LamR_mono (le_of_lt hm0) hmn'
    have hLampow : (LamR ((n : ℝ))) ^ (-c) ≤ (LamR ((m : ℝ))) ^ (-c) :=
      Real.rpow_le_rpow_of_nonpos (LamR_pos (by positivity)) hLam (by linarith)
    exact mul_le_mul hinv hLampow (Real.rpow_nonneg (LamR_nonneg (by positivity)) _)
      (by positivity)
  have hcond : Summable (fun k : ℕ =>
      (2 : ℝ) ^ k * (((2 ^ k : ℕ) : ℝ)⁻¹ * (LamR (((2 ^ k : ℕ)) : ℝ)) ^ (-c))) :=
    (summable_condensed_iff_of_nonneg hnonneg hmono).mpr hS
  have hterm : ∀ k : ℕ, (Real.log 2) ^ (-c) * (((k + 3 : ℕ)) : ℝ)⁻¹ ≤
      (2 : ℝ) ^ k * (((2 ^ k : ℕ) : ℝ)⁻¹ * (LamR (((2 ^ k : ℕ)) : ℝ)) ^ (-c)) := by
    intro k
    have h2k : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
    have hcast : (((2 ^ k : ℕ)) : ℝ) = (2 : ℝ) ^ k := by push_cast; ring
    have hR : (2 : ℝ) ^ k * (((2 ^ k : ℕ) : ℝ)⁻¹ * (LamR (((2 ^ k : ℕ)) : ℝ)) ^ (-c))
        = (LamR (((2 ^ k : ℕ)) : ℝ)) ^ (-c) := by
      rw [hcast, ← mul_assoc, mul_inv_cancel₀ (ne_of_gt h2k), one_mul]
    rw [hR]
    have hlog_le : LamR (((2 ^ k : ℕ)) : ℝ) ≤ (((k + 3 : ℕ)) : ℝ) * Real.log 2 := by
      unfold LamR
      rw [hcast]
      have hle : 2 + (2 : ℝ) ^ k ≤ (2 : ℝ) ^ (k + 3) := by
        have hexp : (2 : ℝ) ^ (k + 3) = (2 : ℝ) ^ k * 8 := by
          rw [pow_add]; norm_num
        have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ k := one_le_pow₀ (by norm_num)
        rw [hexp]; nlinarith
      calc Real.log (2 + (2 : ℝ) ^ k) ≤ Real.log ((2 : ℝ) ^ (k + 3)) :=
            Real.log_le_log (by positivity) hle
        _ = (((k + 3 : ℕ)) : ℝ) * Real.log 2 := by
            rw [Real.log_pow]
    have hstep : (((k + 3 : ℕ)) : ℝ) ^ (-c) * (Real.log 2) ^ (-c) ≤
        (LamR (((2 ^ k : ℕ)) : ℝ)) ^ (-c) := by
      rw [← Real.mul_rpow (by positivity) hlog2.le]
      exact Real.rpow_le_rpow_of_nonpos
        (LamR_pos (s := (((2 ^ k : ℕ)) : ℝ)) (by positivity)) hlog_le (by linarith)
    have hk3 : (1 : ℝ) < (((k + 3 : ℕ)) : ℝ) := by
      have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      push_cast
      linarith
    have hexp_le : (((k + 3 : ℕ)) : ℝ)⁻¹ ≤ (((k + 3 : ℕ)) : ℝ) ^ (-c) := by
      have h1 : (((k + 3 : ℕ)) : ℝ) ^ (-1 : ℝ) ≤ (((k + 3 : ℕ)) : ℝ) ^ (-c) := by
        rw [Real.rpow_le_rpow_left_iff hk3]
        linarith
      rwa [rpow_neg_one_eq_inv (x := (((k + 3 : ℕ)) : ℝ)) (Nat.cast_nonneg _)] at h1
    have hlogpow_nonneg : 0 ≤ (Real.log 2) ^ (-c) := Real.rpow_nonneg hlog2.le _
    calc (Real.log 2) ^ (-c) * (((k + 3 : ℕ)) : ℝ)⁻¹
      _ ≤ (Real.log 2) ^ (-c) * (((k + 3 : ℕ)) : ℝ) ^ (-c) :=
          mul_le_mul_of_nonneg_left hexp_le hlogpow_nonneg
      _ = (((k + 3 : ℕ)) : ℝ) ^ (-c) * (Real.log 2) ^ (-c) := by ring
      _ ≤ (LamR (((2 ^ k : ℕ)) : ℝ)) ^ (-c) := hstep
  have hbdd : ∀ K : ℕ, ∑ k ∈ range K,
        (2 : ℝ) ^ k * (((2 ^ k : ℕ) : ℝ)⁻¹ * (LamR (((2 ^ k : ℕ)) : ℝ)) ^ (-c))
      ≤ ∑' k, (2 : ℝ) ^ k *
          (((2 ^ k : ℕ) : ℝ)⁻¹ * (LamR (((2 ^ k : ℕ)) : ℝ)) ^ (-c)) := by
    intro K
    refine Summable.sum_le_tsum (range K) (fun i _ => ?_) hcond
    exact mul_nonneg (by positivity)
      (mul_nonneg (by positivity) (Real.rpow_nonneg (LamR_nonneg (by positivity)) _))
  have hlow : ∀ K : ℕ, (Real.log 2) ^ (-c) * ∑ k ∈ range K, (((k + 3 : ℕ)) : ℝ)⁻¹
      ≤ ∑ k ∈ range K,
        (2 : ℝ) ^ k * (((2 ^ k : ℕ) : ℝ)⁻¹ * (LamR (((2 ^ k : ℕ)) : ℝ)) ^ (-c)) := by
    intro K
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun k _ => hterm k)
  have hlim : Tendsto (fun K : ℕ =>
      (Real.log 2) ^ (-c) * ∑ k ∈ range K, (((k + 3 : ℕ)) : ℝ)⁻¹) atTop atTop :=
    tendsto_sum_range_inv_add_three.const_mul_atTop (Real.rpow_pos_of_pos hlog2 _)
  have hev : ∀ᶠ K : ℕ in atTop,
      (∑' k, (2 : ℝ) ^ k *
        (((2 ^ k : ℕ) : ℝ)⁻¹ * (LamR (((2 ^ k : ℕ)) : ℝ)) ^ (-c))) + 1
        < (Real.log 2) ^ (-c) * ∑ k ∈ range K, (((k + 3 : ℕ)) : ℝ)⁻¹ :=
    hlim.eventually (eventually_gt_atTop _)
  obtain ⟨K, hK⟩ := eventually_atTop.mp hev
  have h1 := hK K le_rfl
  have h2 := hlow K
  have h3 := hbdd K
  linarith

/-! ## §6 Layer counts and the reduction to the one-dimensional series

The layer `B_{m+1} \ B_m` has `2d` faces and at least `(2m+1)^{d-1}` points on each, so it
carries at least `2 d m^{d-1}` points; combined with the exact layer decomposition of a box
sum this turns a lower bound for the lattice sum into the one-dimensional series of §5. -/

/-- The layer `B_{m+1} \ B_m` of the sup-norm box carries at least `2 d m^{d-1}` points. -/
lemma card_layer_ge {d : ℕ} (hd : 0 < d) (m : ℕ) :
    2 * d * m ^ (d - 1) ≤ ((PercLib.CriticalLRP.FiniteVolume.box d (m + 1) \
      PercLib.CriticalLRP.FiniteVolume.box d m).card : ℕ) := by
  have hA : (0 : ℝ) < 2 * (m : ℝ) + 1 := by positivity
  have hcard : (((PercLib.CriticalLRP.FiniteVolume.box d (m + 1) \
      PercLib.CriticalLRP.FiniteVolume.box d m).card : ℕ) : ℝ)
      = (2 * (m : ℝ) + 3) ^ d - (2 * (m : ℝ) + 1) ^ d := by
    rw [PercLib.CriticalLRP.FiniteVolume.card_box_sdiff,
      show 2 * (m + 1) + 1 = 2 * m + 3 from by ring]
    have hle : (2 * m + 1) ^ d ≤ (2 * m + 3) ^ d := Nat.pow_le_pow_left (by omega) d
    rw [Nat.cast_sub hle]
    push_cast
    ring
  -- Bernoulli: `(A+2)^d ≥ A^d + 2 d A^{d-1}` with `A = 2m+1`
  have hBern : (1 : ℝ) + (d : ℝ) * (2 / (2 * (m : ℝ) + 1)) ≤
      (1 + 2 / (2 * (m : ℝ) + 1)) ^ d := by
    refine one_add_mul_le_pow ?_ d
    have h2 : (0 : ℝ) < 2 / (2 * (m : ℝ) + 1) := by positivity
    linarith
  have hAd : (0 : ℝ) < (2 * (m : ℝ) + 1) ^ d := by positivity
  have hAne : (2 * (m : ℝ) + 1) ≠ 0 := ne_of_gt hA
  have hpow : (2 * (m : ℝ) + 1) ^ d
      = (2 * (m : ℝ) + 1) * (2 * (m : ℝ) + 1) ^ (d - 1) := by
    conv_lhs => rw [(Nat.succ_pred_eq_of_pos hd).symm]
    rw [pow_succ, Nat.pred_eq_sub_one]
    ring
  have hterm : (2 * (m : ℝ) + 1) ^ d * ((d : ℝ) * (2 / (2 * (m : ℝ) + 1)))
      = 2 * (d : ℝ) * (2 * (m : ℝ) + 1) ^ (d - 1) := by
    rw [hpow]
    field_simp
  have hR : (2 * (m : ℝ) + 1) ^ d * (1 + 2 / (2 * (m : ℝ) + 1)) ^ d
      = (2 * (m : ℝ) + 3) ^ d := by
    rw [← mul_pow]
    congr 1
    field_simp
    ring
  have hfin : 2 * (d : ℝ) * (2 * (m : ℝ) + 1) ^ (d - 1)
      ≤ (2 * (m : ℝ) + 3) ^ d - (2 * (m : ℝ) + 1) ^ d := by
    have hmul := mul_le_mul_of_nonneg_left hBern hAd.le
    rw [mul_add, mul_one, hterm, hR] at hmul
    linarith
  have hmono : (m : ℝ) ^ (d - 1) ≤ (2 * (m : ℝ) + 1) ^ (d - 1) := by
    refine pow_le_pow_left₀ (by positivity) ?_ (d - 1)
    linarith
  have h2d : (0 : ℝ) ≤ 2 * (d : ℝ) := by positivity
  have hfinal : 2 * (d : ℝ) * (m : ℝ) ^ (d - 1)
      ≤ (2 * (m : ℝ) + 3) ^ d - (2 * (m : ℝ) + 1) ^ d := by
    have := mul_le_mul_of_nonneg_left hmono h2d
    linarith
  have hreal : 2 * (d : ℝ) * (m : ℝ) ^ (d - 1)
      ≤ (((PercLib.CriticalLRP.FiniteVolume.box d (m + 1) \
        PercLib.CriticalLRP.FiniteVolume.box d m).card : ℕ) : ℝ) := by
    rw [hcard]
    exact hfinal
  exact_mod_cast hreal

/-- **Core product estimate**: `m^{d-1} (m+2)^{-d} ≥ 3^{-d} m^{-1}` for `m ≥ 1`. -/
lemma rpow_core_ge {d : ℕ} (hd : 0 < d) {m : ℕ} (hm : 0 < m) :
    (3 : ℝ) ^ (-(d : ℝ)) * ((m : ℝ))⁻¹
      ≤ (m : ℝ) ^ (((d - 1 : ℕ)) : ℝ) * ((m : ℝ) + 2) ^ (-(d : ℝ)) := by
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hm2 : (0 : ℝ) < (m : ℝ) + 2 := by linarith
  have hle : (m : ℝ) + 2 ≤ 3 * (m : ℝ) := by linarith
  have hdnn : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  have hstep1 : (3 * (m : ℝ)) ^ (-(d : ℝ)) ≤ ((m : ℝ) + 2) ^ (-(d : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hm2 hle (by linarith)
  have hstep2 : (3 * (m : ℝ)) ^ (-(d : ℝ))
      = (3 : ℝ) ^ (-(d : ℝ)) * (m : ℝ) ^ (-(d : ℝ)) := by
    rw [Real.mul_rpow (by norm_num) hm0.le]
  have hstep3 : (m : ℝ) ^ (((d - 1 : ℕ)) : ℝ) * (m : ℝ) ^ (-(d : ℝ))
      = ((m : ℝ))⁻¹ := by
    rw [← Real.rpow_add hm0]
    have hcast : (((d - 1 : ℕ)) : ℝ) = (d : ℝ) - 1 := by
      have := Nat.cast_sub (R := ℝ) hd
      simpa using this
    rw [hcast, show (d : ℝ) - 1 + -(d : ℝ) = -1 by ring]
    exact rpow_neg_one_eq_inv hm0.le
  calc (3 : ℝ) ^ (-(d : ℝ)) * ((m : ℝ))⁻¹
      = (3 : ℝ) ^ (-(d : ℝ)) *
          ((m : ℝ) ^ (((d - 1 : ℕ)) : ℝ) * (m : ℝ) ^ (-(d : ℝ))) := by rw [hstep3]
    _ = (m : ℝ) ^ (((d - 1 : ℕ)) : ℝ) * (3 * (m : ℝ)) ^ (-(d : ℝ)) := by
        rw [hstep2]; ring
    _ ≤ (m : ℝ) ^ (((d - 1 : ℕ)) : ℝ) * ((m : ℝ) + 2) ^ (-(d : ℝ)) :=
        mul_le_mul_of_nonneg_left hstep1 (by positivity)

/-- **One layer of the critical sum.** -/
lemma layer_term_ge {d : ℕ} (hd : 0 < d) {c : ℝ} (hc0 : 0 ≤ c) (m : ℕ) :
    (2 * (d : ℝ) * (3 : ℝ) ^ (-(d : ℝ)) * (2 : ℝ) ^ (-c)) *
        (((m : ℝ))⁻¹ * LamR (m : ℝ) ^ (-c))
      ≤ ((PercLib.CriticalLRP.FiniteVolume.box d (m + 1) \
          PercLib.CriticalLRP.FiniteVolume.box d m).card : ℝ) *
        Wt (d : ℝ) c (((m + 1 : ℕ)) : ℝ) := by
  rcases Nat.eq_zero_or_pos m with hmz | hm
  · subst hmz
    rw [Nat.cast_zero, inv_zero, zero_mul, mul_zero]
    exact mul_nonneg (by positivity) (Wt_nonneg (by positivity))
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hcard : 2 * (d : ℝ) * (m : ℝ) ^ (((d - 1 : ℕ)) : ℝ) ≤
      ((PercLib.CriticalLRP.FiniteVolume.box d (m + 1) \
        PercLib.CriticalLRP.FiniteVolume.box d m).card : ℝ) := by
    have h := card_layer_ge hd m
    have h' : ((2 * d * m ^ (d - 1) : ℕ) : ℝ) ≤
        (((PercLib.CriticalLRP.FiniteVolume.box d (m + 1) \
          PercLib.CriticalLRP.FiniteVolume.box d m).card : ℕ) : ℝ) := by exact_mod_cast h
    have hcast : ((2 * d * m ^ (d - 1) : ℕ) : ℝ) = 2 * (d : ℝ) * (m : ℝ) ^ (d - 1) := by
      push_cast; ring
    rw [hcast, ← Real.rpow_natCast] at h'
    exact h'
  have hWtnn : 0 ≤ Wt (d : ℝ) c (((m + 1 : ℕ)) : ℝ) := Wt_nonneg (by positivity)
  have hWt : Wt (d : ℝ) c (((m + 1 : ℕ)) : ℝ)
      = ((m : ℝ) + 2) ^ (-(d : ℝ)) * (LamR (((m + 1 : ℕ)) : ℝ)) ^ (-c) := by
    unfold Wt
    rw [show (1 : ℝ) + (((m + 1 : ℕ)) : ℝ) = (m : ℝ) + 2 by push_cast; ring]
  have hLam : LamR (((m : ℝ)) + 1) ≤ 2 * LamR (m : ℝ) := LamR_succ_le_two m
  have hLampow : (2 * LamR (m : ℝ)) ^ (-c) ≤ (LamR (((m + 1 : ℕ)) : ℝ)) ^ (-c) := by
    have harg : (((m + 1 : ℕ)) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
    rw [harg]
    exact Real.rpow_le_rpow_of_nonpos (LamR_pos (by positivity)) hLam (by linarith)
  have hmulpow : (2 * LamR (m : ℝ)) ^ (-c) = (2 : ℝ) ^ (-c) * (LamR (m : ℝ)) ^ (-c) :=
    Real.mul_rpow (by norm_num) (LamR_nonneg (s := (m : ℝ)) (Nat.cast_nonneg m))
  have hstepA : ((m : ℝ) + 2) ^ (-(d : ℝ)) * (2 : ℝ) ^ (-c) * (LamR (m : ℝ)) ^ (-c)
      ≤ ((m : ℝ) + 2) ^ (-(d : ℝ)) * (LamR (((m + 1 : ℕ)) : ℝ)) ^ (-c) := by
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg (by positivity : (0:ℝ) ≤ (m:ℝ)+2) _)
    rw [← hmulpow]
    exact hLampow
  have hpos2d : (0 : ℝ) ≤ 2 * (d : ℝ) * (m : ℝ) ^ (((d - 1 : ℕ)) : ℝ) := by positivity
  have hcore : (2 * (d : ℝ) * (2 : ℝ) ^ (-c) * (LamR (m : ℝ)) ^ (-c)) *
      ((3 : ℝ) ^ (-(d : ℝ)) * ((m : ℝ))⁻¹)
      ≤ (2 * (d : ℝ) * (2 : ℝ) ^ (-c) * (LamR (m : ℝ)) ^ (-c)) *
        ((m : ℝ) ^ (((d - 1 : ℕ)) : ℝ) * ((m : ℝ) + 2) ^ (-(d : ℝ))) :=
    mul_le_mul_of_nonneg_left (rpow_core_ge hd hm)
      (mul_nonneg (mul_nonneg (by positivity) (Real.rpow_pos_of_pos (by norm_num) (-c)).le)
        (Real.rpow_nonneg (LamR_nonneg (s := (m : ℝ)) (Nat.cast_nonneg m)) _))
  rw [hWt]
  calc (2 * (d : ℝ) * (3 : ℝ) ^ (-(d : ℝ)) * (2 : ℝ) ^ (-c)) *
        (((m : ℝ))⁻¹ * LamR (m : ℝ) ^ (-c))
      = (2 * (d : ℝ) * (2 : ℝ) ^ (-c) * (LamR (m : ℝ)) ^ (-c)) *
          ((3 : ℝ) ^ (-(d : ℝ)) * ((m : ℝ))⁻¹) := by ring
    _ ≤ (2 * (d : ℝ) * (2 : ℝ) ^ (-c) * (LamR (m : ℝ)) ^ (-c)) *
          ((m : ℝ) ^ (((d - 1 : ℕ)) : ℝ) * ((m : ℝ) + 2) ^ (-(d : ℝ))) := hcore
    _ = (2 * (d : ℝ) * (m : ℝ) ^ (((d - 1 : ℕ)) : ℝ)) *
          (((m : ℝ) + 2) ^ (-(d : ℝ)) * (2 : ℝ) ^ (-c) * (LamR (m : ℝ)) ^ (-c)) := by ring
    _ ≤ (2 * (d : ℝ) * (m : ℝ) ^ (((d - 1 : ℕ)) : ℝ)) *
          (((m : ℝ) + 2) ^ (-(d : ℝ)) * (LamR (((m + 1 : ℕ)) : ℝ)) ^ (-c)) :=
        mul_le_mul_of_nonneg_left hstepA hpos2d
    _ ≤ ((PercLib.CriticalLRP.FiniteVolume.box d (m + 1) \
          PercLib.CriticalLRP.FiniteVolume.box d m).card : ℝ) *
          (((m : ℝ) + 2) ^ (-(d : ℝ)) * (LamR (((m + 1 : ℕ)) : ℝ)) ^ (-c)) :=
        mul_le_mul_of_nonneg_right hcard
          (mul_nonneg (Real.rpow_nonneg (by positivity : (0:ℝ) ≤ (m:ℝ)+2) _)
            (Real.rpow_nonneg (LamR_nonneg (s := ((m + 1 : ℕ) : ℝ)) (by positivity)) _))

/-- If the partial sums over `range` of a nonnegative series are bounded, the series
converges. -/
lemma summable_of_sum_range_le {f : ℕ → ℝ} (hnn : ∀ n, 0 ≤ f n) {C : ℝ}
    (h : ∀ N : ℕ, ∑ n ∈ range N, f n ≤ C) : Summable f := by
  refine summable_of_sum_le (c := C) hnn ?_
  intro u
  have hsub : u ⊆ range (u.sup id + 1) := by
    intro n hn
    rw [Finset.mem_range]
    have h1 : n ≤ u.sup id := Finset.le_sup (f := id) hn
    omega
  calc ∑ n ∈ u, f n ≤ ∑ n ∈ range (u.sup id + 1), f n :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => hnn i)
    _ ≤ C := h _

/-- **Divergence at the critical exponent.** For `d ≥ 1`, `c ≥ 0` and `c ≤ 1` the weight
`Wt d c` is not summable over `ℤ^d`: the layer count of §6 turns the box sum into the
one-dimensional critical series of §5. -/
theorem not_summable_Wt_marginal {d : ℕ} (hd : 0 < d) {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    ¬ Summable (fun y : Fin d → ℤ => Wt (d : ℝ) c (linfNorm y : ℝ)) := by
  intro hS
  set K : ℝ := 2 * (d : ℝ) * (3 : ℝ) ^ (-(d : ℝ)) * (2 : ℝ) ^ (-c) with hKdef
  have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hK : 0 < K := by
    rw [hKdef]
    exact mul_pos (mul_pos (mul_pos (by norm_num) hd0)
      (Real.rpow_pos_of_pos (by norm_num) _)) (Real.rpow_pos_of_pos (by norm_num) _)
  have hnn : ∀ y : Fin d → ℤ, 0 ≤ Wt (d : ℝ) c (linfNorm y : ℝ) :=
    fun y => Wt_nonneg (by positivity)
  have htsum_nn : 0 ≤ ∑' (y : Fin d → ℤ), Wt (d : ℝ) c (linfNorm y : ℝ) :=
    tsum_nonneg hnn
  have hboxeq : ∀ N : ℕ, ∑ y ∈ box d N, Wt (d : ℝ) c (linfNorm y : ℝ)
      = Wt (d : ℝ) c 0 + ∑ m ∈ range N,
        (((box d (m + 1) \ box d m).card : ℕ) : ℝ) *
          Wt (d : ℝ) c (((m + 1 : ℕ)) : ℝ) := by
    intro N
    have h := sum_box_eq d N (fun n : ℕ => Wt (d : ℝ) c (n : ℝ))
    simpa using h
  have hbdd : ∀ N : ℕ, ∑ m ∈ range N, (((m : ℝ))⁻¹ * LamR (m : ℝ) ^ (-c))
      ≤ (∑' (y : Fin d → ℤ), Wt (d : ℝ) c (linfNorm y : ℝ)) / K := by
    intro N
    have hlow : K * ∑ m ∈ range N, (((m : ℝ))⁻¹ * LamR (m : ℝ) ^ (-c))
        ≤ ∑ y ∈ box d N, Wt (d : ℝ) c (linfNorm y : ℝ) := by
      have h1 : K * ∑ m ∈ range N, (((m : ℝ))⁻¹ * LamR (m : ℝ) ^ (-c))
          = ∑ m ∈ range N, K * (((m : ℝ))⁻¹ * LamR (m : ℝ) ^ (-c)) := Finset.mul_sum ..
      rw [h1, hboxeq N]
      have hzero : (0 : ℝ) ≤ Wt (d : ℝ) c 0 := Wt_nonneg (le_refl (0 : ℝ))
      have hlayers : ∑ m ∈ range N, K * (((m : ℝ))⁻¹ * LamR (m : ℝ) ^ (-c))
          ≤ ∑ m ∈ range N,
            (((box d (m + 1) \ box d m).card : ℕ) : ℝ) *
              Wt (d : ℝ) c (((m + 1 : ℕ)) : ℝ) := by
        refine Finset.sum_le_sum (fun m _ => ?_)
        have h := layer_term_ge hd hc0 m
        rw [hKdef]
        exact h
      linarith
    have hup : ∑ y ∈ box d N, Wt (d : ℝ) c (linfNorm y : ℝ)
        ≤ ∑' (y : Fin d → ℤ), Wt (d : ℝ) c (linfNorm y : ℝ) :=
      hS.sum_le_tsum (box d N) (fun i _ => hnn i)
    rw [le_div_iff₀ hK]
    calc (∑ m ∈ range N, (((m : ℝ))⁻¹ * LamR (m : ℝ) ^ (-c))) * K
        = K * ∑ m ∈ range N, (((m : ℝ))⁻¹ * LamR (m : ℝ) ^ (-c)) := by ring
      _ ≤ ∑ y ∈ box d N, Wt (d : ℝ) c (linfNorm y : ℝ) := hlow
      _ ≤ ∑' (y : Fin d → ℤ), Wt (d : ℝ) c (linfNorm y : ℝ) := hup
  refine not_summable_inv_mul_LamR hc0 hc1
    (summable_of_sum_range_le (fun m => mul_nonneg (by positivity)
      (Real.rpow_nonneg (LamR_nonneg (by positivity)) _)) hbdd)

/-! ## §7 The subcritical divergence -/

/-- **Polynomial beats every power of the logarithm**: for `A > 0` and `c ≥ 0` the quantity
`N^A (log (2+N))^{-c}` is unbounded along `ℕ`. -/
lemma exists_nat_pow_mul_LamR_gt {A c : ℝ} (hA : 0 < A) (hc : 0 ≤ c) (B : ℝ) :
    ∃ N : ℕ, B < (N : ℝ) ^ A * (LamR (N : ℝ)) ^ (-c) := by
  rcases eq_or_lt_of_le hc with hc0 | hcpos
  · subst hc0
    have hlim : Tendsto (fun N : ℕ => (N : ℝ) ^ A) atTop atTop :=
      (tendsto_rpow_atTop hA).comp tendsto_natCast_atTop_atTop
    obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp (hlim.eventually (eventually_gt_atTop B))
    have hN := hN₀ (max N₀ 1) (le_max_left _ _)
    refine ⟨max N₀ 1, ?_⟩
    rw [neg_zero, Real.rpow_zero, mul_one]
    exact hN
  · set a : ℝ := A / (2 * c) with ha
    have ha0 : 0 < a := by rw [ha]; positivity
    have hac : a * c = A / 2 := by rw [ha]; field_simp
    have hAc : A - a * c = A / 2 := by rw [hac]; ring
    have hcoef : 0 < a ^ c * (2 : ℝ) ^ (-(a * c)) :=
      mul_pos (Real.rpow_pos_of_pos ha0 _) (Real.rpow_pos_of_pos (by norm_num) _)
    have hlim : Tendsto (fun N : ℕ => a ^ c * (2 : ℝ) ^ (-(a * c)) * (N : ℝ) ^ (A / 2))
        atTop atTop :=
      Tendsto.const_mul_atTop hcoef
        ((tendsto_rpow_atTop (by linarith : 0 < A / 2)).comp tendsto_natCast_atTop_atTop)
    obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp (hlim.eventually (eventually_gt_atTop B))
    set N : ℕ := max N₀ 2 with hNdef
    have hN : B < a ^ c * (2 : ℝ) ^ (-(a * c)) * (N : ℝ) ^ (A / 2) :=
      hN₀ N (le_max_left _ _)
    have hlog : LamR (N : ℝ) ≤ (((N : ℝ) + 2)) ^ a / a := by
      unfold LamR
      rw [show (2 : ℝ) + (N : ℝ) = (N : ℝ) + 2 by ring]
      exact Real.log_le_rpow_div (by positivity) ha0
    have hLpos : (0 : ℝ) < LamR (N : ℝ) := LamR_pos (Nat.cast_nonneg N)
    have hkey : a ^ c * (((N : ℝ) + 2)) ^ (-(a * c)) ≤ (LamR (N : ℝ)) ^ (-c) := by
      have hstep : ((((N : ℝ) + 2)) ^ a / a) ^ (-c) ≤ (LamR (N : ℝ)) ^ (-c) :=
        Real.rpow_le_rpow_of_nonpos hLpos hlog (by linarith)
      have hval : ((((N : ℝ) + 2)) ^ a / a) ^ (-c) = a ^ c * (((N : ℝ) + 2)) ^ (-(a * c)) := by
        have hx0 : (0 : ℝ) ≤ (N : ℝ) + 2 := by positivity
        rw [Real.div_rpow (Real.rpow_nonneg hx0 a) ha0.le,
          Real.rpow_neg (Real.rpow_nonneg hx0 a), Real.rpow_neg ha0.le,
          ← Real.rpow_mul hx0, Real.rpow_neg hx0, div_inv_eq_mul]
        ring
      rw [hval] at hstep
      exact hstep
    have hN1 : (2 : ℝ) ≤ (N : ℝ) := by
      have h1 : 2 ≤ N := le_max_right _ _
      exact_mod_cast h1
    have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
    have hstep2 : (2 * (N : ℝ)) ^ (-(a * c)) ≤ (((N : ℝ) + 2)) ^ (-(a * c)) := by
      have hle : (N : ℝ) + 2 ≤ 2 * (N : ℝ) := by linarith
      exact Real.rpow_le_rpow_of_nonpos (by linarith) hle (by linarith)
    have hstep3 : (2 * (N : ℝ)) ^ (-(a * c)) = (2 : ℝ) ^ (-(a * c)) * (N : ℝ) ^ (-(a * c)) :=
      Real.mul_rpow (by norm_num) (Nat.cast_nonneg N)
    have hac0 : (0 : ℝ) ≤ a ^ c := (Real.rpow_pos_of_pos ha0 c).le
    have h1 : a ^ c * (2 : ℝ) ^ (-(a * c)) * (N : ℝ) ^ (-(a * c))
        ≤ a ^ c * (((N : ℝ) + 2)) ^ (-(a * c)) := by
      have h2 : (2 : ℝ) ^ (-(a * c)) * (N : ℝ) ^ (-(a * c))
          ≤ (((N : ℝ) + 2)) ^ (-(a * c)) := by
        rw [← hstep3]
        exact hstep2
      calc a ^ c * (2 : ℝ) ^ (-(a * c)) * (N : ℝ) ^ (-(a * c))
          = a ^ c * ((2 : ℝ) ^ (-(a * c)) * (N : ℝ) ^ (-(a * c))) := by ring
        _ ≤ a ^ c * (((N : ℝ) + 2)) ^ (-(a * c)) := mul_le_mul_of_nonneg_left h2 hac0
    have h2 : (N : ℝ) ^ (-(a * c)) * (N : ℝ) ^ A = (N : ℝ) ^ (A / 2) := by
      rw [← Real.rpow_add hNpos, show -(a * c) + A = A / 2 by rw [hac]; ring]
    have hfin : a ^ c * (2 : ℝ) ^ (-(a * c)) * (N : ℝ) ^ (A / 2)
        ≤ (N : ℝ) ^ A * (LamR (N : ℝ)) ^ (-c) := by
      have hNnn : (0 : ℝ) ≤ (N : ℝ) ^ A := Real.rpow_nonneg (Nat.cast_nonneg N) A
      calc a ^ c * (2 : ℝ) ^ (-(a * c)) * (N : ℝ) ^ (A / 2)
          = (a ^ c * (2 : ℝ) ^ (-(a * c)) * (N : ℝ) ^ (-(a * c))) * (N : ℝ) ^ A := by
              rw [← h2]; ring
        _ ≤ (a ^ c * (((N : ℝ) + 2)) ^ (-(a * c))) * (N : ℝ) ^ A :=
              mul_le_mul_of_nonneg_right h1 hNnn
        _ ≤ (LamR (N : ℝ)) ^ (-c) * (N : ℝ) ^ A := mul_le_mul_of_nonneg_right hkey hNnn
        _ = (N : ℝ) ^ A * (LamR (N : ℝ)) ^ (-c) := by ring
    exact ⟨N, lt_of_lt_of_le hN hfin⟩

/-! ## §8 The subcritical case and the membership criterion -/

/-- **Divergence below the critical exponent**: for `e < d` the weight `Wt e c` is not
summable, for every log exponent `c ≥ 0`. -/
theorem not_summable_Wt_of_lt {d : ℕ} (hd : 0 < d) {e c : ℝ} (he : e < (d : ℝ))
    (hc : 0 ≤ c) :
    ¬ Summable (fun y : Fin d → ℤ => Wt e c (linfNorm y : ℝ)) := by
  intro hS
  have hnn : ∀ y : Fin d → ℤ, 0 ≤ Wt e c (linfNorm y : ℝ) :=
    fun y => Wt_nonneg (by positivity)
  have htsum_nn : 0 ≤ ∑' (y : Fin d → ℤ), Wt e c (linfNorm y : ℝ) := tsum_nonneg hnn
  have hbox_le : ∀ N : ℕ, ∑ y ∈ box d N, Wt e c (linfNorm y : ℝ)
      ≤ ∑' (y : Fin d → ℤ), Wt e c (linfNorm y : ℝ) :=
    fun N => hS.sum_le_tsum (box d N) (fun i _ => hnn i)
  by_cases he0 : e ≤ 0
  · -- `e ≤ 0`: the power factor is at least `1`
    obtain ⟨N, hN⟩ := exists_nat_pow_mul_LamR_gt (A := (d : ℝ)) (by exact_mod_cast hd) hc
      (∑' (y : Fin d → ℤ), Wt e c (linfNorm y : ℝ))
    have hN0 : 0 < N := by
      rcases Nat.eq_zero_or_pos N with h | h
      · exfalso
        rw [h] at hN
        simp only [Nat.cast_zero,
          Real.zero_rpow (ne_of_gt (by exact_mod_cast hd : (0:ℝ) < (d:ℝ))),
          zero_mul] at hN
        linarith
      · exact h
    have hpt : ∀ y ∈ box d N, (LamR (N : ℝ)) ^ (-c) ≤ Wt e c (linfNorm y : ℝ) := by
      intro y hy
      have hyN : (linfNorm y : ℝ) ≤ (N : ℝ) := by
        have := mem_box_iff.mp hy
        exact_mod_cast this
      have hpowe : (1 : ℝ) ≤ (1 + (linfNorm y : ℝ)) ^ (-e) := by
        have h1 : (1 : ℝ) ≤ 1 + (linfNorm y : ℝ) := by
          have h0 : (0 : ℝ) ≤ (linfNorm y : ℝ) := Nat.cast_nonneg _
          linarith
        have := Real.one_le_rpow h1 (by linarith : (0:ℝ) ≤ -e)
        simpa using this
      have hlogpart : (LamR (N : ℝ)) ^ (-c) ≤ (LamR (linfNorm y : ℝ)) ^ (-c) := by
        refine Real.rpow_le_rpow_of_nonpos (LamR_pos (by positivity))
          (LamR_mono (by positivity) hyN) (by linarith)
      have := mul_le_mul hpowe hlogpart (Real.rpow_nonneg (LamR_nonneg (by positivity)) _)
        (by positivity : (0:ℝ) ≤ (1 + (linfNorm y : ℝ)) ^ (-e))
      simpa [Wt, mul_comm] using this
    have hsum : ((box d N).card : ℝ) * (LamR (N : ℝ)) ^ (-c)
        ≤ ∑ y ∈ box d N, Wt e c (linfNorm y : ℝ) := by
      have h := Finset.sum_le_sum hpt
      rwa [Finset.sum_const, nsmul_eq_mul] at h
    have hcard : ((N : ℝ)) ^ d ≤ ((box d N).card : ℝ) := by
      rw [card_box]
      have h1 : N ^ d ≤ (2 * N + 1) ^ d := Nat.pow_le_pow_left (by omega) d
      have h2 : ((N ^ d : ℕ) : ℝ) ≤ (((2 * N + 1) ^ d : ℕ) : ℝ) := by exact_mod_cast h1
      calc ((N : ℝ)) ^ d = ((N ^ d : ℕ) : ℝ) := by push_cast; ring
        _ ≤ _ := h2
    have : ((N : ℝ)) ^ d * (LamR (N : ℝ)) ^ (-c)
        ≤ ∑ y ∈ box d N, Wt e c (linfNorm y : ℝ) := by
      calc ((N : ℝ)) ^ d * (LamR (N : ℝ)) ^ (-c)
          ≤ ((box d N).card : ℝ) * (LamR (N : ℝ)) ^ (-c) := by
            refine mul_le_mul_of_nonneg_right hcard
              (Real.rpow_nonneg (LamR_nonneg (by positivity)) _)
        _ ≤ _ := hsum
    have hN' : ∑' (y : Fin d → ℤ), Wt e c (linfNorm y : ℝ)
        < ((N : ℝ)) ^ d * (LamR (N : ℝ)) ^ (-c) := by
      rw [Real.rpow_natCast] at hN
      exact hN
    linarith [hbox_le N]
  · -- `0 < e`: the far term is at least `2^{-e} N^{-e}` times the log profile
    have hepos : 0 < e := not_le.mp he0
    obtain ⟨N, hN⟩ := exists_nat_pow_mul_LamR_gt (A := (d : ℝ) - e) (by linarith) hc
      ((2 : ℝ) ^ e * ∑' (y : Fin d → ℤ), Wt e c (linfNorm y : ℝ))
    have hN0 : 0 < N := by
      rcases Nat.eq_zero_or_pos N with h | h
      · exfalso
        rw [h] at hN
        simp only [Nat.cast_zero,
          Real.zero_rpow (ne_of_gt (by linarith : (0:ℝ) < (d:ℝ) - e)), zero_mul] at hN
        nlinarith [htsum_nn, Real.rpow_pos_of_pos (by norm_num : (0:ℝ) < 2) e]
      · exact h
    have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN0
    have hconst_nn : (0 : ℝ) ≤ 2 ^ (-e) * (N : ℝ) ^ (-e) * (LamR (N : ℝ)) ^ (-c) :=
      mul_nonneg (mul_nonneg (Real.rpow_nonneg (by norm_num) _)
        (Real.rpow_nonneg (by linarith) _))
        (Real.rpow_nonneg (LamR_nonneg (by positivity)) _)
    have hpt : ∀ y ∈ box d N, 2 ^ (-e) * (N : ℝ) ^ (-e) * (LamR (N : ℝ)) ^ (-c)
        ≤ Wt e c (linfNorm y : ℝ) := by
      intro y hy
      have hyN : (linfNorm y : ℝ) ≤ (N : ℝ) := by
        have := mem_box_iff.mp hy
        exact_mod_cast this
      have hYe : Wt e c (N : ℝ) ≤ Wt e c (linfNorm y : ℝ) :=
        Wt_antitone hepos hc (by positivity) hyN
      have h1 : (1 + (N : ℝ)) ≤ 2 * (N : ℝ) := by linarith
      have h2 : (2 * (N : ℝ)) ^ (-e) ≤ (1 + (N : ℝ)) ^ (-e) :=
        Real.rpow_le_rpow_of_nonpos (by linarith) h1 (by linarith)
      have h3 : (2 * (N : ℝ)) ^ (-e) = 2 ^ (-e) * (N : ℝ) ^ (-e) :=
        Real.mul_rpow (by norm_num) (by linarith)
      have hWtN : Wt e c (N : ℝ) = (1 + (N : ℝ)) ^ (-e) * (LamR (N : ℝ)) ^ (-c) := rfl
      calc 2 ^ (-e) * (N : ℝ) ^ (-e) * (LamR (N : ℝ)) ^ (-c)
          = (2 * (N : ℝ)) ^ (-e) * (LamR (N : ℝ)) ^ (-c) := by rw [h3]
        _ ≤ (1 + (N : ℝ)) ^ (-e) * (LamR (N : ℝ)) ^ (-c) :=
            mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg (LamR_nonneg (by positivity)) _)
        _ = Wt e c (N : ℝ) := hWtN.symm
        _ ≤ Wt e c (linfNorm y : ℝ) := hYe
    have hsum : ((box d N).card : ℝ) *
        (2 ^ (-e) * (N : ℝ) ^ (-e) * (LamR (N : ℝ)) ^ (-c))
        ≤ ∑ y ∈ box d N, Wt e c (linfNorm y : ℝ) := by
      have h := Finset.sum_le_sum hpt
      rwa [Finset.sum_const, nsmul_eq_mul] at h
    have hcard : ((N : ℝ)) ^ d ≤ ((box d N).card : ℝ) := by
      rw [card_box]
      have h1 : N ^ d ≤ (2 * N + 1) ^ d := Nat.pow_le_pow_left (by omega) d
      have h2 : ((N ^ d : ℕ) : ℝ) ≤ (((2 * N + 1) ^ d : ℕ) : ℝ) := by exact_mod_cast h1
      calc ((N : ℝ)) ^ d = ((N ^ d : ℕ) : ℝ) := by push_cast; ring
        _ ≤ _ := h2
    have hstep : ((N : ℝ)) ^ d * (2 ^ (-e) * (N : ℝ) ^ (-e) * (LamR (N : ℝ)) ^ (-c))
        ≤ ((box d N).card : ℝ) * (2 ^ (-e) * (N : ℝ) ^ (-e) * (LamR (N : ℝ)) ^ (-c)) :=
      mul_le_mul_of_nonneg_right hcard hconst_nn
    have hcombine : ((N : ℝ)) ^ d * (2 ^ (-e) * (N : ℝ) ^ (-e) * (LamR (N : ℝ)) ^ (-c))
        = 2 ^ (-e) * ((N : ℝ) ^ ((d : ℝ) - e) * (LamR (N : ℝ)) ^ (-c)) := by
      have hpow : ((N : ℝ)) ^ d * (N : ℝ) ^ (-e) = (N : ℝ) ^ ((d : ℝ) - e) := by
        rw [← Real.rpow_natCast (x := (N : ℝ)) (n := d), ← Real.rpow_add (by linarith),
          show (d : ℝ) + -e = (d : ℝ) - e by ring]
      calc ((N : ℝ)) ^ d * (2 ^ (-e) * (N : ℝ) ^ (-e) * (LamR (N : ℝ)) ^ (-c))
          = 2 ^ (-e) * (((N : ℝ)) ^ d * (N : ℝ) ^ (-e)) * (LamR (N : ℝ)) ^ (-c) := by ring
        _ = 2 ^ (-e) * ((N : ℝ) ^ ((d : ℝ) - e) * (LamR (N : ℝ)) ^ (-c)) := by rw [hpow]; ring
    have hfinal : 2 ^ (-e) * ((N : ℝ) ^ ((d : ℝ) - e) * (LamR (N : ℝ)) ^ (-c))
        ≤ ∑ y ∈ box d N, Wt e c (linfNorm y : ℝ) := by
      rw [← hcombine]
      exact le_trans hstep hsum
    have htsum_lt : ∑' (y : Fin d → ℤ), Wt e c (linfNorm y : ℝ)
        < 2 ^ (-e) * ((N : ℝ) ^ ((d : ℝ) - e) * (LamR (N : ℝ)) ^ (-c)) := by
      have hne : (0 : ℝ) < (2 : ℝ) ^ (-e) := Real.rpow_pos_of_pos (by norm_num) (-e)
      have hmul := mul_lt_mul_of_pos_left hN hne
      have hone : (2 : ℝ) ^ (-e) * (2 : ℝ) ^ e = 1 := by
        rw [← Real.rpow_add (by norm_num : (0:ℝ) < 2), show -e + e = 0 by ring, Real.rpow_zero]
      calc ∑' (y : Fin d → ℤ), Wt e c (linfNorm y : ℝ)
          = (2 : ℝ) ^ (-e) *
              ((2 : ℝ) ^ e * ∑' (y : Fin d → ℤ), Wt e c (linfNorm y : ℝ)) := by
            rw [← mul_assoc, hone, one_mul]
        _ < (2 : ℝ) ^ (-e) * ((N : ℝ) ^ ((d : ℝ) - e) * (LamR (N : ℝ)) ^ (-c)) := hmul
    linarith [hbox_le N]

/-- **The `ℓ^p` membership criterion** for the campaign's weight. -/
theorem summable_Wt_iff {d : ℕ} (hd : 0 < d) {e c : ℝ} (hc : 0 ≤ c) :
    Summable (fun y : Fin d → ℤ => Wt e c (linfNorm y : ℝ)) ↔
      ((d : ℝ) < e ∨ (e = (d : ℝ) ∧ 1 < c)) := by
  constructor
  · intro hS
    by_contra hcon
    rw [not_or, not_and] at hcon
    have hle : e ≤ (d : ℝ) := not_lt.mp hcon.1
    rcases lt_or_eq_of_le hle with hlt | heq
    · exact not_summable_Wt_of_lt hd hlt hc hS
    · have hc1 : c ≤ 1 := not_lt.mp (hcon.2 heq)
      have h' : Summable (fun y : Fin d → ℤ => Wt (d : ℝ) c (linfNorm y : ℝ)) := by
        rw [← heq]
        exact hS
      exact not_summable_Wt_marginal hd hc hc1 h'
  · rintro (h | ⟨h1, h2⟩)
    · exact summable_Wt_of_lt hd h hc
    · rw [h1]
      exact summable_Wt_marginal hd h2

/-- **`ℓ^p` membership, in the form of the weight family**: the `p`-th power of
`Wt γ ĉ` is `p`-summable exactly when `p γ > d`, or `p γ = d` with `p ĉ > 1`. -/
theorem summable_abs_rpow_Wt_iff {d : ℕ} (hd : 0 < d) {γ ĉ p : ℝ} (hp : 0 < p)
    (hĉ : 0 ≤ ĉ) :
    Summable (fun y : Fin d → ℤ => |Wt γ ĉ (linfNorm y : ℝ)| ^ p) ↔
      ((d : ℝ) < p * γ ∨ (p * γ = (d : ℝ) ∧ 1 < p * ĉ)) := by
  have hfun : (fun y : Fin d → ℤ => |Wt γ ĉ (linfNorm y : ℝ)| ^ p)
      = fun y => Wt (p * γ) (p * ĉ) (linfNorm y : ℝ) := by
    funext y
    rw [abs_of_pos (Wt_pos (by positivity)), Wt_rpow (by positivity)]
  rw [hfun]
  exact summable_Wt_iff hd (by positivity)

/-! ## §9 The `ℓ²` column mass of a two-point kernel

The campaign's two-point kernels are dominated by `Wt (d - a) ac` at the sup-norm distance.
The `ℓ²` mass of a column is therefore a summable `ℓ^p` weight with radius exponent
`2 (d - a)`: by §8 it is finite exactly when `2 (d - a) > d`, i.e. `a < d/2`, and at the
boundary `a = d/2` exactly when `ac > 1/2`.  This is the precise sense in which the
Hilbert–Schmidt / `ℓ²` route to boundedness stops short of the critical exponent. -/

/-- Squaring the weight doubles both exponents. -/
lemma Wt_sq {e c r : ℝ} (hr : 0 ≤ r) : (Wt e c r) ^ 2 = Wt (2 * e) (2 * c) r := by
  rw [← Real.rpow_natCast, Wt_rpow hr]
  norm_num

/-- Translation invariance of the lattice weight sum. -/
lemma tsum_Wt_sub_left {d : ℕ} {e c : ℝ} (x : Fin d → ℤ) :
    ∑' y : Fin d → ℤ, Wt e c (linfNorm (x - y) : ℝ)
      = ∑' z : Fin d → ℤ, Wt e c (linfNorm z : ℝ) := by
  have hinj : Function.Injective (fun y : Fin d → ℤ => x - y) := by
    intro a b h
    have h2 := congrArg (fun z => x - z) h
    simpa using h2
  have hsurj : Function.Surjective (fun y : Fin d → ℤ => x - y) := by
    intro z
    exact ⟨x - z, by simp⟩
  set σ : (Fin d → ℤ) ≃ (Fin d → ℤ) := Equiv.ofBijective _ ⟨hinj, hsurj⟩ with hσ
  have hσy : ∀ y : Fin d → ℤ, σ y = x - y := fun y => rfl
  calc ∑' y : Fin d → ℤ, Wt e c (linfNorm (x - y) : ℝ)
      = ∑' y : Fin d → ℤ, Wt e c (linfNorm (σ y) : ℝ) := by simp [hσy]
    _ = ∑' z : Fin d → ℤ, Wt e c (linfNorm z : ℝ) :=
        Equiv.tsum_eq σ (fun z => Wt e c (linfNorm z : ℝ))

/-- Summability of the shifted weight along a column. -/
lemma summable_Wt_sub_left {d : ℕ} (hd : 0 < d) {e c : ℝ} (he : (d : ℝ) < e) (hc : 0 ≤ c)
    (x : Fin d → ℤ) : Summable (fun y : Fin d → ℤ => Wt e c (linfNorm (x - y) : ℝ)) := by
  have h := summable_Wt_of_lt hd he hc
  have hinj : Function.Injective (fun y : Fin d → ℤ => x - y) := by
    intro a b hab
    have h2 := congrArg (fun z => x - z) hab
    simpa using h2
  have := h.comp_injective hinj
  simpa [Function.comp_def] using this

/-- **`ℓ²` column bound below the Hilbert–Schmidt threshold.** If `|κ x y|` is dominated by
`C` times the weight `Wt (d - a) ac` at the distance `‖x - y‖` and `2 a < d`, then every
column of `κ` is square summable with an `x`-independent bound. -/
theorem summable_col_sq {d : ℕ} (hd : 0 < d) {κ : (Fin d → ℤ) → (Fin d → ℤ) → ℝ}
    {C a ac : ℝ} (ha : 2 * a < (d : ℝ)) (hac : 0 ≤ ac)
    (hdom : ∀ x y, |κ x y| ≤ C * Wt ((d : ℝ) - a) ac (linfNorm (x - y) : ℝ))
    (x : Fin d → ℤ) :
    Summable (fun y => (κ x y) ^ 2) ∧
      ∑' y, (κ x y) ^ 2
        ≤ C ^ 2 * ∑' z : Fin d → ℤ, Wt (2 * ((d : ℝ) - a)) (2 * ac) (linfNorm z : ℝ) := by
  have he : (d : ℝ) < 2 * ((d : ℝ) - a) := by linarith
  have hWshift : Summable (fun y : Fin d → ℤ =>
      Wt (2 * ((d : ℝ) - a)) (2 * ac) (linfNorm (x - y) : ℝ)) :=
    summable_Wt_sub_left hd he (by positivity) x
  have hpt : ∀ y : Fin d → ℤ, (κ x y) ^ 2
      ≤ C ^ 2 * Wt (2 * ((d : ℝ) - a)) (2 * ac) (linfNorm (x - y) : ℝ) := by
    intro y
    have h0 : (0 : ℝ) ≤ Wt ((d : ℝ) - a) ac (linfNorm (x - y) : ℝ) :=
      Wt_nonneg (by positivity)
    have h1 : |κ x y| ≤ C * Wt ((d : ℝ) - a) ac (linfNorm (x - y) : ℝ) := hdom x y
    have h2 : (κ x y) ^ 2 = |κ x y| ^ 2 := by rw [sq, sq, abs_mul_abs_self]
    rw [h2]
    have h3 : |κ x y| ^ 2 ≤ (C * Wt ((d : ℝ) - a) ac (linfNorm (x - y) : ℝ)) ^ 2 :=
      pow_le_pow_left₀ (abs_nonneg _) h1 2
    refine le_trans h3 (le_of_eq ?_)
    rw [mul_pow, Wt_sq (by positivity)]
  have hsum1 : Summable (fun y => (κ x y) ^ 2) :=
    Summable.of_nonneg_of_le (fun y => sq_nonneg _) hpt (hWshift.mul_left _)
  refine ⟨hsum1, ?_⟩
  refine le_trans (Summable.tsum_le_tsum hpt hsum1 (hWshift.mul_left _)) (le_of_eq ?_)
  rw [tsum_mul_left, tsum_Wt_sub_left]

/-- **The column mass diverges above the threshold.** If the column dominates the weight from
below and `2 a > d`, the column is not square summable, so no Hilbert–Schmidt estimate is
available there. -/
theorem not_summable_col_sq {d : ℕ} (hd : 0 < d) {κ : (Fin d → ℤ) → (Fin d → ℤ) → ℝ}
    {c₀ a ac : ℝ} (hc₀ : 0 < c₀) (hac : 0 ≤ ac) (ha : (d : ℝ) < 2 * a)
    (hlo : ∀ y, c₀ * Wt ((d : ℝ) - a) ac (linfNorm y : ℝ) ≤ κ 0 y) :
    ¬ Summable (fun y => (κ 0 y) ^ 2) := by
  intro hS
  have he : 2 * ((d : ℝ) - a) < (d : ℝ) := by linarith
  have hpt : ∀ y : Fin d → ℤ,
      c₀ ^ 2 * Wt (2 * ((d : ℝ) - a)) (2 * ac) (linfNorm y : ℝ) ≤ (κ 0 y) ^ 2 := by
    intro y
    have h0 : (0 : ℝ) ≤ Wt ((d : ℝ) - a) ac (linfNorm y : ℝ) := Wt_nonneg (by positivity)
    have h1 : c₀ * Wt ((d : ℝ) - a) ac (linfNorm y : ℝ) ≤ κ 0 y := hlo y
    have h2 : (c₀ * Wt ((d : ℝ) - a) ac (linfNorm y : ℝ)) ^ 2 ≤ (κ 0 y) ^ 2 :=
      pow_le_pow_left₀ (by positivity) h1 2
    refine le_trans (le_of_eq ?_) h2
    rw [mul_pow, Wt_sq (by positivity)]
  have hshift : Summable (fun y : Fin d → ℤ =>
      c₀ ^ 2 * Wt (2 * ((d : ℝ) - a)) (2 * ac) (linfNorm y : ℝ)) :=
    Summable.of_nonneg_of_le
      (fun y => mul_nonneg (by positivity) (Wt_nonneg (by positivity))) hpt hS
  have hW : Summable (fun y : Fin d → ℤ =>
      Wt (2 * ((d : ℝ) - a)) (2 * ac) (linfNorm y : ℝ)) := by
    refine (hshift.mul_left ((c₀ ^ 2)⁻¹)).congr (fun y => ?_)
    rw [← mul_assoc, inv_mul_cancel₀ (by positivity : c₀ ^ 2 ≠ 0), one_mul]
  exact not_summable_Wt_of_lt hd he (by positivity) hW

end CriticalLRPConv


set_option linter.hashCommand false
/-! ## §10 Axiom audit (no `sorry`, no custom axioms, no `native_decide`) -/
#print axioms CriticalLRPConv.Wt_zero
#print axioms CriticalLRPConv.summable_Wt_of_tail_bound
#print axioms CriticalLRPConv.summable_Wt_of_lt
#print axioms CriticalLRPConv.summable_Wt_marginal
#print axioms CriticalLRPConv.Wt_rpow
#print axioms CriticalLRPConv.summable_abs_rpow_Wt
#print axioms CriticalLRPConv.rpow_neg_one_eq_inv
#print axioms CriticalLRPConv.tendsto_sum_range_inv_add_three
#print axioms CriticalLRPConv.not_summable_inv_mul_LamR
#print axioms CriticalLRPConv.card_layer_ge
#print axioms CriticalLRPConv.rpow_core_ge
#print axioms CriticalLRPConv.layer_term_ge
#print axioms CriticalLRPConv.summable_of_sum_range_le
#print axioms CriticalLRPConv.not_summable_Wt_marginal
#print axioms CriticalLRPConv.exists_nat_pow_mul_LamR_gt
#print axioms CriticalLRPConv.not_summable_Wt_of_lt
#print axioms CriticalLRPConv.summable_Wt_iff
#print axioms CriticalLRPConv.summable_abs_rpow_Wt_iff
#print axioms CriticalLRPConv.Wt_sq
#print axioms CriticalLRPConv.tsum_Wt_sub_left
#print axioms CriticalLRPConv.summable_Wt_sub_left
#print axioms CriticalLRPConv.summable_col_sq
#print axioms CriticalLRPConv.not_summable_col_sq
