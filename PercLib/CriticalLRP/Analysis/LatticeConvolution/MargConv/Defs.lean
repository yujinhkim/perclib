module

public import PercLib.CriticalLRP.Analysis.LatticeConvolution.ConvAssembly.Defs

/-!
# Marginal (`a + b = d`) convolution assembly: constants and target profile

For `a, b > 0` with `a + b = d` the `A1`/`A2` region bounds of the strict-case assembly
(`CriticalLRPConv.sum_convReg1_le`, `sum_convReg2_le`) still produce the profile
`⟨x⟩^0 Λ(x)^{-(â+b̂)}`, but the `A3` region no longer decays in the power variable: outside
both half-balls the product weight is `(1+‖y‖)^{-d} Λ(‖y‖)^{-(â+b̂)}` in the variable
`v = min ‖y‖ ‖x-y‖`, so summing it over the lattice costs exactly one logarithm
(`CriticalLRPConv.sum_Wt_tail_le_pureLog`).  The resulting profile is
`Λ(x)^{-((â+b̂)-1)} = (log (2+‖x‖))^{-(â+b̂)+1}`.  This is the `a + b = d` companion of the
existing strict-regime assembly `CriticalLRPConv.conv_tsum_le` (which covers `a + b < d`,
`docs/CRITICAL_LRP_CONVOLUTION_ASSEMBLY.md`), i.e. the critical case of the two convolution
estimates of Lemma I.4.3 that the strict assembly explicitly left open.

This file only fixes notations and the elementary comparisons of the profiles; the region
estimates are in `MargConv.Regions` and the assembly in `MargConv.Main`.
-/

set_option autoImplicit false

@[expose] public section

namespace CriticalLRPConv

/-! ## §1 Constants -/

/-- The `A3` contribution constant of the marginal assembly.  It is the pure-log tail-shell
constant `tailShellConstLog d (â+b̂)`, in which the exponent drop `c ↦ c - 1` is the exact cost
of summing `n^{-1} (log n)^{-c}` over the lattice, together with the profile-freezing factor
`2^{â+b̂-1}` of applying the tail estimate at the half radius `‖x‖/2` (`Λ A ≤ 2 Λ (A/2)`
against the negative exponent `1 - (â+b̂)`). -/
noncomputable def margReg3Const (d : ℕ) (ah bh : ℝ) : ℝ :=
  (2 : ℝ) ^ (ah + bh - 1) * tailShellConstLog d (ah + bh)

/-- The target profile of the marginal assembly: `Λ A ^{-((â+b̂)-1)}`. -/
noncomputable def margTargetR (ah bh A : ℝ) : ℝ := Wt 0 (ah + bh - 1) A

/-- The marginal target profile `(log (2+‖x‖))^{-(â+b̂)+1}` at a lattice point. -/
noncomputable def margTarget {d : ℕ} (ah bh : ℝ) (x : Fin d → ℤ) : ℝ :=
  margTargetR ah bh ‖x‖

/-- The total constant of the marginal assembly: the `A1`/`A2` contributions, each of which
costs one further logarithm (a factor `2`, see `convTargetR_le_two_margTargetR`), plus the `A3`
contribution, which already sits at the target profile. -/
noncomputable def margConst (d : ℕ) (a b ah bh : ℝ) : ℝ :=
  2 * (convReg1Const d a b ah bh + convReg2Const d a b ah bh + margReg3Const d ah bh)

/-! ## §2 The marginal target profile -/

/-- `margTargetR` written out as a logarithmic power. -/
lemma margTargetR_eq_explicit (ah bh A : ℝ) :
    margTargetR ah bh A = Real.log (2 + A) ^ (1 - (ah + bh)) := by
  unfold margTargetR Wt LamR
  have h0 : (1 + A) ^ (-(0 : ℝ)) = 1 := by simp
  rw [h0, one_mul]
  congr 1
  ring

/-- The marginal target profile at a lattice point, written out. -/
lemma margTarget_eq_explicit {d : ℕ} (ah bh : ℝ) (x : Fin d → ℤ) :
    margTarget ah bh x = Real.log (2 + ‖x‖) ^ (1 - (ah + bh)) := by
  rw [margTarget]
  exact margTargetR_eq_explicit ah bh ‖x‖

/-- The marginal target profile is positive. -/
lemma margTargetR_pos {ah bh A : ℝ} (hA : 0 ≤ A) : 0 < margTargetR ah bh A := by
  rw [margTargetR]
  exact Wt_pos hA

/-- The marginal target profile is nonnegative. -/
lemma margTargetR_nonneg {ah bh A : ℝ} (hA : 0 ≤ A) : 0 ≤ margTargetR ah bh A :=
  (margTargetR_pos hA).le

/-- The marginal target profile at a lattice point is positive. -/
lemma margTarget_pos {d : ℕ} (ah bh : ℝ) (x : Fin d → ℤ) : 0 < margTarget ah bh x :=
  margTargetR_pos (norm_nonneg x)

/-- The marginal target profile at a lattice point is nonnegative. -/
lemma margTarget_nonneg {d : ℕ} (ah bh : ℝ) (x : Fin d → ℤ) : 0 ≤ margTarget ah bh x :=
  (margTarget_pos ah bh x).le

/-! ## §3 `Λ` is bounded below by `log 2` -/

/-- `log 2` is a lower bound for the logarithm profile `Λ A` at every `A ≥ 0`. -/
lemma LamR_ge_log_two {A : ℝ} (hA : 0 ≤ A) : Real.log 2 ≤ LamR A := by
  rw [LamR_def]
  exact Real.log_le_log (by norm_num) (by linarith)

/-- `2 ^ z` is positive for every real exponent. -/
lemma two_rpow_pos (z : ℝ) : (0 : ℝ) < (2 : ℝ) ^ z :=
  Real.rpow_pos_of_pos (by norm_num) z

/-! ## §4 Comparison of the strict target with the marginal target -/

/-- **The strict-case target is one logarithm sharper than the marginal target.**  When
`a + b = d` the strict-case target `convTargetR d a b â b̂ A = Λ A^{-(â+b̂)}` is at most twice
the marginal target `Λ A^{-((â+b̂)-1)}`; the factor `2` is the loss of dividing by
`Λ A ≥ log 2 ≥ 1/2` (`CriticalLRPConv.rpow_decay_step`). -/
lemma convTargetR_le_two_margTargetR {d : ℕ} {a b ah bh : ℝ} (hab : a + b = (d : ℝ)) {A : ℝ}
    (hA : 0 ≤ A) :
    convTargetR d a b ah bh A ≤ 2 * margTargetR ah bh A := by
  have hz : (d : ℝ) - a - b = 0 := by linarith
  have hL0 : (0 : ℝ) ≤ LamR A := LamR_nonneg hA
  have hLlog : Real.log 2 ≤ LamR A := LamR_ge_log_two hA
  have hdec : LamR A ^ (-(ah + bh)) ≤ 2 * LamR A ^ (-(ah + bh - 1)) := by
    have h := rpow_decay_step (c := ah + bh - 1) hL0 hLlog
    have he : -(ah + bh - 1) - 1 = -(ah + bh) := by ring
    rwa [he] at h
  have hleft : convTargetR d a b ah bh A = LamR A ^ (-(ah + bh)) := by
    unfold convTargetR Wt
    rw [hz, neg_zero, Real.rpow_zero, one_mul]
  rw [hleft, margTargetR_eq_explicit]
  calc LamR A ^ (-(ah + bh)) ≤ 2 * LamR A ^ (-(ah + bh - 1)) := hdec
    _ = 2 * Real.log (2 + A) ^ (1 - (ah + bh)) := by
        rw [LamR_def]
        congr 2
        ring

/-! ## §5 Halving the radius in the marginal target -/

/-- **Halving the radius costs a constant.**  For `â+b̂ ≥ 1` the marginal target at the half
radius is at most `2^{(â+b̂)-1}` times the target at the radius: this is `Λ A ≤ 2 Λ (A/2)`
against the negative exponent `1 - (â+b̂)`. -/
lemma margTargetR_halve_le {ah bh A : ℝ} (hS : 1 ≤ ah + bh) (hA : 0 ≤ A) :
    margTargetR ah bh (A / 2) ≤ (2 : ℝ) ^ (ah + bh - 1) * margTargetR ah bh A := by
  rw [margTargetR_eq_explicit, margTargetR_eq_explicit]
  have hmono : LamR A ≤ 2 * LamR (A / 2) :=
    LamR_le_two_of_le_two_mul (n := A) (m := A / 2) hA (by linarith)
  have hApos : (0 : ℝ) < LamR A := LamR_pos hA
  have hpos : (0 : ℝ) < LamR (A / 2) := LamR_pos (by linarith)
  have hexp : 1 - (ah + bh) ≤ 0 := by linarith
  have h1 : Real.log (2 + A / 2) ^ (1 - (ah + bh)) ≤
      ((2 : ℝ) ^ (ah + bh - 1)) * Real.log (2 + A) ^ (1 - (ah + bh)) := by
    have h2 : Real.log (2 + A / 2) = LamR (A / 2) := rfl
    have h3 : Real.log (2 + A) = LamR A := rfl
    rw [h2, h3]
    have hb : ((2 : ℝ) ^ (ah + bh - 1)) * LamR A ^ (1 - (ah + bh)) =
        ((2 : ℝ) ^ (1 - (ah + bh)))⁻¹ * LamR A ^ (1 - (ah + bh)) := by
      rw [show (2 : ℝ) ^ (ah + bh - 1) = ((2 : ℝ) ^ (1 - (ah + bh)))⁻¹ by
        rw [← Real.rpow_neg (by norm_num), show -(1 - (ah + bh)) = ah + bh - 1 by ring]]
    rw [hb, inv_mul_eq_div, le_div_iff₀ (two_rpow_pos _)]
    calc LamR (A / 2) ^ (1 - (ah + bh)) * (2 : ℝ) ^ (1 - (ah + bh))
        = ((2 : ℝ) * LamR (A / 2)) ^ (1 - (ah + bh)) := by
          rw [Real.mul_rpow (by norm_num) hpos.le]
          ring
      _ ≤ LamR A ^ (1 - (ah + bh)) :=
          Real.rpow_le_rpow_of_nonpos hApos hmono hexp
  exact h1

/-! ## §6 Nonnegativity of the constants -/

/-- The pure-log tail-shell constant is positive. -/
lemma tailShellConstLog_pos {d : ℕ} (hd : 1 ≤ d) {c : ℝ} (hc : 1 < c) :
    0 < tailShellConstLog d c := by
  unfold tailShellConstLog
  have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have h3 : (0 : ℝ) < 3 ^ (d - 1) := by positivity
  have hp : (0 : ℝ) < (2 : ℝ) ^ c := Real.rpow_pos_of_pos (by norm_num) _
  have hdiv : (0 : ℝ) < 8 * (2 : ℝ) ^ c / (c - 1) := div_pos (by linarith) (by linarith)
  have h2 : (0 : ℝ) < 2 := by norm_num
  exact mul_pos (mul_pos (mul_pos h2 hd0) h3) hdiv

/-- The pure-log tail-shell constant is nonnegative. -/
lemma tailShellConstLog_nonneg {d : ℕ} (hd : 1 ≤ d) {c : ℝ} (hc : 1 < c) :
    0 ≤ tailShellConstLog d c :=
  (tailShellConstLog_pos hd hc).le

/-- The `A3` constant of the marginal assembly is nonnegative. -/
lemma margReg3Const_nonneg {d : ℕ} (hd : 1 ≤ d) {ah bh : ℝ} (hS : 1 < ah + bh) :
    0 ≤ margReg3Const d ah bh := by
  unfold margReg3Const
  exact mul_nonneg (Real.rpow_nonneg (by norm_num) _) (tailShellConstLog_nonneg hd hS)

end CriticalLRPConv

/-! ## Axiom audit -/

set_option linter.hashCommand false

#print axioms CriticalLRPConv.margTargetR_eq_explicit
#print axioms CriticalLRPConv.margTarget_eq_explicit
#print axioms CriticalLRPConv.margTargetR_pos
#print axioms CriticalLRPConv.margTargetR_nonneg
#print axioms CriticalLRPConv.margTarget_pos
#print axioms CriticalLRPConv.margTarget_nonneg
#print axioms CriticalLRPConv.LamR_ge_log_two
#print axioms CriticalLRPConv.two_rpow_pos
#print axioms CriticalLRPConv.convTargetR_le_two_margTargetR
#print axioms CriticalLRPConv.margTargetR_halve_le
#print axioms CriticalLRPConv.tailShellConstLog_pos
#print axioms CriticalLRPConv.tailShellConstLog_nonneg
#print axioms CriticalLRPConv.margReg3Const_nonneg
