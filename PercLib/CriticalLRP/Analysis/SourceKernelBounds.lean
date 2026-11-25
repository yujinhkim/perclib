/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

# Power bounds and ratio bounds for the source kernel

For the actual `SourceModelData` kernel `K` this module exports the two-sided
explicit power bound on a tail and the consequent ratio bound, i.e. regular
variation of `K` at `∞` up to the explicit constant `4`.

Only the structure fields `K_antitone`, `K_eq_integral` and `exists_error` are
used.  No continuity, differentiability or monotonicity statement about the
cutoff mass is made here.
-/
module

public import PercLib.CriticalLRP.MomentMonotonicity.SourceModelCutoffLimit
public import PercLib.CriticalLRP.MomentMonotonicity.StrictCutoffEpsilon
public import PercLib.CriticalLRP.Analysis.RegularVariation

/-! # Source-kernel parameters and regular variation -/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal Topology BigOperators

@[expose] public section

noncomputable section

namespace PercLib.CriticalLRP.Orchestration

namespace SourceModelData

variable (M : SourceModelData)

/-- The source exponent `d + α` is positive. -/
theorem kernelExponent_pos : 0 < (M.d : ℝ) + M.α := by
  have h : (0 : ℝ) ≤ (M.d : ℝ) := Nat.cast_nonneg M.d
  linarith [M.hα]

/-- **Two-sided explicit power bound for the source kernel on a tail.**
There is `R > 0` with
`(1/(2(d+α))) r^{-(d+α)} ≤ K r ≤ (2/(d+α)) r^{-(d+α)}` for every `r ≥ R`. -/
theorem exists_K_power_bounds :
    ∃ R : ℝ, 0 < R ∧ ∀ r : ℝ, R ≤ r →
      (1 / (2 * ((M.d : ℝ) + M.α))) * r ^ (-((M.d : ℝ) + M.α)) ≤ M.K r ∧
        M.K r ≤ (2 / ((M.d : ℝ) + M.α)) * r ^ (-((M.d : ℝ) + M.α)) := by
  obtain ⟨R, hRpos, hint, hlow, hupp⟩ := M.exists_deriv_bounds
  have hexp : -(M.d : ℝ) - M.α - 1 < -1 := by linarith [M.hα]
  refine ⟨R, hRpos, fun r hr => ⟨?_, ?_⟩⟩
  · have hrpos : 0 < r := lt_of_lt_of_le hRpos hr
    have hInt : IntegrableOn (fun s : ℝ => |deriv M.K s|) (Set.Ioi r) :=
      hint.mono_set (Set.Ioi_subset_Ioi hr)
    have hg : IntegrableOn (fun s : ℝ => (1 / 2) * s ^ (-(M.d : ℝ) - M.α - 1))
        (Set.Ioi r) :=
      (integrableOn_Ioi_rpow_of_lt hexp hrpos).const_mul (1 / 2)
    have hmono : ∫ s in Set.Ioi r, (1 / 2) * s ^ (-(M.d : ℝ) - M.α - 1)
        ≤ ∫ s in Set.Ioi r, |deriv M.K s| :=
      setIntegral_mono_on hg hInt measurableSet_Ioi
        (fun s hs => hlow s (lt_of_le_of_lt hr hs))
    have hval : ∫ s in Set.Ioi r, (1 / 2) * s ^ (-(M.d : ℝ) - M.α - 1)
        = (1 / (2 * ((M.d : ℝ) + M.α))) * r ^ (-((M.d : ℝ) + M.α)) := by
      rw [integral_const_mul, integral_Ioi_rpow_of_lt hexp hrpos]
      have hb1 : -(M.d : ℝ) - M.α - 1 + 1 = -((M.d : ℝ) + M.α) := by ring
      rw [hb1]
      field_simp
    rw [M.K_eq_integral r hrpos, ← hval]
    exact hmono
  · have hrpos : 0 < r := lt_of_lt_of_le hRpos hr
    have hInt : IntegrableOn (fun s : ℝ => |deriv M.K s|) (Set.Ioi r) :=
      hint.mono_set (Set.Ioi_subset_Ioi hr)
    have hg : IntegrableOn (fun s : ℝ => 2 * s ^ (-(M.d : ℝ) - M.α - 1))
        (Set.Ioi r) :=
      (integrableOn_Ioi_rpow_of_lt hexp hrpos).const_mul 2
    have hmono : ∫ s in Set.Ioi r, |deriv M.K s|
        ≤ ∫ s in Set.Ioi r, 2 * s ^ (-(M.d : ℝ) - M.α - 1) :=
      setIntegral_mono_on hInt hg measurableSet_Ioi
        (fun s hs => hupp s (lt_of_le_of_lt hr hs))
    have hval : ∫ s in Set.Ioi r, 2 * s ^ (-(M.d : ℝ) - M.α - 1)
        = (2 / ((M.d : ℝ) + M.α)) * r ^ (-((M.d : ℝ) + M.α)) := by
      rw [integral_const_mul, integral_Ioi_rpow_of_lt hexp hrpos]
      have hb1 : -(M.d : ℝ) - M.α - 1 + 1 = -((M.d : ℝ) + M.α) := by ring
      rw [hb1]
      field_simp
    rw [M.K_eq_integral r hrpos, ← hval]
    exact hmono

/-- Upper power bound. -/
theorem exists_K_le_power :
    ∃ R : ℝ, 0 < R ∧ ∀ r : ℝ, R ≤ r →
      M.K r ≤ (2 / ((M.d : ℝ) + M.α)) * r ^ (-((M.d : ℝ) + M.α)) := by
  obtain ⟨R, hRpos, h⟩ := M.exists_K_power_bounds
  exact ⟨R, hRpos, fun r hr => (h r hr).2⟩

/-- Lower power bound. -/
theorem exists_K_ge_power :
    ∃ R : ℝ, 0 < R ∧ ∀ r : ℝ, R ≤ r →
      (1 / (2 * ((M.d : ℝ) + M.α))) * r ^ (-((M.d : ℝ) + M.α)) ≤ M.K r := by
  obtain ⟨R, hRpos, h⟩ := M.exists_K_power_bounds
  exact ⟨R, hRpos, fun r hr => (h r hr).1⟩

/-- **Ratio bound: `K` is regularly varying up to the explicit constant `4`.**
For `R ≤ r ≤ r'` one has `K r' / K r ≤ 4 (r / r')^{d+α}`. -/
theorem exists_K_ratio_le :
    ∃ R : ℝ, 0 < R ∧ ∀ r r' : ℝ, R ≤ r → r ≤ r' →
      M.K r' / M.K r ≤ 4 * (r / r') ^ ((M.d : ℝ) + M.α) := by
  obtain ⟨R, hRpos, hb⟩ := M.exists_K_power_bounds
  refine ⟨R, hRpos, fun r r' hr hrr' => ?_⟩
  have hrpos : 0 < r := lt_of_lt_of_le hRpos hr
  have hr'pos : 0 < r' := lt_of_lt_of_le hrpos hrr'
  have hlow := (hb r hr).1
  have hupp := (hb r' (le_trans hr hrr')).2
  have hKr : 0 < M.K r := M.K_pos hrpos
  have hrr : (r / r') ^ ((M.d : ℝ) + M.α) * r ^ (-((M.d : ℝ) + M.α))
      = r' ^ (-((M.d : ℝ) + M.α)) := by
    rw [Real.div_rpow hrpos.le hr'pos.le, Real.rpow_neg hrpos.le, Real.rpow_neg hr'pos.le]
    field_simp
  rw [div_le_iff₀ hKr]
  refine le_trans hupp ?_
  calc (2 / ((M.d : ℝ) + M.α)) * r' ^ (-((M.d : ℝ) + M.α))
      = (2 / ((M.d : ℝ) + M.α))
          * ((r / r') ^ ((M.d : ℝ) + M.α) * r ^ (-((M.d : ℝ) + M.α))) := by rw [hrr]
    _ = (4 * (r / r') ^ ((M.d : ℝ) + M.α))
          * ((1 / (2 * ((M.d : ℝ) + M.α))) * r ^ (-((M.d : ℝ) + M.α))) := by
        field_simp
        ring
    _ ≤ (4 * (r / r') ^ ((M.d : ℝ) + M.α)) * M.K r :=
        mul_le_mul_of_nonneg_left hlow (by positivity)


/-- The power identity behind the dyadic shell bound:
`2^{dj} · (2^j)^{-(d+α)} = 2^{-α j}`. -/
theorem two_pow_mul_two_pow_rpow_neg (j : ℕ) :
    (2 : ℝ) ^ (M.d * j) * ((2 : ℝ) ^ j) ^ (-((M.d : ℝ) + M.α))
      = (2 : ℝ) ^ (-(M.α * (j : ℝ))) := by
  have hy : ((2 : ℝ) ^ j) ^ (-((M.d : ℝ) + M.α))
      = (2 : ℝ) ^ (-(M.α * (j : ℝ))) * (2 : ℝ) ^ (-((M.d : ℝ) * (j : ℝ))) := by
    rw [← Real.rpow_natCast (2 : ℝ) j, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    rw [show ((j : ℕ) : ℝ) * -((M.d : ℝ) + M.α)
        = -(M.α * ((j : ℕ) : ℝ)) + -((M.d : ℝ) * ((j : ℕ) : ℝ)) by ring,
      Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  have h3 : (2 : ℝ) ^ (M.d * j) * (2 : ℝ) ^ (-((M.d : ℝ) * ((j : ℕ) : ℝ))) = 1 := by
    rw [← Real.rpow_natCast (2 : ℝ) (M.d * j), ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    rw [show ((M.d * j : ℕ) : ℝ) + -((M.d : ℝ) * ((j : ℕ) : ℝ)) = 0 by push_cast; ring,
      Real.rpow_zero]
  calc (2 : ℝ) ^ (M.d * j) * ((2 : ℝ) ^ j) ^ (-((M.d : ℝ) + M.α))
      = (2 : ℝ) ^ (M.d * j) * ((2 : ℝ) ^ (-(M.α * (j : ℝ)))
          * (2 : ℝ) ^ (-((M.d : ℝ) * (j : ℝ)))) := by rw [hy]
    _ = (2 : ℝ) ^ (-(M.α * (j : ℝ)))
          * ((2 : ℝ) ^ (M.d * j) * (2 : ℝ) ^ (-((M.d : ℝ) * (j : ℝ)))) := by ring
    _ = (2 : ℝ) ^ (-(M.α * (j : ℝ))) * 1 := by rw [h3]
    _ = (2 : ℝ) ^ (-(M.α * (j : ℝ))) := by ring

/-- **Dyadic shell bound with a geometric constant.**  For `r ≥ R` and every scale `j`,
the shell mass at scale `j`, weighted by the lattice volume factor `2^{dj}`, is at most
`4 · 2^{-α j} · K r`.  Summing over `j` gives the explicit geometric bound
`4/(1 - 2^{-α}) · K r`. -/
theorem exists_K_dyadic_shell_le :
    ∃ R : ℝ, 0 < R ∧ ∀ r : ℝ, R ≤ r → ∀ j : ℕ,
      (2 : ℝ) ^ (M.d * j) * (M.K ((2 : ℝ) ^ j * r) - M.K ((2 : ℝ) ^ (j + 1) * r))
        ≤ 4 * (2 : ℝ) ^ (-(M.α * (j : ℝ))) * M.K r := by
  obtain ⟨R, hRpos, hb⟩ := M.exists_K_power_bounds
  refine ⟨R, hRpos, fun r hr j => ?_⟩
  have hrpos : 0 < r := lt_of_lt_of_le hRpos hr
  have h2j1 : (1 : ℝ) ≤ (2 : ℝ) ^ j := one_le_pow₀ (by norm_num)
  have h2jpos : (0 : ℝ) < (2 : ℝ) ^ j := by positivity
  have hrj : R ≤ (2 : ℝ) ^ j * r := by nlinarith
  have hupper := (hb ((2 : ℝ) ^ j * r) hrj).2
  have hlow := (hb r hr).1
  have hKr : 0 < M.K r := M.K_pos hrpos
  have hcpos := M.kernelExponent_pos
  have hcne : ((M.d : ℝ) + M.α) ≠ 0 := ne_of_gt hcpos
  have hshell : M.K ((2 : ℝ) ^ j * r) - M.K ((2 : ℝ) ^ (j + 1) * r)
      ≤ M.K ((2 : ℝ) ^ j * r) := by
    have hnn : 0 ≤ M.K ((2 : ℝ) ^ (j + 1) * r) := (M.K_pos (by positivity)).le
    linarith
  have hexpand : ((2 : ℝ) ^ j * r) ^ (-((M.d : ℝ) + M.α))
      = ((2 : ℝ) ^ j) ^ (-((M.d : ℝ) + M.α)) * r ^ (-((M.d : ℝ) + M.α)) :=
    Real.mul_rpow h2jpos.le hrpos.le
  have hrpow : r ^ (-((M.d : ℝ) + M.α)) ≤ 2 * ((M.d : ℝ) + M.α) * M.K r := by
    have hmul := mul_le_mul_of_nonneg_left hlow (by linarith [M.kernelExponent_pos] :
      (0 : ℝ) ≤ 2 * ((M.d : ℝ) + M.α))
    calc r ^ (-((M.d : ℝ) + M.α))
        = 2 * ((M.d : ℝ) + M.α)
            * ((1 / (2 * ((M.d : ℝ) + M.α))) * r ^ (-((M.d : ℝ) + M.α))) := by
          field_simp
      _ ≤ 2 * ((M.d : ℝ) + M.α) * M.K r := hmul
  have hchain : (2 : ℝ) ^ (M.d * j)
        * (M.K ((2 : ℝ) ^ j * r) - M.K ((2 : ℝ) ^ (j + 1) * r))
      ≤ (2 : ℝ) ^ (M.d * j)
          * ((2 / ((M.d : ℝ) + M.α)) * ((2 : ℝ) ^ j * r) ^ (-((M.d : ℝ) + M.α))) := by
    have h1 : (0 : ℝ) ≤ (2 : ℝ) ^ (M.d * j) := by positivity
    exact mul_le_mul_of_nonneg_left (le_trans hshell hupper) h1
  refine le_trans hchain ?_
  rw [hexpand]
  have hstep : (2 : ℝ) ^ (M.d * j)
        * ((2 / ((M.d : ℝ) + M.α))
          * (((2 : ℝ) ^ j) ^ (-((M.d : ℝ) + M.α)) * r ^ (-((M.d : ℝ) + M.α))))
      = (2 / ((M.d : ℝ) + M.α))
          * ((2 : ℝ) ^ (-(M.α * (j : ℝ))) * r ^ (-((M.d : ℝ) + M.α))) := by
    rw [show (2 : ℝ) ^ (M.d * j)
          * ((2 / ((M.d : ℝ) + M.α))
            * (((2 : ℝ) ^ j) ^ (-((M.d : ℝ) + M.α)) * r ^ (-((M.d : ℝ) + M.α))))
        = (2 / ((M.d : ℝ) + M.α))
          * (((2 : ℝ) ^ (M.d * j) * ((2 : ℝ) ^ j) ^ (-((M.d : ℝ) + M.α)))
            * r ^ (-((M.d : ℝ) + M.α))) from by ring,
      M.two_pow_mul_two_pow_rpow_neg j]
  rw [hstep]
  have hfin : (2 / ((M.d : ℝ) + M.α)) * r ^ (-((M.d : ℝ) + M.α)) ≤ 4 * M.K r := by
    have hmul := mul_le_mul_of_nonneg_left hrpow
      (le_of_lt (div_pos (by norm_num) M.kernelExponent_pos) : (0 : ℝ) ≤ 2 / ((M.d : ℝ) + M.α))
    calc (2 / ((M.d : ℝ) + M.α)) * r ^ (-((M.d : ℝ) + M.α))
        ≤ (2 / ((M.d : ℝ) + M.α)) * (2 * ((M.d : ℝ) + M.α) * M.K r) := hmul
      _ = 4 * M.K r := by
        field_simp
        norm_num
  have hpos2 : (0 : ℝ) ≤ (2 : ℝ) ^ (-(M.α * (j : ℝ))) := by positivity
  calc (2 / ((M.d : ℝ) + M.α)) * ((2 : ℝ) ^ (-(M.α * (j : ℝ))) * r ^ (-((M.d : ℝ) + M.α)))
      = (2 : ℝ) ^ (-(M.α * (j : ℝ)))
          * ((2 / ((M.d : ℝ) + M.α)) * r ^ (-((M.d : ℝ) + M.α))) := by ring
    _ ≤ (2 : ℝ) ^ (-(M.α * (j : ℝ))) * (4 * M.K r) :=
        mul_le_mul_of_nonneg_left hfin hpos2
    _ = 4 * (2 : ℝ) ^ (-(M.α * (j : ℝ))) * M.K r := by ring

end SourceModelData

end PercLib.CriticalLRP.Orchestration

end

set_option linter.hashCommand false

#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.kernelExponent_pos
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.exists_K_power_bounds
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.exists_K_le_power
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.exists_K_ge_power
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.exists_K_ratio_le
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.two_pow_mul_two_pow_rpow_neg
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.exists_K_dyadic_shell_le
