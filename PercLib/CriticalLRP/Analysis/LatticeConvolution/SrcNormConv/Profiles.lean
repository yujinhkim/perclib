/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.
-/
module

public import PercLib.CriticalLRP.Analysis.LatticeConvolution.SrcNormConv.Defs

/-!
# Real-variable profile lemmas for the source-norm assembly

Monotonicity of `Wt` in its radius, the product formula at a common radius, nonnegativity
of the source-norm constants, and the two transferred ball/tail shell estimates that the
`A1`/`A2` and `A3` region bounds consume.
-/

set_option autoImplicit false

@[expose] public section

namespace SrcNormConv

open PercLib.CriticalLRP.Orchestration
open CriticalLRPConv

variable {d : ℕ}

/-! ## §1 Monotonicity and the product formula -/

/-- `Wt e c` is antitone in the radius for `e, c ≥ 0`. -/
theorem Wt_antitone {e c r s : ℝ} (he : 0 ≤ e) (hc : 0 ≤ c) (hr : 0 ≤ r) (hrs : r ≤ s) :
    Wt e c s ≤ Wt e c r := by
  have hs : (0 : ℝ) ≤ s := le_trans hr hrs
  have hpow : (1 + s) ^ (-e) ≤ (1 + r) ^ (-e) :=
    Real.rpow_le_rpow_of_nonpos (show (0 : ℝ) < 1 + r by linarith)
      (show (1 + r) ≤ 1 + s by linarith) (show -e ≤ 0 by linarith)
  have hlog : LamR s ^ (-c) ≤ LamR r ^ (-c) :=
    Real.rpow_le_rpow_of_nonpos (LamR_pos hr) (LamR_mono hr hrs) (show -c ≤ 0 by linarith)
  have hB : (0 : ℝ) ≤ (1 + r) ^ (-e) := Real.rpow_nonneg (by linarith) _
  have hC : (0 : ℝ) ≤ LamR s ^ (-c) := Real.rpow_nonneg (LamR_nonneg hs) _
  simp only [Wt]
  exact mul_le_mul hpow hlog hC hB

/-- The product of two `Wt` factors at a common radius is again a `Wt` factor: the power
exponents and the logarithmic exponents add. -/
theorem Wt_mul_same {e₁ c₁ e₂ c₂ r : ℝ} (hr : 0 ≤ r) :
    Wt e₁ c₁ r * Wt e₂ c₂ r = Wt (e₁ + e₂) (c₁ + c₂) r := by
  have hb : (0 : ℝ) < 1 + r := by linarith
  have hl : (0 : ℝ) < LamR r := LamR_pos hr
  have h1 : (-e₁) + (-e₂) = -(e₁ + e₂) := by ring
  have h2 : (-c₁) + (-c₂) = -(c₁ + c₂) := by ring
  simp only [Wt]
  rw [← h1, ← h2, Real.rpow_add hb, Real.rpow_add hl]
  ring

/-! ## §2 Nonnegativity of the source-norm constants -/

/-- The transferred ball-shell factor is nonnegative. -/
theorem srcBallShellConst_nonneg (S : SourceNormData d) {a c : ℝ} (hd : 1 ≤ d)
    (haD : a ≤ (d : ℝ)) (hc : 0 ≤ c) : 0 ≤ srcBallShellConst (d := d) S a c := by
  have h1 : (0 : ℝ) ≤ (2 : ℝ) ^ a := Real.rpow_nonneg (by norm_num) _
  have h2 : 0 ≤ srcCountConst S := srcCountConst_nonneg S hd
  have h3 : (0 : ℝ) ≤ (d : ℝ) - a + 2 * (c + 1) := by linarith
  have h4 : (0 : ℝ) < coreConst a c := coreConst_pos a c
  have h5 : (0 : ℝ) ≤ 1 + ((d : ℝ) - a + 2 * (c + 1)) * coreConst a c := by
    have := mul_nonneg h3 h4.le
    linarith
  exact mul_nonneg h1 (mul_nonneg h2 h5)

/-- The norm-dependent factor of the transferred pure power tail is nonnegative. -/
theorem srcPowTailConst_nonneg (S : SourceNormData d) {γ : ℝ} (hd : 1 ≤ d) (hγ : 0 < γ) :
    0 ≤ srcPowTailConst (d := d) S γ := by
  have hm : 0 < srcLowerUnit S := srcLowerUnit_pos S hd
  have hC : 0 < srcUpperConst S := srcUpperConst_pos S
  have ht : 0 < tailShellConst d γ := tailShellConst_pos hd hγ
  have h1 : (0 : ℝ) ≤ srcLowerUnit S ^ (-((d : ℝ) + γ)) := Real.rpow_nonneg hm.le _
  have h2 : (0 : ℝ) ≤ tailShellConst d γ := ht.le
  have h3 : (0 : ℝ) ≤ srcUpperConst S ^ γ := Real.rpow_nonneg hC.le _
  exact mul_nonneg (mul_nonneg h1 h2) h3

/-! ## §3 The transferred `A1`/`A2` ball shell at the half radius -/

/-- **The `A1`/`A2` ball shell at the half radius.**  Summing the source-norm weight over a
finite set of `S.ρ`-radius at most `A/2` and halving the profile costs `srcBallShellConst`
times the exact halving factor `2^c (1+A)^a Λ(A)^{-c}`. -/
theorem srcBallShell_sum_le (S : SourceNormData d) (hd : 1 ≤ d) {a c A : ℝ} (ha : 0 < a)
    (haD : a < (d : ℝ)) (hc : 0 ≤ c) (hA : 0 ≤ A) {F : Finset (Fin d → ℤ)}
    (hrad : ∀ y ∈ F, S.ρ (toVec y) ≤ A / 2) :
    ∑ y ∈ F, Wt ((d : ℝ) - a) c (S.ρ (toVec y)) ≤
      srcBallShellConst (d := d) S a c * ((2 : ℝ) ^ c * ((1 + A) ^ a * LamR A ^ (-c))) := by
  have hhalf : (0 : ℝ) ≤ A / 2 := by linarith
  have h1 : ∑ y ∈ F, Wt ((d : ℝ) - a) c (S.ρ (toVec y)) ≤
      srcBallShellConst (d := d) S a c * ((1 + A / 2) ^ a * LamR (A / 2) ^ (-c)) :=
    srcNorm_ball_shell_bound S hd ha haD hc hhalf hrad
  have h2 := ball_profile_halve ha.le hc hA
  have hK : 0 ≤ srcBallShellConst (d := d) S a c :=
    srcBallShellConst_nonneg S hd haD.le hc
  exact h1.trans (mul_le_mul_of_nonneg_left h2 hK)

/-! ## §4 The transferred pure power tail beyond the half radius -/

/-- **The pure power tail beyond `A/2` in the source norm.**  The `A3` decay: the pure power
weight summed over the source-norm tail beyond `A/2` is bounded by the norm-dependent
constant times the halved profile. -/
theorem srcPowTail_sum_le (S : SourceNormData d) (hd : 1 ≤ d) {γ A : ℝ} (hγ : 0 < γ)
    (hA : 0 ≤ A) (F : Finset (Fin d → ℤ)) (hF : ∀ y ∈ F, A / 2 < S.ρ (toVec y)) :
    ∑ y ∈ F, Wt ((d : ℝ) + γ) 0 (S.ρ (toVec y)) ≤
      (2 : ℝ) ^ γ * srcPowTailConst (d := d) S γ * Wt γ 0 A := by
  have hhalf : (0 : ℝ) ≤ A / 2 := by linarith
  have hm : 0 < srcLowerUnit S := srcLowerUnit_pos S hd
  have hC : 0 < srcUpperConst S := srcUpperConst_pos S
  have ht : 0 < tailShellConst d γ := tailShellConst_pos hd hγ
  -- the transferred shell estimate at the threshold `A/2`
  have h1 : ∑ y ∈ F, Wt ((d : ℝ) + γ) 0 (S.ρ (toVec y)) ≤
      srcLowerUnit S ^ (-((d : ℝ) + γ)) * tailShellConst d γ *
        Wt γ 0 ((A / 2) / srcUpperConst S) := by
    have h := sum_Wt_tail_le_srcNorm S hd hγ (le_refl (0 : ℝ)) hhalf F hF
    calc ∑ y ∈ F, Wt ((d : ℝ) + γ) 0 (S.ρ (toVec y))
        ≤ srcLowerUnit S ^ (-((d : ℝ) + γ)) * srcLogConst S ^ (0 : ℝ) *
            (tailShellConst d γ * Wt γ 0 ((A / 2) / srcUpperConst S)) := h
      _ = srcLowerUnit S ^ (-((d : ℝ) + γ)) * tailShellConst d γ *
            Wt γ 0 ((A / 2) / srcUpperConst S) := by
          rw [Real.rpow_zero, mul_one, mul_assoc]
  -- rescaling the outer radius by the upper comparison constant
  have h2 : Wt γ 0 ((A / 2) / srcUpperConst S) ≤
      srcUpperConst S ^ γ * Wt γ 0 (A / 2) := by
    have h := Wt_div_srcUpper_le (S := S) (e := γ) (c := 0) (S₀ := A / 2) hγ.le
      (le_refl (0 : ℝ)) hhalf
    calc Wt γ 0 ((A / 2) / srcUpperConst S)
        ≤ srcUpperConst S ^ γ * srcLogConstUpper S ^ (0 : ℝ) * Wt γ 0 (A / 2) := h
      _ = srcUpperConst S ^ γ * Wt γ 0 (A / 2) := by rw [Real.rpow_zero, mul_one]
  -- halving the pure power radius
  have h3 : Wt γ 0 (A / 2) ≤ (2 : ℝ) ^ γ * Wt γ 0 A := by
    rw [Wt_zero_log, Wt_zero_log]
    exact one_add_halve_rpow_le_neg hγ.le hA
  have hmK : (0 : ℝ) ≤ srcLowerUnit S ^ (-((d : ℝ) + γ)) := Real.rpow_nonneg hm.le _
  have hstep : ∑ y ∈ F, Wt ((d : ℝ) + γ) 0 (S.ρ (toVec y)) ≤
      srcLowerUnit S ^ (-((d : ℝ) + γ)) * tailShellConst d γ *
        (srcUpperConst S ^ γ * ((2 : ℝ) ^ γ * Wt γ 0 A)) := by
    have h2' : Wt γ 0 ((A / 2) / srcUpperConst S) ≤
        srcUpperConst S ^ γ * ((2 : ℝ) ^ γ * Wt γ 0 A) := by
      refine h2.trans ?_
      calc srcUpperConst S ^ γ * Wt γ 0 (A / 2)
          ≤ srcUpperConst S ^ γ * ((2 : ℝ) ^ γ * Wt γ 0 A) :=
            mul_le_mul_of_nonneg_left h3 (Real.rpow_nonneg hC.le _)
        _ = srcUpperConst S ^ γ * ((2 : ℝ) ^ γ * Wt γ 0 A) := rfl
    refine h1.trans ?_
    calc srcLowerUnit S ^ (-((d : ℝ) + γ)) * tailShellConst d γ *
          Wt γ 0 ((A / 2) / srcUpperConst S)
        ≤ srcLowerUnit S ^ (-((d : ℝ) + γ)) * tailShellConst d γ *
            (srcUpperConst S ^ γ * ((2 : ℝ) ^ γ * Wt γ 0 A)) :=
          mul_le_mul_of_nonneg_left h2' (mul_nonneg hmK ht.le)
      _ = srcLowerUnit S ^ (-((d : ℝ) + γ)) * tailShellConst d γ *
            (srcUpperConst S ^ γ * ((2 : ℝ) ^ γ * Wt γ 0 A)) := rfl
  calc ∑ y ∈ F, Wt ((d : ℝ) + γ) 0 (S.ρ (toVec y))
      ≤ srcLowerUnit S ^ (-((d : ℝ) + γ)) * tailShellConst d γ *
          (srcUpperConst S ^ γ * ((2 : ℝ) ^ γ * Wt γ 0 A)) := hstep
    _ = (2 : ℝ) ^ γ * srcPowTailConst (d := d) S γ * Wt γ 0 A := by
        rw [srcPowTailConst]
        ring

/-- **The centred pure power tail beyond `A/2` in the source norm.**  The same tail estimate
for the weight `Wt (d+γ) 0 (S.ρ (x-y))`, transported along the injective reflection
`y ↦ x - y`. -/
theorem srcPowTail_sum_le_sub (S : SourceNormData d) (hd : 1 ≤ d) {γ A : ℝ} (hγ : 0 < γ)
    (hA : 0 ≤ A) (x : Fin d → ℤ) (F : Finset (Fin d → ℤ))
    (hF : ∀ y ∈ F, A / 2 < S.ρ (toVec (x - y))) :
    ∑ y ∈ F, Wt ((d : ℝ) + γ) 0 (S.ρ (toVec (x - y))) ≤
      (2 : ℝ) ^ γ * srcPowTailConst (d := d) S γ * Wt γ 0 A := by
  classical
  have hinj : Set.InjOn (fun y : Fin d → ℤ => (x - y : Fin d → ℤ)) ↑F := by
    intro u _ v _ huv
    have huv' : x - u = x - v := huv
    have h : x - (x - u) = x - (x - v) := by rw [huv']
    simpa using h
  rw [← Finset.sum_image (f := fun z => Wt ((d : ℝ) + γ) 0 (S.ρ (toVec z))) hinj]
  refine srcPowTail_sum_le S hd hγ hA _ ?_
  intro z hz
  obtain ⟨y, hyF, rfl⟩ := Finset.mem_image.mp hz
  exact hF y hyF

end SrcNormConv
