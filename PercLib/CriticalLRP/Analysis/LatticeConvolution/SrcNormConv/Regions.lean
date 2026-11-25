/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.
-/
module

public import PercLib.CriticalLRP.Analysis.LatticeConvolution.SrcNormConv.Profiles

/-!
# The `A1`/`A2`/`A3` region bounds in the source norm

Each of the three regions of the frozen strict assembly is re-derived for the source
norm `S.ρ (toVec ·)`: the reverse triangle inequalities are those of the quasi-norm
`S.ρ` itself (`S.ρ_add_le`), the ball shell is the transferred `srcNorm_ball_shell_bound`,
and the far tails are the transferred pure power tails `srcPowTail_sum_le`.  The only
norm input is therefore the landed `NormShell` material, and the resulting constants
depend on `S` only through `srcCountConst`, `srcLowerUnit`, `srcUpperConst` and
`srcLogConstUpper`.
-/

set_option autoImplicit false

@[expose] public section

namespace SrcNormConv

open PercLib.CriticalLRP.Orchestration
open CriticalLRPConv

variable {d : ℕ}

/-! ## §1 Additivity of `toVec` and the reverse triangle inequalities in `S.ρ` -/

/-- `toVec` is additive. -/
theorem toVec_add {d : ℕ} (x y : Fin d → ℤ) : toVec (x + y) = toVec x + toVec y := by
  funext i
  simp [toVec]

/-- **`A1` reverse triangle in the source norm.**  Inside the `S.ρ`-half-ball around the
origin, the source distance to `x` is at least half the source radius of `x`. -/
theorem srcNorm_halve_le_sub (S : SourceNormData d) {x y : Fin d → ℤ}
    (hy : S.ρ (toVec y) ≤ S.ρ (toVec x) / 2) :
    S.ρ (toVec x) / 2 ≤ S.ρ (toVec (x - y)) := by
  have htri : S.ρ (toVec x) ≤ S.ρ (toVec (x - y)) + S.ρ (toVec y) := by
    calc S.ρ (toVec x) = S.ρ (toVec ((x - y) + y)) := by rw [sub_add_cancel]
      _ = S.ρ (toVec (x - y) + toVec y) := by rw [toVec_add]
      _ ≤ S.ρ (toVec (x - y)) + S.ρ (toVec y) := S.ρ_add_le _ _
  linarith

/-- **`A2` reverse triangle in the source norm.**  Inside the `S.ρ`-half-ball around `x`,
the source radius of `y` is at least half the source radius of `x`. -/
theorem srcNorm_halve_le_of_sub_le (S : SourceNormData d) {x y : Fin d → ℤ}
    (h : S.ρ (toVec (x - y)) ≤ S.ρ (toVec x) / 2) :
    S.ρ (toVec x) / 2 ≤ S.ρ (toVec y) := by
  have htri : S.ρ (toVec x) ≤ S.ρ (toVec (x - y)) + S.ρ (toVec y) := by
    calc S.ρ (toVec x) = S.ρ (toVec ((x - y) + y)) := by rw [sub_add_cancel]
      _ = S.ρ (toVec (x - y) + toVec y) := by rw [toVec_add]
      _ ≤ S.ρ (toVec (x - y)) + S.ρ (toVec y) := S.ρ_add_le _ _
  linarith

/-! ## §2 The real-arithmetic identities of the three regions -/

/-- The `A1` region arithmetic: freezing the outer factor at the half radius and halving the
ball shell combine into the region-1 constant times the target profile. -/
theorem reg1_arith {A B a b ah bh : ℝ} (hA : 0 ≤ A) :
    (2 : ℝ) ^ (((d : ℝ) - b) + bh) * ((1 + A) ^ (-((d : ℝ) - b)) * LamR A ^ (-bh)) *
        (B * ((2 : ℝ) ^ ah * ((1 + A) ^ a * LamR A ^ (-ah))))
      = ((2 : ℝ) ^ (((d : ℝ) - b) + bh) * (B * (2 : ℝ) ^ ah)) *
        ((1 + A) ^ (-((d : ℝ) - a - b)) * LamR A ^ (-(ah + bh))) := by
  have hb : (0 : ℝ) < 1 + A := by linarith
  have hl : (0 : ℝ) < LamR A := LamR_pos hA
  have h1 : (1 + A) ^ (-((d : ℝ) - b)) * (1 + A) ^ a = (1 + A) ^ (-((d : ℝ) - a - b)) := by
    rw [← Real.rpow_add hb]
    congr 1
    ring
  have h2 : LamR A ^ (-bh) * LamR A ^ (-ah) = LamR A ^ (-(ah + bh)) := by
    rw [← Real.rpow_add hl]
    congr 1
    ring
  calc (2 : ℝ) ^ (((d : ℝ) - b) + bh) * ((1 + A) ^ (-((d : ℝ) - b)) * LamR A ^ (-bh)) *
        (B * ((2 : ℝ) ^ ah * ((1 + A) ^ a * LamR A ^ (-ah))))
      = ((2 : ℝ) ^ (((d : ℝ) - b) + bh) * (B * (2 : ℝ) ^ ah)) *
          ((1 + A) ^ (-((d : ℝ) - b)) * (1 + A) ^ a * (LamR A ^ (-bh) * LamR A ^ (-ah))) := by
        ring
    _ = ((2 : ℝ) ^ (((d : ℝ) - b) + bh) * (B * (2 : ℝ) ^ ah)) *
          ((1 + A) ^ (-((d : ℝ) - a - b)) * LamR A ^ (-(ah + bh))) := by
        rw [h1, h2]

/-- The `A2` region arithmetic. -/
theorem reg2_arith {A B a b ah bh : ℝ} (hA : 0 ≤ A) :
    (2 : ℝ) ^ (((d : ℝ) - a) + ah) * ((1 + A) ^ (-((d : ℝ) - a)) * LamR A ^ (-ah)) *
        (B * ((2 : ℝ) ^ bh * ((1 + A) ^ b * LamR A ^ (-bh))))
      = ((2 : ℝ) ^ (((d : ℝ) - a) + ah) * (B * (2 : ℝ) ^ bh)) *
        ((1 + A) ^ (-((d : ℝ) - a - b)) * LamR A ^ (-(ah + bh))) := by
  have hb : (0 : ℝ) < 1 + A := by linarith
  have hl : (0 : ℝ) < LamR A := LamR_pos hA
  have h1 : (1 + A) ^ (-((d : ℝ) - a)) * (1 + A) ^ b = (1 + A) ^ (-((d : ℝ) - a - b)) := by
    rw [← Real.rpow_add hb]
    congr 1
    ring
  have h2 : LamR A ^ (-ah) * LamR A ^ (-bh) = LamR A ^ (-(ah + bh)) := by
    rw [← Real.rpow_add hl]
    congr 1
    ring
  calc (2 : ℝ) ^ (((d : ℝ) - a) + ah) * ((1 + A) ^ (-((d : ℝ) - a)) * LamR A ^ (-ah)) *
        (B * ((2 : ℝ) ^ bh * ((1 + A) ^ b * LamR A ^ (-bh))))
      = ((2 : ℝ) ^ (((d : ℝ) - a) + ah) * (B * (2 : ℝ) ^ bh)) *
          ((1 + A) ^ (-((d : ℝ) - a)) * (1 + A) ^ b * (LamR A ^ (-ah) * LamR A ^ (-bh))) := by
        ring
    _ = ((2 : ℝ) ^ (((d : ℝ) - a) + ah) * (B * (2 : ℝ) ^ bh)) *
          ((1 + A) ^ (-((d : ℝ) - a - b)) * LamR A ^ (-(ah + bh))) := by
        rw [h1, h2]

/-- The `A3` region arithmetic: one far half, with the pure power tail. -/
theorem reg3_arith {A P a b ah bh : ℝ} (hA : 0 ≤ A) :
    ((2 : ℝ) ^ ah * LamR A ^ (-ah)) * ((2 : ℝ) ^ bh * LamR A ^ (-bh)) *
        ((2 : ℝ) ^ ((d : ℝ) - a - b) * P * (1 + A) ^ (-((d : ℝ) - a - b)))
      = ((2 : ℝ) ^ ah * (2 : ℝ) ^ bh *
          ((2 : ℝ) ^ ((d : ℝ) - a - b) * P)) *
        ((1 + A) ^ (-((d : ℝ) - a - b)) * LamR A ^ (-(ah + bh))) := by
  have hl : (0 : ℝ) < LamR A := LamR_pos hA
  have h2 : LamR A ^ (-ah) * LamR A ^ (-bh) = LamR A ^ (-(ah + bh)) := by
    rw [← Real.rpow_add hl]
    congr 1
    ring
  calc ((2 : ℝ) ^ ah * LamR A ^ (-ah)) * ((2 : ℝ) ^ bh * LamR A ^ (-bh)) *
        ((2 : ℝ) ^ ((d : ℝ) - a - b) * P * (1 + A) ^ (-((d : ℝ) - a - b)))
      = ((2 : ℝ) ^ ah * (2 : ℝ) ^ bh * ((2 : ℝ) ^ ((d : ℝ) - a - b) * P)) *
          ((1 + A) ^ (-((d : ℝ) - a - b)) * (LamR A ^ (-ah) * LamR A ^ (-bh))) := by
        ring
    _ = ((2 : ℝ) ^ ah * (2 : ℝ) ^ bh *
          ((2 : ℝ) ^ ((d : ℝ) - a - b) * P)) *
        ((1 + A) ^ (-((d : ℝ) - a - b)) * LamR A ^ (-(ah + bh))) := by
        rw [h2]

/-! ## §3 The `A1` region bound in the source norm -/

/-- **The `A1` region.**  On `S.ρ y ≤ S.ρ x / 2` the second factor is frozen at the half
radius and the first is summed by the transferred ball-shell estimate. -/
theorem sum_srcConvReg1_le (S : SourceNormData d) (hd : 1 ≤ d) {a b ah bh : ℝ} (ha : 0 < a)
    (hb : 0 < b) (hab : a + b < (d : ℝ)) (hah : 0 ≤ ah) (hbh : 0 ≤ bh) (x : Fin d → ℤ)
    (F : Finset (Fin d → ℤ)) (hF : ∀ y ∈ F, srcConvReg1 S x y) :
    ∑ y ∈ F, srcConvMajorant S a b ah bh x y ≤
      srcConvReg1Const (d := d) S a b ah bh * srcConvTarget S a b ah bh x := by
  classical
  have hA : (0 : ℝ) ≤ S.ρ (toVec x) := src_nonneg S _
  have had : a < (d : ℝ) := by linarith
  have hbd : b < (d : ℝ) := by linarith
  have he : (0 : ℝ) ≤ (d : ℝ) - b := by linarith
  set C : ℝ := (2 : ℝ) ^ (((d : ℝ) - b) + bh) *
    ((1 + S.ρ (toVec x)) ^ (-((d : ℝ) - b)) * LamR (S.ρ (toVec x)) ^ (-bh)) with hCdef
  have hCnn : 0 ≤ C := by
    rw [hCdef]
    have h1 : (0 : ℝ) ≤ (2 : ℝ) ^ (((d : ℝ) - b) + bh) := Real.rpow_nonneg (by norm_num) _
    have h2 : (0 : ℝ) ≤ (1 + S.ρ (toVec x)) ^ (-((d : ℝ) - b)) :=
      Real.rpow_nonneg (by linarith) _
    have h3 : (0 : ℝ) ≤ LamR (S.ρ (toVec x)) ^ (-bh) :=
      Real.rpow_nonneg (LamR_nonneg hA) _
    exact mul_nonneg h1 (mul_nonneg h2 h3)
  have hterm : ∀ y ∈ F,
      srcConvMajorant S a b ah bh x y ≤ C * Wt ((d : ℝ) - a) ah (S.ρ (toVec y)) := by
    intro y hy
    have hreg : S.ρ (toVec y) ≤ S.ρ (toVec x) / 2 := (srcConvReg1_iff S x y).mp (hF y hy)
    have hv : S.ρ (toVec x) / 2 ≤ S.ρ (toVec (x - y)) := srcNorm_halve_le_sub S hreg
    have hfreeze : Wt ((d : ℝ) - b) bh (S.ρ (toVec (x - y))) ≤ C := by
      rw [hCdef]
      exact Wt_freeze_halve he hbh hA hv
    have h1 : (0 : ℝ) ≤ Wt ((d : ℝ) - a) ah (S.ρ (toVec y)) := Wt_nonneg (src_nonneg S _)
    calc srcConvMajorant S a b ah bh x y
        = Wt ((d : ℝ) - a) ah (S.ρ (toVec y)) *
            Wt ((d : ℝ) - b) bh (S.ρ (toVec (x - y))) :=
          srcConvMajorant_eq S a b ah bh x y
      _ ≤ Wt ((d : ℝ) - a) ah (S.ρ (toVec y)) * C :=
          mul_le_mul_of_nonneg_left hfreeze h1
      _ = C * Wt ((d : ℝ) - a) ah (S.ρ (toVec y)) := by ring
  have hbs : ∑ y ∈ F, Wt ((d : ℝ) - a) ah (S.ρ (toVec y)) ≤
      srcBallShellConst (d := d) S a ah *
        ((2 : ℝ) ^ ah * ((1 + S.ρ (toVec x)) ^ a * LamR (S.ρ (toVec x)) ^ (-ah))) :=
    srcBallShell_sum_le S hd ha had hah hA (fun y hy => (srcConvReg1_iff S x y).mp (hF y hy))
  calc ∑ y ∈ F, srcConvMajorant S a b ah bh x y
      ≤ ∑ y ∈ F, C * Wt ((d : ℝ) - a) ah (S.ρ (toVec y)) := Finset.sum_le_sum hterm
    _ = C * ∑ y ∈ F, Wt ((d : ℝ) - a) ah (S.ρ (toVec y)) := by rw [Finset.mul_sum]
    _ ≤ C * (srcBallShellConst (d := d) S a ah *
          ((2 : ℝ) ^ ah * ((1 + S.ρ (toVec x)) ^ a * LamR (S.ρ (toVec x)) ^ (-ah)))) :=
        mul_le_mul_of_nonneg_left hbs hCnn
    _ = srcConvReg1Const (d := d) S a b ah bh * srcConvTarget S a b ah bh x := by
        rw [hCdef, srcConvReg1Const, srcConvTarget_eq]
        exact reg1_arith (d := d) hA

/-! ## §4 The `A2` region bound in the source norm -/

/-- **The `A2` region.**  On `S.ρ (x-y) ≤ S.ρ x / 2` the first factor is frozen at the half
radius and the second is summed by the transferred centred ball-shell estimate. -/
theorem sum_srcConvReg2_le (S : SourceNormData d) (hd : 1 ≤ d) {a b ah bh : ℝ} (ha : 0 < a)
    (hb : 0 < b) (hab : a + b < (d : ℝ)) (hah : 0 ≤ ah) (hbh : 0 ≤ bh) (x : Fin d → ℤ)
    (F : Finset (Fin d → ℤ)) (hF : ∀ y ∈ F, srcConvReg2 S x y) :
    ∑ y ∈ F, srcConvMajorant S a b ah bh x y ≤
      srcConvReg2Const (d := d) S a b ah bh * srcConvTarget S a b ah bh x := by
  classical
  have hA : (0 : ℝ) ≤ S.ρ (toVec x) := src_nonneg S _
  have had : a < (d : ℝ) := by linarith
  have hbd : b < (d : ℝ) := by linarith
  have he : (0 : ℝ) ≤ (d : ℝ) - a := by linarith
  set C : ℝ := (2 : ℝ) ^ (((d : ℝ) - a) + ah) *
    ((1 + S.ρ (toVec x)) ^ (-((d : ℝ) - a)) * LamR (S.ρ (toVec x)) ^ (-ah)) with hCdef
  have hCnn : 0 ≤ C := by
    rw [hCdef]
    have h1 : (0 : ℝ) ≤ (2 : ℝ) ^ (((d : ℝ) - a) + ah) := Real.rpow_nonneg (by norm_num) _
    have h2 : (0 : ℝ) ≤ (1 + S.ρ (toVec x)) ^ (-((d : ℝ) - a)) :=
      Real.rpow_nonneg (by linarith) _
    have h3 : (0 : ℝ) ≤ LamR (S.ρ (toVec x)) ^ (-ah) :=
      Real.rpow_nonneg (LamR_nonneg hA) _
    exact mul_nonneg h1 (mul_nonneg h2 h3)
  have hterm : ∀ y ∈ F,
      srcConvMajorant S a b ah bh x y ≤ C * Wt ((d : ℝ) - b) bh (S.ρ (toVec (x - y))) := by
    intro y hy
    have hreg : S.ρ (toVec (x - y)) ≤ S.ρ (toVec x) / 2 :=
      (srcConvReg2_iff S x y).mp (hF y hy)
    have hv : S.ρ (toVec x) / 2 ≤ S.ρ (toVec y) := srcNorm_halve_le_of_sub_le S hreg
    have hfreeze : Wt ((d : ℝ) - a) ah (S.ρ (toVec y)) ≤ C := by
      rw [hCdef]
      exact Wt_freeze_halve he hah hA hv
    have h1 : (0 : ℝ) ≤ Wt ((d : ℝ) - b) bh (S.ρ (toVec (x - y))) :=
      Wt_nonneg (src_nonneg S _)
    calc srcConvMajorant S a b ah bh x y
        = Wt ((d : ℝ) - a) ah (S.ρ (toVec y)) *
            Wt ((d : ℝ) - b) bh (S.ρ (toVec (x - y))) :=
          srcConvMajorant_eq S a b ah bh x y
      _ ≤ C * Wt ((d : ℝ) - b) bh (S.ρ (toVec (x - y))) :=
          mul_le_mul_of_nonneg_right hfreeze h1
  have hinj : Set.InjOn (fun y : Fin d → ℤ => (x - y : Fin d → ℤ)) ↑F := by
    intro u _ v _ huv
    have huv' : x - u = x - v := huv
    have h : x - (x - u) = x - (x - v) := by rw [huv']
    simpa using h
  have hbs : ∑ y ∈ F, Wt ((d : ℝ) - b) bh (S.ρ (toVec (x - y))) ≤
      srcBallShellConst (d := d) S b bh *
        ((2 : ℝ) ^ bh * ((1 + S.ρ (toVec x)) ^ b * LamR (S.ρ (toVec x)) ^ (-bh))) := by
    rw [← Finset.sum_image (f := fun z => Wt ((d : ℝ) - b) bh (S.ρ (toVec z))) hinj]
    refine srcBallShell_sum_le S hd hb hbd hbh hA ?_
    intro z hz
    obtain ⟨y, hyF, rfl⟩ := Finset.mem_image.mp hz
    exact (srcConvReg2_iff S x y).mp (hF y hyF)
  calc ∑ y ∈ F, srcConvMajorant S a b ah bh x y
      ≤ ∑ y ∈ F, C * Wt ((d : ℝ) - b) bh (S.ρ (toVec (x - y))) := Finset.sum_le_sum hterm
    _ = C * ∑ y ∈ F, Wt ((d : ℝ) - b) bh (S.ρ (toVec (x - y))) := by rw [Finset.mul_sum]
    _ ≤ C * (srcBallShellConst (d := d) S b bh *
          ((2 : ℝ) ^ bh * ((1 + S.ρ (toVec x)) ^ b * LamR (S.ρ (toVec x)) ^ (-bh)))) :=
        mul_le_mul_of_nonneg_left hbs hCnn
    _ = srcConvReg2Const (d := d) S a b ah bh * srcConvTarget S a b ah bh x := by
        rw [hCdef, srcConvReg2Const, srcConvTarget_eq]
        exact reg2_arith (d := d) hA

/-! ## §5 The `A3` region: pure power tails beyond the half radius -/

/-- **The `A3` far half, `S.ρ y ≤ S.ρ (x-y)`.**  The second factor is dominated by the first
and the remaining pure power tail is the transferred `A3` estimate. -/
theorem sum_srcConvReg3a_le (S : SourceNormData d) (hd : 1 ≤ d) {a b ah bh : ℝ} (ha : 0 < a)
    (_hb : 0 < b) (hab : a + b < (d : ℝ)) (hah : 0 ≤ ah) (hbh : 0 ≤ bh) (x : Fin d → ℤ)
    (F : Finset (Fin d → ℤ)) (hF1 : ∀ y ∈ F, ¬ srcConvReg1 S x y)
    (hle : ∀ y ∈ F, S.ρ (toVec y) ≤ S.ρ (toVec (x - y))) :
    ∑ y ∈ F, srcConvMajorant S a b ah bh x y ≤
      srcConvReg3aConst (d := d) S a b ah bh * srcConvTarget S a b ah bh x := by
  classical
  have hA : (0 : ℝ) ≤ S.ρ (toVec x) := src_nonneg S _
  have hLam : (0 : ℝ) < LamR (S.ρ (toVec x)) := LamR_pos hA
  have hbd : b < (d : ℝ) := by linarith
  set γ : ℝ := (d : ℝ) - a - b with hγdef
  have hγ : 0 < γ := by rw [hγdef]; linarith
  have hdexp : (d : ℝ) + γ = 2 * (d : ℝ) - a - b := by rw [hγdef]; ring
  have htail : ∀ y ∈ F, S.ρ (toVec x) / 2 < S.ρ (toVec y) := by
    intro y hy
    exact not_le.mp ((srcConvReg1_iff S x y).not.mp (hF1 y hy))
  have hterm : ∀ y ∈ F, srcConvMajorant S a b ah bh x y ≤
      ((2 : ℝ) ^ ah * LamR (S.ρ (toVec x)) ^ (-ah)) *
        ((2 : ℝ) ^ bh * LamR (S.ρ (toVec x)) ^ (-bh)) *
          Wt ((d : ℝ) + γ) 0 (S.ρ (toVec y)) := by
    intro y hy
    have hAy : S.ρ (toVec x) / 2 ≤ S.ρ (toVec y) := le_of_lt (htail y hy)
    have hAv : S.ρ (toVec x) / 2 ≤ S.ρ (toVec (x - y)) := le_trans hAy (hle y hy)
    have hl1 := LamR_rpow_freeze hah hA hAy
    have hl2 := LamR_rpow_freeze hbh hA hAv
    have hp : (1 + S.ρ (toVec (x - y))) ^ (-((d : ℝ) - b)) ≤
        (1 + S.ρ (toVec y)) ^ (-((d : ℝ) - b)) :=
      Real.rpow_le_rpow_of_nonpos (show (0 : ℝ) < 1 + S.ρ (toVec y) by linarith)
        (show (1 + S.ρ (toVec y)) ≤ 1 + S.ρ (toVec (x - y)) by linarith [hle y hy])
        (show -((d : ℝ) - b) ≤ 0 by linarith)
    have hpow : (1 + S.ρ (toVec y)) ^ (-((d : ℝ) - a)) *
        (1 + S.ρ (toVec y)) ^ (-((d : ℝ) - b)) =
        (1 + S.ρ (toVec y)) ^ (-((d : ℝ) + γ)) := by
      rw [← Real.rpow_add (show (0 : ℝ) < 1 + S.ρ (toVec y) by linarith)]
      congr 1
      rw [hdexp]
      ring
    have hstep1 : (1 + S.ρ (toVec y)) ^ (-((d : ℝ) - a)) *
          LamR (S.ρ (toVec y)) ^ (-ah) ≤
        (1 + S.ρ (toVec y)) ^ (-((d : ℝ) - a)) *
          ((2 : ℝ) ^ ah * LamR (S.ρ (toVec x)) ^ (-ah)) :=
      mul_le_mul_of_nonneg_left hl1 (Real.rpow_nonneg (by linarith) _)
    have hstep2 : (1 + S.ρ (toVec (x - y))) ^ (-((d : ℝ) - b)) *
          LamR (S.ρ (toVec (x - y))) ^ (-bh) ≤
        (1 + S.ρ (toVec y)) ^ (-((d : ℝ) - b)) *
          ((2 : ℝ) ^ bh * LamR (S.ρ (toVec x)) ^ (-bh)) := by
      refine (mul_le_mul_of_nonneg_right hp
        (Real.rpow_nonneg (LamR_nonneg (src_nonneg S _)) _)).trans ?_
      exact mul_le_mul_of_nonneg_left hl2 (Real.rpow_nonneg (by linarith) _)
    have h1nn : (0 : ℝ) ≤ (1 + S.ρ (toVec y)) ^ (-((d : ℝ) - a)) *
        ((2 : ℝ) ^ ah * LamR (S.ρ (toVec x)) ^ (-ah)) :=
      mul_nonneg (Real.rpow_nonneg (by linarith) _)
        (mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.rpow_nonneg hLam.le _))
    calc srcConvMajorant S a b ah bh x y
        = ((1 + S.ρ (toVec y)) ^ (-((d : ℝ) - a)) * LamR (S.ρ (toVec y)) ^ (-ah)) *
            ((1 + S.ρ (toVec (x - y))) ^ (-((d : ℝ) - b)) *
              LamR (S.ρ (toVec (x - y))) ^ (-bh)) := by
          rw [srcConvMajorant_eq, Wt, Wt]
      _ ≤ ((1 + S.ρ (toVec y)) ^ (-((d : ℝ) - a)) *
            ((2 : ℝ) ^ ah * LamR (S.ρ (toVec x)) ^ (-ah))) *
            ((1 + S.ρ (toVec y)) ^ (-((d : ℝ) - b)) *
              ((2 : ℝ) ^ bh * LamR (S.ρ (toVec x)) ^ (-bh))) :=
          mul_le_mul hstep1 hstep2
            (mul_nonneg (Real.rpow_nonneg (by linarith) _)
              (Real.rpow_nonneg (LamR_nonneg (src_nonneg S _)) _)) h1nn
      _ = ((2 : ℝ) ^ ah * LamR (S.ρ (toVec x)) ^ (-ah)) *
            ((2 : ℝ) ^ bh * LamR (S.ρ (toVec x)) ^ (-bh)) *
            ((1 + S.ρ (toVec y)) ^ (-((d : ℝ) - a)) *
              (1 + S.ρ (toVec y)) ^ (-((d : ℝ) - b))) := by ring
      _ = ((2 : ℝ) ^ ah * LamR (S.ρ (toVec x)) ^ (-ah)) *
            ((2 : ℝ) ^ bh * LamR (S.ρ (toVec x)) ^ (-bh)) *
            Wt ((d : ℝ) + γ) 0 (S.ρ (toVec y)) := by
          rw [Wt_zero_log, ← hpow]
  have hKnn : (0 : ℝ) ≤ (2 : ℝ) ^ ah * LamR (S.ρ (toVec x)) ^ (-ah) *
      ((2 : ℝ) ^ bh * LamR (S.ρ (toVec x)) ^ (-bh)) :=
    mul_nonneg
      (mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.rpow_nonneg hLam.le _))
      (mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.rpow_nonneg hLam.le _))
  calc ∑ y ∈ F, srcConvMajorant S a b ah bh x y
      ≤ ∑ y ∈ F, ((2 : ℝ) ^ ah * LamR (S.ρ (toVec x)) ^ (-ah)) *
          ((2 : ℝ) ^ bh * LamR (S.ρ (toVec x)) ^ (-bh)) *
            Wt ((d : ℝ) + γ) 0 (S.ρ (toVec y)) := Finset.sum_le_sum hterm
    _ = ((2 : ℝ) ^ ah * LamR (S.ρ (toVec x)) ^ (-ah)) *
          ((2 : ℝ) ^ bh * LamR (S.ρ (toVec x)) ^ (-bh)) *
          ∑ y ∈ F, Wt ((d : ℝ) + γ) 0 (S.ρ (toVec y)) := by rw [Finset.mul_sum]
    _ ≤ ((2 : ℝ) ^ ah * LamR (S.ρ (toVec x)) ^ (-ah)) *
          ((2 : ℝ) ^ bh * LamR (S.ρ (toVec x)) ^ (-bh)) *
          ((2 : ℝ) ^ γ * srcPowTailConst (d := d) S γ * Wt γ 0 (S.ρ (toVec x))) :=
        mul_le_mul_of_nonneg_left (srcPowTail_sum_le S hd hγ hA F htail) hKnn
    _ = srcConvReg3aConst (d := d) S a b ah bh * srcConvTarget S a b ah bh x := by
        rw [srcConvReg3aConst, srcConvTarget_eq, Wt_zero_log]
        exact reg3_arith (d := d) hA

/-- **The `A3` far half, `S.ρ (x-y) < S.ρ y`.**  Now the first factor is dominated by the
second, and the centred transferred `A3` tail estimate closes the bound. -/
theorem sum_srcConvReg3b_le (S : SourceNormData d) (hd : 1 ≤ d) {a b ah bh : ℝ} (_ha : 0 < a)
    (hb : 0 < b) (hab : a + b < (d : ℝ)) (hah : 0 ≤ ah) (hbh : 0 ≤ bh) (x : Fin d → ℤ)
    (F : Finset (Fin d → ℤ)) (hF1 : ∀ y ∈ F, ¬ srcConvReg1 S x y)
    (hF2 : ∀ y ∈ F, ¬ srcConvReg2 S x y)
    (hlt : ∀ y ∈ F, ¬ S.ρ (toVec y) ≤ S.ρ (toVec (x - y))) :
    ∑ y ∈ F, srcConvMajorant S a b ah bh x y ≤
      srcConvReg3aConst (d := d) S a b ah bh * srcConvTarget S a b ah bh x := by
  classical
  have hA : (0 : ℝ) ≤ S.ρ (toVec x) := src_nonneg S _
  have hLam : (0 : ℝ) < LamR (S.ρ (toVec x)) := LamR_pos hA
  have had : a < (d : ℝ) := by linarith
  set γ : ℝ := (d : ℝ) - a - b with hγdef
  have hγ : 0 < γ := by rw [hγdef]; linarith
  have hdexp : (d : ℝ) + γ = 2 * (d : ℝ) - a - b := by rw [hγdef]; ring
  have htail : ∀ y ∈ F, S.ρ (toVec x) / 2 < S.ρ (toVec (x - y)) := by
    intro y hy
    exact not_le.mp ((srcConvReg2_iff S x y).not.mp (hF2 y hy))
  have hterm : ∀ y ∈ F, srcConvMajorant S a b ah bh x y ≤
      ((2 : ℝ) ^ ah * LamR (S.ρ (toVec x)) ^ (-ah)) *
        ((2 : ℝ) ^ bh * LamR (S.ρ (toVec x)) ^ (-bh)) *
          Wt ((d : ℝ) + γ) 0 (S.ρ (toVec (x - y))) := by
    intro y hy
    have hAv : S.ρ (toVec x) / 2 ≤ S.ρ (toVec (x - y)) := le_of_lt (htail y hy)
    have hAy : S.ρ (toVec x) / 2 ≤ S.ρ (toVec y) :=
      le_of_lt (not_le.mp ((srcConvReg1_iff S x y).not.mp (hF1 y hy)))
    have hl1 := LamR_rpow_freeze hah hA hAy
    have hl2 := LamR_rpow_freeze hbh hA hAv
    have hp : (1 + S.ρ (toVec y)) ^ (-((d : ℝ) - a)) ≤
        (1 + S.ρ (toVec (x - y))) ^ (-((d : ℝ) - a)) :=
      Real.rpow_le_rpow_of_nonpos (show (0 : ℝ) < 1 + S.ρ (toVec (x - y)) by linarith)
        (show (1 + S.ρ (toVec (x - y))) ≤ 1 + S.ρ (toVec y) by linarith [not_le.mp (hlt y hy)])
        (show -((d : ℝ) - a) ≤ 0 by linarith)
    have hpow : (1 + S.ρ (toVec (x - y))) ^ (-((d : ℝ) - a)) *
        (1 + S.ρ (toVec (x - y))) ^ (-((d : ℝ) - b)) =
        (1 + S.ρ (toVec (x - y))) ^ (-((d : ℝ) + γ)) := by
      rw [← Real.rpow_add (show (0 : ℝ) < 1 + S.ρ (toVec (x - y)) by linarith)]
      congr 1
      rw [hdexp]
      ring
    have hstep1 : (1 + S.ρ (toVec y)) ^ (-((d : ℝ) - a)) * LamR (S.ρ (toVec y)) ^ (-ah) ≤
        (1 + S.ρ (toVec (x - y))) ^ (-((d : ℝ) - a)) *
          ((2 : ℝ) ^ ah * LamR (S.ρ (toVec x)) ^ (-ah)) := by
      refine (mul_le_mul_of_nonneg_right hp
        (Real.rpow_nonneg (LamR_nonneg (src_nonneg S _)) _)).trans ?_
      exact mul_le_mul_of_nonneg_left hl1 (Real.rpow_nonneg (by linarith) _)
    have hstep2 : (1 + S.ρ (toVec (x - y))) ^ (-((d : ℝ) - b)) *
          LamR (S.ρ (toVec (x - y))) ^ (-bh) ≤
        (1 + S.ρ (toVec (x - y))) ^ (-((d : ℝ) - b)) *
          ((2 : ℝ) ^ bh * LamR (S.ρ (toVec x)) ^ (-bh)) :=
      mul_le_mul_of_nonneg_left hl2 (Real.rpow_nonneg (by linarith) _)
    have h1nn : (0 : ℝ) ≤ (1 + S.ρ (toVec (x - y))) ^ (-((d : ℝ) - a)) *
        ((2 : ℝ) ^ ah * LamR (S.ρ (toVec x)) ^ (-ah)) :=
      mul_nonneg (Real.rpow_nonneg (by linarith) _)
        (mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.rpow_nonneg hLam.le _))
    calc srcConvMajorant S a b ah bh x y
        = ((1 + S.ρ (toVec y)) ^ (-((d : ℝ) - a)) * LamR (S.ρ (toVec y)) ^ (-ah)) *
            ((1 + S.ρ (toVec (x - y))) ^ (-((d : ℝ) - b)) *
              LamR (S.ρ (toVec (x - y))) ^ (-bh)) := by
          rw [srcConvMajorant_eq, Wt, Wt]
      _ ≤ ((1 + S.ρ (toVec (x - y))) ^ (-((d : ℝ) - a)) *
            ((2 : ℝ) ^ ah * LamR (S.ρ (toVec x)) ^ (-ah))) *
            ((1 + S.ρ (toVec (x - y))) ^ (-((d : ℝ) - b)) *
              ((2 : ℝ) ^ bh * LamR (S.ρ (toVec x)) ^ (-bh))) :=
          mul_le_mul hstep1 hstep2
            (mul_nonneg (Real.rpow_nonneg (by linarith) _)
              (Real.rpow_nonneg (LamR_nonneg (src_nonneg S _)) _)) h1nn
      _ = ((2 : ℝ) ^ ah * LamR (S.ρ (toVec x)) ^ (-ah)) *
            ((2 : ℝ) ^ bh * LamR (S.ρ (toVec x)) ^ (-bh)) *
            ((1 + S.ρ (toVec (x - y))) ^ (-((d : ℝ) - a)) *
              (1 + S.ρ (toVec (x - y))) ^ (-((d : ℝ) - b))) := by ring
      _ = ((2 : ℝ) ^ ah * LamR (S.ρ (toVec x)) ^ (-ah)) *
            ((2 : ℝ) ^ bh * LamR (S.ρ (toVec x)) ^ (-bh)) *
            Wt ((d : ℝ) + γ) 0 (S.ρ (toVec (x - y))) := by
          rw [Wt_zero_log, ← hpow]
  have hKnn : (0 : ℝ) ≤ (2 : ℝ) ^ ah * LamR (S.ρ (toVec x)) ^ (-ah) *
      ((2 : ℝ) ^ bh * LamR (S.ρ (toVec x)) ^ (-bh)) :=
    mul_nonneg
      (mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.rpow_nonneg hLam.le _))
      (mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.rpow_nonneg hLam.le _))
  calc ∑ y ∈ F, srcConvMajorant S a b ah bh x y
      ≤ ∑ y ∈ F, ((2 : ℝ) ^ ah * LamR (S.ρ (toVec x)) ^ (-ah)) *
          ((2 : ℝ) ^ bh * LamR (S.ρ (toVec x)) ^ (-bh)) *
            Wt ((d : ℝ) + γ) 0 (S.ρ (toVec (x - y))) := Finset.sum_le_sum hterm
    _ = ((2 : ℝ) ^ ah * LamR (S.ρ (toVec x)) ^ (-ah)) *
          ((2 : ℝ) ^ bh * LamR (S.ρ (toVec x)) ^ (-bh)) *
          ∑ y ∈ F, Wt ((d : ℝ) + γ) 0 (S.ρ (toVec (x - y))) := by rw [Finset.mul_sum]
    _ ≤ ((2 : ℝ) ^ ah * LamR (S.ρ (toVec x)) ^ (-ah)) *
          ((2 : ℝ) ^ bh * LamR (S.ρ (toVec x)) ^ (-bh)) *
          ((2 : ℝ) ^ γ * srcPowTailConst (d := d) S γ * Wt γ 0 (S.ρ (toVec x))) :=
        mul_le_mul_of_nonneg_left (srcPowTail_sum_le_sub S hd hγ hA x F htail) hKnn
    _ = srcConvReg3aConst (d := d) S a b ah bh * srcConvTarget S a b ah bh x := by
        rw [srcConvReg3aConst, srcConvTarget_eq, Wt_zero_log]
        exact reg3_arith (d := d) hA

/-- **The `A3` region.**  Splitting on `S.ρ y ≤ S.ρ (x-y)` and applying the two far halves. -/
theorem sum_srcConvReg3_le (S : SourceNormData d) (hd : 1 ≤ d) {a b ah bh : ℝ} (ha : 0 < a)
    (hb : 0 < b) (hab : a + b < (d : ℝ)) (hah : 0 ≤ ah) (hbh : 0 ≤ bh) (x : Fin d → ℤ)
    (F : Finset (Fin d → ℤ)) (hF1 : ∀ y ∈ F, ¬ srcConvReg1 S x y)
    (hF2 : ∀ y ∈ F, ¬ srcConvReg2 S x y) :
    ∑ y ∈ F, srcConvMajorant S a b ah bh x y ≤
      srcConvReg3Const (d := d) S a b ah bh * srcConvTarget S a b ah bh x := by
  classical
  have hsplit := Finset.sum_filter_add_sum_filter_not F
    (fun y => S.ρ (toVec y) ≤ S.ρ (toVec (x - y))) (fun y => srcConvMajorant S a b ah bh x y)
  rw [← hsplit]
  have h1 := sum_srcConvReg3a_le S hd ha hb hab hah hbh x
    (F.filter (fun y => S.ρ (toVec y) ≤ S.ρ (toVec (x - y))))
    (fun y hy => hF1 y (Finset.mem_filter.mp hy).1)
    (fun y hy => (Finset.mem_filter.mp hy).2)
  have h2 := sum_srcConvReg3b_le S hd ha hb hab hah hbh x
    (F.filter (fun y => ¬ S.ρ (toVec y) ≤ S.ρ (toVec (x - y))))
    (fun y hy => hF1 y (Finset.mem_filter.mp hy).1)
    (fun y hy => hF2 y (Finset.mem_filter.mp hy).1)
    (fun y hy => (Finset.mem_filter.mp hy).2)
  calc ∑ y ∈ F.filter (fun y => S.ρ (toVec y) ≤ S.ρ (toVec (x - y))),
          srcConvMajorant S a b ah bh x y +
        ∑ y ∈ F.filter (fun y => ¬ S.ρ (toVec y) ≤ S.ρ (toVec (x - y))),
          srcConvMajorant S a b ah bh x y
      ≤ srcConvReg3aConst (d := d) S a b ah bh * srcConvTarget S a b ah bh x +
        srcConvReg3aConst (d := d) S a b ah bh * srcConvTarget S a b ah bh x :=
        add_le_add h1 h2
    _ = srcConvReg3Const (d := d) S a b ah bh * srcConvTarget S a b ah bh x := by
        rw [srcConvReg3Const]
        ring

end SrcNormConv
