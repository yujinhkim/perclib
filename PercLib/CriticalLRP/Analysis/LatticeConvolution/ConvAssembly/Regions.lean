module

public import PercLib.CriticalLRP.Analysis.LatticeConvolution.ConvAssembly.Profiles

/-!
# Generic convolution assembly (`a + b < d`): the `A1`/`A2`/`A3` region bounds
-/

set_option autoImplicit false

@[expose] public section

namespace CriticalLRPConv

open PercLib.CriticalLRP.FiniteVolume (linfNorm)

/-! ## §5 Reverse triangle inequality and the ball-shell bound centred at `x` -/

/-- Inside the half-ball around the origin, the distance to `x` is at least `‖x‖/2`. -/
lemma norm_half_le_norm_sub {d : ℕ} {x y : Fin d → ℤ} (hy : ‖y‖ ≤ ‖x‖ / 2) :
    ‖x‖ / 2 ≤ ‖(x - y : Fin d → ℤ)‖ := by
  have htri : ‖x‖ ≤ ‖y‖ + ‖(x - y : Fin d → ℤ)‖ := by
    have h : x = y + (x - y) := by abel
    calc ‖x‖ = ‖y + (x - y)‖ := by rw [← h]
      _ ≤ ‖y‖ + ‖(x - y : Fin d → ℤ)‖ := norm_add_le _ _
  linarith

/-- **The weighted ball shell bound centred at `x`.**  The `A2` counterpart of
`ball_shell_bound_latticeInt`: the same estimate for the weight `Wt (d-a) c ‖x - y‖`
over a set contained in the half-ball of radius `S` around `x`. -/
theorem ball_shell_bound_centred {d : ℕ} {a c S : ℝ} (ha : 0 < a) (haD : a < (d : ℝ))
    (hc : 0 ≤ c) (hS : 0 ≤ S) {x : Fin d → ℤ} {F : Finset (Fin d → ℤ)}
    (hrad : ∀ y ∈ F, ‖(x - y : Fin d → ℤ)‖ ≤ S) :
    ∑ y ∈ F, Wt ((d : ℝ) - a) c ‖(x - y : Fin d → ℤ)‖ ≤
      ballShellConst d a c * ((1 + S) ^ a * LamR S ^ (-c)) := by
  classical
  have hinj : Set.InjOn (fun y : Fin d → ℤ => (x - y : Fin d → ℤ)) ↑F := by
    intro u _ v _ huv
    have huv' : x - u = x - v := huv
    have h : x - (x - u) = x - (x - v) := by rw [huv']
    simpa using h
  rw [← Finset.sum_image (f := fun z => Wt ((d : ℝ) - a) c ‖z‖) hinj]
  refine ball_shell_bound_latticeInt d ha haD hc hS ?_
  intro z hz
  obtain ⟨y, hyF, rfl⟩ := Finset.mem_image.mp hz
  exact hrad y hyF

/-- **The weighted tail shell bound in terms of the real sup norm.** -/
theorem sum_Wt_tail_le_norm {d : ℕ} (hd : 1 ≤ d) {γ c S : ℝ} (hγ : 0 < γ) (hc : 0 ≤ c)
    (hS : 0 ≤ S) (F : Finset (Fin d → ℤ)) (hF : ∀ y ∈ F, S < ‖y‖) :
    ∑ y ∈ F, Wt ((d : ℝ) + γ) c ‖y‖ ≤ tailShellConst d γ * Wt γ c S := by
  have h : ∀ y : Fin d → ℤ, Wt ((d : ℝ) + γ) c ‖y‖ = Wt ((d : ℝ) + γ) c (linfNorm y : ℝ) :=
    fun y => by rw [coe_norm_eq_linfNorm]
  simp only [h]
  refine sum_Wt_tail_le hd hγ hc hS F ?_
  intro y hy
  rw [← coe_norm_eq_linfNorm]
  exact hF y hy

/-! ## §6 Nonnegativity of the explicit constants -/

lemma ballShellConst_nonneg {d : ℕ} {a c : ℝ} (_ha : 0 ≤ a) (had : a ≤ (d : ℝ)) (hc : 0 ≤ c) :
    0 ≤ ballShellConst d a c := by
  have h1 : (0 : ℝ) ≤ (2 : ℝ) ^ a := Real.rpow_nonneg (by norm_num) _
  have h2 : (0 : ℝ) ≤ (2 : ℝ) ^ (d : ℝ) := Real.rpow_nonneg (by norm_num) _
  have h3 : (0 : ℝ) ≤ (d : ℝ) - a + 2 * (c + 1) := by linarith
  have h4 : 0 < coreConst a c := coreConst_pos a c
  have h5 : (0 : ℝ) ≤ 1 + ((d : ℝ) - a + 2 * (c + 1)) * coreConst a c := by
    have := mul_nonneg h3 h4.le; linarith
  unfold ballShellConst
  exact mul_nonneg h1 (mul_nonneg h2 h5)

/-! ## §7 The `A1` region bound -/

/-- **The `A1` region.**  On `‖y‖ ≤ ‖x‖/2` the second factor is frozen at `‖x‖/2` and the
first is summed by the ball shell estimate. -/
lemma sum_convReg1_le {d : ℕ} {a b ah bh : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hab : a + b < (d : ℝ)) (hah : 0 ≤ ah) (hbh : 0 ≤ bh) (x : Fin d → ℤ)
    (F : Finset (Fin d → ℤ)) (hF : ∀ y ∈ F, convReg1 x y) :
    ∑ y ∈ F, convMajorant a b ah bh x y ≤
      convReg1Const d a b ah bh * convTargetR d a b ah bh ‖x‖ := by
  classical
  have hA : (0 : ℝ) ≤ ‖x‖ := norm_nonneg x
  have hhalf : (0 : ℝ) ≤ ‖x‖ / 2 := by linarith
  have had : a < (d : ℝ) := by linarith
  have hbd : b < (d : ℝ) := by linarith
  set C : ℝ :=
    (2 : ℝ) ^ (((d : ℝ) - b) + bh) * ((1 + ‖x‖) ^ (-((d : ℝ) - b)) * LamR ‖x‖ ^ (-bh))
    with hCdef
  have hCnn : (0 : ℝ) ≤ C := by
    rw [hCdef]
    have h1 : (0 : ℝ) ≤ (2 : ℝ) ^ (((d : ℝ) - b) + bh) := Real.rpow_nonneg (by norm_num) _
    have h2 : (0 : ℝ) ≤ (1 + ‖x‖) ^ (-((d : ℝ) - b)) := Real.rpow_nonneg (by linarith) _
    have h3 : (0 : ℝ) ≤ LamR ‖x‖ ^ (-bh) := Real.rpow_nonneg (LamR_nonneg hA) _
    have := mul_nonneg h2 h3
    exact mul_nonneg h1 this
  have hBnn : (0 : ℝ) ≤ ballShellConst d a ah := ballShellConst_nonneg ha.le had.le hah
  have hterm : ∀ y ∈ F, convMajorant a b ah bh x y ≤ C * Wt ((d : ℝ) - a) ah ‖y‖ := by
    intro y hy
    have hv : ‖x‖ / 2 ≤ ‖(x - y : Fin d → ℤ)‖ := norm_half_le_norm_sub (hF y hy)
    have hfreeze := Wt_freeze_halve (e := (d : ℝ) - b) (c := bh) (A := ‖x‖)
      (v := ‖(x - y : Fin d → ℤ)‖) (by linarith) hbh hA hv
    have h1 : (0 : ℝ) ≤ Wt ((d : ℝ) - a) ah ‖y‖ := Wt_nonneg (norm_nonneg y)
    calc convMajorant a b ah bh x y
        = Wt ((d : ℝ) - a) ah ‖y‖ * Wt ((d : ℝ) - b) bh ‖(x - y : Fin d → ℤ)‖ := rfl
      _ ≤ Wt ((d : ℝ) - a) ah ‖y‖ * C := mul_le_mul_of_nonneg_left hfreeze h1
      _ = C * Wt ((d : ℝ) - a) ah ‖y‖ := by ring
  have hbase : (0 : ℝ) < 1 + ‖x‖ := by linarith
  have hLam : (0 : ℝ) < LamR ‖x‖ := LamR_pos hA
  have e1 : (1 + ‖x‖) ^ (-((d : ℝ) - b)) * (1 + ‖x‖) ^ a =
      (1 + ‖x‖) ^ (-((d : ℝ) - a - b)) := by
    rw [← Real.rpow_add hbase]
    congr 1
    ring
  have e2 : LamR ‖x‖ ^ (-bh) * LamR ‖x‖ ^ (-ah) = LamR ‖x‖ ^ (-(ah + bh)) := by
    rw [← Real.rpow_add hLam]
    congr 1
    ring
  calc ∑ y ∈ F, convMajorant a b ah bh x y
      ≤ ∑ y ∈ F, C * Wt ((d : ℝ) - a) ah ‖y‖ := Finset.sum_le_sum hterm
    _ = C * ∑ y ∈ F, Wt ((d : ℝ) - a) ah ‖y‖ := by rw [Finset.mul_sum]
    _ ≤ C * (ballShellConst d a ah * ((1 + ‖x‖ / 2) ^ a * LamR (‖x‖ / 2) ^ (-ah))) := by
        refine mul_le_mul_of_nonneg_left ?_ hCnn
        exact ball_shell_bound_latticeInt d ha had hah hhalf (fun y hy => hF y hy)
    _ ≤ C * (ballShellConst d a ah * ((2 : ℝ) ^ ah * ((1 + ‖x‖) ^ a * LamR ‖x‖ ^ (-ah)))) := by
        refine mul_le_mul_of_nonneg_left ?_ hCnn
        exact mul_le_mul_of_nonneg_left (ball_profile_halve ha.le hah hA) hBnn
    _ = convReg1Const d a b ah bh * convTargetR d a b ah bh ‖x‖ := by
        rw [hCdef, convReg1Const, convTargetR, Wt]
        calc (2 : ℝ) ^ (((d : ℝ) - b) + bh) *
              ((1 + ‖x‖) ^ (-((d : ℝ) - b)) * LamR ‖x‖ ^ (-bh)) *
              (ballShellConst d a ah *
                ((2 : ℝ) ^ ah * ((1 + ‖x‖) ^ a * LamR ‖x‖ ^ (-ah))))
            = ((2 : ℝ) ^ (((d : ℝ) - b) + bh) * (2 : ℝ) ^ ah) *
                (((1 + ‖x‖) ^ (-((d : ℝ) - b)) * (1 + ‖x‖) ^ a) *
                  (LamR ‖x‖ ^ (-bh) * LamR ‖x‖ ^ (-ah))) * ballShellConst d a ah := by
              ring
          _ = ((2 : ℝ) ^ (((d : ℝ) - b) + bh) * (2 : ℝ) ^ ah) *
                ((1 + ‖x‖) ^ (-((d : ℝ) - a - b)) * LamR ‖x‖ ^ (-(ah + bh))) *
                ballShellConst d a ah := by rw [e1, e2]
          _ = (2 : ℝ) ^ (((d : ℝ) - b) + bh) * (2 : ℝ) ^ ah * ballShellConst d a ah *
                ((1 + ‖x‖) ^ (-((d : ℝ) - a - b)) * LamR ‖x‖ ^ (-(ah + bh))) := by
              ring

/-! ## §8 The `A2` region bound -/

/-- Reverse triangle inequality from the other side: inside the half-ball around `x`, the
point `y` is at least `‖x‖/2` away from the origin. -/
lemma norm_half_le_norm_of_sub_le {d : ℕ} {x y : Fin d → ℤ}
    (h : ‖(x - y : Fin d → ℤ)‖ ≤ ‖x‖ / 2) : ‖x‖ / 2 ≤ ‖y‖ := by
  have htri : ‖x‖ ≤ ‖(x - y : Fin d → ℤ)‖ + ‖y‖ := by
    have h' : x = (x - y) + y := by abel
    calc ‖x‖ = ‖(x - y) + y‖ := by rw [← h']
      _ ≤ ‖(x - y : Fin d → ℤ)‖ + ‖y‖ := norm_add_le _ _
  linarith

/-- **The `A2` region.**  On `‖x - y‖ ≤ ‖x‖/2` the first factor is frozen at `‖x‖/2` and the
second is summed by the centred ball shell estimate. -/
lemma sum_convReg2_le {d : ℕ} {a b ah bh : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hab : a + b < (d : ℝ)) (hah : 0 ≤ ah) (hbh : 0 ≤ bh) (x : Fin d → ℤ)
    (F : Finset (Fin d → ℤ)) (hF : ∀ y ∈ F, convReg2 x y) :
    ∑ y ∈ F, convMajorant a b ah bh x y ≤
      convReg2Const d a b ah bh * convTargetR d a b ah bh ‖x‖ := by
  classical
  have hA : (0 : ℝ) ≤ ‖x‖ := norm_nonneg x
  have hhalf : (0 : ℝ) ≤ ‖x‖ / 2 := by linarith
  have had : a < (d : ℝ) := by linarith
  have hbd : b < (d : ℝ) := by linarith
  set C : ℝ :=
    (2 : ℝ) ^ (((d : ℝ) - a) + ah) * ((1 + ‖x‖) ^ (-((d : ℝ) - a)) * LamR ‖x‖ ^ (-ah))
    with hCdef
  have hCnn : (0 : ℝ) ≤ C := by
    rw [hCdef]
    have h1 : (0 : ℝ) ≤ (2 : ℝ) ^ (((d : ℝ) - a) + ah) := Real.rpow_nonneg (by norm_num) _
    have h2 : (0 : ℝ) ≤ (1 + ‖x‖) ^ (-((d : ℝ) - a)) := Real.rpow_nonneg (by linarith) _
    have h3 : (0 : ℝ) ≤ LamR ‖x‖ ^ (-ah) := Real.rpow_nonneg (LamR_nonneg hA) _
    exact mul_nonneg h1 (mul_nonneg h2 h3)
  have hBnn : (0 : ℝ) ≤ ballShellConst d b bh := ballShellConst_nonneg hb.le hbd.le hbh
  have hterm : ∀ y ∈ F, convMajorant a b ah bh x y ≤
      C * Wt ((d : ℝ) - b) bh ‖(x - y : Fin d → ℤ)‖ := by
    intro y hy
    have hv : ‖x‖ / 2 ≤ ‖y‖ := norm_half_le_norm_of_sub_le (x := x) (y := y) (hF y hy)
    have hfreeze := Wt_freeze_halve (e := (d : ℝ) - a) (c := ah) (A := ‖x‖)
      (v := ‖y‖) (by linarith) hah hA hv
    have h1 : (0 : ℝ) ≤ Wt ((d : ℝ) - b) bh ‖(x - y : Fin d → ℤ)‖ := Wt_nonneg (norm_nonneg _)
    calc convMajorant a b ah bh x y
        = Wt ((d : ℝ) - a) ah ‖y‖ * Wt ((d : ℝ) - b) bh ‖(x - y : Fin d → ℤ)‖ := rfl
      _ ≤ C * Wt ((d : ℝ) - b) bh ‖(x - y : Fin d → ℤ)‖ :=
          mul_le_mul_of_nonneg_right hfreeze h1
  have hbase : (0 : ℝ) < 1 + ‖x‖ := by linarith
  have hLam : (0 : ℝ) < LamR ‖x‖ := LamR_pos hA
  have e1 : (1 + ‖x‖) ^ (-((d : ℝ) - a)) * (1 + ‖x‖) ^ b =
      (1 + ‖x‖) ^ (-((d : ℝ) - a - b)) := by
    rw [← Real.rpow_add hbase]
    congr 1
    ring
  have e2 : LamR ‖x‖ ^ (-ah) * LamR ‖x‖ ^ (-bh) = LamR ‖x‖ ^ (-(ah + bh)) := by
    rw [← Real.rpow_add hLam]
    congr 1
    ring
  calc ∑ y ∈ F, convMajorant a b ah bh x y
      ≤ ∑ y ∈ F, C * Wt ((d : ℝ) - b) bh ‖(x - y : Fin d → ℤ)‖ := Finset.sum_le_sum hterm
    _ = C * ∑ y ∈ F, Wt ((d : ℝ) - b) bh ‖(x - y : Fin d → ℤ)‖ := by rw [Finset.mul_sum]
    _ ≤ C * (ballShellConst d b bh *
          ((1 + ‖x‖ / 2) ^ b * LamR (‖x‖ / 2) ^ (-bh))) := by
        refine mul_le_mul_of_nonneg_left ?_ hCnn
        exact ball_shell_bound_centred hb hbd hbh hhalf (fun y hy => hF y hy)
    _ ≤ C * (ballShellConst d b bh *
          ((2 : ℝ) ^ bh * ((1 + ‖x‖) ^ b * LamR ‖x‖ ^ (-bh)))) := by
        refine mul_le_mul_of_nonneg_left ?_ hCnn
        exact mul_le_mul_of_nonneg_left (ball_profile_halve hb.le hbh hA) hBnn
    _ = convReg2Const d a b ah bh * convTargetR d a b ah bh ‖x‖ := by
        rw [hCdef, convReg2Const, convTargetR, Wt]
        calc (2 : ℝ) ^ (((d : ℝ) - a) + ah) *
              ((1 + ‖x‖) ^ (-((d : ℝ) - a)) * LamR ‖x‖ ^ (-ah)) *
              (ballShellConst d b bh *
                ((2 : ℝ) ^ bh * ((1 + ‖x‖) ^ b * LamR ‖x‖ ^ (-bh))))
            = ((2 : ℝ) ^ (((d : ℝ) - a) + ah) * (2 : ℝ) ^ bh) *
                (((1 + ‖x‖) ^ (-((d : ℝ) - a)) * (1 + ‖x‖) ^ b) *
                  (LamR ‖x‖ ^ (-ah) * LamR ‖x‖ ^ (-bh))) * ballShellConst d b bh := by
              ring
          _ = ((2 : ℝ) ^ (((d : ℝ) - a) + ah) * (2 : ℝ) ^ bh) *
                ((1 + ‖x‖) ^ (-((d : ℝ) - a - b)) * LamR ‖x‖ ^ (-(ah + bh))) *
                ballShellConst d b bh := by rw [e1, e2]
          _ = (2 : ℝ) ^ (((d : ℝ) - a) + ah) * (2 : ℝ) ^ bh * ballShellConst d b bh *
                ((1 + ‖x‖) ^ (-((d : ℝ) - a - b)) * LamR ‖x‖ ^ (-(ah + bh))) := by
              ring

/-! ## §9 The `A3` region: pure power tails beyond the half radius -/

/-- The weight with vanishing log power. -/
lemma Wt_zero_log {e A : ℝ} : Wt e 0 A = (1 + A) ^ (-e) := by
  simp [Wt]

/-- Halving the radius in the pure power profile `⟨·⟩^{-γ}`, `γ ≥ 0`. -/
lemma one_add_halve_rpow_le_neg {γ A : ℝ} (hγ : 0 ≤ γ) (hA : 0 ≤ A) :
    (1 + A / 2) ^ (-γ) ≤ (2 : ℝ) ^ γ * (1 + A) ^ (-γ) := by
  have h := one_add_halve_rpow_le (e := -γ) (by linarith) hA
  simpa using h

/-- **The pure power tail beyond `A/2`.**  The `A3` decay in the power variable only. -/
lemma sum_pow_tail_le {d : ℕ} (hd : 1 ≤ d) {γ A : ℝ} (hγ : 0 < γ) (hA : 0 ≤ A)
    (F : Finset (Fin d → ℤ)) (hF : ∀ y ∈ F, A / 2 < ‖y‖) :
    ∑ y ∈ F, Wt ((d : ℝ) + γ) 0 ‖y‖ ≤
      (2 : ℝ) ^ γ * (tailShellConst d γ * Wt γ 0 A) := by
  have hhalf : (0 : ℝ) ≤ A / 2 := by linarith
  have htail := sum_Wt_tail_le_norm hd hγ (le_refl 0) hhalf F hF
  refine htail.trans ?_
  have hWt1 : Wt γ 0 (A / 2) = (1 + A / 2) ^ (-γ) := by
    simp [Wt]
  have hWt2 : Wt γ 0 A = (1 + A) ^ (-γ) := by
    simp [Wt]
  rw [hWt1, hWt2]
  calc tailShellConst d γ * (1 + A / 2) ^ (-γ)
      ≤ tailShellConst d γ * ((2 : ℝ) ^ γ * (1 + A) ^ (-γ)) :=
        mul_le_mul_of_nonneg_left (one_add_halve_rpow_le_neg hγ.le hA)
          (tailShellConst_pos hd hγ).le
    _ = (2 : ℝ) ^ γ * (tailShellConst d γ * (1 + A) ^ (-γ)) := by ring

/-- The same pure power tail for the weight centred at `x`. -/
lemma sum_pow_tail_le_sub {d : ℕ} (hd : 1 ≤ d) {γ A : ℝ} (hγ : 0 < γ) (hA : 0 ≤ A)
    (x : Fin d → ℤ) (F : Finset (Fin d → ℤ))
    (hF : ∀ y ∈ F, A / 2 < ‖(x - y : Fin d → ℤ)‖) :
    ∑ y ∈ F, Wt ((d : ℝ) + γ) 0 ‖(x - y : Fin d → ℤ)‖ ≤
      (2 : ℝ) ^ γ * (tailShellConst d γ * Wt γ 0 A) := by
  classical
  have hinj : Set.InjOn (fun y : Fin d → ℤ => (x - y : Fin d → ℤ)) ↑F := by
    intro u _ v _ huv
    have huv' : x - u = x - v := huv
    have h : x - (x - u) = x - (x - v) := by rw [huv']
    simpa using h
  rw [← Finset.sum_image (f := fun z => Wt ((d : ℝ) + γ) 0 ‖z‖) hinj]
  refine sum_pow_tail_le hd hγ hA _ ?_
  intro z hz
  obtain ⟨y, hyF, rfl⟩ := Finset.mem_image.mp hz
  exact hF y hyF

/-- **The `A3` far half.**  On `‖y‖ ≤ ‖x - y‖` the second factor is dominated by the first,
and the remaining pure power tail is the `A3` estimate. -/
lemma sum_convReg3a_le {d : ℕ} (hd : 1 ≤ d) {a b ah bh : ℝ} (ha : 0 < a) (_hb : 0 < b)
    (hab : a + b < (d : ℝ)) (hah : 0 ≤ ah) (hbh : 0 ≤ bh) (x : Fin d → ℤ)
    (F : Finset (Fin d → ℤ)) (hF1 : ∀ y ∈ F, ¬ convReg1 x y)
    (hle : ∀ y ∈ F, ‖y‖ ≤ ‖(x - y : Fin d → ℤ)‖) :
    ∑ y ∈ F, convMajorant a b ah bh x y ≤
      ((2 : ℝ) ^ ah * (2 : ℝ) ^ bh *
        ((2 : ℝ) ^ ((d : ℝ) - a - b) * tailShellConst d ((d : ℝ) - a - b))) *
        convTargetR d a b ah bh ‖x‖ := by
  classical
  have hA : (0 : ℝ) ≤ ‖x‖ := norm_nonneg x
  have hLam : (0 : ℝ) < LamR ‖x‖ := LamR_pos hA
  have hbd : b < (d : ℝ) := by linarith
  set γ : ℝ := (d : ℝ) - a - b with hγdef
  have hγ : 0 < γ := by rw [hγdef]; linarith
  have hdexp : (d : ℝ) + γ = 2 * (d : ℝ) - a - b := by rw [hγdef]; ring
  have hKnn : (0 : ℝ) ≤ (2 : ℝ) ^ ah * (2 : ℝ) ^ bh :=
    mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.rpow_nonneg (by norm_num) _)
  have hterm : ∀ y ∈ F, convMajorant a b ah bh x y ≤
      ((2 : ℝ) ^ ah * LamR ‖x‖ ^ (-ah)) * ((2 : ℝ) ^ bh * LamR ‖x‖ ^ (-bh)) *
        Wt ((d : ℝ) + γ) 0 ‖y‖ := by
    intro y hy
    have hAy : ‖x‖ / 2 < ‖y‖ := not_le.mp (hF1 y hy)
    have hAy' : ‖x‖ / 2 ≤ ‖y‖ := le_of_lt hAy
    have hAv : ‖x‖ / 2 ≤ ‖(x - y : Fin d → ℤ)‖ := le_trans hAy' (hle y hy)
    have hl1 := LamR_rpow_freeze hah hA hAy'
    have hl2 := LamR_rpow_freeze hbh hA hAv
    have hp : (1 + ‖(x - y : Fin d → ℤ)‖) ^ (-((d : ℝ) - b)) ≤
        (1 + ‖y‖) ^ (-((d : ℝ) - b)) :=
      Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith [hle y hy]) (by linarith [hbd])
    have hpow : (1 + ‖y‖) ^ (-((d : ℝ) - a)) * (1 + ‖y‖) ^ (-((d : ℝ) - b)) =
        (1 + ‖y‖) ^ (-((d : ℝ) + γ)) := by
      rw [← Real.rpow_add (by linarith : (0 : ℝ) < 1 + ‖y‖)]
      congr 1
      rw [hdexp]
      ring
    have hstep1 : (1 + ‖y‖) ^ (-((d : ℝ) - a)) * LamR ‖y‖ ^ (-ah) ≤
        (1 + ‖y‖) ^ (-((d : ℝ) - a)) * ((2 : ℝ) ^ ah * LamR ‖x‖ ^ (-ah)) :=
      mul_le_mul_of_nonneg_left hl1 (Real.rpow_nonneg (by linarith) _)
    have hstep2 : (1 + ‖(x - y : Fin d → ℤ)‖) ^ (-((d : ℝ) - b)) *
          LamR ‖(x - y : Fin d → ℤ)‖ ^ (-bh) ≤
        (1 + ‖y‖) ^ (-((d : ℝ) - b)) * ((2 : ℝ) ^ bh * LamR ‖x‖ ^ (-bh)) := by
      refine (mul_le_mul_of_nonneg_right hp
        (Real.rpow_nonneg (LamR_nonneg (norm_nonneg _)) _)).trans ?_
      exact mul_le_mul_of_nonneg_left hl2 (Real.rpow_nonneg (by linarith) _)
    have h1nn : (0 : ℝ) ≤ (1 + ‖y‖) ^ (-((d : ℝ) - a)) * ((2 : ℝ) ^ ah * LamR ‖x‖ ^ (-ah)) :=
      mul_nonneg (Real.rpow_nonneg (by linarith) _)
        (mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.rpow_nonneg hLam.le _))
    calc convMajorant a b ah bh x y
        = ((1 + ‖y‖) ^ (-((d : ℝ) - a)) * LamR ‖y‖ ^ (-ah)) *
            ((1 + ‖(x - y : Fin d → ℤ)‖) ^ (-((d : ℝ) - b)) *
              LamR ‖(x - y : Fin d → ℤ)‖ ^ (-bh)) := rfl
      _ ≤ ((1 + ‖y‖) ^ (-((d : ℝ) - a)) * ((2 : ℝ) ^ ah * LamR ‖x‖ ^ (-ah))) *
            ((1 + ‖y‖) ^ (-((d : ℝ) - b)) * ((2 : ℝ) ^ bh * LamR ‖x‖ ^ (-bh))) :=
          mul_le_mul hstep1 hstep2
            (mul_nonneg (Real.rpow_nonneg (by linarith) _)
              (Real.rpow_nonneg (LamR_nonneg (norm_nonneg _)) _)) h1nn
      _ = ((2 : ℝ) ^ ah * LamR ‖x‖ ^ (-ah)) * ((2 : ℝ) ^ bh * LamR ‖x‖ ^ (-bh)) *
            ((1 + ‖y‖) ^ (-((d : ℝ) - a)) * (1 + ‖y‖) ^ (-((d : ℝ) - b))) := by ring
      _ = ((2 : ℝ) ^ ah * LamR ‖x‖ ^ (-ah)) * ((2 : ℝ) ^ bh * LamR ‖x‖ ^ (-bh)) *
            Wt ((d : ℝ) + γ) 0 ‖y‖ := by
          rw [Wt_zero_log, ← hpow]
  have hbase : (0 : ℝ) < 1 + ‖x‖ := by linarith
  have e2 : LamR ‖x‖ ^ (-ah) * LamR ‖x‖ ^ (-bh) = LamR ‖x‖ ^ (-(ah + bh)) := by
    rw [← Real.rpow_add hLam]
    congr 1
    ring
  calc ∑ y ∈ F, convMajorant a b ah bh x y
      ≤ ∑ y ∈ F, ((2 : ℝ) ^ ah * LamR ‖x‖ ^ (-ah)) * ((2 : ℝ) ^ bh * LamR ‖x‖ ^ (-bh)) *
          Wt ((d : ℝ) + γ) 0 ‖y‖ := Finset.sum_le_sum hterm
    _ = ((2 : ℝ) ^ ah * LamR ‖x‖ ^ (-ah)) * ((2 : ℝ) ^ bh * LamR ‖x‖ ^ (-bh)) *
          ∑ y ∈ F, Wt ((d : ℝ) + γ) 0 ‖y‖ := by rw [Finset.mul_sum]
    _ ≤ ((2 : ℝ) ^ ah * LamR ‖x‖ ^ (-ah)) * ((2 : ℝ) ^ bh * LamR ‖x‖ ^ (-bh)) *
          ((2 : ℝ) ^ γ * (tailShellConst d γ * Wt γ 0 ‖x‖)) := by
        refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (mul_nonneg
          (Real.rpow_nonneg (by norm_num) _) (Real.rpow_nonneg hLam.le _))
          (mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.rpow_nonneg hLam.le _)))
        exact sum_pow_tail_le hd hγ hA F (fun y hy => not_le.mp (hF1 y hy))
    _ = ((2 : ℝ) ^ ah * (2 : ℝ) ^ bh *
          ((2 : ℝ) ^ ((d : ℝ) - a - b) * tailShellConst d ((d : ℝ) - a - b))) *
          convTargetR d a b ah bh ‖x‖ := by
        have hWy : Wt γ 0 ‖x‖ = (1 + ‖x‖) ^ (-γ) := Wt_zero_log
        rw [hWy, convTargetR, Wt]
        calc (2 : ℝ) ^ ah * LamR ‖x‖ ^ (-ah) * ((2 : ℝ) ^ bh * LamR ‖x‖ ^ (-bh)) *
              ((2 : ℝ) ^ γ * (tailShellConst d γ * (1 + ‖x‖) ^ (-γ)))
            = (2 : ℝ) ^ ah * (2 : ℝ) ^ bh * ((2 : ℝ) ^ γ * tailShellConst d γ) *
                ((1 + ‖x‖) ^ (-γ) * (LamR ‖x‖ ^ (-ah) * LamR ‖x‖ ^ (-bh))) := by ring
          _ = (2 : ℝ) ^ ah * (2 : ℝ) ^ bh * ((2 : ℝ) ^ γ * tailShellConst d γ) *
                ((1 + ‖x‖) ^ (-γ) * LamR ‖x‖ ^ (-(ah + bh))) := by rw [e2]
          _ = (2 : ℝ) ^ ah * (2 : ℝ) ^ bh *
                ((2 : ℝ) ^ ((d : ℝ) - a - b) * tailShellConst d ((d : ℝ) - a - b)) *
                ((1 + ‖x‖) ^ (-((d : ℝ) - a - b)) * LamR ‖x‖ ^ (-(ah + bh))) := by
              rw [hγdef]

/-- **The `A3` near half.**  On `‖x - y‖ < ‖y‖` the first factor is dominated by the second,
and the remaining pure power tail is the `A3` estimate. -/
lemma sum_convReg3b_le {d : ℕ} (hd : 1 ≤ d) {a b ah bh : ℝ} (_ha : 0 < a) (hb : 0 < b)
    (hab : a + b < (d : ℝ)) (hah : 0 ≤ ah) (hbh : 0 ≤ bh) (x : Fin d → ℤ)
    (F : Finset (Fin d → ℤ)) (hF1 : ∀ y ∈ F, ¬ convReg1 x y)
    (hF2 : ∀ y ∈ F, ¬ convReg2 x y)
    (hlt : ∀ y ∈ F, ¬ ‖y‖ ≤ ‖(x - y : Fin d → ℤ)‖) :
    ∑ y ∈ F, convMajorant a b ah bh x y ≤
      ((2 : ℝ) ^ ah * (2 : ℝ) ^ bh *
        ((2 : ℝ) ^ ((d : ℝ) - a - b) * tailShellConst d ((d : ℝ) - a - b))) *
        convTargetR d a b ah bh ‖x‖ := by
  classical
  have hA : (0 : ℝ) ≤ ‖x‖ := norm_nonneg x
  have hLam : (0 : ℝ) < LamR ‖x‖ := LamR_pos hA
  have had : a < (d : ℝ) := by linarith
  set γ : ℝ := (d : ℝ) - a - b with hγdef
  have hγ : 0 < γ := by rw [hγdef]; linarith
  have hdexp : (d : ℝ) + γ = 2 * (d : ℝ) - a - b := by rw [hγdef]; ring
  have hterm : ∀ y ∈ F, convMajorant a b ah bh x y ≤
      ((2 : ℝ) ^ ah * LamR ‖x‖ ^ (-ah)) * ((2 : ℝ) ^ bh * LamR ‖x‖ ^ (-bh)) *
        Wt ((d : ℝ) + γ) 0 ‖(x - y : Fin d → ℤ)‖ := by
    intro y hy
    have hAv : ‖x‖ / 2 < ‖(x - y : Fin d → ℤ)‖ := not_le.mp (hF2 y hy)
    have hAy : ‖x‖ / 2 ≤ ‖y‖ := le_of_lt (not_le.mp (hF1 y hy))
    have hAv' : ‖x‖ / 2 ≤ ‖(x - y : Fin d → ℤ)‖ := le_of_lt hAv
    have hl1 := LamR_rpow_freeze hah hA hAy
    have hl2 := LamR_rpow_freeze hbh hA hAv'
    have hp : (1 + ‖y‖) ^ (-((d : ℝ) - a)) ≤ (1 + ‖(x - y : Fin d → ℤ)‖) ^ (-((d : ℝ) - a)) :=
      Real.rpow_le_rpow_of_nonpos (by linarith)
        (by linarith [not_le.mp (hlt y hy)]) (by linarith [had])
    have hpow : (1 + ‖(x - y : Fin d → ℤ)‖) ^ (-((d : ℝ) - a)) *
        (1 + ‖(x - y : Fin d → ℤ)‖) ^ (-((d : ℝ) - b)) =
        (1 + ‖(x - y : Fin d → ℤ)‖) ^ (-((d : ℝ) + γ)) := by
      rw [← Real.rpow_add (by linarith : (0 : ℝ) < 1 + ‖(x - y : Fin d → ℤ)‖)]
      congr 1
      rw [hdexp]
      ring
    have hstep1 : (1 + ‖y‖) ^ (-((d : ℝ) - a)) * LamR ‖y‖ ^ (-ah) ≤
        (1 + ‖(x - y : Fin d → ℤ)‖) ^ (-((d : ℝ) - a)) *
          ((2 : ℝ) ^ ah * LamR ‖x‖ ^ (-ah)) := by
      refine (mul_le_mul_of_nonneg_right hp
        (Real.rpow_nonneg (LamR_nonneg (norm_nonneg _)) _)).trans ?_
      exact mul_le_mul_of_nonneg_left hl1 (Real.rpow_nonneg (by linarith) _)
    have hstep2 : (1 + ‖(x - y : Fin d → ℤ)‖) ^ (-((d : ℝ) - b)) *
          LamR ‖(x - y : Fin d → ℤ)‖ ^ (-bh) ≤
        (1 + ‖(x - y : Fin d → ℤ)‖) ^ (-((d : ℝ) - b)) * ((2 : ℝ) ^ bh * LamR ‖x‖ ^ (-bh)) :=
      mul_le_mul_of_nonneg_left hl2 (Real.rpow_nonneg (by linarith) _)
    have h1nn : (0 : ℝ) ≤ (1 + ‖(x - y : Fin d → ℤ)‖) ^ (-((d : ℝ) - a)) *
        ((2 : ℝ) ^ ah * LamR ‖x‖ ^ (-ah)) :=
      mul_nonneg (Real.rpow_nonneg (by linarith) _)
        (mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.rpow_nonneg hLam.le _))
    calc convMajorant a b ah bh x y
        = ((1 + ‖y‖) ^ (-((d : ℝ) - a)) * LamR ‖y‖ ^ (-ah)) *
            ((1 + ‖(x - y : Fin d → ℤ)‖) ^ (-((d : ℝ) - b)) *
              LamR ‖(x - y : Fin d → ℤ)‖ ^ (-bh)) := rfl
      _ ≤ ((1 + ‖(x - y : Fin d → ℤ)‖) ^ (-((d : ℝ) - a)) *
            ((2 : ℝ) ^ ah * LamR ‖x‖ ^ (-ah))) *
            ((1 + ‖(x - y : Fin d → ℤ)‖) ^ (-((d : ℝ) - b)) *
              ((2 : ℝ) ^ bh * LamR ‖x‖ ^ (-bh))) :=
          mul_le_mul hstep1 hstep2
            (mul_nonneg (Real.rpow_nonneg (by linarith) _)
              (Real.rpow_nonneg (LamR_nonneg (norm_nonneg _)) _)) h1nn
      _ = ((2 : ℝ) ^ ah * LamR ‖x‖ ^ (-ah)) * ((2 : ℝ) ^ bh * LamR ‖x‖ ^ (-bh)) *
            ((1 + ‖(x - y : Fin d → ℤ)‖) ^ (-((d : ℝ) - a)) *
              (1 + ‖(x - y : Fin d → ℤ)‖) ^ (-((d : ℝ) - b))) := by ring
      _ = ((2 : ℝ) ^ ah * LamR ‖x‖ ^ (-ah)) * ((2 : ℝ) ^ bh * LamR ‖x‖ ^ (-bh)) *
            Wt ((d : ℝ) + γ) 0 ‖(x - y : Fin d → ℤ)‖ := by
          rw [Wt_zero_log, ← hpow]
  have e2 : LamR ‖x‖ ^ (-ah) * LamR ‖x‖ ^ (-bh) = LamR ‖x‖ ^ (-(ah + bh)) := by
    rw [← Real.rpow_add hLam]
    congr 1
    ring
  calc ∑ y ∈ F, convMajorant a b ah bh x y
      ≤ ∑ y ∈ F, ((2 : ℝ) ^ ah * LamR ‖x‖ ^ (-ah)) * ((2 : ℝ) ^ bh * LamR ‖x‖ ^ (-bh)) *
          Wt ((d : ℝ) + γ) 0 ‖(x - y : Fin d → ℤ)‖ := Finset.sum_le_sum hterm
    _ = ((2 : ℝ) ^ ah * LamR ‖x‖ ^ (-ah)) * ((2 : ℝ) ^ bh * LamR ‖x‖ ^ (-bh)) *
          ∑ y ∈ F, Wt ((d : ℝ) + γ) 0 ‖(x - y : Fin d → ℤ)‖ := by rw [Finset.mul_sum]
    _ ≤ ((2 : ℝ) ^ ah * LamR ‖x‖ ^ (-ah)) * ((2 : ℝ) ^ bh * LamR ‖x‖ ^ (-bh)) *
          ((2 : ℝ) ^ γ * (tailShellConst d γ * Wt γ 0 ‖x‖)) := by
        refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (mul_nonneg
          (Real.rpow_nonneg (by norm_num) _) (Real.rpow_nonneg hLam.le _))
          (mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.rpow_nonneg hLam.le _)))
        exact sum_pow_tail_le_sub hd hγ hA x F (fun y hy => not_le.mp (hF2 y hy))
    _ = ((2 : ℝ) ^ ah * (2 : ℝ) ^ bh *
          ((2 : ℝ) ^ ((d : ℝ) - a - b) * tailShellConst d ((d : ℝ) - a - b))) *
          convTargetR d a b ah bh ‖x‖ := by
        have hWy : Wt γ 0 ‖x‖ = (1 + ‖x‖) ^ (-γ) := Wt_zero_log
        rw [hWy, convTargetR, Wt]
        calc (2 : ℝ) ^ ah * LamR ‖x‖ ^ (-ah) * ((2 : ℝ) ^ bh * LamR ‖x‖ ^ (-bh)) *
              ((2 : ℝ) ^ γ * (tailShellConst d γ * (1 + ‖x‖) ^ (-γ)))
            = (2 : ℝ) ^ ah * (2 : ℝ) ^ bh * ((2 : ℝ) ^ γ * tailShellConst d γ) *
                ((1 + ‖x‖) ^ (-γ) * (LamR ‖x‖ ^ (-ah) * LamR ‖x‖ ^ (-bh))) := by ring
          _ = (2 : ℝ) ^ ah * (2 : ℝ) ^ bh * ((2 : ℝ) ^ γ * tailShellConst d γ) *
                ((1 + ‖x‖) ^ (-γ) * LamR ‖x‖ ^ (-(ah + bh))) := by rw [e2]
          _ = (2 : ℝ) ^ ah * (2 : ℝ) ^ bh *
                ((2 : ℝ) ^ ((d : ℝ) - a - b) * tailShellConst d ((d : ℝ) - a - b)) *
                ((1 + ‖x‖) ^ (-((d : ℝ) - a - b)) * LamR ‖x‖ ^ (-(ah + bh))) := by
              rw [hγdef]

/-- **The `A3` region.**  Splitting on `‖y‖ ≤ ‖x - y‖` and applying the two far halves. -/
lemma sum_convReg3_le {d : ℕ} (hd : 1 ≤ d) {a b ah bh : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hab : a + b < (d : ℝ)) (hah : 0 ≤ ah) (hbh : 0 ≤ bh) (x : Fin d → ℤ)
    (F : Finset (Fin d → ℤ)) (hF1 : ∀ y ∈ F, ¬ convReg1 x y)
    (hF2 : ∀ y ∈ F, ¬ convReg2 x y) :
    ∑ y ∈ F, convMajorant a b ah bh x y ≤
      convReg3Const d a b ah bh * convTargetR d a b ah bh ‖x‖ := by
  classical
  have hsplit := Finset.sum_filter_add_sum_filter_not F
    (fun y => ‖y‖ ≤ ‖(x - y : Fin d → ℤ)‖) (fun y => convMajorant a b ah bh x y)
  rw [← hsplit]
  have h1 := sum_convReg3a_le hd ha hb hab hah hbh x
    (F.filter (fun y => ‖y‖ ≤ ‖(x - y : Fin d → ℤ)‖))
    (fun y hy => hF1 y (Finset.mem_filter.mp hy).1)
    (fun y hy => (Finset.mem_filter.mp hy).2)
  have h2 := sum_convReg3b_le hd ha hb hab hah hbh x
    (F.filter (fun y => ¬ ‖y‖ ≤ ‖(x - y : Fin d → ℤ)‖))
    (fun y hy => hF1 y (Finset.mem_filter.mp hy).1)
    (fun y hy => hF2 y (Finset.mem_filter.mp hy).1)
    (fun y hy => (Finset.mem_filter.mp hy).2)
  calc ∑ y ∈ F.filter (fun y => ‖y‖ ≤ ‖(x - y : Fin d → ℤ)‖), convMajorant a b ah bh x y +
        ∑ y ∈ F.filter (fun y => ¬ ‖y‖ ≤ ‖(x - y : Fin d → ℤ)‖), convMajorant a b ah bh x y
      ≤ ((2 : ℝ) ^ ah * (2 : ℝ) ^ bh *
            ((2 : ℝ) ^ ((d : ℝ) - a - b) * tailShellConst d ((d : ℝ) - a - b))) *
          convTargetR d a b ah bh ‖x‖ +
        ((2 : ℝ) ^ ah * (2 : ℝ) ^ bh *
            ((2 : ℝ) ^ ((d : ℝ) - a - b) * tailShellConst d ((d : ℝ) - a - b))) *
          convTargetR d a b ah bh ‖x‖ := add_le_add h1 h2
    _ = convReg3Const d a b ah bh * convTargetR d a b ah bh ‖x‖ := by
        rw [convReg3Const]
        ring

end CriticalLRPConv
