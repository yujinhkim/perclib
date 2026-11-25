module

public import PercLib.CriticalLRP.Analysis.LatticeConvolution.MargConv.Defs
public import PercLib.CriticalLRP.Analysis.LatticeConvolution.ConvAssembly.Regions

/-!
# Marginal (`a + b = d`) convolution assembly: the `A1`/`A2`/`A3` region bounds

The three regions of the strict-case split, re-run with `a + b = d`:

* `A1` (`‖y‖ ≤ ‖x‖/2`) and `A2` (`‖x-y‖ ≤ ‖x‖/2`) are the strict-case bounds: the summed
  factor is estimated by the weighted ball-shell bound and the frozen factor by
  `Wt_freeze_halve`, which produces `⟨x⟩^0 Λ(x)^{-(â+b̂)}`; one extra logarithm is lost
  because `Λ ≥ log 2 ≥ 1/2`.
* `A3` is genuinely different: with `a + b = d` the product weight is
  `Wt d (â+b̂) v` in the variable `v = min ‖y‖ ‖x-y‖`, whose lattice sum only converges
  logarithmically.  The pure-log tail-shell bound `sum_Wt_tail_le_pureLog` converts
  `Λ^{-(â+b̂)}` into `Λ^{-((â+b̂)-1)}`, exactly one logarithm weaker.  This is the sharp
  marginal statement: `Λ^{-(â+b̂)}` is false here.
-/

set_option autoImplicit false

@[expose] public section

namespace CriticalLRPConv

open PercLib.CriticalLRP.FiniteVolume (linfNorm)

/-! ## §1 Nonnegativity of the `A1`/`A2` constants and of the total constant -/

/-- The `A1` contribution constant is nonnegative. -/
lemma convReg1Const_nonneg {d : ℕ} {a b ah bh : ℝ} (ha : 0 ≤ a) (had : a ≤ (d : ℝ))
    (hah : 0 ≤ ah) : 0 ≤ convReg1Const d a b ah bh := by
  unfold convReg1Const
  exact mul_nonneg (mul_nonneg (Real.rpow_nonneg (by norm_num) _)
    (Real.rpow_nonneg (by norm_num) _)) (ballShellConst_nonneg ha had hah)

/-- The `A2` contribution constant is nonnegative. -/
lemma convReg2Const_nonneg {d : ℕ} {a b ah bh : ℝ} (hb : 0 ≤ b) (hbd : b ≤ (d : ℝ))
    (hbh : 0 ≤ bh) : 0 ≤ convReg2Const d a b ah bh := by
  unfold convReg2Const
  exact mul_nonneg (mul_nonneg (Real.rpow_nonneg (by norm_num) _)
    (Real.rpow_nonneg (by norm_num) _)) (ballShellConst_nonneg hb hbd hbh)

/-- The total constant of the marginal assembly is nonnegative. -/
lemma margConst_nonneg {d : ℕ} (hd : 1 ≤ d) {a b ah bh : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hab : a + b = (d : ℝ)) (hah : 0 ≤ ah) (hbh : 0 ≤ bh) (hS : 1 < ah + bh) :
    0 ≤ margConst d a b ah bh := by
  have had : a ≤ (d : ℝ) := by linarith
  have hbd : b ≤ (d : ℝ) := by linarith
  unfold margConst
  refine mul_nonneg (by norm_num) ?_
  exact add_nonneg (add_nonneg (convReg1Const_nonneg ha.le had hah)
    (convReg2Const_nonneg hb.le hbd hbh)) (margReg3Const_nonneg hd hS)

/-! ## §2 The `A1` region -/

/-- **The `A1` region in the marginal case.**  On `‖y‖ ≤ ‖x‖/2` the second factor is frozen at
`‖x‖/2` and the first is summed by the ball shell estimate; `a + b = d` makes the power part
of the target trivial and leaves `Λ(x)^{-(â+b̂)}`, which costs one logarithm against the
marginal target. -/
lemma sum_convReg1_le_marg {d : ℕ} {a b ah bh : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hab : a + b = (d : ℝ)) (hah : 0 ≤ ah) (hbh : 0 ≤ bh) (x : Fin d → ℤ)
    (F : Finset (Fin d → ℤ)) (hF : ∀ y ∈ F, convReg1 x y) :
    ∑ y ∈ F, convMajorant a b ah bh x y ≤
      (2 * convReg1Const d a b ah bh) * margTarget ah bh x := by
  classical
  have hA : (0 : ℝ) ≤ ‖x‖ := norm_nonneg x
  have hhalf : (0 : ℝ) ≤ ‖x‖ / 2 := by linarith
  have had : a < (d : ℝ) := by linarith
  have hbd : b < (d : ℝ) := by linarith
  have hC1nn : (0 : ℝ) ≤ convReg1Const d a b ah bh := convReg1Const_nonneg ha.le had.le hah
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
    _ ≤ convReg1Const d a b ah bh * (2 * margTarget ah bh x) := by
        refine mul_le_mul_of_nonneg_left ?_ hC1nn
        exact convTargetR_le_two_margTargetR hab hA
    _ = (2 * convReg1Const d a b ah bh) * margTarget ah bh x := by ring

/-! ## §3 The `A2` region -/

/-- **The `A2` region in the marginal case.**  The mirror image of `sum_convReg1_le_marg`. -/
lemma sum_convReg2_le_marg {d : ℕ} {a b ah bh : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hab : a + b = (d : ℝ)) (hah : 0 ≤ ah) (hbh : 0 ≤ bh) (x : Fin d → ℤ)
    (F : Finset (Fin d → ℤ)) (hF : ∀ y ∈ F, convReg2 x y) :
    ∑ y ∈ F, convMajorant a b ah bh x y ≤
      (2 * convReg2Const d a b ah bh) * margTarget ah bh x := by
  classical
  have hA : (0 : ℝ) ≤ ‖x‖ := norm_nonneg x
  have hhalf : (0 : ℝ) ≤ ‖x‖ / 2 := by linarith
  have had : a < (d : ℝ) := by linarith
  have hbd : b < (d : ℝ) := by linarith
  have hC2nn : (0 : ℝ) ≤ convReg2Const d a b ah bh := convReg2Const_nonneg hb.le hbd.le hbh
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
    _ ≤ convReg2Const d a b ah bh * (2 * margTarget ah bh x) := by
        refine mul_le_mul_of_nonneg_left ?_ hC2nn
        exact convTargetR_le_two_margTargetR hab hA
    _ = (2 * convReg2Const d a b ah bh) * margTarget ah bh x := by ring

/-! ## §4 The pure-log tail shell centred at `x` -/

/-- The pure-log tail-shell bound `sum_Wt_tail_le_pureLog` with the weight centred at `x`.
The substitution `z = x - y` is injective on a `Finset`. -/
lemma sum_Wt_tail_le_pureLog_sub {d : ℕ} (hd : 1 ≤ d) {c A : ℝ} (hc : 1 < c) (hA : 0 ≤ A)
    (x : Fin d → ℤ) (F : Finset (Fin d → ℤ))
    (hF : ∀ y ∈ F, A < ‖(x - y : Fin d → ℤ)‖) :
    ∑ y ∈ F, Wt (d : ℝ) c ‖(x - y : Fin d → ℤ)‖ ≤
      tailShellConstLog d c * Wt 0 (c - 1) A := by
  classical
  have hinj : Set.InjOn (fun y : Fin d → ℤ => (x - y : Fin d → ℤ)) ↑F := by
    intro u _ v _ huv
    have huv' : x - u = x - v := huv
    have h : x - (x - u) = x - (x - v) := by rw [huv']
    simpa using h
  have hEq : ∑ y ∈ F, Wt (d : ℝ) c ‖(x - y : Fin d → ℤ)‖ =
      ∑ z ∈ F.image (fun y => (x - y : Fin d → ℤ)), Wt (d : ℝ) c (↑(linfNorm z) : ℝ) := by
    have h1 : (∑ y ∈ F, Wt (d : ℝ) c ‖(x - y : Fin d → ℤ)‖) =
        ∑ y ∈ F, Wt (d : ℝ) c (↑(linfNorm (x - y)) : ℝ) :=
      Finset.sum_congr rfl (fun y _ => by rw [coe_norm_eq_linfNorm])
    have h2 := Finset.sum_image (s := F) (g := fun y : Fin d → ℤ => (x - y : Fin d → ℤ))
      (f := fun z => Wt (d : ℝ) c (↑(linfNorm z) : ℝ)) hinj
    rw [h1, ← h2]
  rw [hEq]
  refine sum_Wt_tail_le_pureLog hd hc hA _ ?_
  intro z hz
  obtain ⟨y, hyF, rfl⟩ := Finset.mem_image.mp hz
  rw [← coe_norm_eq_linfNorm]
  exact hF y hyF

/-! ## §5 The `A3` region in the marginal case -/

/-- **The `A3` far half in the marginal case.**  On `‖y‖ ≤ ‖x-y‖` the two logarithms collapse
to the smaller one and the two powers add up to `(1+‖y‖)^{-d}`, so the term is exactly the
`(d, â+b̂)` weight of `y`; summing it over `‖y‖ > ‖x‖/2` costs one logarithm, which
`sum_Wt_tail_le_pureLog` charges as the exponent drop `â+b̂ ↦ (â+b̂)-1`. -/
lemma sum_convReg3a_le_marg {d : ℕ} (hd : 1 ≤ d) {a b ah bh : ℝ} (_ha : 0 < a) (_hb : 0 < b)
    (hab : a + b = (d : ℝ)) (_hah : 0 ≤ ah) (hbh : 0 ≤ bh) (hS : 1 < ah + bh)
    (x : Fin d → ℤ) (F : Finset (Fin d → ℤ)) (hF1 : ∀ y ∈ F, ¬ convReg1 x y)
    (hle : ∀ y ∈ F, ‖y‖ ≤ ‖(x - y : Fin d → ℤ)‖) :
    ∑ y ∈ F, convMajorant a b ah bh x y ≤ margReg3Const d ah bh * margTarget ah bh x := by
  classical
  have hA : (0 : ℝ) ≤ ‖x‖ := norm_nonneg x
  have hbd : b < (d : ℝ) := by linarith
  have hterm : ∀ y ∈ F, convMajorant a b ah bh x y ≤ Wt (d : ℝ) (ah + bh) ‖y‖ := by
    intro y hy
    have hy0 : (0 : ℝ) ≤ ‖y‖ := norm_nonneg y
    have hvy : ‖y‖ ≤ ‖(x - y : Fin d → ℤ)‖ := hle y hy
    have hply : (0 : ℝ) < 1 + ‖y‖ := by linarith
    have hp : (1 + ‖(x - y : Fin d → ℤ)‖) ^ (-((d : ℝ) - b)) ≤
        (1 + ‖y‖) ^ (-((d : ℝ) - b)) :=
      Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) (by linarith)
    have hl : LamR ‖(x - y : Fin d → ℤ)‖ ^ (-bh) ≤ LamR ‖y‖ ^ (-bh) :=
      Real.rpow_le_rpow_of_nonpos (LamR_pos hy0) (LamR_mono hy0 hvy) (by linarith)
    have hnn1 : (0 : ℝ) ≤ (1 + ‖(x - y : Fin d → ℤ)‖) ^ (-((d : ℝ) - b)) :=
      Real.rpow_nonneg (by linarith) _
    have hnn2 : (0 : ℝ) ≤ LamR ‖(x - y : Fin d → ℤ)‖ ^ (-bh) :=
      Real.rpow_nonneg (LamR_nonneg (norm_nonneg _)) _
    have hin : (1 + ‖(x - y : Fin d → ℤ)‖) ^ (-((d : ℝ) - b)) *
          LamR ‖(x - y : Fin d → ℤ)‖ ^ (-bh) ≤
        (1 + ‖y‖) ^ (-((d : ℝ) - b)) * LamR ‖y‖ ^ (-bh) :=
      mul_le_mul hp hl hnn2 (Real.rpow_nonneg (by linarith) _)
    have e1 : (1 + ‖y‖) ^ (-((d : ℝ) - a)) * (1 + ‖y‖) ^ (-((d : ℝ) - b)) =
        (1 + ‖y‖) ^ (-(d : ℝ)) := by
      rw [← Real.rpow_add hply]
      congr 1
      linarith
    have e2 : LamR ‖y‖ ^ (-ah) * LamR ‖y‖ ^ (-bh) = LamR ‖y‖ ^ (-(ah + bh)) := by
      rw [← Real.rpow_add (LamR_pos hy0)]
      congr 1
      ring
    calc convMajorant a b ah bh x y
        = ((1 + ‖y‖) ^ (-((d : ℝ) - a)) * LamR ‖y‖ ^ (-ah)) *
            ((1 + ‖(x - y : Fin d → ℤ)‖) ^ (-((d : ℝ) - b)) *
              LamR ‖(x - y : Fin d → ℤ)‖ ^ (-bh)) := rfl
      _ ≤ ((1 + ‖y‖) ^ (-((d : ℝ) - a)) * LamR ‖y‖ ^ (-ah)) *
            ((1 + ‖y‖) ^ (-((d : ℝ) - b)) * LamR ‖y‖ ^ (-bh)) :=
          mul_le_mul_of_nonneg_left hin (Wt_nonneg hy0)
      _ = Wt (d : ℝ) (ah + bh) ‖y‖ := by
          rw [Wt, ← e1, ← e2]
          ring
  have hsum : ∑ y ∈ F, Wt (d : ℝ) (ah + bh) ‖y‖ ≤
      tailShellConstLog d (ah + bh) * Wt 0 (ah + bh - 1) (‖x‖ / 2) := by
    have hEq : ∑ y ∈ F, Wt (d : ℝ) (ah + bh) ‖y‖ =
        ∑ y ∈ F, Wt (d : ℝ) (ah + bh) (↑(linfNorm y) : ℝ) :=
      Finset.sum_congr rfl (fun y _ => by rw [coe_norm_eq_linfNorm])
    rw [hEq]
    refine sum_Wt_tail_le_pureLog hd hS (by linarith) F ?_
    intro y hy
    rw [← coe_norm_eq_linfNorm]
    exact not_le.mp (hF1 y hy)
  calc ∑ y ∈ F, convMajorant a b ah bh x y
      ≤ ∑ y ∈ F, Wt (d : ℝ) (ah + bh) ‖y‖ := Finset.sum_le_sum hterm
    _ ≤ tailShellConstLog d (ah + bh) * Wt 0 (ah + bh - 1) (‖x‖ / 2) := hsum
    _ ≤ tailShellConstLog d (ah + bh) *
          ((2 : ℝ) ^ (ah + bh - 1) * margTargetR ah bh ‖x‖) := by
        refine mul_le_mul_of_nonneg_left ?_ (tailShellConstLog_nonneg hd hS)
        exact margTargetR_halve_le (by linarith) hA
    _ = margReg3Const d ah bh * margTarget ah bh x := by
        rw [margReg3Const, margTarget]
        ring

/-- **The `A3` near half in the marginal case.**  On `‖x-y‖ < ‖y‖` the roles of the two points
are exchanged; the substitution `z = x - y` turns the sum into the pure-log tail shell centred
at `x`. -/
lemma sum_convReg3b_le_marg {d : ℕ} (hd : 1 ≤ d) {a b ah bh : ℝ} (_ha : 0 < a) (_hb : 0 < b)
    (hab : a + b = (d : ℝ)) (hah : 0 ≤ ah) (_hbh : 0 ≤ bh) (hS : 1 < ah + bh)
    (x : Fin d → ℤ) (F : Finset (Fin d → ℤ)) (hF2 : ∀ y ∈ F, ¬ convReg2 x y)
    (hlt : ∀ y ∈ F, ¬ ‖y‖ ≤ ‖(x - y : Fin d → ℤ)‖) :
    ∑ y ∈ F, convMajorant a b ah bh x y ≤ margReg3Const d ah bh * margTarget ah bh x := by
  classical
  have hA : (0 : ℝ) ≤ ‖x‖ := norm_nonneg x
  have had : a < (d : ℝ) := by linarith
  have hterm : ∀ y ∈ F, convMajorant a b ah bh x y ≤
      Wt (d : ℝ) (ah + bh) ‖(x - y : Fin d → ℤ)‖ := by
    intro y hy
    have hv0 : (0 : ℝ) ≤ ‖(x - y : Fin d → ℤ)‖ := norm_nonneg _
    have hyv : ‖(x - y : Fin d → ℤ)‖ ≤ ‖y‖ := le_of_lt (not_le.mp (hlt y hy))
    have hply : (0 : ℝ) < 1 + ‖(x - y : Fin d → ℤ)‖ := by linarith
    have hp : (1 + ‖y‖) ^ (-((d : ℝ) - a)) ≤
        (1 + ‖(x - y : Fin d → ℤ)‖) ^ (-((d : ℝ) - a)) :=
      Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) (by linarith)
    have hl : LamR ‖y‖ ^ (-ah) ≤ LamR ‖(x - y : Fin d → ℤ)‖ ^ (-ah) :=
      Real.rpow_le_rpow_of_nonpos (LamR_pos hv0) (LamR_mono hv0 hyv) (by linarith)
    have hnn2 : (0 : ℝ) ≤ LamR ‖y‖ ^ (-ah) :=
      Real.rpow_nonneg (LamR_nonneg (norm_nonneg _)) _
    have hin : (1 + ‖y‖) ^ (-((d : ℝ) - a)) * LamR ‖y‖ ^ (-ah) ≤
        (1 + ‖(x - y : Fin d → ℤ)‖) ^ (-((d : ℝ) - a)) *
          LamR ‖(x - y : Fin d → ℤ)‖ ^ (-ah) :=
      mul_le_mul hp hl hnn2 (Real.rpow_nonneg (by linarith) _)
    have e1 : (1 + ‖(x - y : Fin d → ℤ)‖) ^ (-((d : ℝ) - a)) *
        (1 + ‖(x - y : Fin d → ℤ)‖) ^ (-((d : ℝ) - b)) =
        (1 + ‖(x - y : Fin d → ℤ)‖) ^ (-(d : ℝ)) := by
      rw [← Real.rpow_add hply]
      congr 1
      linarith
    have e2 : LamR ‖(x - y : Fin d → ℤ)‖ ^ (-ah) * LamR ‖(x - y : Fin d → ℤ)‖ ^ (-bh) =
        LamR ‖(x - y : Fin d → ℤ)‖ ^ (-(ah + bh)) := by
      rw [← Real.rpow_add (LamR_pos hv0)]
      congr 1
      ring
    calc convMajorant a b ah bh x y
        = ((1 + ‖y‖) ^ (-((d : ℝ) - a)) * LamR ‖y‖ ^ (-ah)) *
            ((1 + ‖(x - y : Fin d → ℤ)‖) ^ (-((d : ℝ) - b)) *
              LamR ‖(x - y : Fin d → ℤ)‖ ^ (-bh)) := rfl
      _ ≤ ((1 + ‖(x - y : Fin d → ℤ)‖) ^ (-((d : ℝ) - a)) *
            LamR ‖(x - y : Fin d → ℤ)‖ ^ (-ah)) *
            ((1 + ‖(x - y : Fin d → ℤ)‖) ^ (-((d : ℝ) - b)) *
              LamR ‖(x - y : Fin d → ℤ)‖ ^ (-bh)) :=
          mul_le_mul_of_nonneg_right hin (Wt_nonneg hv0)
      _ = Wt (d : ℝ) (ah + bh) ‖(x - y : Fin d → ℤ)‖ := by
          rw [Wt, ← e1, ← e2]
          ring
  have hsum : ∑ y ∈ F, Wt (d : ℝ) (ah + bh) ‖(x - y : Fin d → ℤ)‖ ≤
      tailShellConstLog d (ah + bh) * Wt 0 (ah + bh - 1) (‖x‖ / 2) :=
    sum_Wt_tail_le_pureLog_sub hd hS (by linarith) x F
      (fun y hy => not_le.mp (hF2 y hy))
  calc ∑ y ∈ F, convMajorant a b ah bh x y
      ≤ ∑ y ∈ F, Wt (d : ℝ) (ah + bh) ‖(x - y : Fin d → ℤ)‖ := Finset.sum_le_sum hterm
    _ ≤ tailShellConstLog d (ah + bh) * Wt 0 (ah + bh - 1) (‖x‖ / 2) := hsum
    _ ≤ tailShellConstLog d (ah + bh) *
          ((2 : ℝ) ^ (ah + bh - 1) * margTargetR ah bh ‖x‖) := by
        refine mul_le_mul_of_nonneg_left ?_ (tailShellConstLog_nonneg hd hS)
        exact margTargetR_halve_le (by linarith) hA
    _ = margReg3Const d ah bh * margTarget ah bh x := by
        rw [margReg3Const, margTarget]
        ring

/-- **The `A3` region in the marginal case**, splitting on `‖y‖ ≤ ‖x-y‖`. -/
lemma sum_convReg3_le_marg {d : ℕ} (hd : 1 ≤ d) {a b ah bh : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hab : a + b = (d : ℝ)) (hah : 0 ≤ ah) (hbh : 0 ≤ bh) (hS : 1 < ah + bh)
    (x : Fin d → ℤ) (F : Finset (Fin d → ℤ)) (hF1 : ∀ y ∈ F, ¬ convReg1 x y)
    (hF2 : ∀ y ∈ F, ¬ convReg2 x y) :
    ∑ y ∈ F, convMajorant a b ah bh x y ≤
      (2 * margReg3Const d ah bh) * margTarget ah bh x := by
  classical
  have hsplit := Finset.sum_filter_add_sum_filter_not F
    (fun y => ‖y‖ ≤ ‖(x - y : Fin d → ℤ)‖) (fun y => convMajorant a b ah bh x y)
  rw [← hsplit]
  have h1 := sum_convReg3a_le_marg (d := d) hd ha hb hab hah hbh hS x
    (F.filter (fun y => ‖y‖ ≤ ‖(x - y : Fin d → ℤ)‖))
    (fun y hy => hF1 y (Finset.mem_filter.mp hy).1)
    (fun y hy => (Finset.mem_filter.mp hy).2)
  have h2 := sum_convReg3b_le_marg (d := d) hd ha hb hab hah hbh hS x
    (F.filter (fun y => ¬ ‖y‖ ≤ ‖(x - y : Fin d → ℤ)‖))
    (fun y hy => hF2 y (Finset.mem_filter.mp hy).1)
    (fun y hy => (Finset.mem_filter.mp hy).2)
  exact (add_le_add h1 h2).trans (le_of_eq (by ring))

end CriticalLRPConv

/-! ## Axiom audit -/

set_option linter.hashCommand false

#print axioms CriticalLRPConv.convReg1Const_nonneg
#print axioms CriticalLRPConv.convReg2Const_nonneg
#print axioms CriticalLRPConv.margConst_nonneg
#print axioms CriticalLRPConv.sum_convReg1_le_marg
#print axioms CriticalLRPConv.sum_convReg2_le_marg
#print axioms CriticalLRPConv.sum_Wt_tail_le_pureLog_sub
#print axioms CriticalLRPConv.sum_convReg3a_le_marg
#print axioms CriticalLRPConv.sum_convReg3b_le_marg
#print axioms CriticalLRPConv.sum_convReg3_le_marg
