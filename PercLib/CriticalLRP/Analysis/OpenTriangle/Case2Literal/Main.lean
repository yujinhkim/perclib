/-
Scratch deliverable of swarm `smwu2am6k`, member `m1`, direction `d1`.

# The literal Case 2 open triangle

`TriTail.openTriangle J hJ β 0 x` is by definition the iterated `ℝ≥0∞` sum
`∑' u, ∑' v, τ(0,u) τ(u,v) τ(v,x)` of the *literal* two-point function.  The committed abstract
Case 2 assembly (`Orchestration.HD.triple_convolution_case2`) is a statement about an abstract real
radial profile `t` with `t 0 = 1` and `t z ≤ C ‖z‖^{-d+2}`, whose *iterated convolution*
`∑' b, (∑' a, t a t (b - a)) t (x - b)` is bounded by `⟨x⟩^{-(d-6)}`.

This file supplies the missing identification between the two:

* `openTriangle_eq_tsum_ENNReal` — **unconditional**: for *any* translation-invariant kernel `J`
  (no domination, no summability, no nonnegativity beyond `hJ` for the `τ` values to be real
  probabilities) the literal open triangle **is** the abstract iterated convolution of the profile
  `litT`, as an equality in `ℝ≥0∞`.  It is proved from `twoPointFunction_eq_origin` alone.
* `openTriangle_eq_ofReal_tsum` — the `ℝ`-valued form, where the two summabilities produced by
  `convolution_two_case2` / `triple_convolution_case2` are used to push `ENNReal.ofReal` through
  both `tsum`s.  No `∞` is ever sent to `0`: finiteness of the literal object is *derived*
  (`openTriangle_ne_top`) rather than assumed.
* `openTriangle_toReal_le_powMajorant` — the Case 2 pointwise bound `∇(0,x) ⪯ ‖x‖^{-(d-6)}` at
  `x ≠ 0`, in the exact shape consumed by
  `Orchestration.SourceModelData.isLogErrorFunction_nablaTail_of_pow`.
* `isLogErrorFunction_openTriangleTail` — the plain sup-norm lattice tail
  `TriTail.openTriangleTail` is a logarithmically integrable error function, i.e.
  `∫^∞ ∇_r dr / r < ∞` and `∇_r → 0`.

Everything is conditional on the *HD Case 2 domination* at `β`: the hypothesis

`hHD : ∀ x ≠ 0, τ_β(0,x) ≤ ofReal (C ‖x‖^{-d+2})`  with `C ≥ 1` and `d > 6`,

which is (HD)(2) of the source (`P_{β_c}(x↔y) ⪯ ‖x-y‖^{-d+2}` for `x ≠ y`) in `ℝ≥0∞` form, with
the `C ≥ 1` slack that covers the excluded origin (`abs_le_conv_wt_of_case2`).  It is *not*
produced here from the connectivity expansion; it is the source's HD input.
-/
module

public import PercLib.CriticalLRP.Analysis.OpenTriangle.Case2Literal.Defs

/-! # Literal Case 2: Main

The literal Case 2 open-triangle identification and sup-norm tail estimate.
-/

set_option autoImplicit false


set_option linter.hashCommand false

@[expose] public section

open scoped ENNReal Topology

namespace PercLib.CriticalLRP.Orchestration.HD

open CriticalLRPConv Filter MeasureTheory Set

variable {d : ℕ} {J : Sym2 (Fin d → ℤ) → ℝ} {hJ : ∀ e, 0 ≤ J e} {β : NNReal}

/-! ## 1. The identification, unconditionally

The literal open triangle is the iterated convolution of `litT`.  Nothing but translation
invariance is used: `ENNReal.tsum_comm` swaps the two sums and `ENNReal.tsum_mul_right` factors the
outer leg `τ(v,x)`, which no longer depends on the inner index, out of the inner sum.  There is no
finiteness or summability hypothesis anywhere, so no `∞` is discarded. -/
theorem openTriangle_eq_tsum_ENNReal
    (hJinv : ∀ (a : Fin d → ℤ) (e : Sym2 (Fin d → ℤ)), J (Sym2.map (fun x => x + a) e) = J e)
    (x : Fin d → ℤ) :
    TriTail.openTriangle J hJ β 0 x
      = ∑' b, (∑' a, twoPointFunction J hJ β 0 a * twoPointFunction J hJ β 0 (b - a)) *
          twoPointFunction J hJ β 0 (x - b) := by
  rw [TriTail.openTriangle, ENNReal.tsum_comm]
  refine tsum_congr fun b => ?_
  rw [ENNReal.tsum_mul_right, twoPointFunction_eq_origin hJinv hJ β b x]
  congr 1
  exact tsum_congr fun a => by rw [twoPointFunction_eq_origin hJinv hJ β a b]

/-! ## 2. The HD Case 2 domination, read in `ℝ` -/

theorem litT_le_of_HD {C : ℝ} (hC : 1 ≤ C)
    (hHD : ∀ x : Fin d → ℤ, x ≠ 0 →
      twoPointFunction J hJ β 0 x ≤ ENNReal.ofReal (C * ‖x‖ ^ (-(d : ℝ) + 2)))
    {x : Fin d → ℤ} (hx : x ≠ 0) : litT J hJ β x ≤ C * ‖x‖ ^ (-(d : ℝ) + 2) := by
  have hC0 : (0 : ℝ) ≤ C := by linarith
  have hnon : 0 ≤ C * ‖x‖ ^ (-(d : ℝ) + 2) :=
    mul_nonneg hC0 (Real.rpow_nonneg (norm_nonneg x) _)
  calc litT J hJ β x = (twoPointFunction J hJ β 0 x).toReal := rfl
    _ ≤ (ENNReal.ofReal (C * ‖x‖ ^ (-(d : ℝ) + 2))).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top (hHD x hx)
    _ = C * ‖x‖ ^ (-(d : ℝ) + 2) := ENNReal.toReal_ofReal hnon

/-! ## 3. The identification in `ℝ`, and the `ℝ≥0∞`/`ℝ` correspondence

The two summabilities are *not* extra hypotheses: they are the ones the abstract Case 2 assembly
already returns at every `x`.  Note which one is used where — the inner one at the *middle* index
`b` (from `convolution_two_case2 b`) and the outer one at the *target* index `x` (from
`triple_convolution_case2 x`). -/
theorem openTriangle_eq_ofReal_tsum
    (hJinv : ∀ (a : Fin d → ℤ) (e : Sym2 (Fin d → ℤ)), J (Sym2.map (fun x => x + a) e) = J e)
    (hd : 6 < d) {C : ℝ} (hC : 1 ≤ C)
    (hHD : ∀ x : Fin d → ℤ, x ≠ 0 →
      twoPointFunction J hJ β 0 x ≤ ENNReal.ofReal (C * ‖x‖ ^ (-(d : ℝ) + 2)))
    (x : Fin d → ℤ) :
    TriTail.openTriangle J hJ β 0 x
      = ENNReal.ofReal
          (∑' b, (∑' a, litT J hJ β a * litT J hJ β (b - a)) * litT J hJ β (x - b)) := by
  have ht : ∀ z : Fin d → ℤ, z ≠ 0 → litT J hJ β z ≤ C * ‖z‖ ^ (-(d : ℝ) + 2) :=
    fun z hz => litT_le_of_HD hC hHD hz
  have hconv : ∀ b : Fin d → ℤ, Summable (fun a => litT J hJ β a * litT J hJ β (b - a)) :=
    fun b => (convolution_two_case2 hd hC (litT_nonneg J hJ β) (litT_zero J hJ β) ht b).1
  have htrip : Summable
      (fun b => (∑' a, litT J hJ β a * litT J hJ β (b - a)) * litT J hJ β (x - b)) :=
    (triple_convolution_case2 hd hC (litT_nonneg J hJ β) (litT_zero J hJ β) ht x).1
  rw [openTriangle_eq_tsum_ENNReal hJinv x]
  simp only [← ofReal_litT]
  trans ∑' b, ENNReal.ofReal
      ((∑' a, litT J hJ β a * litT J hJ β (b - a)) * litT J hJ β (x - b))
  · refine tsum_congr fun b => ?_
    have hinner : (∑' a, ENNReal.ofReal (litT J hJ β a) * ENNReal.ofReal (litT J hJ β (b - a)))
        = ENNReal.ofReal (∑' a, litT J hJ β a * litT J hJ β (b - a)) := by
      have hstep : (∑' a, ENNReal.ofReal (litT J hJ β a) *
            ENNReal.ofReal (litT J hJ β (b - a)))
          = ∑' a, ENNReal.ofReal (litT J hJ β a * litT J hJ β (b - a)) :=
        tsum_congr fun a => (ENNReal.ofReal_mul (litT_nonneg J hJ β a)).symm
      rw [hstep, ENNReal.ofReal_tsum_of_nonneg
        (f := fun a => litT J hJ β a * litT J hJ β (b - a))
        (fun a => mul_nonneg (litT_nonneg J hJ β a) (litT_nonneg J hJ β (b - a))) (hconv b)]
    have htsum : 0 ≤ ∑' a, litT J hJ β a * litT J hJ β (b - a) :=
      tsum_nonneg fun a => mul_nonneg (litT_nonneg J hJ β a) (litT_nonneg J hJ β (b - a))
    calc (∑' a, ENNReal.ofReal (litT J hJ β a) * ENNReal.ofReal (litT J hJ β (b - a))) *
          ENNReal.ofReal (litT J hJ β (x - b))
        = ENNReal.ofReal (∑' a, litT J hJ β a * litT J hJ β (b - a)) *
            ENNReal.ofReal (litT J hJ β (x - b)) := by rw [hinner]
      _ = ENNReal.ofReal
            ((∑' a, litT J hJ β a * litT J hJ β (b - a)) * litT J hJ β (x - b)) :=
          (ENNReal.ofReal_mul htsum).symm
  · exact (ENNReal.ofReal_tsum_of_nonneg
      (fun b => mul_nonneg (tsum_nonneg fun a =>
        mul_nonneg (litT_nonneg J hJ β a) (litT_nonneg J hJ β (b - a)))
        (litT_nonneg J hJ β (x - b))) htrip).symm

/-! ## 4. The Case 2 bound at the literal object -/

theorem openTriangle_le_ofReal_wt
    (hJinv : ∀ (a : Fin d → ℤ) (e : Sym2 (Fin d → ℤ)), J (Sym2.map (fun x => x + a) e) = J e)
    (hd : 6 < d) {C : ℝ} (hC : 1 ≤ C)
    (hHD : ∀ x : Fin d → ℤ, x ≠ 0 →
      twoPointFunction J hJ β 0 x ≤ ENNReal.ofReal (C * ‖x‖ ^ (-(d : ℝ) + 2)))
    (x : Fin d → ℤ) :
    TriTail.openTriangle J hJ β 0 x
      ≤ ENNReal.ofReal (case2Const d C * Wt ((d : ℝ) - 6) 0 ‖x‖) := by
  have ht : ∀ z : Fin d → ℤ, z ≠ 0 → litT J hJ β z ≤ C * ‖z‖ ^ (-(d : ℝ) + 2) :=
    fun z hz => litT_le_of_HD hC hHD hz
  rw [openTriangle_eq_ofReal_tsum hJinv hd hC hHD x]
  refine ENNReal.ofReal_le_ofReal ?_
  have h := (triple_convolution_case2 hd hC (litT_nonneg J hJ β) (litT_zero J hJ β) ht x).2
  refine (le_abs_self _).trans (h.trans_eq ?_)
  rw [case2Const]
  ring

/-- **The literal open triangle is finite** under the HD Case 2 domination.  This is what lets the
`ℝ≥0∞` statements be read as real numbers at all: no `∞` is turned into `0`. -/
theorem openTriangle_ne_top
    (hJinv : ∀ (a : Fin d → ℤ) (e : Sym2 (Fin d → ℤ)), J (Sym2.map (fun x => x + a) e) = J e)
    (hd : 6 < d) {C : ℝ} (hC : 1 ≤ C)
    (hHD : ∀ x : Fin d → ℤ, x ≠ 0 →
      twoPointFunction J hJ β 0 x ≤ ENNReal.ofReal (C * ‖x‖ ^ (-(d : ℝ) + 2)))
    (x : Fin d → ℤ) : TriTail.openTriangle J hJ β 0 x ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top (openTriangle_le_ofReal_wt hJinv hd hC hHD x)

/-- **The Case 2 profile at the literal open triangle**: `∇(0,x) ⪯ ‖x‖^{-(d-6)}` for `x ≠ 0`.

`⟨x⟩` is replaced by `‖x‖` on the nonzero lattice, where `‖x‖ ≥ 1`; the loss is absorbed in the
constant `case2Const d C` with no extra factor (it is the *same* constant, since
`(1 + ‖x‖)^{-a} ≤ ‖x‖^{-a}`). -/
theorem openTriangle_toReal_le_powMajorant
    (hJinv : ∀ (a : Fin d → ℤ) (e : Sym2 (Fin d → ℤ)), J (Sym2.map (fun x => x + a) e) = J e)
    (hd : 6 < d) {C : ℝ} (hC : 1 ≤ C)
    (hHD : ∀ x : Fin d → ℤ, x ≠ 0 →
      twoPointFunction J hJ β 0 x ≤ ENNReal.ofReal (C * ‖x‖ ^ (-(d : ℝ) + 2)))
    {x : Fin d → ℤ} (hx : x ≠ 0) :
    (TriTail.openTriangle J hJ β 0 x).toReal
      ≤ Analysis.powMajorant (case2Const d C) ((d : ℝ) - 6) ‖x‖ := by
  have hK := case2Const_nonneg (d := d) hd hC
  have hbound := openTriangle_le_ofReal_wt hJinv hd hC hHD x
  have hpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hdR : (6 : ℝ) ≤ (d : ℝ) := by exact_mod_cast Nat.le_of_lt hd
  have hle : Wt ((d : ℝ) - 6) 0 ‖x‖ ≤ ‖x‖ ^ (-((d : ℝ) - 6)) := by
    rw [Wt_zero_log]
    exact Real.rpow_le_rpow_of_nonpos hpos (by linarith) (by linarith)
  calc (TriTail.openTriangle J hJ β 0 x).toReal
      ≤ (ENNReal.ofReal (case2Const d C * Wt ((d : ℝ) - 6) 0 ‖x‖)).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound
    _ = case2Const d C * Wt ((d : ℝ) - 6) 0 ‖x‖ :=
        ENNReal.toReal_ofReal (mul_nonneg hK (Wt_nonneg (norm_nonneg x)))
    _ ≤ case2Const d C * ‖x‖ ^ (-((d : ℝ) - 6)) := mul_le_mul_of_nonneg_left hle hK
    _ = Analysis.powMajorant (case2Const d C) ((d : ℝ) - 6) ‖x‖ := rfl

/-! ## 4b. The radial/tail form of the Case 2 bound -/

/-- **The Case 2 radial bound in the shape `PowRadialBound` consumes.**

At every vertex of positive `ℓ^∞` radius, the literal open triangle is at most
`case2Const d C * (latticeDist 0 x) ^ (-(d-6))`.  This is
`openTriangle_toReal_le_powMajorant` with the sup-norm `‖x‖` identified with
`FiniteVolume.latticeDist 0 x`, and with the bound converted from `ℝ` to `ℝ≥0∞`. -/
theorem powRadialBound_openTriangle
    (hJinv : ∀ (a : Fin d → ℤ) (e : Sym2 (Fin d → ℤ)), J (Sym2.map (fun x => x + a) e) = J e)
    (hd : 6 < d) {C : ℝ} (hC : 1 ≤ C)
    (hHD : ∀ x : Fin d → ℤ, x ≠ 0 →
      twoPointFunction J hJ β 0 x ≤ ENNReal.ofReal (C * ‖x‖ ^ (-(d : ℝ) + 2))) :
    Analysis.PowRadialBound (fun x : Fin d → ℤ => FiniteVolume.latticeDist 0 x)
      (fun x : Fin d → ℤ => TriTail.openTriangle J hJ β 0 x) (case2Const d C) ((d : ℝ) - 6) := by
  intro x hx
  dsimp only at hx ⊢
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [FiniteVolume.latticeDist_self] at hx
    exact lt_irrefl 0 hx
  rw [← ENNReal.ofReal_toReal (openTriangle_ne_top hJinv hd hC hHD x)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hdist : FiniteVolume.latticeDist 0 x = ‖x‖ := by
    rw [FiniteVolume.latticeDist, show (0 : Fin d → ℤ) - x = -x from by simp,
      FiniteVolume.linfNorm_neg]
    exact (CriticalLRPConv.coe_norm_eq_linfNorm x).symm
  rw [hdist]
  exact openTriangle_toReal_le_powMajorant hJinv hd hC hHD hx0

/-- **The explicit tail bound `∇_r ⪯ r ^ (-(d-6))`** at the plain `ℓ^∞` open-triangle tail, for
every `r > 0`.  This is the Case 2 bound (I.4.11) after taking the spatial supremum; it is only
claimed on `r > 0`, where the diagonal `x = 0` is never seen. -/
theorem openTriangleTail_le_powMajorant
    (hJinv : ∀ (a : Fin d → ℤ) (e : Sym2 (Fin d → ℤ)), J (Sym2.map (fun x => x + a) e) = J e)
    (hd : 6 < d) {C : ℝ} (hC : 1 ≤ C)
    (hHD : ∀ x : Fin d → ℤ, x ≠ 0 →
      twoPointFunction J hJ β 0 x ≤ ENNReal.ofReal (C * ‖x‖ ^ (-(d : ℝ) + 2)))
    {r : ℝ} (hr : 0 < r) :
    TriTail.openTriangleTail J hJ β r
      ≤ ENNReal.ofReal (Analysis.powMajorant (case2Const d C) ((d : ℝ) - 6) r) := by
  have hpow := powRadialBound_openTriangle hJinv hd hC hHD
  have hexp : (0 : ℝ) ≤ (d : ℝ) - 6 := by
    have : (6 : ℝ) < (d : ℝ) := by exact_mod_cast hd
    linarith
  have hmain := Analysis.radialTailSup_le_powMajorant
    (nrm := fun x : Fin d → ℤ => FiniteVolume.latticeDist 0 x)
    (F := fun x : Fin d → ℤ => TriTail.openTriangle J hJ β 0 x)
    (case2Const_nonneg hd hC) hexp hr hpow
  simpa only [TriTail.openTriangleTail_eq_radialTailSup] using hmain

/-! ## 5. The plain sup-norm log tail

`TriTail.openTriangleTail` is the `ℓ^∞`-radius supremum `∇_r = sup_{‖x‖ ≥ r} ∇(0,x)`.  The
`ℓ^∞` radius is `FiniteVolume.latticeDist 0 x`, which is `‖x‖`; the nonzero-vertex restriction is
invisible to the tail at `r > 0`, which is exactly why `PowRadialBound` is only required at
`0 < nrm x`. -/
theorem isLogErrorFunction_openTriangleTail
    (hJinv : ∀ (a : Fin d → ℤ) (e : Sym2 (Fin d → ℤ)), J (Sym2.map (fun x => x + a) e) = J e)
    (hd : 6 < d) {C : ℝ} (hC : 1 ≤ C)
    (hHD : ∀ x : Fin d → ℤ, x ≠ 0 →
      twoPointFunction J hJ β 0 x ≤ ENNReal.ofReal (C * ‖x‖ ^ (-(d : ℝ) + 2))) :
    Analysis.IsLogErrorFunction (fun r => (TriTail.openTriangleTail J hJ β r).toReal) := by
  have hdR : (6 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hmain := Analysis.isLogErrorFunction_radialTailSup_pow
    (nrm := fun x : Fin d → ℤ => FiniteVolume.latticeDist 0 x)
    (F := fun x : Fin d → ℤ => TriTail.openTriangle J hJ β 0 x)
    (case2Const_nonneg hd hC) (by linarith) (powRadialBound_openTriangle hJinv hd hC hHD)
  simpa only [TriTail.openTriangleTail_eq_radialTailSup] using hmain

/-- **`∫^∞ ∇_r dr / r < ∞`**, displayed in the source's own form: there is `r₀ > 0` with
`r ↦ |∇_r| / r` integrable on `(r₀, ∞)`.

`Analysis.LogarithmicallyIntegrable` is *defined* as exactly this (plus measurability), and it
carries **no local compact-integrability clause**: nothing about `r ≤ r₀` is asserted.  This is
recorded deliberately — no claim is made about compact subintervals of `(0,∞)`, because the
`ℝ≥0∞`-valued tail is only known to be finite through the pointwise bound at positive radius. -/
theorem openTriangleTail_logIntegrable
    (hJinv : ∀ (a : Fin d → ℤ) (e : Sym2 (Fin d → ℤ)), J (Sym2.map (fun x => x + a) e) = J e)
    (hd : 6 < d) {C : ℝ} (hC : 1 ≤ C)
    (hHD : ∀ x : Fin d → ℤ, x ≠ 0 →
      twoPointFunction J hJ β 0 x ≤ ENNReal.ofReal (C * ‖x‖ ^ (-(d : ℝ) + 2))) :
    Analysis.LogarithmicallyIntegrable (fun r : ℝ => (TriTail.openTriangleTail J hJ β r).toReal) ∧
    Tendsto (fun r : ℝ => (TriTail.openTriangleTail J hJ β r).toReal) atTop (𝓝 0) :=
  isLogErrorFunction_openTriangleTail hJinv hd hC hHD

end PercLib.CriticalLRP.Orchestration.HD

#print axioms PercLib.CriticalLRP.Orchestration.HD.openTriangle_eq_tsum_ENNReal
#print axioms PercLib.CriticalLRP.Orchestration.HD.openTriangle_eq_ofReal_tsum
#print axioms PercLib.CriticalLRP.Orchestration.HD.openTriangle_le_ofReal_wt
#print axioms PercLib.CriticalLRP.Orchestration.HD.openTriangle_ne_top
#print axioms PercLib.CriticalLRP.Orchestration.HD.openTriangle_toReal_le_powMajorant
#print axioms PercLib.CriticalLRP.Orchestration.HD.powRadialBound_openTriangle
#print axioms PercLib.CriticalLRP.Orchestration.HD.openTriangleTail_le_powMajorant
#print axioms PercLib.CriticalLRP.Orchestration.HD.isLogErrorFunction_openTriangleTail
#print axioms PercLib.CriticalLRP.Orchestration.HD.openTriangleTail_logIntegrable
