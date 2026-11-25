/-
The literal Case 3 bridge on the sup-norm lattice (`d = 6`).

Swarm `smwu3to7x`, member `m1`.  Proof-only packet: this file introduces no definitions and no
axioms; every constant it quotes is already defined in `Case3Profile.Defs`.

# Setting and objects

`J : Sym2 (Fin 6 → ℤ) → ℝ` is nonnegative and translation invariant, `β : ℝ≥0`, and

* `τ z = twoPointFunction J hJ β 0 z` is the literal two-point function at the origin;
* `t z = litT J hJ β z = (τ z).toReal` is its real-valued profile (`litT` of `Case2Literal`).

The literal open triangle is `∇ x = TriTail.openTriangle J hJ β 0 x
= ∑' u, ∑' v, τ(0,u) τ(u,v) τ(v,x)`, and the abstract triple convolution of `t` is
`∑' b, (∑' a, t a * t (b - a)) * t (x - b)`.

# What is proved

1. `openTriangle_eq_ofReal_tsum_case3Shell` / `…_case3Raw`: the literal open triangle **is** the
   `ENNReal.ofReal` of the abstract triple convolution of `litT`.  The identity is reduced to the
   unconditional `HD.openTriangle_eq_tsum_ENNReal` and `ENNReal.ofReal` is pushed through the two
   `tsum`s only after the Case 3 profile chain has produced genuine `Summable` facts.
2. `openTriangle_ne_top_case3Shell` / `…_case3Raw`: finiteness of the literal object, derived from
   the explicit square-logarithmic bound — no `⊤` is ever coerced to `0`.
3. `openTriangle_le_ofReal_logMajorant_case3Shell` / `…_case3Raw`: the pointwise square-log bound
   `∇ x ≤ ofReal (K (log (1 + ‖x‖))⁻²)` at every `x ≠ 0`, with the explicit constants
   `case3Conv3ConstShell C` and `case3Conv3Const C`.
4. `isLogErrorFunction_openTriangleTail_case3Shell` / `…_case3Raw`: `Analysis.IsLogErrorFunction`
   of the plain sup-norm tail `r ↦ (TriTail.openTriangleTail J hJ β r).toReal`, whose radius
   predicate is literally `r ≤ latticeDist 0 x` (`TriTail.openTriangleTail`), kept as is.

# Input shapes

* `…Case3Shell` (primary, source shaped): `t ≤ 1` everywhere — for a two-point function this is
  `litT_le_one`, not an extra hypothesis — and the literal HD(3) domination
  `τ z ≤ ofReal (C ‖z‖^{-6+2} (log ‖z‖)⁻¹)` only for `‖z‖ ≥ 2`.
* `…Case3Raw`: the same domination at every `z ≠ 0`.  Lean's `(log 1)⁻¹ = 0` then forces `t = 0`
  on the unit shell (`litT_eq_zero_of_one_le_norm_of_raw`); this accidental strength is recorded,
  not used to replace the hypothesis.

# Conventions made explicit

* The only hypothesis on `C` is `0 ≤ C`.  A source constant `C ≥ 1` is an instance; no
  `max 1 C` adjustment is needed because `case3ShellConst d C` is `max … … + 1 ≥ 1`.
* `z ≠ 0` implies `‖z‖ ≥ 1` (`one_le_norm_of_ne_zero`), the nonzero-vertex convention.
* `log` is Lean's real logarithm, so `log 1 = 0` and `0⁻¹ = 0`; the near-origin behaviour on the
  unit shell is handled by the `max`/`+1` in `case3ShellConst`, not by an unproved decay input.
-/
module

public import PercLib.CriticalLRP.Analysis.OpenTriangle.Case2Literal.Main
public import PercLib.CriticalLRP.Analysis.OpenTriangle.Case3Profile.Main
public import PercLib.CriticalLRP.Analysis.TriTailLogTail

/-! # The literal Case 3 bridge at `d = 6` -/

set_option autoImplicit false

set_option linter.hashCommand false

@[expose] public section

open scoped ENNReal Topology

namespace PercLib.CriticalLRP.Orchestration.HD

open CriticalLRPConv Filter

open PercLib.CriticalLRP.Orchestration.HD.Case3

variable {J : Sym2 (Fin 6 → ℤ) → ℝ} {hJ : ∀ e, 0 ≤ J e} {β : NNReal}

/-! ## §1 The nonzero-vertex convention and the profile bounds -/

/-- **Nonzero vertices have sup-norm at least `1`.**  This is the lattice fact behind the
near-origin bookkeeping: the raw logarithm `(log ‖z‖)⁻¹` is only inspected for `‖z‖ ≥ 1`. -/
theorem one_le_norm_of_ne_zero {z : Fin 6 → ℤ} (hz : z ≠ 0) : (1 : ℝ) ≤ ‖z‖ := by
  have hone : (1 : ℕ) ≤ FiniteVolume.linfNorm z :=
    Nat.one_le_iff_ne_zero.mpr (fun h => hz (FiniteVolume.linfNorm_eq_zero_iff.mp h))
  rw [CriticalLRPConv.coe_norm_eq_linfNorm]
  exact_mod_cast hone

/-- **The source-shaped (shell) Case 3 domination, read in `ℝ`.**

From the `ℝ≥0∞` domination `τ z ≤ ofReal (C ‖z‖^{-6+2} (log ‖z‖)⁻¹)` for `‖z‖ ≥ 2` we get the
same inequality for the real profile `t = litT`, using only `C ≥ 0` and `log ‖z‖ ≥ 0`. -/
theorem litT_le_of_HD_shell {C : ℝ} (hC : 0 ≤ C)
    (hHD : ∀ z : Fin 6 → ℤ, 2 ≤ ‖z‖ →
      twoPointFunction J hJ β 0 z ≤
        ENNReal.ofReal (C * ‖z‖ ^ (-(6 : ℝ) + 2) * (Real.log ‖z‖)⁻¹))
    {z : Fin 6 → ℤ} (hz : 2 ≤ ‖z‖) :
    litT J hJ β z ≤ C * ‖z‖ ^ (-(6 : ℝ) + 2) * (Real.log ‖z‖)⁻¹ := by
  have hlog : 0 ≤ Real.log ‖z‖ := Real.log_nonneg (by linarith)
  have hnon : 0 ≤ C * ‖z‖ ^ (-(6 : ℝ) + 2) * (Real.log ‖z‖)⁻¹ :=
    mul_nonneg (mul_nonneg hC (Real.rpow_nonneg (norm_nonneg z) _)) (inv_nonneg.mpr hlog)
  calc litT J hJ β z = (twoPointFunction J hJ β 0 z).toReal := rfl
    _ ≤ (ENNReal.ofReal (C * ‖z‖ ^ (-(6 : ℝ) + 2) * (Real.log ‖z‖)⁻¹)).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top (hHD z hz)
    _ = C * ‖z‖ ^ (-(6 : ℝ) + 2) * (Real.log ‖z‖)⁻¹ := ENNReal.toReal_ofReal hnon

/-- **The literal (raw) Case 3 domination, read in `ℝ`.**  Same conversion at every `z ≠ 0`. -/
theorem litT_le_of_HD_raw {C : ℝ} (hC : 0 ≤ C)
    (hHD : ∀ z : Fin 6 → ℤ, z ≠ 0 →
      twoPointFunction J hJ β 0 z ≤
        ENNReal.ofReal (C * ‖z‖ ^ (-(6 : ℝ) + 2) * (Real.log ‖z‖)⁻¹))
    {z : Fin 6 → ℤ} (hz : z ≠ 0) :
    litT J hJ β z ≤ C * ‖z‖ ^ (-(6 : ℝ) + 2) * (Real.log ‖z‖)⁻¹ := by
  have hlog : 0 ≤ Real.log ‖z‖ := Real.log_nonneg (one_le_norm_of_ne_zero hz)
  have hnon : 0 ≤ C * ‖z‖ ^ (-(6 : ℝ) + 2) * (Real.log ‖z‖)⁻¹ :=
    mul_nonneg (mul_nonneg hC (Real.rpow_nonneg (norm_nonneg z) _)) (inv_nonneg.mpr hlog)
  calc litT J hJ β z = (twoPointFunction J hJ β 0 z).toReal := rfl
    _ ≤ (ENNReal.ofReal (C * ‖z‖ ^ (-(6 : ℝ) + 2) * (Real.log ‖z‖)⁻¹)).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top (hHD z hz)
    _ = C * ‖z‖ ^ (-(6 : ℝ) + 2) * (Real.log ‖z‖)⁻¹ := ENNReal.toReal_ofReal hnon

/-- **The raw convention at the unit shell, recorded.**  In Lean's real logarithm convention
`(log 1)⁻¹ = 0`, so the raw domination forces `t` to vanish on the unit shell.  This is exactly
the accidental strength that the source-shaped version avoids; it is stated here so that the raw
variant is not silently weakened. -/
theorem litT_eq_zero_of_one_le_norm_of_raw {C : ℝ} (hC : 0 ≤ C)
    (hHD : ∀ z : Fin 6 → ℤ, z ≠ 0 →
      twoPointFunction J hJ β 0 z ≤
        ENNReal.ofReal (C * ‖z‖ ^ (-(6 : ℝ) + 2) * (Real.log ‖z‖)⁻¹))
    {z : Fin 6 → ℤ} (hz : z ≠ 0) (h1 : ‖z‖ = 1) : litT J hJ β z = 0 := by
  have h := litT_le_of_HD_raw hC hHD hz
  rw [h1, Real.log_one, inv_zero, mul_zero] at h
  exact le_antisymm h (litT_nonneg J hJ β z)

/-- **The raw domination implies the source-shaped one.**  The shell hypothesis only asks for the
decay at `‖z‖ ≥ 2`, a subset of the nonzero vertices; the remaining shell input `t ≤ 1` is
automatic (`litT_le_one`).  This records that the source-shaped theorem is the stronger statement
of the two. -/
theorem case3HDShell_of_case3HDRaw {C : ℝ}
    (hHD : ∀ z : Fin 6 → ℤ, z ≠ 0 →
      twoPointFunction J hJ β 0 z ≤
        ENNReal.ofReal (C * ‖z‖ ^ (-(6 : ℝ) + 2) * (Real.log ‖z‖)⁻¹)) :
    ∀ z : Fin 6 → ℤ, 2 ≤ ‖z‖ →
      twoPointFunction J hJ β 0 z ≤
        ENNReal.ofReal (C * ‖z‖ ^ (-(6 : ℝ) + 2) * (Real.log ‖z‖)⁻¹) := by
  intro z hz
  refine hHD z (fun h => ?_)
  rw [h, norm_zero] at hz
  norm_num at hz

/-! ## §2 `ofReal` through the two `tsum`s

The bridging step is stated once for an abstract nonnegative profile with the two `Summable`
facts that the Case 3 convolution assembly provides; both input shapes then differ only in how
those facts are produced. -/

/-- **`ENNReal.ofReal` commutes with the abstract triple convolution.**  For a nonnegative real
profile `t`, if the inner convolution is summable at every `b` and the outer series is summable at
`x`, then the iterated `ℝ≥0∞` sum of the `ofReal`-images is the `ofReal` of the iterated real sum.
Both conversions are `ENNReal.ofReal_tsum_of_nonneg`, so no infinite sum is ever evaluated. -/
theorem ofReal_tsum_tripleConv (t : (Fin 6 → ℤ) → ℝ) (htnn : ∀ z, 0 ≤ t z)
    (hconv : ∀ b : Fin 6 → ℤ, Summable (fun a => t a * t (b - a))) (x : Fin 6 → ℤ)
    (htrip : Summable (fun b => (∑' a, t a * t (b - a)) * t (x - b))) :
    (∑' b, (∑' a, ENNReal.ofReal (t a) * ENNReal.ofReal (t (b - a))) *
        ENNReal.ofReal (t (x - b)))
      = ENNReal.ofReal (∑' b, (∑' a, t a * t (b - a)) * t (x - b)) := by
  trans ∑' b, ENNReal.ofReal ((∑' a, t a * t (b - a)) * t (x - b))
  · refine tsum_congr fun b => ?_
    have hinner : (∑' a, ENNReal.ofReal (t a) * ENNReal.ofReal (t (b - a)))
        = ENNReal.ofReal (∑' a, t a * t (b - a)) := by
      have hstep : (∑' a, ENNReal.ofReal (t a) * ENNReal.ofReal (t (b - a)))
          = ∑' a, ENNReal.ofReal (t a * t (b - a)) :=
        tsum_congr fun a => (ENNReal.ofReal_mul (htnn a)).symm
      rw [hstep, ENNReal.ofReal_tsum_of_nonneg (f := fun a => t a * t (b - a))
        (fun a => mul_nonneg (htnn a) (htnn (b - a))) (hconv b)]
    have htsum : 0 ≤ ∑' a, t a * t (b - a) :=
      tsum_nonneg fun a => mul_nonneg (htnn a) (htnn (b - a))
    calc (∑' a, ENNReal.ofReal (t a) * ENNReal.ofReal (t (b - a))) *
          ENNReal.ofReal (t (x - b))
        = ENNReal.ofReal (∑' a, t a * t (b - a)) * ENNReal.ofReal (t (x - b)) := by
            rw [hinner]
      _ = ENNReal.ofReal ((∑' a, t a * t (b - a)) * t (x - b)) :=
            (ENNReal.ofReal_mul htsum).symm
  · exact (ENNReal.ofReal_tsum_of_nonneg
      (fun b => mul_nonneg (tsum_nonneg fun a => mul_nonneg (htnn a) (htnn (b - a)))
        (htnn (x - b))) htrip).symm

/-! ## §3 The source-shaped (shell) case -/

/-- **The literal first convolution of `litT` is summable** under the source-shaped Case 3
domination.  This is the first `Summable` fact needed by the `ofReal`-through-`tsum` step; it is
produced by the Case 3 first-convolution assembly `convolution_two_of_wt_bound`, fed by the shell
conversion `abs_le_conv_wt_of_case3Shell`. -/
theorem summable_conv_litT_case3Shell {C : ℝ} (hC : 0 ≤ C)
    (hHD : ∀ z : Fin 6 → ℤ, 2 ≤ ‖z‖ →
      twoPointFunction J hJ β 0 z ≤
        ENNReal.ofReal (C * ‖z‖ ^ (-(6 : ℝ) + 2) * (Real.log ‖z‖)⁻¹))
    (b : Fin 6 → ℤ) :
    Summable (fun a => litT J hJ β a * litT J hJ β (b - a)) := by
  have ht : ∀ z : Fin 6 → ℤ, 2 ≤ ‖z‖ →
      litT J hJ β z ≤ C * ‖z‖ ^ (-(6 : ℝ) + 2) * (Real.log ‖z‖)⁻¹ :=
    fun z hz => litT_le_of_HD_shell hC hHD hz
  have hbd : ∀ z : Fin 6 → ℤ,
      |litT J hJ β z| ≤ case3ShellConst 6 C * Wt ((6 : ℝ) - 2) 1 ‖z‖ :=
    fun z => abs_le_conv_wt_of_case3Shell (d := 6) (by norm_num) hC
      (litT_nonneg J hJ β) (litT_le_one J hJ β) ht z
  exact (convolution_two_of_wt_bound (d := 6) (by norm_num)
    (case3ShellConst_nonneg (d := 6) hC) hbd b).1

/-- **The literal second (triple) convolution of `litT` is summable** under the source-shaped
Case 3 domination, by the marginal Case 3 assembly `triple_convolution_case3Shell`. -/
theorem summable_tripleConv_litT_case3Shell {C : ℝ} (hC : 0 ≤ C)
    (hHD : ∀ z : Fin 6 → ℤ, 2 ≤ ‖z‖ →
      twoPointFunction J hJ β 0 z ≤
        ENNReal.ofReal (C * ‖z‖ ^ (-(6 : ℝ) + 2) * (Real.log ‖z‖)⁻¹))
    (x : Fin 6 → ℤ) :
    Summable (fun b =>
      (∑' a, litT J hJ β a * litT J hJ β (b - a)) * litT J hJ β (x - b)) := by
  have ht : ∀ z : Fin 6 → ℤ, 2 ≤ ‖z‖ →
      litT J hJ β z ≤ C * ‖z‖ ^ (-(6 : ℝ) + 2) * (Real.log ‖z‖)⁻¹ :=
    fun z hz => litT_le_of_HD_shell hC hHD hz
  exact (triple_convolution_case3Shell hC (litT_nonneg J hJ β)
    (litT_le_one J hJ β) ht x).1

/-- **The literal open triangle is the `ofReal` of the abstract triple convolution of `litT`**
under the source-shaped Case 3 domination.  The two `Summable` inputs are *derived*: the inner one
from the first Case 3 convolution (`convolution_two_of_wt_bound`, fed by the shell conversion
`abs_le_conv_wt_of_case3Shell`) and the outer one from the marginal Case 3 convolution
(`triple_convolution_case3Shell`).  Only `t ≤ 1` is used for the unit shell and the origin, and it
is `litT_le_one`, a consequence of the probability normalisation. -/
theorem openTriangle_eq_ofReal_tsum_case3Shell
    (hJinv : ∀ (a : Fin 6 → ℤ) (e : Sym2 (Fin 6 → ℤ)),
      J (Sym2.map (fun x => x + a) e) = J e)
    {C : ℝ} (hC : 0 ≤ C)
    (hHD : ∀ z : Fin 6 → ℤ, 2 ≤ ‖z‖ →
      twoPointFunction J hJ β 0 z ≤
        ENNReal.ofReal (C * ‖z‖ ^ (-(6 : ℝ) + 2) * (Real.log ‖z‖)⁻¹))
    (x : Fin 6 → ℤ) :
    TriTail.openTriangle J hJ β 0 x
      = ENNReal.ofReal
          (∑' b, (∑' a, litT J hJ β a * litT J hJ β (b - a)) * litT J hJ β (x - b)) := by
  have hconv : ∀ b : Fin 6 → ℤ,
      Summable (fun a => litT J hJ β a * litT J hJ β (b - a)) :=
    fun b => summable_conv_litT_case3Shell hC hHD b
  have htrip : Summable (fun b =>
      (∑' a, litT J hJ β a * litT J hJ β (b - a)) * litT J hJ β (x - b)) :=
    summable_tripleConv_litT_case3Shell hC hHD x
  rw [openTriangle_eq_tsum_ENNReal (d := 6) hJinv x]
  simp only [← ofReal_litT]
  exact ofReal_tsum_tripleConv (litT J hJ β) (litT_nonneg J hJ β) hconv x htrip

/-- **The real-valued open triangle *is* the abstract triple convolution of `litT`** (shell
input).  This is the `ℝ`-level form of the identification, licensed by the derived finiteness
`openTriangle_ne_top_case3Shell`. -/
theorem openTriangle_toReal_eq_tripleConv_case3Shell
    (hJinv : ∀ (a : Fin 6 → ℤ) (e : Sym2 (Fin 6 → ℤ)),
      J (Sym2.map (fun x => x + a) e) = J e)
    {C : ℝ} (hC : 0 ≤ C)
    (hHD : ∀ z : Fin 6 → ℤ, 2 ≤ ‖z‖ →
      twoPointFunction J hJ β 0 z ≤
        ENNReal.ofReal (C * ‖z‖ ^ (-(6 : ℝ) + 2) * (Real.log ‖z‖)⁻¹))
    (x : Fin 6 → ℤ) :
    (TriTail.openTriangle J hJ β 0 x).toReal
      = ∑' b, (∑' a, litT J hJ β a * litT J hJ β (b - a)) * litT J hJ β (x - b) := by
  rw [openTriangle_eq_ofReal_tsum_case3Shell hJinv hC hHD x, ENNReal.toReal_ofReal]
  exact tsum_nonneg fun b =>
    mul_nonneg (tsum_nonneg fun a =>
      mul_nonneg (litT_nonneg J hJ β a) (litT_nonneg J hJ β (b - a)))
      (litT_nonneg J hJ β (x - b))

/-- **The literal open triangle bound in square-logarithmic form (shell input).** -/
theorem openTriangle_le_ofReal_wt_case3Shell
    (hJinv : ∀ (a : Fin 6 → ℤ) (e : Sym2 (Fin 6 → ℤ)),
      J (Sym2.map (fun x => x + a) e) = J e)
    {C : ℝ} (hC : 0 ≤ C)
    (hHD : ∀ z : Fin 6 → ℤ, 2 ≤ ‖z‖ →
      twoPointFunction J hJ β 0 z ≤
        ENNReal.ofReal (C * ‖z‖ ^ (-(6 : ℝ) + 2) * (Real.log ‖z‖)⁻¹))
    (x : Fin 6 → ℤ) :
    TriTail.openTriangle J hJ β 0 x
      ≤ ENNReal.ofReal (case3Conv3ConstShell C * Wt 0 2 ‖x‖) := by
  have ht : ∀ z : Fin 6 → ℤ, 2 ≤ ‖z‖ →
      litT J hJ β z ≤ C * ‖z‖ ^ (-(6 : ℝ) + 2) * (Real.log ‖z‖)⁻¹ :=
    fun z hz => litT_le_of_HD_shell hC hHD hz
  rw [openTriangle_eq_ofReal_tsum_case3Shell hJinv hC hHD x]
  refine ENNReal.ofReal_le_ofReal ?_
  have h := (triple_convolution_case3Shell hC (litT_nonneg J hJ β)
    (litT_le_one J hJ β) ht x).2
  exact (le_abs_self _).trans h

/-- **The literal open triangle is finite** under the source-shaped Case 3 domination.  Derived
from the explicit bound, not assumed and not obtained by a `⊤.toReal = 0` convention. -/
theorem openTriangle_ne_top_case3Shell
    (hJinv : ∀ (a : Fin 6 → ℤ) (e : Sym2 (Fin 6 → ℤ)),
      J (Sym2.map (fun x => x + a) e) = J e)
    {C : ℝ} (hC : 0 ≤ C)
    (hHD : ∀ z : Fin 6 → ℤ, 2 ≤ ‖z‖ →
      twoPointFunction J hJ β 0 z ≤
        ENNReal.ofReal (C * ‖z‖ ^ (-(6 : ℝ) + 2) * (Real.log ‖z‖)⁻¹))
    (x : Fin 6 → ℤ) : TriTail.openTriangle J hJ β 0 x ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    (openTriangle_le_ofReal_wt_case3Shell hJinv hC hHD x)

/-! ## §4 From the square-logarithmic `Wt` bound to `logMajorant` -/

/-- **`Wt 0 2` is the square-logarithmic majorant.**  For positive radius,
`K · Wt 0 2 r = K (log (2 + r))⁻² ≤ K (log (1 + r))⁻² = logMajorant K 2 r`.  The inequality
direction uses `log (1 + r) ≤ log (2 + r)` and the antitonicity of `x ↦ x⁻²` on `(0, ∞)`; it is
false at `r = 0`, where `logMajorant K 2 0 = 0`, which is why every pointwise statement below
carries `x ≠ 0`. -/
theorem mul_Wt_zero_two_le_logMajorant {K r : ℝ} (hK : 0 ≤ K) (hr : 0 < r) :
    K * Wt 0 2 r ≤ Analysis.logMajorant K 2 r := by
  have hWt : Wt 0 2 r = Real.log (2 + r) ^ (-2 : ℝ) := by
    simp [Wt, LamR]
  have hmono : Real.log (1 + r) ≤ Real.log (2 + r) :=
    Real.log_le_log (by linarith) (by linarith)
  have hp : 0 < Real.log (1 + r) := Real.log_pos (by linarith)
  have hle : Real.log (2 + r) ^ (-2 : ℝ) ≤ Real.log (1 + r) ^ (-2 : ℝ) :=
    Real.rpow_le_rpow_of_nonpos hp hmono (by norm_num)
  rw [hWt]
  calc K * Real.log (2 + r) ^ (-2 : ℝ) ≤ K * Real.log (1 + r) ^ (-2 : ℝ) :=
        mul_le_mul_of_nonneg_left hle hK
    _ = Analysis.logMajorant K 2 r := by simp [Analysis.logMajorant]

/-- **The pointwise square-logarithmic bound at the literal open triangle (shell input)**:
`∇ x ≤ ofReal (case3Conv3ConstShell C · (log (1 + ‖x‖))⁻²)` for `x ≠ 0`. -/
theorem openTriangle_le_ofReal_logMajorant_case3Shell
    (hJinv : ∀ (a : Fin 6 → ℤ) (e : Sym2 (Fin 6 → ℤ)),
      J (Sym2.map (fun x => x + a) e) = J e)
    {C : ℝ} (hC : 0 ≤ C)
    (hHD : ∀ z : Fin 6 → ℤ, 2 ≤ ‖z‖ →
      twoPointFunction J hJ β 0 z ≤
        ENNReal.ofReal (C * ‖z‖ ^ (-(6 : ℝ) + 2) * (Real.log ‖z‖)⁻¹))
    {x : Fin 6 → ℤ} (hx : x ≠ 0) :
    TriTail.openTriangle J hJ β 0 x
      ≤ ENNReal.ofReal (Analysis.logMajorant (case3Conv3ConstShell C) 2 ‖x‖) := by
  refine (openTriangle_le_ofReal_wt_case3Shell hJinv hC hHD x).trans ?_
  refine ENNReal.ofReal_le_ofReal ?_
  exact mul_Wt_zero_two_le_logMajorant (case3Conv3ConstShell_nonneg hC)
    (norm_pos_iff.mpr hx)

/-- **The pointwise square-logarithmic bound with the logarithm displayed (shell input).** -/
theorem openTriangle_le_ofReal_log_sq_case3Shell
    (hJinv : ∀ (a : Fin 6 → ℤ) (e : Sym2 (Fin 6 → ℤ)),
      J (Sym2.map (fun x => x + a) e) = J e)
    {C : ℝ} (hC : 0 ≤ C)
    (hHD : ∀ z : Fin 6 → ℤ, 2 ≤ ‖z‖ →
      twoPointFunction J hJ β 0 z ≤
        ENNReal.ofReal (C * ‖z‖ ^ (-(6 : ℝ) + 2) * (Real.log ‖z‖)⁻¹))
    {x : Fin 6 → ℤ} (hx : x ≠ 0) :
    TriTail.openTriangle J hJ β 0 x
      ≤ ENNReal.ofReal (case3Conv3ConstShell C * (Real.log (1 + ‖x‖)) ^ (-2 : ℝ)) := by
  simpa only [Analysis.logMajorant] using
    openTriangle_le_ofReal_logMajorant_case3Shell hJinv hC hHD hx

/-- **The `LogRadialBound` predicate for the literal open triangle at the `ℓ^∞` radius**, which
is exactly the pointwise hypothesis consumed by `Analysis.isLogErrorFunction_radialTailSup`. -/
theorem logRadialBound_openTriangle_case3Shell
    (hJinv : ∀ (a : Fin 6 → ℤ) (e : Sym2 (Fin 6 → ℤ)),
      J (Sym2.map (fun x => x + a) e) = J e)
    {C : ℝ} (hC : 0 ≤ C)
    (hHD : ∀ z : Fin 6 → ℤ, 2 ≤ ‖z‖ →
      twoPointFunction J hJ β 0 z ≤
        ENNReal.ofReal (C * ‖z‖ ^ (-(6 : ℝ) + 2) * (Real.log ‖z‖)⁻¹)) :
    Analysis.LogRadialBound (fun x : Fin 6 → ℤ => FiniteVolume.latticeDist 0 x)
      (fun x : Fin 6 → ℤ => TriTail.openTriangle J hJ β 0 x) (case3Conv3ConstShell C) 2 := by
  intro x hx
  have hx0 : x ≠ 0 := by
    rintro rfl
    have hx' : 0 < FiniteVolume.latticeDist 0 (0 : Fin 6 → ℤ) := hx
    rw [FiniteVolume.latticeDist_self] at hx'
    exact lt_irrefl 0 hx'
  have hdist : FiniteVolume.latticeDist 0 x = ‖x‖ := by
    rw [FiniteVolume.latticeDist, show (0 : Fin 6 → ℤ) - x = -x from by simp,
      FiniteVolume.linfNorm_neg]
    exact (CriticalLRPConv.coe_norm_eq_linfNorm x).symm
  simp only [] at hx
  dsimp only
  rw [hdist]
  exact openTriangle_le_ofReal_logMajorant_case3Shell hJinv hC hHD hx0

/-! ## §5 The plain sup-norm tail (shell input) -/

/-- **The tail inherits the square-logarithmic bound** at every `r > 0`, with the radius predicate
`r ≤ latticeDist 0 x` untouched. -/
theorem openTriangleTail_le_logMajorant_case3Shell
    (hJinv : ∀ (a : Fin 6 → ℤ) (e : Sym2 (Fin 6 → ℤ)),
      J (Sym2.map (fun x => x + a) e) = J e)
    {C : ℝ} (hC : 0 ≤ C)
    (hHD : ∀ z : Fin 6 → ℤ, 2 ≤ ‖z‖ →
      twoPointFunction J hJ β 0 z ≤
        ENNReal.ofReal (C * ‖z‖ ^ (-(6 : ℝ) + 2) * (Real.log ‖z‖)⁻¹))
    {r : ℝ} (hr : 0 < r) :
    TriTail.openTriangleTail J hJ β r
      ≤ ENNReal.ofReal (Analysis.logMajorant (case3Conv3ConstShell C) 2 r) := by
  have hmain := Analysis.radialTailSup_le_logMajorant
    (nrm := fun x : Fin 6 → ℤ => FiniteVolume.latticeDist 0 x)
    (F := fun x : Fin 6 → ℤ => TriTail.openTriangle J hJ β 0 x)
    (case3Conv3ConstShell_nonneg hC) (by norm_num : (0 : ℝ) ≤ 2) hr
    (logRadialBound_openTriangle_case3Shell hJinv hC hHD)
  simpa only [TriTail.openTriangleTail_eq_radialTailSup] using hmain

/-- **The real-valued tail bound** `(openTriangleTail r).toReal ≤ K (log (1 + r))⁻²`. -/
theorem openTriangleTail_toReal_le_logMajorant_case3Shell
    (hJinv : ∀ (a : Fin 6 → ℤ) (e : Sym2 (Fin 6 → ℤ)),
      J (Sym2.map (fun x => x + a) e) = J e)
    {C : ℝ} (hC : 0 ≤ C)
    (hHD : ∀ z : Fin 6 → ℤ, 2 ≤ ‖z‖ →
      twoPointFunction J hJ β 0 z ≤
        ENNReal.ofReal (C * ‖z‖ ^ (-(6 : ℝ) + 2) * (Real.log ‖z‖)⁻¹))
    {r : ℝ} (hr : 0 < r) :
    (TriTail.openTriangleTail J hJ β r).toReal
      ≤ Analysis.logMajorant (case3Conv3ConstShell C) 2 r := by
  have hmain := Analysis.radialTailSup_toReal_le
    (nrm := fun x : Fin 6 → ℤ => FiniteVolume.latticeDist 0 x)
    (F := fun x : Fin 6 → ℤ => TriTail.openTriangle J hJ β 0 x)
    (case3Conv3ConstShell_nonneg hC) (by norm_num : (0 : ℝ) ≤ 2) hr
    (logRadialBound_openTriangle_case3Shell hJinv hC hHD)
  simpa only [TriTail.openTriangleTail_eq_radialTailSup] using hmain

/-- **The plain sup-norm open-triangle tail is a logarithmically integrable error function**
(Case 3 of `(HD)`, Lemma I.4.3 shape) under the source-shaped domination.  The exponent `p = 2`
comes from the two inverse logarithms produced by the strict-then-marginal Case 3 chain. -/
theorem isLogErrorFunction_openTriangleTail_case3Shell
    (hJinv : ∀ (a : Fin 6 → ℤ) (e : Sym2 (Fin 6 → ℤ)),
      J (Sym2.map (fun x => x + a) e) = J e)
    {C : ℝ} (hC : 0 ≤ C)
    (hHD : ∀ z : Fin 6 → ℤ, 2 ≤ ‖z‖ →
      twoPointFunction J hJ β 0 z ≤
        ENNReal.ofReal (C * ‖z‖ ^ (-(6 : ℝ) + 2) * (Real.log ‖z‖)⁻¹)) :
    Analysis.IsLogErrorFunction (fun r => (TriTail.openTriangleTail J hJ β r).toReal) := by
  have hmain := Analysis.isLogErrorFunction_radialTailSup
    (nrm := fun x : Fin 6 → ℤ => FiniteVolume.latticeDist 0 x)
    (F := fun x : Fin 6 → ℤ => TriTail.openTriangle J hJ β 0 x)
    (case3Conv3ConstShell_nonneg hC) (by norm_num : (1 : ℝ) < 2)
    (logRadialBound_openTriangle_case3Shell hJinv hC hHD)
  simpa only [TriTail.openTriangleTail_eq_radialTailSup] using hmain

/-- The two conjuncts of `IsLogErrorFunction` displayed separately: logarithmic integrability
`∫^∞ |∇_r| dr / r < ∞` and `∇_r → 0`. -/
theorem openTriangleTail_logIntegrable_case3Shell
    (hJinv : ∀ (a : Fin 6 → ℤ) (e : Sym2 (Fin 6 → ℤ)),
      J (Sym2.map (fun x => x + a) e) = J e)
    {C : ℝ} (hC : 0 ≤ C)
    (hHD : ∀ z : Fin 6 → ℤ, 2 ≤ ‖z‖ →
      twoPointFunction J hJ β 0 z ≤
        ENNReal.ofReal (C * ‖z‖ ^ (-(6 : ℝ) + 2) * (Real.log ‖z‖)⁻¹)) :
    Analysis.LogarithmicallyIntegrable (fun r => (TriTail.openTriangleTail J hJ β r).toReal) ∧
      Tendsto (fun r => (TriTail.openTriangleTail J hJ β r).toReal) atTop (𝓝 0) :=
  isLogErrorFunction_openTriangleTail_case3Shell hJinv hC hHD

/-! ## §6 The literal (raw) case -/

/-- **The literal first convolution of `litT` is summable** under the raw Case 3 domination
(`convolution_two_case3`). -/
theorem summable_conv_litT_case3Raw {C : ℝ} (hC : 0 ≤ C)
    (hHD : ∀ z : Fin 6 → ℤ, z ≠ 0 →
      twoPointFunction J hJ β 0 z ≤
        ENNReal.ofReal (C * ‖z‖ ^ (-(6 : ℝ) + 2) * (Real.log ‖z‖)⁻¹))
    (b : Fin 6 → ℤ) :
    Summable (fun a => litT J hJ β a * litT J hJ β (b - a)) := by
  have ht : ∀ z : Fin 6 → ℤ, z ≠ 0 →
      litT J hJ β z ≤ C * ‖z‖ ^ (-(6 : ℝ) + 2) * (Real.log ‖z‖)⁻¹ :=
    fun z hz => litT_le_of_HD_raw hC hHD hz
  exact (convolution_two_case3 (d := 6) (by norm_num) hC (litT_nonneg J hJ β)
    (litT_zero J hJ β) ht b).1

/-- **The literal second (triple) convolution of `litT` is summable** under the raw Case 3
domination (`triple_convolution_case3`). -/
theorem summable_tripleConv_litT_case3Raw {C : ℝ} (hC : 0 ≤ C)
    (hHD : ∀ z : Fin 6 → ℤ, z ≠ 0 →
      twoPointFunction J hJ β 0 z ≤
        ENNReal.ofReal (C * ‖z‖ ^ (-(6 : ℝ) + 2) * (Real.log ‖z‖)⁻¹))
    (x : Fin 6 → ℤ) :
    Summable (fun b =>
      (∑' a, litT J hJ β a * litT J hJ β (b - a)) * litT J hJ β (x - b)) := by
  have ht : ∀ z : Fin 6 → ℤ, z ≠ 0 →
      litT J hJ β z ≤ C * ‖z‖ ^ (-(6 : ℝ) + 2) * (Real.log ‖z‖)⁻¹ :=
    fun z hz => litT_le_of_HD_raw hC hHD hz
  exact (triple_convolution_case3 hC (litT_nonneg J hJ β) (litT_zero J hJ β) ht x).1

/-- **The literal open triangle is the `ofReal` of the abstract triple convolution of `litT`**
under the literal domination at every `z ≠ 0`.  The inner summability is the first raw Case 3
convolution `convolution_two_case3` and the outer one is `triple_convolution_case3`. -/
theorem openTriangle_eq_ofReal_tsum_case3Raw
    (hJinv : ∀ (a : Fin 6 → ℤ) (e : Sym2 (Fin 6 → ℤ)),
      J (Sym2.map (fun x => x + a) e) = J e)
    {C : ℝ} (hC : 0 ≤ C)
    (hHD : ∀ z : Fin 6 → ℤ, z ≠ 0 →
      twoPointFunction J hJ β 0 z ≤
        ENNReal.ofReal (C * ‖z‖ ^ (-(6 : ℝ) + 2) * (Real.log ‖z‖)⁻¹))
    (x : Fin 6 → ℤ) :
    TriTail.openTriangle J hJ β 0 x
      = ENNReal.ofReal
          (∑' b, (∑' a, litT J hJ β a * litT J hJ β (b - a)) * litT J hJ β (x - b)) := by
  have hconv : ∀ b : Fin 6 → ℤ,
      Summable (fun a => litT J hJ β a * litT J hJ β (b - a)) :=
    fun b => summable_conv_litT_case3Raw hC hHD b
  have htrip : Summable (fun b =>
      (∑' a, litT J hJ β a * litT J hJ β (b - a)) * litT J hJ β (x - b)) :=
    summable_tripleConv_litT_case3Raw hC hHD x
  rw [openTriangle_eq_tsum_ENNReal (d := 6) hJinv x]
  simp only [← ofReal_litT]
  exact ofReal_tsum_tripleConv (litT J hJ β) (litT_nonneg J hJ β) hconv x htrip

/-- **The real-valued open triangle *is* the abstract triple convolution of `litT`** (raw
input). -/
theorem openTriangle_toReal_eq_tripleConv_case3Raw
    (hJinv : ∀ (a : Fin 6 → ℤ) (e : Sym2 (Fin 6 → ℤ)),
      J (Sym2.map (fun x => x + a) e) = J e)
    {C : ℝ} (hC : 0 ≤ C)
    (hHD : ∀ z : Fin 6 → ℤ, z ≠ 0 →
      twoPointFunction J hJ β 0 z ≤
        ENNReal.ofReal (C * ‖z‖ ^ (-(6 : ℝ) + 2) * (Real.log ‖z‖)⁻¹))
    (x : Fin 6 → ℤ) :
    (TriTail.openTriangle J hJ β 0 x).toReal
      = ∑' b, (∑' a, litT J hJ β a * litT J hJ β (b - a)) * litT J hJ β (x - b) := by
  rw [openTriangle_eq_ofReal_tsum_case3Raw hJinv hC hHD x, ENNReal.toReal_ofReal]
  exact tsum_nonneg fun b =>
    mul_nonneg (tsum_nonneg fun a =>
      mul_nonneg (litT_nonneg J hJ β a) (litT_nonneg J hJ β (b - a)))
      (litT_nonneg J hJ β (x - b))

/-- **The literal open triangle bound in square-logarithmic form (raw input).** -/
theorem openTriangle_le_ofReal_wt_case3Raw
    (hJinv : ∀ (a : Fin 6 → ℤ) (e : Sym2 (Fin 6 → ℤ)),
      J (Sym2.map (fun x => x + a) e) = J e)
    {C : ℝ} (hC : 0 ≤ C)
    (hHD : ∀ z : Fin 6 → ℤ, z ≠ 0 →
      twoPointFunction J hJ β 0 z ≤
        ENNReal.ofReal (C * ‖z‖ ^ (-(6 : ℝ) + 2) * (Real.log ‖z‖)⁻¹))
    (x : Fin 6 → ℤ) :
    TriTail.openTriangle J hJ β 0 x
      ≤ ENNReal.ofReal (case3Conv3Const C * Wt 0 2 ‖x‖) := by
  have ht : ∀ z : Fin 6 → ℤ, z ≠ 0 →
      litT J hJ β z ≤ C * ‖z‖ ^ (-(6 : ℝ) + 2) * (Real.log ‖z‖)⁻¹ :=
    fun z hz => litT_le_of_HD_raw hC hHD hz
  rw [openTriangle_eq_ofReal_tsum_case3Raw hJinv hC hHD x]
  refine ENNReal.ofReal_le_ofReal ?_
  have h := (triple_convolution_case3 hC (litT_nonneg J hJ β) (litT_zero J hJ β) ht x).2
  exact (le_abs_self _).trans h

/-- **The literal open triangle is finite** under the raw Case 3 domination. -/
theorem openTriangle_ne_top_case3Raw
    (hJinv : ∀ (a : Fin 6 → ℤ) (e : Sym2 (Fin 6 → ℤ)),
      J (Sym2.map (fun x => x + a) e) = J e)
    {C : ℝ} (hC : 0 ≤ C)
    (hHD : ∀ z : Fin 6 → ℤ, z ≠ 0 →
      twoPointFunction J hJ β 0 z ≤
        ENNReal.ofReal (C * ‖z‖ ^ (-(6 : ℝ) + 2) * (Real.log ‖z‖)⁻¹))
    (x : Fin 6 → ℤ) : TriTail.openTriangle J hJ β 0 x ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    (openTriangle_le_ofReal_wt_case3Raw hJinv hC hHD x)

/-- **The pointwise square-logarithmic bound at the literal open triangle (raw input)**:
`∇ x ≤ ofReal (case3Conv3Const C · (log (1 + ‖x‖))⁻²)` for `x ≠ 0`. -/
theorem openTriangle_le_ofReal_logMajorant_case3Raw
    (hJinv : ∀ (a : Fin 6 → ℤ) (e : Sym2 (Fin 6 → ℤ)),
      J (Sym2.map (fun x => x + a) e) = J e)
    {C : ℝ} (hC : 0 ≤ C)
    (hHD : ∀ z : Fin 6 → ℤ, z ≠ 0 →
      twoPointFunction J hJ β 0 z ≤
        ENNReal.ofReal (C * ‖z‖ ^ (-(6 : ℝ) + 2) * (Real.log ‖z‖)⁻¹))
    {x : Fin 6 → ℤ} (hx : x ≠ 0) :
    TriTail.openTriangle J hJ β 0 x
      ≤ ENNReal.ofReal (Analysis.logMajorant (case3Conv3Const C) 2 ‖x‖) := by
  refine (openTriangle_le_ofReal_wt_case3Raw hJinv hC hHD x).trans ?_
  refine ENNReal.ofReal_le_ofReal ?_
  exact mul_Wt_zero_two_le_logMajorant (case3Conv3Const_nonneg hC) (norm_pos_iff.mpr hx)

/-- **The pointwise square-logarithmic bound with the logarithm displayed (raw input).** -/
theorem openTriangle_le_ofReal_log_sq_case3Raw
    (hJinv : ∀ (a : Fin 6 → ℤ) (e : Sym2 (Fin 6 → ℤ)),
      J (Sym2.map (fun x => x + a) e) = J e)
    {C : ℝ} (hC : 0 ≤ C)
    (hHD : ∀ z : Fin 6 → ℤ, z ≠ 0 →
      twoPointFunction J hJ β 0 z ≤
        ENNReal.ofReal (C * ‖z‖ ^ (-(6 : ℝ) + 2) * (Real.log ‖z‖)⁻¹))
    {x : Fin 6 → ℤ} (hx : x ≠ 0) :
    TriTail.openTriangle J hJ β 0 x
      ≤ ENNReal.ofReal (case3Conv3Const C * (Real.log (1 + ‖x‖)) ^ (-2 : ℝ)) := by
  simpa only [Analysis.logMajorant] using
    openTriangle_le_ofReal_logMajorant_case3Raw hJinv hC hHD hx

/-- **The `LogRadialBound` predicate for the literal open triangle (raw input).** -/
theorem logRadialBound_openTriangle_case3Raw
    (hJinv : ∀ (a : Fin 6 → ℤ) (e : Sym2 (Fin 6 → ℤ)),
      J (Sym2.map (fun x => x + a) e) = J e)
    {C : ℝ} (hC : 0 ≤ C)
    (hHD : ∀ z : Fin 6 → ℤ, z ≠ 0 →
      twoPointFunction J hJ β 0 z ≤
        ENNReal.ofReal (C * ‖z‖ ^ (-(6 : ℝ) + 2) * (Real.log ‖z‖)⁻¹)) :
    Analysis.LogRadialBound (fun x : Fin 6 → ℤ => FiniteVolume.latticeDist 0 x)
      (fun x : Fin 6 → ℤ => TriTail.openTriangle J hJ β 0 x) (case3Conv3Const C) 2 := by
  intro x hx
  have hx0 : x ≠ 0 := by
    rintro rfl
    have hx' : 0 < FiniteVolume.latticeDist 0 (0 : Fin 6 → ℤ) := hx
    rw [FiniteVolume.latticeDist_self] at hx'
    exact lt_irrefl 0 hx'
  have hdist : FiniteVolume.latticeDist 0 x = ‖x‖ := by
    rw [FiniteVolume.latticeDist, show (0 : Fin 6 → ℤ) - x = -x from by simp,
      FiniteVolume.linfNorm_neg]
    exact (CriticalLRPConv.coe_norm_eq_linfNorm x).symm
  simp only [] at hx
  dsimp only
  rw [hdist]
  exact openTriangle_le_ofReal_logMajorant_case3Raw hJinv hC hHD hx0

/-- **The plain sup-norm tail is a logarithmic error function (raw input).** -/
theorem isLogErrorFunction_openTriangleTail_case3Raw
    (hJinv : ∀ (a : Fin 6 → ℤ) (e : Sym2 (Fin 6 → ℤ)),
      J (Sym2.map (fun x => x + a) e) = J e)
    {C : ℝ} (hC : 0 ≤ C)
    (hHD : ∀ z : Fin 6 → ℤ, z ≠ 0 →
      twoPointFunction J hJ β 0 z ≤
        ENNReal.ofReal (C * ‖z‖ ^ (-(6 : ℝ) + 2) * (Real.log ‖z‖)⁻¹)) :
    Analysis.IsLogErrorFunction (fun r => (TriTail.openTriangleTail J hJ β r).toReal) := by
  have hmain := Analysis.isLogErrorFunction_radialTailSup
    (nrm := fun x : Fin 6 → ℤ => FiniteVolume.latticeDist 0 x)
    (F := fun x : Fin 6 → ℤ => TriTail.openTriangle J hJ β 0 x)
    (case3Conv3Const_nonneg hC) (by norm_num : (1 : ℝ) < 2)
    (logRadialBound_openTriangle_case3Raw hJinv hC hHD)
  simpa only [TriTail.openTriangleTail_eq_radialTailSup] using hmain

/-! ## §7 The packaged bridge -/

/-- **The literal Case 3 bridge, source-shaped input, packaged.**  One statement carrying items
1–4: the identification with the abstract triple convolution (and the derived finiteness), the
pointwise square-logarithmic bound at the literal object with the explicit constant
`case3Conv3ConstShell C`, and the `IsLogErrorFunction` conclusion at the plain `ℓ^∞` tail. -/
theorem case3LiteralBridge_case3Shell
    (hJinv : ∀ (a : Fin 6 → ℤ) (e : Sym2 (Fin 6 → ℤ)),
      J (Sym2.map (fun x => x + a) e) = J e)
    {C : ℝ} (hC : 0 ≤ C)
    (hHD : ∀ z : Fin 6 → ℤ, 2 ≤ ‖z‖ →
      twoPointFunction J hJ β 0 z ≤
        ENNReal.ofReal (C * ‖z‖ ^ (-(6 : ℝ) + 2) * (Real.log ‖z‖)⁻¹)) :
    (∀ x : Fin 6 → ℤ, TriTail.openTriangle J hJ β 0 x =
        ENNReal.ofReal (∑' b, (∑' a, litT J hJ β a * litT J hJ β (b - a)) *
          litT J hJ β (x - b)) ∧
      TriTail.openTriangle J hJ β 0 x ≠ ⊤) ∧
    (∀ x : Fin 6 → ℤ, x ≠ 0 → TriTail.openTriangle J hJ β 0 x ≤
        ENNReal.ofReal (case3Conv3ConstShell C * (Real.log (1 + ‖x‖)) ^ (-2 : ℝ))) ∧
    Analysis.IsLogErrorFunction (fun r => (TriTail.openTriangleTail J hJ β r).toReal) :=
  ⟨fun x => ⟨openTriangle_eq_ofReal_tsum_case3Shell hJinv hC hHD x,
      openTriangle_ne_top_case3Shell hJinv hC hHD x⟩,
    fun _x hx => openTriangle_le_ofReal_log_sq_case3Shell hJinv hC hHD hx,
    isLogErrorFunction_openTriangleTail_case3Shell hJinv hC hHD⟩

/-- **The literal Case 3 bridge, raw input, packaged.**  Same content under the literal
domination at every `z ≠ 0`; recall `litT_eq_zero_of_one_le_norm_of_raw` for the unit shell. -/
theorem case3LiteralBridge_case3Raw
    (hJinv : ∀ (a : Fin 6 → ℤ) (e : Sym2 (Fin 6 → ℤ)),
      J (Sym2.map (fun x => x + a) e) = J e)
    {C : ℝ} (hC : 0 ≤ C)
    (hHD : ∀ z : Fin 6 → ℤ, z ≠ 0 →
      twoPointFunction J hJ β 0 z ≤
        ENNReal.ofReal (C * ‖z‖ ^ (-(6 : ℝ) + 2) * (Real.log ‖z‖)⁻¹)) :
    (∀ x : Fin 6 → ℤ, TriTail.openTriangle J hJ β 0 x =
        ENNReal.ofReal (∑' b, (∑' a, litT J hJ β a * litT J hJ β (b - a)) *
          litT J hJ β (x - b)) ∧
      TriTail.openTriangle J hJ β 0 x ≠ ⊤) ∧
    (∀ x : Fin 6 → ℤ, x ≠ 0 → TriTail.openTriangle J hJ β 0 x ≤
        ENNReal.ofReal (case3Conv3Const C * (Real.log (1 + ‖x‖)) ^ (-2 : ℝ))) ∧
    Analysis.IsLogErrorFunction (fun r => (TriTail.openTriangleTail J hJ β r).toReal) :=
  ⟨fun x => ⟨openTriangle_eq_ofReal_tsum_case3Raw hJinv hC hHD x,
      openTriangle_ne_top_case3Raw hJinv hC hHD x⟩,
    fun _x hx => openTriangle_le_ofReal_log_sq_case3Raw hJinv hC hHD hx,
    isLogErrorFunction_openTriangleTail_case3Raw hJinv hC hHD⟩

/-! ## §8 Axiom audit

Every named result of this packet is expected to depend only on Lean's three standard axioms
`propext`, `Classical.choice` and `Quot.sound`; there is no `sorry`, `admit`, `native_decide`,
custom axiom or `Frozen` occurrence anywhere in the file. -/
#print axioms PercLib.CriticalLRP.Orchestration.HD.summable_conv_litT_case3Shell
#print axioms PercLib.CriticalLRP.Orchestration.HD.summable_tripleConv_litT_case3Shell
#print axioms PercLib.CriticalLRP.Orchestration.HD.openTriangle_toReal_eq_tripleConv_case3Shell
#print axioms PercLib.CriticalLRP.Orchestration.HD.openTriangle_le_ofReal_log_sq_case3Shell
#print axioms PercLib.CriticalLRP.Orchestration.HD.summable_conv_litT_case3Raw
#print axioms PercLib.CriticalLRP.Orchestration.HD.summable_tripleConv_litT_case3Raw
#print axioms PercLib.CriticalLRP.Orchestration.HD.openTriangle_toReal_eq_tripleConv_case3Raw
#print axioms PercLib.CriticalLRP.Orchestration.HD.openTriangle_le_ofReal_log_sq_case3Raw
#print axioms PercLib.CriticalLRP.Orchestration.HD.case3LiteralBridge_case3Shell
#print axioms PercLib.CriticalLRP.Orchestration.HD.case3LiteralBridge_case3Raw
#print axioms PercLib.CriticalLRP.Orchestration.HD.one_le_norm_of_ne_zero
#print axioms PercLib.CriticalLRP.Orchestration.HD.litT_le_of_HD_shell
#print axioms PercLib.CriticalLRP.Orchestration.HD.litT_le_of_HD_raw
#print axioms PercLib.CriticalLRP.Orchestration.HD.case3HDShell_of_case3HDRaw
#print axioms PercLib.CriticalLRP.Orchestration.HD.litT_eq_zero_of_one_le_norm_of_raw
#print axioms PercLib.CriticalLRP.Orchestration.HD.ofReal_tsum_tripleConv
#print axioms PercLib.CriticalLRP.Orchestration.HD.openTriangle_eq_ofReal_tsum_case3Shell
#print axioms PercLib.CriticalLRP.Orchestration.HD.openTriangle_le_ofReal_wt_case3Shell
#print axioms PercLib.CriticalLRP.Orchestration.HD.openTriangle_ne_top_case3Shell
#print axioms PercLib.CriticalLRP.Orchestration.HD.mul_Wt_zero_two_le_logMajorant
#print axioms PercLib.CriticalLRP.Orchestration.HD.openTriangle_le_ofReal_logMajorant_case3Shell
#print axioms PercLib.CriticalLRP.Orchestration.HD.logRadialBound_openTriangle_case3Shell
#print axioms PercLib.CriticalLRP.Orchestration.HD.openTriangleTail_le_logMajorant_case3Shell
#print axioms PercLib.CriticalLRP.Orchestration.HD.openTriangleTail_toReal_le_logMajorant_case3Shell
#print axioms PercLib.CriticalLRP.Orchestration.HD.isLogErrorFunction_openTriangleTail_case3Shell
#print axioms PercLib.CriticalLRP.Orchestration.HD.openTriangleTail_logIntegrable_case3Shell
#print axioms PercLib.CriticalLRP.Orchestration.HD.openTriangle_eq_ofReal_tsum_case3Raw
#print axioms PercLib.CriticalLRP.Orchestration.HD.openTriangle_le_ofReal_wt_case3Raw
#print axioms PercLib.CriticalLRP.Orchestration.HD.openTriangle_ne_top_case3Raw
#print axioms PercLib.CriticalLRP.Orchestration.HD.openTriangle_le_ofReal_logMajorant_case3Raw
#print axioms PercLib.CriticalLRP.Orchestration.HD.logRadialBound_openTriangle_case3Raw
#print axioms PercLib.CriticalLRP.Orchestration.HD.isLogErrorFunction_openTriangleTail_case3Raw

end PercLib.CriticalLRP.Orchestration.HD
