/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

# The Gram-tail computation: `Γ_f ^ 3` is the autocorrelation of `f * f * f`

Integrated and independently rebuilt from accepted Ultramath `smwyq4kak`, member `m1`,
direction `d1`, at production base `860204bba022fa59110751d428c2bd8f123ad604`.
The profile and convolution definitions are in `TriTailConvolution.Defs`.

`TriTailNormalization` derives the *finiteness* of the open triangle (`hTri`) from a nonnegative
summable autocorrelation profile `f` (`twoPointFunction = gramKernel f`).  Its own docstring says the
other §I.4.1 input, the tail vanishing `∇_r → 0`, is not derived there: `∇(0,·)` should be the
autocorrelation of the triple convolution `f * f * f`, and the chain of `conv_assoc` / `conv_comm` /
`refl` rewrites showing it was left undone.  This file does that chain, and then feeds the result to
`TriTailSqrt.openTriangleTail_tendsto_of_sqrtKernel`.

Contents.

* `ofRealFn f` — a real profile as an `ℝ≥0∞`-valued function; `tripleConv f` — the triple lattice
  convolution `f * f * f` as a real number, `tripleConv f x = ∑_p (∑_q f q * f (p - q)) * f (x - p)`.
* `conv_ofRealFn_apply`, `conv3_ofRealFn_apply` — the `ofReal` conversion of the double and triple
  convolution (only `0 ≤ f` summable is used).
* `summable_tripleConv`, `tsum_tripleConv` — `f * f * f` is summable with total mass `(∑ f) ^ 3`
  (the `ℓ¹`-algebra closure, proved through the `ℝ≥0∞` convolution, where no summability is needed).
* `summable_tripleConv_sq` — `f * f * f ∈ ℓ²`.
* `refl_conv`, `refl_refl`, `conv_exchange`, `tsum_conv`, `gramKernel_eq_gramProfile`,
  `gramProfile_refl`, `openTriangleKernel_gramKernel_eq_conv3`, `gramProfile_cube_eq` — the exact
  algebra `Γ_f ^ 3 = Γ_f * Γ_f∨ * Γ_f = (f*f*f) * (f*f*f)∨`: reflection, commutativity,
  associativity (the "middle four exchange" for the lattice convolution).
* `openTriangleKernel_gramKernel_eq_tripleAutocorr` — `∇(0,x) = ofReal (∑_y g y · g (y - x))` for
  `g = f * f * f`, i.e. `(gramKernel f) ^ 3` is the autocorrelation of the triple convolution.
* `openTriangleTail_tendsto_of_gramProfile` — `∇_r → 0` from a summable nonnegative profile, through
  `openTriangleTail_tendsto_of_sqrtKernel` at `ξ = g`.
* `SourceModelData.nablaTail_le_openTriangleTail` and `..._tendsto_nablaTail_toReal_of_gramProfile` —
  the explicit normalization bridge from the plain `ℓ^∞` tail to the model's `M.nablaTail` at the
  normalized source norm `M.S.ρ` (`CriticalLRPConv.srcUpperConst`), and the real-valued limit.

No `sorry`, no `admit`, no `native_decide`, no custom axioms.
-/
module

public import PercLib.CriticalLRP.Analysis.TriTailNormalization.Main
public import PercLib.CriticalLRP.Analysis.TriTailConvolution.Defs
public import PercLib.CriticalLRP.Analysis.TriTailSqrt
public import PercLib.CriticalLRP.Analysis.LatticeConvolution.NormShell
public import PercLib.CriticalLRP.Analysis.Polygon.Defs

/-! # Exact triple convolution and Gram-tail convergence -/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option linter.style.setOption false
set_option linter.hashCommand false
set_option maxHeartbeats 1600000

open scoped ENNReal Topology
open Filter

@[expose] public section

namespace PercLib.CriticalLRP.TriTail

variable {d : ℕ}

/-! ## §1 The profile as an `ℝ≥0∞` function and the real triple convolution -/

theorem ofRealFn_apply (f : (Fin d → ℤ) → ℝ) (z : Fin d → ℤ) :
    ofRealFn f z = ENNReal.ofReal (f z) := rfl

theorem tripleConv_apply (f : (Fin d → ℤ) → ℝ) (x : Fin d → ℤ) :
    tripleConv f x = ∑' p, (∑' q, f q * f (p - q)) * f (x - p) := rfl

/-! ## §2 Summability and mass of `f * f * f` -/

/-- Reindexing a lattice shift: `∑_w K (w - z) = ∑_u K u`. -/
theorem tsum_subRight_ennreal (K : (Fin d → ℤ) → ℝ≥0∞) (z : Fin d → ℤ) :
    (∑' w, K (w - z)) = ∑' u, K u := by
  simpa [Equiv.subRight_apply] using (Equiv.tsum_eq (Equiv.subRight z) K)

/-- The total mass of a lattice convolution is the product of the masses. -/
theorem tsum_conv (H K : (Fin d → ℤ) → ℝ≥0∞) :
    (∑' w, conv H K w) = (∑' z, H z) * (∑' z, K z) := by
  have h1 : (∑' w, conv H K w) = ∑' z, H z * (∑' u, K u) := by
    change (∑' w, ∑' z, H z * K (w - z)) = ∑' z, H z * (∑' u, K u)
    rw [ENNReal.tsum_comm]
    refine tsum_congr fun z => ?_
    rw [ENNReal.tsum_mul_left, tsum_subRight_ennreal K z]
  rw [h1, ENNReal.tsum_mul_right]


variable {f : (Fin d → ℤ) → ℝ}

theorem tsum_profile_nonneg (hf0 : ∀ z, 0 ≤ f z) : 0 ≤ ∑' z, f z := tsum_nonneg hf0

theorem le_tsum_profile (hf0 : ∀ z, 0 ≤ f z) (hf : Summable f) (z : Fin d → ℤ) :
    f z ≤ ∑' z, f z := by
  simpa using Summable.sum_le_tsum {z} (fun i _ => hf0 i) hf

theorem summable_subLeft (hf : Summable f) (p : Fin d → ℤ) : Summable fun q => f (p - q) := by
  have h := (Equiv.summable_iff (f := f) (Equiv.subLeft p)).mpr hf
  simpa [Equiv.subLeft_apply, Function.comp_def] using h

theorem tsum_subLeft (p : Fin d → ℤ) : (∑' q, f (p - q)) = ∑' z, f z := by
  simpa [Equiv.subLeft_apply] using (Equiv.tsum_eq (Equiv.subLeft p) f)

theorem summable_subRight (hf : Summable f) (p : Fin d → ℤ) : Summable fun q => f (q - p) := by
  have h := (Equiv.summable_iff (f := f) (Equiv.subRight p)).mpr hf
  simpa [Equiv.subRight_apply, Function.comp_def] using h

theorem tsum_subRight (p : Fin d → ℤ) : (∑' q, f (q - p)) = ∑' z, f z := by
  simpa [Equiv.subRight_apply] using (Equiv.tsum_eq (Equiv.subRight p) f)

/-- The partial convolution of a summable profile with itself is summable. -/
theorem summable_mul_shift (hf0 : ∀ z, 0 ≤ f z) (hf : Summable f) (p : Fin d → ℤ) :
    Summable fun q => f q * f (p - q) := by
  refine Summable.of_nonneg_of_le (fun q => mul_nonneg (hf0 q) (hf0 (p - q))) (fun q => ?_)
    ((summable_subLeft hf p).mul_left (∑' z, f z))
  have h1 := le_tsum_profile hf0 hf q
  have h2 := hf0 (p - q)
  nlinarith

theorem mul_shift_nonneg (hf0 : ∀ z, 0 ≤ f z) (p : Fin d → ℤ) :
    0 ≤ ∑' q, f q * f (p - q) :=
  tsum_nonneg fun q => mul_nonneg (hf0 q) (hf0 (p - q))

/-- Each entry of `f * f` is at most `(∑ f) ^ 2`. -/
theorem tsum_mul_shift_le (hf0 : ∀ z, 0 ≤ f z) (hf : Summable f) (p : Fin d → ℤ) :
    (∑' q, f q * f (p - q)) ≤ (∑' z, f z) * (∑' z, f z) := by
  calc (∑' q, f q * f (p - q))
      ≤ ∑' q, (∑' z, f z) * f (p - q) := by
        refine Summable.tsum_le_tsum (fun q => ?_) (summable_mul_shift hf0 hf p)
          ((summable_subLeft hf p).mul_left _)
        have h1 := le_tsum_profile hf0 hf q
        have h2 := hf0 (p - q)
        nlinarith
    _ = (∑' z, f z) * (∑' q, f (p - q)) := tsum_mul_left
    _ = (∑' z, f z) * (∑' z, f z) := by rw [tsum_subLeft p]

theorem tripleConv_nonneg (hf0 : ∀ z, 0 ≤ f z) (x : Fin d → ℤ) : 0 ≤ tripleConv f x :=
  tsum_nonneg fun p => mul_nonneg (mul_shift_nonneg hf0 p) (hf0 (x - p))

theorem summable_tripleConv_summand (hf0 : ∀ z, 0 ≤ f z) (hf : Summable f) (x : Fin d → ℤ) :
    Summable fun p => (∑' q, f q * f (p - q)) * f (x - p) := by
  refine Summable.of_nonneg_of_le
    (fun p => mul_nonneg (mul_shift_nonneg hf0 p) (hf0 (x - p))) (fun p => ?_)
    ((summable_subLeft hf x).mul_left ((∑' z, f z) * (∑' z, f z)))
  have h1 := tsum_mul_shift_le hf0 hf p
  have h2 := hf0 (x - p)
  nlinarith

/-- Each entry of `f * f * f` is at most `(∑ f) ^ 3`. -/
theorem tripleConv_le (hf0 : ∀ z, 0 ≤ f z) (hf : Summable f) (x : Fin d → ℤ) :
    tripleConv f x ≤ (∑' z, f z) ^ 3 := by
  have hstep : tripleConv f x
      ≤ ∑' p, ((∑' z, f z) * (∑' z, f z)) * f (x - p) :=
    Summable.tsum_le_tsum
      (fun p => mul_le_mul_of_nonneg_right (tsum_mul_shift_le hf0 hf p) (hf0 (x - p)))
      (summable_tripleConv_summand hf0 hf x) ((summable_subLeft hf x).mul_left _)
  refine hstep.trans (le_of_eq ?_)
  rw [tsum_mul_left, tsum_subLeft x]
  ring

/-! ### The `ofReal` conversion of the convolutions -/

theorem conv_ofRealFn_ofRealFn_apply (hf0 : ∀ z, 0 ≤ f z) (hf : Summable f) (p : Fin d → ℤ) :
    conv (ofRealFn f) (ofRealFn f) p = ENNReal.ofReal (∑' q, f q * f (p - q)) := by
  change (∑' q, ENNReal.ofReal (f q) * ENNReal.ofReal (f (p - q)))
      = ENNReal.ofReal (∑' q, f q * f (p - q))
  rw [ENNReal.ofReal_tsum_of_nonneg (fun q => mul_nonneg (hf0 q) (hf0 (p - q)))
    (summable_mul_shift hf0 hf p)]
  exact tsum_congr fun q => (ENNReal.ofReal_mul (hf0 q)).symm

theorem conv_conv_ofRealFn_apply (hf0 : ∀ z, 0 ≤ f z) (hf : Summable f) (x : Fin d → ℤ) :
    conv (conv (ofRealFn f) (ofRealFn f)) (ofRealFn f) x
      = ENNReal.ofReal (tripleConv f x) := by
  change (∑' p, conv (ofRealFn f) (ofRealFn f) p * ENNReal.ofReal (f (x - p)))
      = ENNReal.ofReal (∑' p, (∑' q, f q * f (p - q)) * f (x - p))
  rw [ENNReal.ofReal_tsum_of_nonneg
    (fun p => mul_nonneg (mul_shift_nonneg hf0 p) (hf0 (x - p)))
    (summable_tripleConv_summand hf0 hf x)]
  refine tsum_congr fun p => ?_
  rw [conv_ofRealFn_ofRealFn_apply hf0 hf p]
  exact (ENNReal.ofReal_mul (mul_shift_nonneg hf0 p)).symm

theorem tsum_ofRealFn (hf0 : ∀ z, 0 ≤ f z) (hf : Summable f) :
    (∑' z, ofRealFn f z) = ENNReal.ofReal (∑' z, f z) :=
  (ENNReal.ofReal_tsum_of_nonneg hf0 hf).symm

/-- The total mass of `f * f * f` is `(∑ f) ^ 3`, computed in `ℝ≥0∞` (where the convolution
associativity is free). -/
theorem tsum_conv_conv_conv_ofRealFn (hf0 : ∀ z, 0 ≤ f z) (hf : Summable f) :
    (∑' x, conv (conv (ofRealFn f) (ofRealFn f)) (ofRealFn f) x)
      = ENNReal.ofReal ((∑' z, f z) ^ 3) := by
  have hA := tsum_profile_nonneg hf0
  rw [tsum_conv, tsum_conv, tsum_ofRealFn hf0 hf, ENNReal.ofReal_pow hA]
  rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, pow_two]

theorem tsum_ofRealFn_tripleConv (hf0 : ∀ z, 0 ≤ f z) (hf : Summable f) :
    (∑' x, ENNReal.ofReal (tripleConv f x)) = ENNReal.ofReal ((∑' z, f z) ^ 3) := by
  rw [← tsum_conv_conv_conv_ofRealFn hf0 hf]
  exact tsum_congr fun x => (conv_conv_ofRealFn_apply hf0 hf x).symm

/-- **`f * f * f` is summable.**  The `ℓ¹`-algebra closure, transported from the `ℝ≥0∞`
convolution through `ENNReal.summable_toReal`. -/
theorem summable_tripleConv (hf0 : ∀ z, 0 ≤ f z) (hf : Summable f) :
    Summable (tripleConv f) := by
  have hne : (∑' x, ENNReal.ofReal (tripleConv f x)) ≠ ⊤ := by
    rw [tsum_ofRealFn_tripleConv hf0 hf]
    exact ENNReal.ofReal_ne_top
  have h := ENNReal.summable_toReal (f := fun x => ENNReal.ofReal (tripleConv f x)) hne
  exact h.congr fun x => ENNReal.toReal_ofReal (tripleConv_nonneg hf0 x)

/-- **The mass of the triple convolution**: `∑ (f * f * f) = (∑ f) ^ 3`. -/
theorem tsum_tripleConv (hf0 : ∀ z, 0 ≤ f z) (hf : Summable f) :
    (∑' x, tripleConv f x) = (∑' z, f z) ^ 3 := by
  have hpow : 0 ≤ (∑' z, f z) ^ 3 := pow_nonneg (tsum_profile_nonneg hf0) 3
  have h1 : ENNReal.ofReal (∑' x, tripleConv f x) = ENNReal.ofReal ((∑' z, f z) ^ 3) := by
    rw [ENNReal.ofReal_tsum_of_nonneg (fun x => tripleConv_nonneg hf0 x)
      (summable_tripleConv hf0 hf), tsum_ofRealFn_tripleConv hf0 hf]
  calc (∑' x, tripleConv f x)
      = (ENNReal.ofReal (∑' x, tripleConv f x)).toReal :=
        (ENNReal.toReal_ofReal (tsum_nonneg fun x => tripleConv_nonneg hf0 x)).symm
    _ = (ENNReal.ofReal ((∑' z, f z) ^ 3)).toReal := by rw [h1]
    _ = (∑' z, f z) ^ 3 := ENNReal.toReal_ofReal hpow

/-- **`f * f * f ∈ ℓ²`** for a summable nonnegative profile: bounded (by `(∑ f) ^ 3`) times `ℓ¹`. -/
theorem summable_tripleConv_sq (hf0 : ∀ z, 0 ≤ f z) (hf : Summable f) :
    Summable fun x => tripleConv f x ^ 2 := by
  refine Summable.of_nonneg_of_le (fun x => sq_nonneg _) (fun x => ?_)
    ((summable_tripleConv hf0 hf).mul_left ((∑' z, f z) ^ 3))
  have h1 := tripleConv_le hf0 hf x
  have h2 := tripleConv_nonneg hf0 x
  nlinarith

/-- The pointwise autocorrelation products of `f * f * f` are summable (AM--GM from `ℓ²`). -/
theorem summable_pair_tripleConv (hf0 : ∀ z, 0 ≤ f z) (hf : Summable f) (x : Fin d → ℤ) :
    Summable fun y => tripleConv f y * tripleConv f (y - x) := by
  have hsq := summable_tripleConv_sq hf0 hf
  have hshift : Summable fun y => tripleConv f (y - x) ^ 2 := by
    have h := (Equiv.summable_iff (f := fun y => tripleConv f y ^ 2)
      (Equiv.subRight x)).mpr hsq
    simpa [Equiv.subRight_apply, Function.comp_def] using h
  refine Summable.of_nonneg_of_le
    (fun y => mul_nonneg (tripleConv_nonneg hf0 y) (tripleConv_nonneg hf0 (y - x)))
    (fun y => ?_) ((hsq.add hshift).div_const 2)
  nlinarith [sq_nonneg (tripleConv f y - tripleConv f (y - x))]

/-! ## §3 The lattice convolution algebra: reflection, exchange, total mass -/

theorem refl_refl (H : (Fin d → ℤ) → ℝ≥0∞) : refl (refl H) = H := by
  funext w
  change H (- -w) = H w
  rw [neg_neg]

/-- **Reflection is a convolution anti/monomorphism**: `(H * K)∨ = H∨ * K∨`, by the substitution
`z ↦ -z`. -/
theorem refl_conv (H K : (Fin d → ℤ) → ℝ≥0∞) :
    refl (conv H K) = conv (refl H) (refl K) := by
  funext w
  change (∑' z, H z * K (-w - z)) = ∑' z, H (-z) * K (-(w - z))
  rw [← Equiv.tsum_eq (Equiv.neg (Fin d → ℤ)) (fun z => H (-z) * K (-(w - z)))]
  refine tsum_congr fun z => ?_
  simp only [Equiv.neg_apply]
  rw [neg_neg]
  congr 1
  abel

/-- **The middle-four exchange** for the lattice convolution: associativity plus commutativity. -/
theorem conv_exchange (A B C D : (Fin d → ℤ) → ℝ≥0∞) :
    conv (conv A B) (conv C D) = conv (conv A C) (conv B D) := by
  rw [conv_assoc, ← conv_assoc B C D, conv_comm B C, conv_assoc, ← conv_assoc]

/-! ## §4 The autocorrelation kernel `Γ_f` and the cube identity -/

theorem gramKernel_eq_gramProfile (f : (Fin d → ℤ) → ℝ) (u v : Fin d → ℤ) :
    gramKernel f u v = gramProfile f (u - v) := by
  change (∑' z, ENNReal.ofReal (f z) * ENNReal.ofReal (f (z + v - u)))
      = ∑' z, ENNReal.ofReal (f z) * ENNReal.ofReal (f (-((u - v) - z)))
  exact tsum_congr fun z => by rw [show z + v - u = -((u - v) - z) by abel]

/-- **`Γ_f` is symmetric** (equivalently, even in the difference coordinate): the reflection of
`f * f∨` is `f∨ * f = f * f∨`. -/
theorem gramProfile_refl (f : (Fin d → ℤ) → ℝ) : refl (gramProfile f) = gramProfile f := by
  rw [gramProfile, refl_conv, refl_refl, conv_comm]

theorem gramProfile_neg (f : (Fin d → ℤ) → ℝ) (w : Fin d → ℤ) :
    gramProfile f (-w) = gramProfile f w :=
  congrFun (gramProfile_refl f) w

/-- **The open triangle of `Γ_f` is the cube of `Γ_f`** (in the difference coordinate):
`∇(0,x) = ∑_v ((Γ_f * Γ_f)(v)) Γ_f(x - v)`.  The reflection enters through the symmetry of `Γ_f`. -/
theorem openTriangleKernel_gramKernel_eq_conv3 (f : (Fin d → ℤ) → ℝ) (x : Fin d → ℤ) :
    openTriangleKernel (gramKernel f) 0 x
      = conv (conv (gramProfile f) (gramProfile f)) (gramProfile f) x := by
  have hs : ∀ w, gramProfile f (-w) = gramProfile f w := gramProfile_neg f
  have hstep : openTriangleKernel (gramKernel f) 0 x
      = ∑' u, ∑' v,
          gramProfile f u * gramProfile f (v - u) * gramProfile f (x - v) := by
    change (∑' u, ∑' v, gramKernel f 0 u * gramKernel f u v * gramKernel f v x)
      = ∑' u, ∑' v, gramProfile f u * gramProfile f (v - u) * gramProfile f (x - v)
    refine tsum_congr fun u => tsum_congr fun v => ?_
    rw [gramKernel_eq_gramProfile, gramKernel_eq_gramProfile, gramKernel_eq_gramProfile]
    rw [zero_sub, ← neg_sub v u, ← neg_sub x v, hs u, hs (v - u), hs (x - v)]
  rw [hstep]
  rw [ENNReal.tsum_comm (f := fun u v =>
    gramProfile f u * gramProfile f (v - u) * gramProfile f (x - v))]
  refine tsum_congr fun v => ?_
  change (∑' u, gramProfile f u * gramProfile f (v - u) * gramProfile f (x - v))
      = conv (gramProfile f) (gramProfile f) v * gramProfile f (x - v)
  rw [ENNReal.tsum_mul_right]
  rfl

/-- **The cube of the autocorrelation is the autocorrelation of the triple convolution**:
`(f * f∨) ^ 3 = (f * f * f) * (f * f * f)∨`.  Two middle-four exchanges, and
`refl (f*f*f) = f∨ * f∨ * f∨`. -/
theorem gramProfile_cube_eq (f : (Fin d → ℤ) → ℝ) :
    conv (conv (gramProfile f) (gramProfile f)) (gramProfile f) =
      conv (conv (conv (ofRealFn f) (ofRealFn f)) (ofRealFn f))
        (refl (conv (conv (ofRealFn f) (ofRealFn f)) (ofRealFn f))) := by
  have hG : refl (conv (conv (ofRealFn f) (ofRealFn f)) (ofRealFn f))
      = conv (conv (refl (ofRealFn f)) (refl (ofRealFn f))) (refl (ofRealFn f)) := by
    rw [refl_conv, refl_conv]
  calc conv (conv (gramProfile f) (gramProfile f)) (gramProfile f)
      = conv (conv (conv (ofRealFn f) (refl (ofRealFn f)))
            (conv (ofRealFn f) (refl (ofRealFn f))))
            (conv (ofRealFn f) (refl (ofRealFn f))) := by
        rw [gramProfile]
    _ = conv (conv (conv (ofRealFn f) (ofRealFn f))
            (conv (refl (ofRealFn f)) (refl (ofRealFn f))))
            (conv (ofRealFn f) (refl (ofRealFn f))) := by
        exact congrArg (fun Z => conv Z (conv (ofRealFn f) (refl (ofRealFn f))))
          (conv_exchange (ofRealFn f) (refl (ofRealFn f)) (ofRealFn f) (refl (ofRealFn f)))
    _ = conv (conv (conv (ofRealFn f) (ofRealFn f)) (ofRealFn f))
          (conv (conv (refl (ofRealFn f)) (refl (ofRealFn f))) (refl (ofRealFn f))) :=
        conv_exchange (conv (ofRealFn f) (ofRealFn f))
          (conv (refl (ofRealFn f)) (refl (ofRealFn f))) (ofRealFn f) (refl (ofRealFn f))
    _ = conv (conv (conv (ofRealFn f) (ofRealFn f)) (ofRealFn f))
          (refl (conv (conv (ofRealFn f) (ofRealFn f)) (ofRealFn f))) := by rw [hG]

/-- Evaluating the autocorrelation of the triple convolution: it is `ofReal` of the real
autocorrelation sum.  This is the `ofReal` conversion plus finite summability
(`summable_pair_tripleConv`) and the reflection `y ↦ y - x`. -/
theorem conv_conj_ofRealFn_apply (hf0 : ∀ z, 0 ≤ f z) (hf : Summable f) (x : Fin d → ℤ) :
    conv (conv (conv (ofRealFn f) (ofRealFn f)) (ofRealFn f))
        (refl (conv (conv (ofRealFn f) (ofRealFn f)) (ofRealFn f))) x
      = ENNReal.ofReal (∑' y, tripleConv f y * tripleConv f (y - x)) := by
  change (∑' y, conv (conv (ofRealFn f) (ofRealFn f)) (ofRealFn f) y *
      refl (conv (conv (ofRealFn f) (ofRealFn f)) (ofRealFn f)) (x - y))
      = ENNReal.ofReal (∑' y, tripleConv f y * tripleConv f (y - x))
  rw [ENNReal.ofReal_tsum_of_nonneg
    (fun y => mul_nonneg (tripleConv_nonneg hf0 y) (tripleConv_nonneg hf0 (y - x)))
    (summable_pair_tripleConv hf0 hf x)]
  refine tsum_congr fun y => ?_
  have hrefl : refl (conv (conv (ofRealFn f) (ofRealFn f)) (ofRealFn f)) (x - y)
      = conv (conv (ofRealFn f) (ofRealFn f)) (ofRealFn f) (y - x) := by
    change conv (conv (ofRealFn f) (ofRealFn f)) (ofRealFn f) (-(x - y)) = _
    rw [neg_sub]
  rw [hrefl, conv_conv_ofRealFn_apply hf0 hf y, conv_conv_ofRealFn_apply hf0 hf (y - x)]
  exact (ENNReal.ofReal_mul (tripleConv_nonneg hf0 y)).symm

/-- **The main identity.**  For a nonnegative summable profile `f`, the open triangle of the
autocorrelation kernel `Γ_f = gramKernel f` at the origin is the autocorrelation of the triple
convolution `f * f * f`:
`∇_{Γ_f}(0,x) = ofReal (∑_y g y · g (y - x))` with `g = f * f * f`. -/
theorem openTriangleKernel_gramKernel_eq_tripleAutocorr (hf0 : ∀ z, 0 ≤ f z) (hf : Summable f)
    (x : Fin d → ℤ) :
    openTriangleKernel (gramKernel f) 0 x
      = ENNReal.ofReal (∑' y, tripleConv f y * tripleConv f (y - x)) := by
  rw [openTriangleKernel_gramKernel_eq_conv3, gramProfile_cube_eq, conv_conj_ofRealFn_apply hf0 hf]

/-- The same identity in the form the square-root consumer takes: for every `x`,
`∇(0,x) = ENNReal.ofReal (∑_y ξ y · ξ (y - x))` with `ξ = f * f * f`. -/
theorem openTriangle_gramKernel_eq_ofReal_autocorr {J : Sym2 (Fin d → ℤ) → ℝ}
    {hJ : ∀ e, 0 ≤ J e} {β : NNReal} (hf0 : ∀ z, 0 ≤ f z) (hf : Summable f)
    (hident : ∀ u v : Fin d → ℤ, twoPointFunction J hJ β u v = gramKernel f u v)
    (x : Fin d → ℤ) :
    openTriangle J hJ β 0 x
      = ENNReal.ofReal (∑' y, tripleConv f y * tripleConv f (y - x)) := by
  rw [openTriangle_eq_openTriangleKernel]
  rw [show openTriangleKernel (twoPointFunction J hJ β) 0 x = openTriangleKernel (gramKernel f) 0 x
    from tsum_congr fun u => tsum_congr fun v => by rw [hident 0 u, hident u v, hident v x]]
  exact openTriangleKernel_gramKernel_eq_tripleAutocorr hf0 hf x

/-! ## §5 The tail `∇_r → 0` -/

/-- **The open-triangle tail vanishes under the Gram profile hypothesis.**  The profile hypothesis
is the same one that gives `hTri` in `TriTailNormalization`; the vanishing of the tail uses the
triple convolution `ξ = f * f * f` as Kozma's `ℓ²` square root. -/
theorem openTriangleTail_tendsto_of_gramProfile {J : Sym2 (Fin d → ℤ) → ℝ} {hJ : ∀ e, 0 ≤ J e}
    {β : NNReal} (hf0 : ∀ z, 0 ≤ f z) (hf : Summable f)
    (hident : ∀ u v : Fin d → ℤ, twoPointFunction J hJ β u v = gramKernel f u v) :
    Tendsto (openTriangleTail J hJ β) atTop (𝓝 0) :=
  openTriangleTail_tendsto_of_sqrtKernel (ξ := tripleConv f) (summable_tripleConv_sq hf0 hf)
    (fun x => openTriangle_gramKernel_eq_ofReal_autocorr hf0 hf hident x)

/-- `latticeDist 0 y` is the sup-norm of `y`. -/
theorem latticeDist_zero_eq_linfNorm (y : Fin d → ℤ) :
    FiniteVolume.latticeDist (d := d) 0 y = (FiniteVolume.linfNorm y : ℝ) := by
  rw [Percolation.latticeDist_eq_linfNorm]
  simp

/-- Monotonicity of the open triangle in the kernel, at a general pair of endpoints. -/
theorem openTriangleKernel_mono_apply {τ σ : (Fin d → ℤ) → (Fin d → ℤ) → ℝ≥0∞}
    (h : ∀ u v : Fin d → ℤ, τ u v ≤ σ u v) (x y : Fin d → ℤ) :
    openTriangleKernel τ x y ≤ openTriangleKernel σ x y :=
  ENNReal.tsum_le_tsum fun u => ENNReal.tsum_le_tsum fun v =>
    mul_le_mul (mul_le_mul (h x u) (h u v) zero_le zero_le) (h v y) zero_le zero_le

/-- **The open-triangle tail vanishes under domination by a summable Gram profile.**  The
pointwise identification `twoPointFunction = gramKernel f` of
`openTriangleTail_tendsto_of_gramProfile` can be weakened to domination `≤`: the tail of the
majorant is the autocorrelation tail of `f * f * f`, which vanishes by
`exists_linfNorm_tsum_mul_shift_le`.  This is the dominated counterpart of `hTri` in
`TriTailNormalization`. -/
theorem openTriangleTail_tendsto_of_gramDomination {J : Sym2 (Fin d → ℤ) → ℝ}
    {hJ : ∀ e, 0 ≤ J e} {β : NNReal} (hf0 : ∀ z, 0 ≤ f z) (hf : Summable f)
    (hle : ∀ u v : Fin d → ℤ, twoPointFunction J hJ β u v ≤ gramKernel f u v) :
    Tendsto (openTriangleTail J hJ β) atTop (𝓝 0) := by
  rw [tendsto_openTriangleTail_iff]
  intro ε hε
  by_cases htop : ε = ⊤
  · refine ⟨0, fun x _ => ?_⟩
    rw [htop]
    exact le_top
  · have hpos : 0 < ε.toReal := ENNReal.toReal_pos (ne_of_gt hε) htop
    obtain ⟨N, hN⟩ := exists_linfNorm_tsum_mul_shift_le (d := d) (summable_tripleConv_sq hf0 hf)
      (show (0 : ℝ) < ε.toReal / 2 by linarith)
    refine ⟨(N : ℝ), fun x hx => ?_⟩
    have hNx : N ≤ FiniteVolume.linfNorm x := by
      rw [latticeDist_zero_eq_linfNorm] at hx
      exact_mod_cast hx
    have h1 : (∑' y, tripleConv f y * tripleConv f (y - x)) ≤ ε.toReal := by
      have h2 := (abs_le.1 (hN x hNx)).2
      linarith
    calc openTriangle J hJ β 0 x
        ≤ openTriangleKernel (gramKernel f) 0 x := by
          rw [openTriangle_eq_openTriangleKernel]
          exact openTriangleKernel_mono_apply hle 0 x
      _ = ENNReal.ofReal (∑' y, tripleConv f y * tripleConv f (y - x)) :=
          openTriangleKernel_gramKernel_eq_tripleAutocorr hf0 hf x
      _ ≤ ENNReal.ofReal ε.toReal := ENNReal.ofReal_le_ofReal h1
      _ = ε := ENNReal.ofReal_toReal htop

end PercLib.CriticalLRP.TriTail

/-! ## §6 The model: `nablaTail` at the normalized source norm -/

namespace PercLib.CriticalLRP

/-- **The open-triangle tail vanishes under a summable Gram profile**, in the exact shape the
§I.4.18 consumers use (`TriTail.openTriangleTail M.kernel M.kernel_nonneg M.betaCrit`). -/
theorem Orchestration.SourceModelData.openTriangleTail_tendsto_of_gramProfile
    (M : Orchestration.SourceModelData) {f : M.V → ℝ} (hf0 : ∀ z, 0 ≤ f z) (hf : Summable f)
    (hident : ∀ u v : M.V,
      twoPointFunction M.kernel M.kernel_nonneg M.betaCrit u v = TriTail.gramKernel f u v) :
    Tendsto (TriTail.openTriangleTail M.kernel M.kernel_nonneg M.betaCrit) atTop (𝓝 0) :=
  TriTail.openTriangleTail_tendsto_of_gramProfile (d := M.d) hf0 hf hident

/-- **The weight/normalization bridge.**  `M.nablaTail` uses the model's normalized source norm
`M.S.ρ`, while `TriTail.openTriangleTail` uses the lattice sup-norm; the two are related by the
upper norm-comparison constant `srcUpperConst M.S`.  Hence the model tail at radius `r` is dominated
by the plain tail at radius `r / srcUpperConst M.S`: no weight or normalization factor is dropped. -/
theorem Orchestration.SourceModelData.nablaTail_le_openTriangleTail
    (M : Orchestration.SourceModelData) (r : ℝ) :
    M.nablaTail r ≤ TriTail.openTriangleTail M.kernel M.kernel_nonneg M.betaCrit
      (r / CriticalLRPConv.srcUpperConst M.S) := by
  have hC : 0 < CriticalLRPConv.srcUpperConst M.S := CriticalLRPConv.srcUpperConst_pos M.S
  change (⨆ y : M.V, ⨆ (_ : r ≤ M.S.dist 0 y),
      TriTail.openTriangle M.kernel M.kernel_nonneg M.betaCrit 0 y)
    ≤ (⨆ x : M.V, ⨆ (_ : r / CriticalLRPConv.srcUpperConst M.S
        ≤ FiniteVolume.latticeDist (d := M.d) 0 x),
        TriTail.openTriangle M.kernel M.kernel_nonneg M.betaCrit 0 x)
  refine iSup_le fun y => iSup_le fun hy => ?_
  refine le_iSup_of_le y ?_
  refine le_iSup (f := fun (_ : r / CriticalLRPConv.srcUpperConst M.S
      ≤ FiniteVolume.latticeDist (d := M.d) 0 y) =>
      TriTail.openTriangle M.kernel M.kernel_nonneg M.betaCrit 0 y) ?_
  rw [TriTail.latticeDist_zero_eq_linfNorm y]
  have h1 : r ≤ M.S.ρ (Orchestration.toVec y) := by
    rw [← CriticalLRPConv.dist_zero_eq_srcNorm M.S y]
    exact hy
  have h2 : M.S.ρ (Orchestration.toVec y)
      ≤ CriticalLRPConv.srcUpperConst M.S * (FiniteVolume.linfNorm y : ℝ) :=
    CriticalLRPConv.srcNorm_le_upper_linfNorm M.S y
  rw [div_le_iff₀ hC]
  linarith

/-- **`M.nablaTail → 0` in `ℝ≥0∞`** under the summable Gram profile hypothesis, through the
normalization bridge. -/
theorem Orchestration.SourceModelData.tendsto_nablaTail_of_gramProfile
    (M : Orchestration.SourceModelData) {f : M.V → ℝ} (hf0 : ∀ z, 0 ≤ f z) (hf : Summable f)
    (hident : ∀ u v : M.V,
      twoPointFunction M.kernel M.kernel_nonneg M.betaCrit u v = TriTail.gramKernel f u v) :
    Tendsto (fun r => M.nablaTail r) atTop (𝓝 0) := by
  have htail := M.openTriangleTail_tendsto_of_gramProfile hf0 hf hident
  have hC : 0 < CriticalLRPConv.srcUpperConst M.S := CriticalLRPConv.srcUpperConst_pos M.S
  have hdiv : Tendsto (fun r : ℝ => r / CriticalLRPConv.srcUpperConst M.S) atTop atTop := by
    rw [tendsto_atTop_atTop]
    intro b
    exact ⟨b * CriticalLRPConv.srcUpperConst M.S, fun x hx => (le_div_iff₀ hC).mpr hx⟩
  have hcomp : Tendsto (fun r : ℝ =>
      TriTail.openTriangleTail M.kernel M.kernel_nonneg M.betaCrit
        (r / CriticalLRPConv.srcUpperConst M.S)) atTop (𝓝 0) := htail.comp hdiv
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  filter_upwards [(ENNReal.tendsto_nhds_zero.1 hcomp) ε hε] with r hr
  exact (M.nablaTail_le_openTriangleTail r).trans hr

/-- **The real-valued model tail vanishes**: `(M.nablaTail r).toReal → 0`. -/
theorem Orchestration.SourceModelData.tendsto_nablaTail_toReal_of_gramProfile
    (M : Orchestration.SourceModelData) {f : M.V → ℝ} (hf0 : ∀ z, 0 ≤ f z) (hf : Summable f)
    (hident : ∀ u v : M.V,
      twoPointFunction M.kernel M.kernel_nonneg M.betaCrit u v = TriTail.gramKernel f u v) :
    Tendsto (fun r => (M.nablaTail r).toReal) atTop (𝓝 0) := by
  have h := M.tendsto_nablaTail_of_gramProfile hf0 hf hident
  have h2 : Tendsto (fun r => (M.nablaTail r).toReal) atTop (𝓝 ((0 : ℝ≥0∞).toReal)) :=
    (ENNReal.tendsto_toReal (a := (0 : ℝ≥0∞)) (by simp)).comp h
  simpa using h2

/-- **`(M.nablaTail r).toReal → 0` under domination** by a summable Gram profile. -/
theorem Orchestration.SourceModelData.tendsto_nablaTail_toReal_of_gramDomination
    (M : Orchestration.SourceModelData) {f : M.V → ℝ} (hf0 : ∀ z, 0 ≤ f z) (hf : Summable f)
    (hle : ∀ u v : M.V,
      twoPointFunction M.kernel M.kernel_nonneg M.betaCrit u v ≤ TriTail.gramKernel f u v) :
    Tendsto (fun r => (M.nablaTail r).toReal) atTop (𝓝 0) := by
  have htail : Tendsto (TriTail.openTriangleTail M.kernel M.kernel_nonneg M.betaCrit) atTop (𝓝 0) :=
    TriTail.openTriangleTail_tendsto_of_gramDomination (d := M.d) hf0 hf hle
  have hC : 0 < CriticalLRPConv.srcUpperConst M.S := CriticalLRPConv.srcUpperConst_pos M.S
  have hdiv : Tendsto (fun r : ℝ => r / CriticalLRPConv.srcUpperConst M.S) atTop atTop := by
    rw [tendsto_atTop_atTop]
    intro b
    exact ⟨b * CriticalLRPConv.srcUpperConst M.S, fun x hx => (le_div_iff₀ hC).mpr hx⟩
  have hcomp : Tendsto (fun r : ℝ =>
      TriTail.openTriangleTail M.kernel M.kernel_nonneg M.betaCrit
        (r / CriticalLRPConv.srcUpperConst M.S)) atTop (𝓝 0) := htail.comp hdiv
  have hzero : Tendsto (fun r : ℝ => M.nablaTail r) atTop (𝓝 0) := by
    rw [ENNReal.tendsto_nhds_zero]
    intro ε hε
    filter_upwards [(ENNReal.tendsto_nhds_zero.1 hcomp) ε hε] with r hr
    exact (M.nablaTail_le_openTriangleTail r).trans hr
  have h2 : Tendsto (fun r => (M.nablaTail r).toReal) atTop (𝓝 ((0 : ℝ≥0∞).toReal)) :=
    (ENNReal.tendsto_toReal (a := (0 : ℝ≥0∞)) (by simp)).comp hzero
  simpa using h2

end PercLib.CriticalLRP

/-! ## Axiom audit -/

#print axioms PercLib.CriticalLRP.TriTail.summable_mul_shift
#print axioms PercLib.CriticalLRP.TriTail.summable_tripleConv
#print axioms PercLib.CriticalLRP.TriTail.tsum_tripleConv
#print axioms PercLib.CriticalLRP.TriTail.summable_tripleConv_sq
#print axioms PercLib.CriticalLRP.TriTail.conv_conv_ofRealFn_apply
#print axioms PercLib.CriticalLRP.TriTail.refl_conv
#print axioms PercLib.CriticalLRP.TriTail.conv_exchange
#print axioms PercLib.CriticalLRP.TriTail.tsum_conv
#print axioms PercLib.CriticalLRP.TriTail.gramKernel_eq_gramProfile
#print axioms PercLib.CriticalLRP.TriTail.gramProfile_refl
#print axioms PercLib.CriticalLRP.TriTail.openTriangleKernel_gramKernel_eq_conv3
#print axioms PercLib.CriticalLRP.TriTail.gramProfile_cube_eq
#print axioms PercLib.CriticalLRP.TriTail.conv_conj_ofRealFn_apply
#print axioms PercLib.CriticalLRP.TriTail.openTriangleKernel_gramKernel_eq_tripleAutocorr
#print axioms PercLib.CriticalLRP.TriTail.openTriangleTail_tendsto_of_gramProfile
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.openTriangleTail_tendsto_of_gramProfile
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.nablaTail_le_openTriangleTail
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.tendsto_nablaTail_of_gramProfile
#print axioms PercLib.CriticalLRP.TriTail.openTriangleTail_tendsto_of_gramDomination
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.tendsto_nablaTail_toReal_of_gramDomination
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.tendsto_nablaTail_toReal_of_gramProfile
