/-
# D6B package: positive `3/2`-power via CFC, and its realification to real `ℓ²`

Member `m7`, swarm `smwtvrwnn`.  Self-contained package file: it contains

1. `CFC.sqrtCube` : the nonnegative square root of `B ^ 3` (= `B ^ (3/2)`) in a unital
   C⋆-algebra, with `S * S = S† * S = B^3`, uniqueness, and the Hilbert-space Gram identity
   `⟪B^3 f, g⟫ = ⟪S f, S g⟫`  (`Sqrt.lean`),
2. the realification bridge `Realification.nonneg_complexification_iff` and its concrete `ℓ²`
   form `Realification.nonneg_complexification_lp`  (`Realification.lean`),
3. the combined statement `exists_sqrt_cube_real_operator`.

Axioms: every theorem depends only on `propext`, `Classical.choice`, `Quot.sound`.
-/
module

public import PercLib.CriticalLRP.Analysis.KernelOperator.CFC.Defs

/-!
Positive `3/2`-powers through the complex continuous functional calculus, with an explicit
real/complex `ℓ²` bridge.  The complex extension and positivity data remain visible hypotheses.
-/
/-
# The positive `3/2`-power `B^{3/2}` via the continuous functional calculus

Member `m7`, swarm `smwtvrwnn`, direction D6B.

This file produces an actual positive operator square root of `B ^ 3` from Mathlib's
continuous functional calculus (CFC), with `S = CFC.sqrt (B^3) = B^(3/2)`, and proves

* `S` is nonnegative and self-adjoint (`S† = S`),
* `S† * S = S * S = B^3`,
* `S` is the *unique* nonnegative square root of `B^3`,
* the Gram identity `⟪S f, S g⟫ = ⟪B^3 f, g⟫`, hence `‖S f‖^2 = ⟪B^3 f, f⟫ ≥ 0`,

for a unital C⋆-algebra and, in the last section, for bounded operators on a complex
Hilbert space.  Positive-semidefinite data are kept separate from Schur-kernel data: no
positivity is asserted for any kernel operator here, only implications from `0 ≤ B`.
-/

set_option linter.style.longLine false

@[expose] public section
noncomputable section

open scoped NNReal InnerProduct InnerProductSpace

namespace CFC

/-! ### The abstract C⋆-algebra statement -/

section Abstract

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem sqrtCube_nonneg (B : A) : 0 ≤ sqrtCube B := sqrt_nonneg _

theorem sqrtCube_isSelfAdjoint (B : A) : IsSelfAdjoint (sqrtCube B) :=
  IsSelfAdjoint.of_nonneg (sqrtCube_nonneg B)

theorem sqrtCube_star (B : A) : star (sqrtCube B) = sqrtCube B :=
  (sqrtCube_isSelfAdjoint B).star_eq

/-- `B^(3/2) * B^(3/2) = B^3` for nonnegative `B`. -/
theorem sqrtCube_mul_self {B : A} (hB : 0 ≤ B) : sqrtCube B * sqrtCube B = B ^ 3 :=
  sqrt_mul_sqrt_self _ (CStarAlgebra.pow_nonneg B 3 hB)

/-- The adjoint form `B^(3/2)† * B^(3/2) = B^3`. -/
theorem sqrtCube_star_mul_self {B : A} (hB : 0 ≤ B) :
    star (sqrtCube B) * sqrtCube B = B ^ 3 := by
  rw [sqrtCube_star, sqrtCube_mul_self hB]

/-- Uniqueness: any nonnegative square root of `B^3` is `B^(3/2)`. -/
theorem eq_sqrtCube_of_mul_self {B T : A} (hT : 0 ≤ T) (h : T * T = B ^ 3) :
    T = sqrtCube B :=
  (sqrt_unique h hT).symm

/-- `B^(3/2)` is the unique nonnegative `S` with `S * S = B^3`. -/
theorem mul_self_iff_eq_sqrtCube {B T : A} (hB : 0 ≤ B) (hT : 0 ≤ T) :
    T * T = B ^ 3 ↔ T = sqrtCube B :=
  ⟨eq_sqrtCube_of_mul_self hT, fun h => h ▸ sqrtCube_mul_self hB⟩

/-- `B^(3/2)` written as a `ℝ≥0`-power. -/
theorem sqrtCube_eq_nnrpow (B : A) (hB : 0 ≤ B) :
    sqrtCube B = B ^ (3 / 2 : ℝ≥0) := by
  have h3 : B ^ 3 = B ^ (3 : ℝ≥0) := by
    rw [nnrpow_three B hB, pow_three, mul_assoc]
  rw [sqrtCube, h3, sqrt_nnrpow]

/-- `B^(3/2)` written as a real power, in the `CFC.rpow` notation. -/
theorem sqrtCube_eq_rpow (B : A) (hB : 0 ≤ B) : sqrtCube B = B ^ (3 / 2 : ℝ) := by
  rw [sqrtCube_eq_nnrpow B hB,
    nnrpow_eq_rpow (a := B) (x := (3 / 2 : ℝ≥0)) (by norm_num)]
  norm_num

end Abstract

/-! ### Bounded operators on a complex Hilbert space

For `H` a complex Hilbert space, `H →L[ℂ] H` is a unital C⋆-algebra
(`Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap`) carrying the Loewner order
(`Mathlib.Analysis.InnerProductSpace.StarOrder`), and all the CFC instances are available as
instances, so the abstract results apply verbatim.  We record the operator and quadratic-form
forms, which are what a Schur-kernel application consumes. -/

section Hilbert

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- `B^(3/2)† * B^(3/2) = B^3` for a nonnegative bounded operator on a complex Hilbert space. -/
theorem ContinuousLinearMap.sqrtCube_adjoint_mul_self (B : H →L[ℂ] H) (hB : 0 ≤ B) :
    (sqrtCube B)† * sqrtCube B = B ^ 3 := by
  simpa only [ContinuousLinearMap.star_eq_adjoint] using sqrtCube_star_mul_self (A := H →L[ℂ] H) hB

/-- **The cubic Schur form is the Gram form of `B^(3/2)`**:  for a nonnegative bounded operator
`B` on a complex Hilbert space,
`⟪B^3 f, g⟫ = ⟪B^(3/2) f, B^(3/2) g⟫`. -/
theorem ContinuousLinearMap.inner_sqrtCube (B : H →L[ℂ] H) (hB : 0 ≤ B) (f g : H) :
    ⟪(B ^ 3) f, g⟫_ℂ = ⟪sqrtCube B f, sqrtCube B g⟫_ℂ := by
  have hS : (sqrtCube B)† = sqrtCube B := by
    rw [← ContinuousLinearMap.star_eq_adjoint]
    exact (sqrtCube_isSelfAdjoint B).star_eq
  rw [← ContinuousLinearMap.adjoint_inner_left (sqrtCube B) g (sqrtCube B f), hS,
    ← mul_apply_eq_comp, sqrtCube_mul_self hB]

/-- Positivity of the cubic form, `0 ≤ re ⟪B^3 f, f⟫`, as a direct consequence of the Gram
representation. -/
theorem ContinuousLinearMap.re_inner_cube_nonneg (B : H →L[ℂ] H) (hB : 0 ≤ B) (f : H) :
    0 ≤ Complex.re ⟪(B ^ 3) f, f⟫_ℂ := by
  rw [ContinuousLinearMap.inner_sqrtCube B hB f f]
  exact inner_self_nonneg (𝕜 := ℂ) (x := sqrtCube B f)

end Hilbert

end CFC


/-
# The real/complex bridge for the CFC square root

Member `m7`, swarm `smwtvrwnn`, direction D6B, part 2.

Mathlib has a continuous functional calculus only for **complex** C⋆-algebras: operators on a real
Hilbert space `E →L[ℝ] E` carry `NonnegSpectrumClass ℝ` and the Loewner order, but *no*
`ContinuousFunctionalCalculus ℝ (E →L[ℝ] E) IsSelfAdjoint` instance is available
(`Mathlib.Analysis.InnerProductSpace.StarOrder`: "for the moment we only have this for `𝕜 := ℂ`";
`CFC.rpow`/`CFC.sqrt` are unital C⋆-algebra, hence `ℂ`-algebra, constructions).

So a square root of a real Schur operator has to be taken after complexification.  This file
proves the missing positivity bridge: if `F` is a complex Hilbert space with a *real structure*
`ι : E → F` (inner products of `ι`-images are real and every vector of `F` is `ι a + I • ι b`),
and `Tℂ` is a self-adjoint complex-linear operator that is the complexification of a real
operator `T`, then

  `0 ≤ Tℂ  ↔  ∀ x, 0 ≤ ⟪T x, x⟫_ℝ`.

That is exactly the input needed to feed real positive-semidefinite Schur data into `CFC.sqrt`.
No positivity is assumed on either side; one side is derived from the other.

## Main results

* `re_inner_complexification` : `re ⟪Tℂ (ι a + I • ι b), ι a + I • ι b⟫ = ⟪T a, a⟫ + ⟪T b, b⟫`.
* `nonneg_complexification_iff` : `0 ≤ Tℂ ↔ ∀ a, 0 ≤ ⟪T a, a⟫_ℝ` (given `Tℂ` self-adjoint).
-/

@[expose] public section
noncomputable section

open RCLike
open scoped InnerProduct InnerProductSpace ComplexConjugate ComplexOrder ENNReal NNReal lp

namespace Realification

section QuadraticForm

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- The quadratic form of the complexification of a real operator, on the vector
`ι a + I • ι b`, is the sum of the real quadratic forms on `a` and `b`. -/
theorem re_inner_complexification (ι : E → F)
    (hι : ∀ a b : E, ⟪ι a, ι b⟫_ℂ = ((⟪a, b⟫_ℝ : ℝ) : ℂ))
    (T : E →L[ℝ] E) (Tℂ : F →L[ℂ] F) (hT : ∀ a, Tℂ (ι a) = ι (T a)) (a b : E) :
    RCLike.re ⟪Tℂ (ι a + Complex.I • ι b), ι a + Complex.I • ι b⟫_ℂ
      = ⟪T a, a⟫_ℝ + ⟪T b, b⟫_ℝ := by
  simp only [map_add, map_smul, hT, inner_add_left, inner_add_right, inner_smul_left,
    inner_smul_right, hι, Complex.conj_I]
  simp

/-- The full complex inner product of the complexification, on a pair of decomposed vectors. -/
theorem inner_complexification (ι : E → F)
    (hι : ∀ a b : E, ⟪ι a, ι b⟫_ℂ = ((⟪a, b⟫_ℝ : ℝ) : ℂ))
    (T : E →L[ℝ] E) (Tℂ : F →L[ℂ] F) (hT : ∀ a, Tℂ (ι a) = ι (T a)) (a b c d : E) :
    ⟪Tℂ (ι a + Complex.I • ι b), ι c + Complex.I • ι d⟫_ℂ
      = ((⟪T a, c⟫_ℝ : ℝ) : ℂ) + Complex.I * ((⟪T a, d⟫_ℝ : ℝ) : ℂ)
        - Complex.I * ((⟪T b, c⟫_ℝ : ℝ) : ℂ) + ((⟪T b, d⟫_ℝ : ℝ) : ℂ) := by
  simp only [map_add, map_smul, hT, inner_add_left, inner_add_right, inner_smul_left,
    inner_smul_right, hι, Complex.conj_I]
  rw [← sub_eq_zero]
  linear_combination (-(((⟪T b, d⟫_ℝ : ℝ)) : ℂ)) * Complex.I_mul_I

end QuadraticForm

section Positivity

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- **The realification bridge.**  A self-adjoint complex-linear operator which is the
complexification of a real operator `T` is nonnegative in the Loewner order if and only if the
real quadratic form of `T` is nonnegative.  In particular this makes the complex continuous
functional calculus available for real positive data. -/
theorem nonneg_complexification_iff (ι : E → F)
    (hι : ∀ a b : E, ⟪ι a, ι b⟫_ℂ = ((⟪a, b⟫_ℝ : ℝ) : ℂ))
    (hspan : ∀ z : F, ∃ a b : E, z = ι a + Complex.I • ι b)
    (T : E →L[ℝ] E) (Tℂ : F →L[ℂ] F) (hT : ∀ a, Tℂ (ι a) = ι (T a))
    (hsa : IsSelfAdjoint Tℂ) :
    0 ≤ Tℂ ↔ ∀ a : E, 0 ≤ ⟪T a, a⟫_ℝ := by
  constructor
  · intro h a
    have hpos : Tℂ.IsPositive := ContinuousLinearMap.nonneg_iff_isPositive.mp h
    have h1 := hpos.re_inner_nonneg_left (ι a)
    rw [hT, hι] at h1
    simpa using h1
  · intro h
    refine ContinuousLinearMap.nonneg_iff_isPositive.mpr ?_
    rw [ContinuousLinearMap.isPositive_iff_complex]
    intro z
    obtain ⟨a, b, rfl⟩ := hspan z
    have hreal : conj ⟪Tℂ (ι a + Complex.I • ι b), ι a + Complex.I • ι b⟫_ℂ
        = ⟪Tℂ (ι a + Complex.I • ι b), ι a + Complex.I • ι b⟫_ℂ := by
      rw [inner_conj_symm (ι a + Complex.I • ι b) (Tℂ (ι a + Complex.I • ι b))]
      rw [← ContinuousLinearMap.adjoint_inner_right (Tℂ) (ι a + Complex.I • ι b)
        (ι a + Complex.I • ι b), (ContinuousLinearMap.isSelfAdjoint_iff' (A := Tℂ)).mp hsa]
    refine ⟨RCLike.conj_eq_iff_re.mp hreal, ?_⟩
    rw [re_inner_complexification ι hι T Tℂ hT a b]
    exact add_nonneg (h a) (h b)

set_option linter.unusedSectionVars false in
/-- **Uniqueness of the complex-linear extension.**  Two complex-linear operators that agree on
the real structure agree everywhere.  This is what identifies `(Tℂ)^3` with the complexification of
`T^3` once the extension property is known. -/
theorem ext_of_eqOn_real (ι : E → F)
    (hspan : ∀ z : F, ∃ a b : E, z = ι a + Complex.I • ι b)
    {S T : F →L[ℂ] F} (h : ∀ a : E, S (ι a) = T (ι a)) : S = T := by
  ext z
  obtain ⟨a, b, rfl⟩ := hspan z
  simp only [map_add, map_smul, h a, h b]

set_option linter.unusedSectionVars false in
/-- Powers of a complexification act on real vectors as powers of the real operator. -/
theorem complexification_pow_apply (ι : E → F) (T : E →L[ℝ] E) (Tℂ : F →L[ℂ] F)
    (hT : ∀ a, Tℂ (ι a) = ι (T a)) (n : ℕ) : ∀ a : E, (Tℂ ^ n) (ι a) = ι ((T ^ n) a) := by
  induction n with
  | zero => intro a; simp
  | succ n ih =>
    intro a
    rw [pow_succ, pow_succ, mul_apply_eq_comp, mul_apply_eq_comp, hT, ih (T a)]

/-- **Self-adjointness of the complexification from real symmetry.**  If the real operator is
symmetric, then any complex-linear operator extending it on the real structure is self-adjoint;
the imaginary cross-terms of the quadratic form cancel by symmetry. -/
theorem isSelfAdjoint_complexification_of_symmetric (ι : E → F)
    (hι : ∀ a b : E, ⟪ι a, ι b⟫_ℂ = ((⟪a, b⟫_ℝ : ℝ) : ℂ))
    (hspan : ∀ z : F, ∃ a b : E, z = ι a + Complex.I • ι b)
    (T : E →L[ℝ] E) (Tℂ : F →L[ℂ] F) (hT : ∀ a, Tℂ (ι a) = ι (T a))
    (hTsym : ∀ a b : E, ⟪T a, b⟫_ℝ = ⟪a, T b⟫_ℝ) :
    IsSelfAdjoint Tℂ := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  rw [LinearMap.isSymmetric_iff_inner_map_self_real]
  intro z
  obtain ⟨a, b, rfl⟩ := hspan z
  have h := inner_complexification ι hι T Tℂ hT a b a b
  rw [hTsym b a] at h
  rw [real_inner_comm (T a) b] at h
  have hz : ⟪Tℂ (ι a + Complex.I • ι b), ι a + Complex.I • ι b⟫_ℂ
      = (((⟪T a, a⟫_ℝ + ⟪T b, b⟫_ℝ : ℝ)) : ℂ) := by
    rw [h]; push_cast; ring
  change star ⟪Tℂ (ι a + Complex.I • ι b), ι a + Complex.I • ι b⟫_ℂ
    = ⟪Tℂ (ι a + Complex.I • ι b), ι a + Complex.I • ι b⟫_ℂ
  rw [hz]
  simp

/-- A complex-linear operator that is the complexification of a real operator and whose adjoint
also respects the real structure is self-adjoint.  (Together with
`nonneg_complexification_iff` this makes the CFC available for real positive data without assuming
self-adjointness of the complexified operator.) -/
theorem isSelfAdjoint_complexification (ι : E → F)
    (hspan : ∀ z : F, ∃ a b : E, z = ι a + Complex.I • ι b)
    (T : E →L[ℝ] E) (Tℂ : F →L[ℂ] F) (hT : ∀ a, Tℂ (ι a) = ι (T a))
    (hTadj : ∀ a, ContinuousLinearMap.adjoint Tℂ (ι a) = ι (T a)) :
    IsSelfAdjoint Tℂ := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff']
  ext z
  obtain ⟨a, b, rfl⟩ := hspan z
  simp only [map_add, map_smul, hTadj, hT]

end Positivity

/-! ### The concrete real structure on `ℓ²(V)`

The real Hilbert space `lp (fun _ : V => ℝ) 2` sits inside the complex Hilbert space
`lp (fun _ : V => ℂ) 2` as the real-valued functions; this is the real structure to which the
abstract bridge above applies.  In particular every real Schur-kernel operator
(`PercLib.CriticalLRP.KernelOperator.kernelCLM`) is of this shape, so its positive-semidefinite
data can be fed into the complex CFC. -/

section L2

variable {V : Type*}

@[simp]
theorem ofRealLp_apply (f : lp (fun _ : V => ℝ) 2) (v : V) :
    (ofRealLp f : V → ℂ) v = ((f v : ℝ) : ℂ) := rfl

/-- Inner products of real-valued `ℓ²` functions are real. -/
theorem inner_ofRealLp (a b : lp (fun _ : V => ℝ) 2) :
    ⟪ofRealLp a, ofRealLp b⟫_ℂ = ((⟪a, b⟫_ℝ : ℝ) : ℂ) := by
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum, Complex.ofReal_tsum]
  refine tsum_congr fun v => ?_
  rw [ofRealLp_apply, ofRealLp_apply, RCLike.inner_apply, RCLike.inner_apply]
  simp [mul_comm]

/-- Every complex `ℓ²` function is a real-valued one plus `I` times a real-valued one. -/
theorem exists_ofRealLp_add (z : lp (fun _ : V => ℂ) 2) :
    ∃ a b : lp (fun _ : V => ℝ) 2, z = ofRealLp a + Complex.I • ofRealLp b := by
  have h2 : (2 : ℝ≥0∞).toReal = 2 := by norm_num
  have hz : Summable fun v => ‖z v‖ ^ (2 : ℝ≥0∞).toReal :=
    (lp.memℓp z).summable (by norm_num)
  have hre : Memℓp (fun v => (z v).re) 2 := by
    refine memℓp_gen (Summable.of_nonneg_of_le (fun v => by positivity) (fun v => ?_) hz)
    have h1 : ‖(z v).re‖ ≤ ‖z v‖ := by
      simpa [Real.norm_eq_abs] using Complex.abs_re_le_norm (z v)
    simpa [h2] using pow_le_pow_left₀ (norm_nonneg _) h1 2
  have him : Memℓp (fun v => (z v).im) 2 := by
    refine memℓp_gen (Summable.of_nonneg_of_le (fun v => by positivity) (fun v => ?_) hz)
    have h1 : ‖(z v).im‖ ≤ ‖z v‖ := by
      simpa [Real.norm_eq_abs] using Complex.abs_im_le_norm (z v)
    simpa [h2] using pow_le_pow_left₀ (norm_nonneg _) h1 2
  refine ⟨⟨fun v => (z v).re, hre⟩, ⟨fun v => (z v).im, him⟩, ?_⟩
  ext v
  simp only [lp.coeFn_add, Pi.add_apply, lp.coeFn_smul, Pi.smul_apply, ofRealLp_apply,
    smul_eq_mul]
  rw [mul_comm]
  exact (Complex.re_add_im (z v)).symm

/-- **Concrete realification bridge on `ℓ²`.**  A self-adjoint complex-linear operator on
`lp (V, ℂ) 2` which is the complexification of a real operator `T` on `lp (V, ℝ) 2` is
nonnegative in the Loewner order iff the real quadratic form of `T` is nonnegative. -/
theorem nonneg_complexification_lp
    (T : lp (fun _ : V => ℝ) 2 →L[ℝ] lp (fun _ : V => ℝ) 2)
    (Tℂ : lp (fun _ : V => ℂ) 2 →L[ℂ] lp (fun _ : V => ℂ) 2)
    (hT : ∀ a, Tℂ (ofRealLp a) = ofRealLp (T a)) (hsa : IsSelfAdjoint Tℂ) :
    0 ≤ Tℂ ↔ ∀ a, 0 ≤ ⟪T a, a⟫_ℝ :=
  nonneg_complexification_iff ofRealLp inner_ofRealLp exists_ofRealLp_add T Tℂ hT hsa

/-- **Concrete realification bridge on `ℓ²`, symmetric form.**  Only symmetry of the real operator
is needed; self-adjointness of the complexification is derived. -/
theorem nonneg_complexification_lp_of_symmetric
    (T : lp (fun _ : V => ℝ) 2 →L[ℝ] lp (fun _ : V => ℝ) 2)
    (Tℂ : lp (fun _ : V => ℂ) 2 →L[ℂ] lp (fun _ : V => ℂ) 2)
    (hT : ∀ a, Tℂ (ofRealLp a) = ofRealLp (T a))
    (hTsym : ∀ a b, ⟪T a, b⟫_ℝ = ⟪a, T b⟫_ℝ) :
    0 ≤ Tℂ ↔ ∀ a, 0 ≤ ⟪T a, a⟫_ℝ :=
  nonneg_complexification_lp T Tℂ hT
    (isSelfAdjoint_complexification_of_symmetric ofRealLp inner_ofRealLp exists_ofRealLp_add
      T Tℂ hT hTsym)

end L2

end Realification



/-! ### The combined real-operator statement -/

namespace Realification

open scoped lp ENNReal NNReal

/-- **The CFC square root for a complexified real Schur operator.**  Let `T` be a real operator on
`ℓ²(V; ℝ)` with a complex-linear extension `Tℂ` on `ℓ²(V; ℂ)`.  If the real quadratic form of `T`
is nonnegative (in particular `T` symmetric, e.g. a symmetric Schur kernel operator), then
`S = (Tℂ)^(3/2) = CFC.sqrt ((Tℂ)^3)` is a nonnegative self-adjoint square root of `(Tℂ)^3`, and on
real vectors its Gram form is the real cubic form `⟪T^3 a, a⟫_ℝ = ⟪S (ι a), S (ι a)⟫_ℂ`.

This is the conditional form used by the campaign: only the real kernel operator
`PercLib.CriticalLRP.KernelOperator.kernelCLM` and its positive-semidefinite quadratic form are
needed on the real side; the complex extension is an explicit hypothesis (`Tℂ` together with
`∀ a, Tℂ (ι a) = ι (T a)`).  No model kernel positivity or critical-operator boundedness is
asserted, and `Tℂ^3` is later identified with the threefold composed Schur kernel through
`kernelCLM_comp_apply`.
-/
theorem exists_sqrt_cube_real_operator {V : Type*}
    (T : lp (fun _ : V => ℝ) 2 →L[ℝ] lp (fun _ : V => ℝ) 2)
    (Tℂ : lp (fun _ : V => ℂ) 2 →L[ℂ] lp (fun _ : V => ℂ) 2)
    (hT : ∀ a, Tℂ (ofRealLp a) = ofRealLp (T a)) (hsa : IsSelfAdjoint Tℂ)
    (hTpos : ∀ a, 0 ≤ ⟪T a, a⟫_ℝ) :
    ∃ S : lp (fun _ : V => ℂ) 2 →L[ℂ] lp (fun _ : V => ℂ) 2,
      0 ≤ S ∧ S† = S ∧ S† * S = Tℂ ^ 3 ∧
        (∀ a, ⟪(T ^ 3) a, a⟫_ℝ = RCLike.re ⟪S (ofRealLp a), S (ofRealLp a)⟫_ℂ) := by
  have hpos : 0 ≤ Tℂ := (nonneg_complexification_lp T Tℂ hT hsa).mpr hTpos
  refine ⟨CFC.sqrtCube Tℂ, CFC.sqrtCube_nonneg Tℂ, CFC.sqrtCube_star Tℂ,
    CFC.ContinuousLinearMap.sqrtCube_adjoint_mul_self Tℂ hpos, ?_⟩
  intro a
  rw [← CFC.ContinuousLinearMap.inner_sqrtCube Tℂ hpos,
    complexification_pow_apply ofRealLp T Tℂ hT 3 a, inner_ofRealLp]
  exact (Complex.ofReal_re _).symm

end Realification

/-! ### Axiom audit -/

set_option linter.hashCommand false

#print axioms CFC.sqrtCube_nonneg
#print axioms CFC.sqrtCube_isSelfAdjoint
#print axioms CFC.sqrtCube_star
#print axioms CFC.sqrtCube_mul_self
#print axioms CFC.sqrtCube_star_mul_self
#print axioms CFC.eq_sqrtCube_of_mul_self
#print axioms CFC.mul_self_iff_eq_sqrtCube
#print axioms CFC.sqrtCube_eq_nnrpow
#print axioms CFC.sqrtCube_eq_rpow
#print axioms CFC.ContinuousLinearMap.sqrtCube_adjoint_mul_self
#print axioms CFC.ContinuousLinearMap.inner_sqrtCube
#print axioms CFC.ContinuousLinearMap.re_inner_cube_nonneg
#print axioms Realification.re_inner_complexification
#print axioms Realification.inner_complexification
#print axioms Realification.nonneg_complexification_iff
#print axioms Realification.isSelfAdjoint_complexification
#print axioms Realification.isSelfAdjoint_complexification_of_symmetric
#print axioms Realification.ext_of_eqOn_real
#print axioms Realification.complexification_pow_apply
#print axioms Realification.inner_ofRealLp
#print axioms Realification.exists_ofRealLp_add
#print axioms Realification.nonneg_complexification_lp
#print axioms Realification.nonneg_complexification_lp_of_symmetric
#print axioms Realification.exists_sqrt_cube_real_operator
