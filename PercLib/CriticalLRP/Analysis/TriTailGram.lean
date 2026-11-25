/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.
-/
module

public import PercLib.CriticalLRP.Analysis.TriTail.GramDefs

/-!
# Kozma's square-root / Gram factorization: the operator-theoretic fragment

`Analysis/TriTailSqrt.lean` proves Kozma's analytic step *given* an `ℓ²` vector `ξ` with
`∇(0,x) = ∑_y ξ y ξ (y - x)` (its hypothesis `hfac`), and records the construction of that `ξ`
as the remaining input. This file supplies the construction in the operator form of the input,
which is Kozma's own formulation (G. Kozma, *The triangle and the open triangle*, Ann. IHP
Probab. Stat. 47 (2011) 75--79, §2):

  "`Q(v,w) = ⟨S 1_v, S 1_w⟩` ... `S` is invariant to the automorphisms of `G` ... so `S 1_w` is
   a map of `S 1_v` under an automorphism `φ` taking `v` to `w`."

Let `H` be a real Hilbert space with a Hilbert basis `b` indexed by `ℤ^d` and let `S : H →L[ℝ] H`
be bounded with a translation-invariant kernel (`htrans`). Then

* `ξ y := ⟨b y, S (b 0)⟩` is in `ℓ²`, with `∑_y ξ y ^ 2 = ‖S (b 0)‖ ^ 2 < ∞`: the summability
  premise `hξ` of `openTriangleTail_tendsto_of_sqrtKernel` is *discharged*, not assumed;
* the kernel entry `⟨b 0, (S† ∘ S) (b x)⟩` is exactly the autocorrelation `∑_y ξ y ξ (y - x)`.

So the square-root input reduces to: *the configured open triangle is the `(0,·)` kernel of
`S† ∘ S` for a bounded translation-invariant `S`*. No operator square root has to be constructed,
because `S† ∘ S` is automatically positive semidefinite and, conversely, every positive
semidefinite `A` is `S† ∘ S` with `S = A^{1/2}`, which inherits translation invariance from `A`
(being a limit of polynomials in `A`). Hence "existence of the operator square root" is not the
gap; the identification of the model's open triangle with such a kernel is.

Two Lean-checked negative results close the other tempting shortcuts: (i) diagonal / positive
semidefinite data cannot replace the Gram factorization — the constant kernel `K ≡ 1` on `ℤ^d`
(`d ≥ 1`) is symmetric, positive semidefinite, translation invariant, with constant *finite*
diagonal `K x x = 1`, yet it is not the autocorrelation of any `ℓ²` vector; (ii) `ξ` cannot be
read off the kernel row — an `ℓ²` row need not be any autocorrelation, since an autocorrelation
never exceeds its value at the origin (`kernelRow_l2_not_autocorrelation`).

Upstream of the operator statement, `gramCoord_autocorr_of_translationAction` and
`openTriangleTail_tendsto_of_gramVector` give the intrinsic Hilbert-vector form
(`∇(0,x) = ⟨Ξ, U x Ξ⟩`) with no boundedness assumption, and `htrans_of_translationAction` derives
`htrans` from `S` commuting with the translation action.

No `sorry`, no `admit`, no `native_decide`, no custom axioms.
-/

@[expose] public section

open scoped ENNReal Topology RealInnerProductSpace
open Filter

namespace PercLib.CriticalLRP.TriTail

/-! ### Coordinates along a Hilbert basis -/

section Abstract

variable {d : ℕ}
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]


omit [CompleteSpace H] in
/-- **The Gram coordinates are in `ℓ²`.** Parseval along the Hilbert basis: the squared `ℓ²` norm
of `ξ` is the squared norm of the vector it came from. In particular the summability premise
`hξ : Summable (fun y => ξ y ^ 2)` of `openTriangleTail_tendsto_of_sqrtKernel` is automatic for
coordinates of a vector, and needs no hypothesis. -/
theorem gramCoord_sq_summable (b : HilbertBasis (Fin d → ℤ) ℝ H) (Ξ : H) :
    Summable fun y => gramCoord b Ξ y ^ 2 := by
  have h := HilbertBasis.summable_inner_mul_inner b Ξ Ξ
  refine h.congr fun y => ?_
  simp only [gramCoord]
  rw [real_inner_comm Ξ (b y)]
  ring

omit [CompleteSpace H] in
/-- The squared `ℓ²` norm of the Gram coordinates is the squared norm of the vector. -/
theorem gramCoord_tsum_sq (b : HilbertBasis (Fin d → ℤ) ℝ H) (Ξ : H) :
    ∑' y, gramCoord b Ξ y ^ 2 = ‖Ξ‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq Ξ, ← HilbertBasis.tsum_inner_mul_inner b Ξ Ξ]
  refine tsum_congr fun y => ?_
  simp only [gramCoord]
  rw [real_inner_comm Ξ (b y)]
  ring

omit [CompleteSpace H] in
/-- **Kernel summability**: the autocorrelation series defining the kernel entry converges, with
no further hypothesis — it is `HilbertBasis.summable_inner_mul_inner` for the pair
`(S (b 0), S (b x))`. Both `ℓ²` factors are essential; the diagonal alone cannot supply this
(`constantKernel_not_gram`). -/
theorem gramCoord_kernel_summable (b : HilbertBasis (Fin d → ℤ) ℝ H) (S : H →L[ℝ] H)
    (x : Fin d → ℤ) :
    Summable fun y => gramCoord b (S (b 0)) y * ⟪b y, S (b x)⟫ := by
  have h := HilbertBasis.summable_inner_mul_inner b (S (b 0)) (S (b x))
  refine h.congr fun y => ?_
  simp only [gramCoord]
  rw [real_inner_comm (S (b 0)) (b y)]

/-- **The kernel of `S† ∘ S` is the autocorrelation of the Gram coordinates.** This is Kozma's
`Q(v,w) = ⟨S 1_v, S 1_w⟩ = ⟨ξ, T_{v-w} ξ⟩`, with the translation invariance of the kernel of `S`
supplied as the explicit hypothesis `htrans`. -/
theorem gramCoord_autocorr_eq (b : HilbertBasis (Fin d → ℤ) ℝ H) (S : H →L[ℝ] H)
    (htrans : ∀ (x y : Fin d → ℤ), ⟪b (y - x), S (b 0)⟫ = ⟪b y, S (b x)⟫)
    (x : Fin d → ℤ) :
    (∑' y, gramCoord b (S (b 0)) y * gramCoord b (S (b 0)) (y - x))
      = ⟪b 0, (ContinuousLinearMap.adjoint S).comp S (b x)⟫ := by
  have hshift : ∀ y : Fin d → ℤ, gramCoord b (S (b 0)) (y - x) = ⟪b y, S (b x)⟫ := by
    intro y
    simpa only [gramCoord] using htrans x y
  have hker : (⟪b 0, (ContinuousLinearMap.adjoint S).comp S (b x)⟫ : ℝ)
      = ⟪S (b 0), S (b x)⟫ := by
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right]
  rw [hker, ← HilbertBasis.tsum_inner_mul_inner b (S (b 0)) (S (b x))]
  refine tsum_congr fun y => ?_
  simp only [gramCoord]
  rw [real_inner_comm (S (b 0)) (b y), htrans x y]

omit [CompleteSpace H] in
/-- The identity operator has a translation-invariant kernel, so `htrans` is satisfiable. -/
theorem identity_htrans (b : HilbertBasis (Fin d → ℤ) ℝ H) :
    ∀ (x y : Fin d → ℤ),
      ⟪b (y - x), (1 : H →L[ℝ] H) (b 0)⟫ = ⟪b y, (1 : H →L[ℝ] H) (b x)⟫ := by
  intro x y
  have hone : ∀ z : Fin d → ℤ, (1 : H →L[ℝ] H) (b z) = b z := fun z => rfl
  rw [hone, hone, orthonormal_iff_ite.mp b.orthonormal (y - x) 0,
    orthonormal_iff_ite.mp b.orthonormal y x]
  simp only [sub_eq_zero]

/-- **Concrete non-vacuity witness**: for the identity operator the Gram coordinates of the basis
vector `b 0` are the delta sequence at the origin, and their autocorrelation is the delta
function. So the main identity holds for a concrete non-degenerate operator. -/
theorem identity_gram_witness (b : HilbertBasis (Fin d → ℤ) ℝ H) (x : Fin d → ℤ) :
    (∑' y, gramCoord b (b 0) y * gramCoord b (b 0) (y - x)) = if x = 0 then 1 else 0 := by
  have hid : (1 : H →L[ℝ] H) (b 0) = b 0 := rfl
  rw [← hid, gramCoord_autocorr_eq b 1 (identity_htrans b) x]
  have hker : (⟪b 0, (ContinuousLinearMap.adjoint (1 : H →L[ℝ] H)).comp
      (1 : H →L[ℝ] H) (b x)⟫ : ℝ) = ⟪b 0, b x⟫ := by
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right]
    simp
  rw [hker, orthonormal_iff_ite.mp b.orthonormal 0 x]
  by_cases hx : x = 0
  · subst hx
    simp
  · have hx' : ¬ (0 = x) := fun h => hx h.symm
    simp [hx, hx']

end Abstract

/-- **The abstract setting is the model's own space**: `ℓ²(ℤ^d, ℝ)` carries a Hilbert basis, so
the hypothesis `b` of the theorems above is available in the function space on which Kozma's `S`
acts. -/
theorem nonempty_hilbertBasis_l2 (d : ℕ) :
    Nonempty (HilbertBasis (Fin d → ℤ) ℝ (lp (fun _ : Fin d → ℤ => ℝ) 2)) :=
  ⟨default⟩

/-! ### The reduction of Kozma's square-root input to a bounded operator -/

section Reduction

variable {d : ℕ}

/-- **Kozma's square-root input, reduced to a bounded translation-invariant operator.**

If the open triangle at `(0,x)` is the kernel entry `⟨b 0, (S† ∘ S) (b x)⟩` of a bounded operator
`S† ∘ S` whose kernel is translation invariant (`htrans`), then the open-triangle tail decays.

Compared with `openTriangleTail_tendsto_of_sqrtKernel` the summability of `ξ` is not a hypothesis:
it is `gramCoord_sq_summable`. -/
theorem openTriangleTail_tendsto_of_translationInvariantFactor
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {J : Sym2 (Fin d → ℤ) → ℝ} {hJ : ∀ e, 0 ≤ J e} {β : NNReal}
    (b : HilbertBasis (Fin d → ℤ) ℝ H) (S : H →L[ℝ] H)
    (htrans : ∀ (x y : Fin d → ℤ), ⟪b (y - x), S (b 0)⟫ = ⟪b y, S (b x)⟫)
    (hfac : ∀ x : Fin d → ℤ, openTriangle J hJ β 0 x
      = ENNReal.ofReal ⟪b 0, (ContinuousLinearMap.adjoint S).comp S (b x)⟫) :
    Tendsto (openTriangleTail J hJ β) atTop (𝓝 0) := by
  refine openTriangleTail_tendsto_of_sqrtKernel (ξ := gramCoord b (S (b 0)))
    (gramCoord_sq_summable b (S (b 0))) fun x => ?_
  rw [hfac x, gramCoord_autocorr_eq b S htrans x]

section VectorForm

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- **Kozma's autocorrelation identity in intrinsic Hilbert form.** If `U z` implements the
translations of `ℤ^d` on the Hilbert basis (`U z (b y) = b (y + z)`), then for *any* `Ξ : H` the
autocorrelation of its Gram coordinates is the translation matrix element `⟨Ξ, U x Ξ⟩`. No
boundedness, no positivity, and no square root is involved: this is exactly Kozma's
`Q(v,w) = ⟨ξ, T_{v-w} ξ⟩` with `ξ = Ξ`. -/
theorem gramCoord_autocorr_of_translationAction (b : HilbertBasis (Fin d → ℤ) ℝ H)
    (U : (Fin d → ℤ) → H ≃ₗᵢ[ℝ] H) (hU : ∀ (z y : Fin d → ℤ), U z (b y) = b (y + z))
    (Ξ : H) (x : Fin d → ℤ) :
    (∑' y, gramCoord b Ξ y * gramCoord b Ξ (y - x)) = ⟪Ξ, U x Ξ⟫ := by
  have hsymm : ∀ y : Fin d → ℤ, (U x).symm (b y) = b (y - x) := by
    intro y
    have h1 : U x (b (y - x)) = b y := by
      rw [hU x (y - x), sub_add_cancel]
    rw [← h1, LinearIsometryEquiv.symm_apply_apply]
  have hcoord : ∀ y : Fin d → ℤ, gramCoord b Ξ (y - x) = ⟪b y, U x Ξ⟫ := by
    intro y
    have h := LinearIsometryEquiv.inner_map_map (U x) ((U x).symm (b y)) Ξ
    rw [LinearIsometryEquiv.apply_symm_apply, hsymm y] at h
    simpa only [gramCoord] using h.symm
  rw [← HilbertBasis.tsum_inner_mul_inner b Ξ (U x Ξ)]
  refine tsum_congr fun y => ?_
  rw [hcoord y]
  simp only [gramCoord]
  rw [real_inner_comm Ξ (b y)]

omit [CompleteSpace H] in
/-- **Kozma's square-root input in translation-action form.** If the configured open triangle at
`(0,x)` is the translation matrix element `⟨Ξ, U x Ξ⟩` of a single vector `Ξ` under a translation
action `U` permuting the Hilbert basis, then the open-triangle tail decays. The `ℓ²` summability of
the Gram coordinates is automatic (`gramCoord_sq_summable`). -/
theorem openTriangleTail_tendsto_of_gramVector
    {J : Sym2 (Fin d → ℤ) → ℝ} {hJ : ∀ e, 0 ≤ J e} {β : NNReal}
    (b : HilbertBasis (Fin d → ℤ) ℝ H) (U : (Fin d → ℤ) → H ≃ₗᵢ[ℝ] H)
    (hU : ∀ (z y : Fin d → ℤ), U z (b y) = b (y + z)) (Ξ : H)
    (hfac : ∀ x : Fin d → ℤ, openTriangle J hJ β 0 x = ENNReal.ofReal ⟪Ξ, U x Ξ⟫) :
    Tendsto (openTriangleTail J hJ β) atTop (𝓝 0) := by
  refine openTriangleTail_tendsto_of_sqrtKernel (ξ := gramCoord b Ξ)
    (gramCoord_sq_summable b Ξ) fun x => ?_
  rw [hfac x, gramCoord_autocorr_of_translationAction b U hU Ξ x]

omit [CompleteSpace H] in
/-- **The diagonal supplies the constant**, recovered from the Gram structure: the translation
matrix element never exceeds its value at the origin, `|⟨Ξ, U x Ξ⟩| ≤ ⟨Ξ, Ξ⟩`. This is the
`ℓ²` Cauchy–Schwarz bound that the landed `openTriangle_le_diagonal` obtains from the model; here it
is automatic, which is why the Gram form needs no separate diagonal estimate. -/
theorem gramVector_abs_le_self (U : (Fin d → ℤ) → H ≃ₗᵢ[ℝ] H) (Ξ : H) (x : Fin d → ℤ) :
    |⟪Ξ, U x Ξ⟫| ≤ ⟪Ξ, Ξ⟫ := by
  have h1 : |⟪Ξ, U x Ξ⟫| ≤ ‖Ξ‖ * ‖Ξ‖ := by
    simpa using abs_real_inner_le_norm Ξ (U x Ξ)
  rw [real_inner_self_eq_norm_sq Ξ, pow_two]
  exact h1

omit [CompleteSpace H] in
/-- **The triangle condition from the vector form.** -/
theorem openTriangleSelf_lt_top_of_gramVector
    {J : Sym2 (Fin d → ℤ) → ℝ} {hJ : ∀ e, 0 ≤ J e} {β : NNReal}
    (b : HilbertBasis (Fin d → ℤ) ℝ H) (U : (Fin d → ℤ) → H ≃ₗᵢ[ℝ] H)
    (hU : ∀ (z y : Fin d → ℤ), U z (b y) = b (y + z)) (Ξ : H)
    (hfac : ∀ x : Fin d → ℤ, openTriangle J hJ β 0 x = ENNReal.ofReal ⟪Ξ, U x Ξ⟫) :
    openTriangleSelf J hJ β 0 < ⊤ := by
  refine openTriangleSelf_lt_top_of_sqrtKernel (ξ := gramCoord b Ξ) fun x => ?_
  rw [hfac x, gramCoord_autocorr_of_translationAction b U hU Ξ x]

end VectorForm

/-- **Translation invariance of `S` in the form of Kozma (2011), §2.** If a family `U z` of linear
isometry equivalences implements the translations of `ℤ^d` on the Hilbert basis
(`U z (b y) = b (y + z)`) and the bounded operator `S` commutes with that action
(`S (U x v) = U x (S v)` — Kozma's "`S` is invariant to the automorphisms of `G`"), then the
kernel of `S` is translation invariant in the sense of `htrans`. So `htrans` is not an extra
matrix-entry assumption: it is implied by intertwining the translation action. -/
theorem htrans_of_translationAction
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (b : HilbertBasis (Fin d → ℤ) ℝ H)
    (U : (Fin d → ℤ) → H ≃ₗᵢ[ℝ] H) (hU : ∀ (z y : Fin d → ℤ), U z (b y) = b (y + z))
    (S : H →L[ℝ] H) (hS : ∀ (x : Fin d → ℤ) (v : H), S (U x v) = U x (S v)) :
    ∀ (x y : Fin d → ℤ), ⟪b (y - x), S (b 0)⟫ = ⟪b y, S (b x)⟫ := by
  intro x y
  have hSb : S (b x) = U x (S (b 0)) := by
    have hbx : b x = U x (b 0) := by
      rw [hU x 0, zero_add]
    rw [hbx, hS]
  have hsymm : (U x).symm (b y) = b (y - x) := by
    have h1 : U x (b (y - x)) = b y := by
      rw [hU x (y - x), sub_add_cancel]
    rw [← h1, LinearIsometryEquiv.symm_apply_apply]
  have hinner : (⟪b y, U x (S (b 0))⟫ : ℝ) = ⟪(U x).symm (b y), S (b 0)⟫ := by
    have h := LinearIsometryEquiv.inner_map_map (U x) ((U x).symm (b y)) (S (b 0))
    rwa [LinearIsometryEquiv.apply_symm_apply] at h
  rw [hSb, hinner, hsymm]

/-- **The end-user form of the reduction**: Kozma's hypotheses written as a translation action on
`H` (`U`, `hU`) plus invariance of `S` (`hS`), with no matrix-entry condition. -/
theorem openTriangleTail_tendsto_of_translationAction
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {J : Sym2 (Fin d → ℤ) → ℝ} {hJ : ∀ e, 0 ≤ J e} {β : NNReal}
    (b : HilbertBasis (Fin d → ℤ) ℝ H) (U : (Fin d → ℤ) → H ≃ₗᵢ[ℝ] H)
    (hU : ∀ (z y : Fin d → ℤ), U z (b y) = b (y + z))
    (S : H →L[ℝ] H) (hS : ∀ (x : Fin d → ℤ) (v : H), S (U x v) = U x (S v))
    (hfac : ∀ x : Fin d → ℤ, openTriangle J hJ β 0 x
      = ENNReal.ofReal ⟪b 0, (ContinuousLinearMap.adjoint S).comp S (b x)⟫) :
    Tendsto (openTriangleTail J hJ β) atTop (𝓝 0) :=
  openTriangleTail_tendsto_of_translationInvariantFactor b S
    (htrans_of_translationAction b U hU S hS) hfac

/-- **The triangle condition from the factorization**: under the same operator hypothesis the
triangle diagram `∇_{β} = ∇_β(0,0)` is finite, with no separate summability input (contrast
`openTriangleSelf_lt_top_of_sqrtKernel`, which takes `hfac` for the `ℓ²` vector directly). -/
theorem openTriangleSelf_lt_top_of_translationInvariantFactor
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {J : Sym2 (Fin d → ℤ) → ℝ} {hJ : ∀ e, 0 ≤ J e} {β : NNReal}
    (b : HilbertBasis (Fin d → ℤ) ℝ H) (S : H →L[ℝ] H)
    (htrans : ∀ (x y : Fin d → ℤ), ⟪b (y - x), S (b 0)⟫ = ⟪b y, S (b x)⟫)
    (hfac : ∀ x : Fin d → ℤ, openTriangle J hJ β 0 x
      = ENNReal.ofReal ⟪b 0, (ContinuousLinearMap.adjoint S).comp S (b x)⟫) :
    openTriangleSelf J hJ β 0 < ⊤ := by
  refine openTriangleSelf_lt_top_of_sqrtKernel (ξ := gramCoord b (S (b 0))) fun x => ?_
  rw [hfac x, gramCoord_autocorr_eq b S htrans x]

/-- **The self-adjoint (positive semidefinite) form**, which is literally Kozma's
`Q(v,w) = ⟨S 1_v, S 1_w⟩` for a positive operator `S`: for self-adjoint `S` the kernel entry of
`S† ∘ S = S ∘ S` is `⟨b 0, S (S (b x))⟩ = ⟨S (b 0), S (b x)⟩`. -/
theorem openTriangleTail_tendsto_of_selfAdjointFactor
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {J : Sym2 (Fin d → ℤ) → ℝ} {hJ : ∀ e, 0 ≤ J e} {β : NNReal}
    (b : HilbertBasis (Fin d → ℤ) ℝ H) (S : H →L[ℝ] H)
    (hsadj : ContinuousLinearMap.adjoint S = S)
    (htrans : ∀ (x y : Fin d → ℤ), ⟪b (y - x), S (b 0)⟫ = ⟪b y, S (b x)⟫)
    (hfac : ∀ x : Fin d → ℤ, openTriangle J hJ β 0 x
      = ENNReal.ofReal ⟪b 0, S (S (b x))⟫) :
    Tendsto (openTriangleTail J hJ β) atTop (𝓝 0) := by
  refine openTriangleTail_tendsto_of_translationInvariantFactor b S htrans fun x => ?_
  rw [hfac x, hsadj]
  rfl

end Reduction

/-! ### Diagonal finiteness is not a substitute for Gram vectors -/

section Negative

variable {d : ℕ}


/-- **The insufficient condition, Lean-checked.** The constant kernel on `ℤ^d` is symmetric,
positive semidefinite (a rank-one Gram matrix `v x * v y` with `v ≡ 1`), translation invariant, and
has constant diagonal `K x x = 1`. Every hypothesis of the tempting argument "the diagonal is
finite and the kernel is positive, hence the off-diagonal decays" holds. -/
theorem constantKernel_psd_data (d : ℕ) :
    (∀ x y : Fin d → ℤ, constantKernel d x y = constantKernel d y x) ∧
      (∃ v : (Fin d → ℤ) → ℝ, ∀ x y : Fin d → ℤ, constantKernel d x y = v x * v y) ∧
      (∀ x : Fin d → ℤ, constantKernel d x x = 1) ∧
      (∀ x y z : Fin d → ℤ, constantKernel d (x + z) (y + z) = constantKernel d x y) := by
  refine ⟨fun x y => rfl, ⟨fun _ => 1, fun x y => by simp [constantKernel]⟩, fun x => rfl,
    fun x y z => rfl⟩

/-- **A Lean-checked counterexample to the tempting insufficient condition.**

The constant kernel `K x y = 1` on `ℤ^d` (`d ≥ 1`) is

* symmetric: `K x y = K y x`,
* positive semidefinite: it is the Gram matrix `v x * v y` of the constant family `v ≡ 1`,
* translation invariant, with constant *finite* diagonal: `K x x = 1` for every `x`,

and yet it is **not** the autocorrelation `∑_y ξ y ξ (y - x)` of any `ℓ²` vector. Hence diagonal /
positive-semidefinite / finite-diagonal data cannot replace the Gram factorization `hfac`: the
`ℓ²` summability of `ξ` is a genuinely stronger requirement, and Kozma's argument cannot be run
from the diagonal bound alone. -/
theorem constantKernel_not_gram (hd : 0 < d) :
    ¬ ∃ ξ : (Fin d → ℤ) → ℝ, Summable (fun y => ξ y ^ 2) ∧
      ∀ x : Fin d → ℤ, (∑' y, ξ y * ξ (y - x)) = 1 := by
  rintro ⟨ξ, hξ, hval⟩
  obtain ⟨N, hN⟩ := exists_linfNorm_tsum_mul_shift_le (d := d) hξ (ε := 1 / 2) (by norm_num)
  have hlarge : ∃ x : Fin d → ℤ, N ≤ FiniteVolume.linfNorm x := by
    refine ⟨fun _ => (N : ℤ), ?_⟩
    have hmem : (⟨0, hd⟩ : Fin d) ∈ (Finset.univ : Finset (Fin d)) := Finset.mem_univ _
    have hle : ((fun _ : Fin d => (N : ℤ)) ⟨0, hd⟩).natAbs ≤
        FiniteVolume.linfNorm (fun _ : Fin d => (N : ℤ)) := by
      unfold FiniteVolume.linfNorm
      exact Finset.le_sup (f := fun i : Fin d => ((fun _ : Fin d => (N : ℤ)) i).natAbs) hmem
    simpa using hle
  obtain ⟨x, hx⟩ := hlarge
  have h1 : |∑' y, ξ y * ξ (y - x)| ≤ (1 : ℝ) / 2 := hN x hx
  rw [hval x] at h1
  norm_num at h1

end Negative


section RowL2

variable {d : ℕ}

/-- **The kernel row being in `ℓ²` is not enough to be an autocorrelation.**  The tempting move
"take `ξ` to be the row `K(0,·)` of the kernel" is invalid: in Kozma's argument `ξ = S 1_0`, and
the kernel entry `⟨b 0, (S†S) (b x)⟩` is *not* the row of `ξ`.  Here is a finitely supported (hence
`ℓ²`) row `c` with `c 0 = 1` and `c a = 2` at a nonzero lattice point `a`; no `ℓ²` vector has `c`
as its autocorrelation, because an autocorrelation never exceeds its value at `0` (AM--GM). -/
theorem kernelRow_l2_not_autocorrelation (hd : 0 < d) :
    ∃ c : (Fin d → ℤ) → ℝ, Summable (fun x => c x ^ 2) ∧
      ¬ ∃ ξ : (Fin d → ℤ) → ℝ, Summable (fun y => ξ y ^ 2) ∧
        ∀ x : Fin d → ℤ, (∑' y, ξ y * ξ (y - x)) = c x := by
  classical
  set a : Fin d → ℤ := fun _ => 1 with ha
  have ha0 : a ≠ 0 := by
    intro h
    have hv := congrFun h ⟨0, hd⟩
    simp [ha] at hv
  set c : (Fin d → ℤ) → ℝ := fun x => if x = 0 then 1 else if x = a then 2 else 0 with hc
  have hc0 : c 0 = 1 := by simp [hc]
  have hca : c a = 2 := by simp [hc, ha0]
  refine ⟨c, ?_, ?_⟩
  · have hF : Summable (fun x : Fin d → ℤ =>
        if x ∈ ({0, a} : Finset (Fin d → ℤ)) then (if x = 0 then (1 : ℝ) else 4) else 0) :=
      summable_ite_finset ({0, a} : Finset (Fin d → ℤ))
        (fun x : Fin d → ℤ => if x = 0 then (1 : ℝ) else 4)
    refine hF.congr fun x => ?_
    simp only [Finset.mem_insert, Finset.mem_singleton]
    by_cases h0 : x = 0
    · subst h0
      simp [c]
    · by_cases h1 : x = a
      · subst h1
        norm_num [c, h0]
      · simp [c, h0, h1]
  · rintro ⟨ξ, hξ, hval⟩
    have h0 : (∑' y : Fin d → ℤ, ξ y * ξ y) = 1 := by
      have h := hval 0
      rw [hc0] at h
      simpa using h
    have hA : (∑' y : Fin d → ℤ, ξ y * ξ (y - a)) = 2 := by
      have h := hval a
      rwa [hca] at h
    have hsq : (∑' y : Fin d → ℤ, ξ y ^ 2) = 1 := by
      rw [← h0]
      exact tsum_congr fun y => by ring
    have hshift : Summable fun y : Fin d → ℤ => ξ (y - a) ^ 2 := by
      have h := (Equiv.summable_iff (f := fun z : Fin d → ℤ => ξ z ^ 2)
        (Equiv.subRight a)).mpr hξ
      simpa [Equiv.subRight_apply, Function.comp_def] using h
    have hsqshift : (∑' y : Fin d → ℤ, ξ (y - a) ^ 2) = 1 := by
      rw [show (∑' y : Fin d → ℤ, ξ (y - a) ^ 2) = ∑' y : Fin d → ℤ, ξ y ^ 2 from by
        simpa [Equiv.subRight_apply] using
          (Equiv.tsum_eq (Equiv.subRight a) (fun z : Fin d → ℤ => ξ z ^ 2))]
      exact hsq
    have hpt : ∀ y : Fin d → ℤ, ξ y * ξ (y - a) ≤ (1 / 2) * (ξ y ^ 2 + ξ (y - a) ^ 2) := by
      intro y
      nlinarith [sq_nonneg (ξ y - ξ (y - a))]
    have hprod : Summable fun y : Fin d → ℤ => ξ y * ξ (y - a) := by
      refine Summable.of_norm_bounded (g := fun y : Fin d → ℤ =>
        (1 / 2) * (ξ y ^ 2 + ξ (y - a) ^ 2)) ((hξ.add hshift).mul_left (1 / 2)) fun y => ?_
      rw [Real.norm_eq_abs, abs_le]
      constructor
      · nlinarith [sq_nonneg (ξ y + ξ (y - a))]
      · exact hpt y
    have hle := Summable.tsum_le_tsum hpt hprod ((hξ.add hshift).mul_left (1 / 2))
    rw [tsum_mul_left, Summable.tsum_add hξ hshift, hsq, hsqshift] at hle
    rw [hA] at hle
    norm_num at hle

end RowL2

end PercLib.CriticalLRP.TriTail

/-! ### Axiom audit -/

set_option linter.hashCommand false
#print axioms PercLib.CriticalLRP.TriTail.gramCoord_sq_summable
#print axioms PercLib.CriticalLRP.TriTail.gramCoord_tsum_sq
#print axioms PercLib.CriticalLRP.TriTail.gramCoord_kernel_summable
#print axioms PercLib.CriticalLRP.TriTail.gramCoord_autocorr_eq
#print axioms PercLib.CriticalLRP.TriTail.identity_htrans
#print axioms PercLib.CriticalLRP.TriTail.identity_gram_witness
#print axioms PercLib.CriticalLRP.TriTail.nonempty_hilbertBasis_l2
#print axioms PercLib.CriticalLRP.TriTail.openTriangleTail_tendsto_of_translationInvariantFactor
#print axioms PercLib.CriticalLRP.TriTail.gramCoord_autocorr_of_translationAction
#print axioms PercLib.CriticalLRP.TriTail.openTriangleTail_tendsto_of_gramVector
#print axioms PercLib.CriticalLRP.TriTail.gramVector_abs_le_self
#print axioms PercLib.CriticalLRP.TriTail.openTriangleSelf_lt_top_of_gramVector
#print axioms PercLib.CriticalLRP.TriTail.htrans_of_translationAction
#print axioms PercLib.CriticalLRP.TriTail.openTriangleTail_tendsto_of_translationAction
#print axioms PercLib.CriticalLRP.TriTail.openTriangleSelf_lt_top_of_translationInvariantFactor
#print axioms PercLib.CriticalLRP.TriTail.openTriangleTail_tendsto_of_selfAdjointFactor
#print axioms PercLib.CriticalLRP.TriTail.constantKernel_psd_data
#print axioms PercLib.CriticalLRP.TriTail.constantKernel_not_gram
#print axioms PercLib.CriticalLRP.TriTail.kernelRow_l2_not_autocorrelation
