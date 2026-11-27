/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

# Triangle normalization from a concrete autocorrelation profile

Integrated and independently rebuilt from accepted Ultramath `smwyop3kc`, member `m3`.
Definitions have been moved to `Analysis.TriTailNormalization.Defs`.  Read-only base: `.scratch/critical-lrp-orchestration`
HEAD `2e544875fbae83810bd1aa1de1d8faddcdeacc05`.

`TriTail.openTriangleSelf J hJ β 0 < ⊤` (Kozma's `∇_{β_c} < ∞`) is used as an
input (`hTri`) by the §I.4.18/§I.4.20 consumers.  `TriTailSqrt` /
`TriTailGram` derive it from the *operator* statement “`∇` is the Gram matrix
`⟨Ξ, U x Ξ⟩` of an `ℓ²` vector” (`hfac`), but `hfac` at `x = 0` already *is* the
finiteness statement, so nothing in the worktree *derives* `hTri` from data
about the two-point function itself.

This file derives it from a concrete, diagonal-normalized autocorrelation
kernel, and records what the remaining structural hypotheses cannot do.

Context from the source (`paper.txt` L1820–1837): the triangle condition is
Case 3 of the hypothesis of Proposition I.4.2, i.e. a genuine source hypothesis;
the only source-level derivation would be the pointwise bound (I.1.15) of
Corollary II.1.9, established only at the end of the series (Remark I.1.13,
`paper.txt` L753–765).  So `hTri` is not a formalization gap, and the content
here is a *derived* route to it from structural data.

* `openTriangleKernel` — the open triangle of an abstract nonnegative kernel,
  definitionally the model's `openTriangle` at `τ = twoPointFunction J hJ β`.

* `openTriangleKernel_zero_le_of_rowSum_le` — **the row-sum criterion**:
  a uniform bound `R` on the row sums of `τ` gives `∇(0,0) ≤ R ^ 3`
  (`∇ = ⟨δ_0, τ³ δ_0⟩`, so this is the ℓ¹→ℓ¹ operator-norm bound, i.e. a
  sufficient ℓ¹-row form of Kozma's requirement that `τ` be a bounded operator).
  It cannot reach the critical model — `τ(0,y) ≍ |y|^{−d+α}` is not row-summable
  for `α > 0` — which is exactly why `hTri` is not free.

* `gramKernel f` — the translation-invariant Gram/autocorrelation kernel
  `Γ_f(u,v) = ∑_z f z · f (z + v - u)`, i.e. Kozma's `Q(v,w) = ⟨S 1_v, S 1_w⟩`
  for the profile `f` (an *actual* square root, not an assumed one), with the
  diagonal checked: `Γ_f(u,u) = ∑_z f z ^ 2`.

* `openTriangleSelf_le_of_gramProfile` / `_lt_top_of_gramProfile` — **`hTri`
  from a summable normalized profile**: if the model's two-point function is
  `Γ_f` for `0 ≤ f` summable, then `∇_{β_c} ≤ (∑ f)^6 < ∞`.  The boundedness of
  `∇` is *derived*, not assumed; the only structural input is the pointwise
  identification of `τ` with the autocorrelation kernel, and the `ℓ¹` row sums
  are computed here (`Γ_f`'s rows have mass exactly `(∑ f)^2`).  The domination
  versions (`openTriangleSelf_le_of_gramDomination`, `..._lt_top_of_...`) need
  only `τ ≤ Γ_f` pointwise, and
  `exists_lt_gramKernel_of_openTriangleKernel_eq_top` is their contrapositive.

* `gramKernel_self` / `one_eq_tsum_sq_of_ident` — the diagonal normalization
  `τ(x,x) = 1` (`twoPointFunction_self`) is *exactly* `∑_z f z ^ 2 = 1`, so the
  profile is forced to be an `ℓ²` unit vector; the hypothesis set is
  consistent with the model's own normalization.

* `gramKernel_delta` / `openTriangleKernel_gramKernel_delta` — a computed
  non-vacuity witness: the delta profile gives the identity kernel, `τ(x,x)=1`,
  and `∇(0,0) = 1 < ⊤`.

* `diagonal_one_translationInvariant_not_sufficient` — a **formal obstruction**:
  `τ ≡ 1` is symmetric, bounded by `1`, translation invariant and has diagonal
  `1` (and is the Gram matrix of the constant family,
  `constantKernel_psd_data`), yet its open-triangle self energy is `⊤`.  So none
  of the four properties production proves about its own `twoPointFunction` —
  even with positive semidefiniteness — can supply `hTri`; the summability of
  the profile in the Gram representation is genuinely used.

No `sorry`, no `admit`, no `native_decide`, no custom axioms.
-/
module

public import PercLib.CriticalLRP.Analysis.TriTailNormalization.Defs
public import PercLib.CriticalLRP.Analysis.TriTailGram
public import PercLib.CriticalLRP.Orchestration.Defs

/-! # Triangle normalization from an explicit autocorrelation profile -/

@[expose] public section

open scoped ENNReal
open Filter

set_option linter.unusedSectionVars false
set_option linter.hashCommand false

namespace PercLib.CriticalLRP.TriTail

variable {d : ℕ}

/-! ### The open triangle of an abstract kernel -/

/-! The open triangle `∇(x,y) = ∑_{u,v} τ(x,u) τ(u,v) τ(v,y)` of an abstract nonnegative
two-point kernel `τ`.  The model's `openTriangle J hJ β` is the case `τ = twoPointFunction J hJ β`
(`openTriangle_eq_openTriangleKernel`, by `rfl`). -/



/-- The configured open triangle is the abstract one at `τ = twoPointFunction J hJ β`. -/
theorem openTriangle_eq_openTriangleKernel (J : Sym2 (Fin d → ℤ) → ℝ) (hJ : ∀ e, 0 ≤ J e)
    (β : NNReal) (x y : Fin d → ℤ) :
    openTriangle J hJ β x y = openTriangleKernel (twoPointFunction J hJ β) x y := rfl

/-! ### The row-sum criterion -/

/-- **Uniformly bounded row sums give the triangle condition.**  If every row of the kernel `τ`
carries at most mass `R`, then the open-triangle self energy at the origin is at most `R ^ 3`.

The proof is the ℓ¹ operator-norm estimate `⟨δ_0, τ³ δ_0⟩ ≤ ‖τ‖₁³`, split as
`∑_u τ(0,u) · (sup_v τ(v,0)) · (∑_v τ(u,v))`; no positivity of `τ` beyond `ℝ≥0∞`-valuedness and
no absolute values are needed. -/
theorem openTriangleKernel_zero_le_of_rowSum_le (τ : (Fin d → ℤ) → (Fin d → ℤ) → ℝ≥0∞)
    {R : ℝ≥0∞} (hR : ∀ x, ∑' y, τ x y ≤ R) :
    openTriangleKernel τ 0 0 ≤ R ^ 3 := by
  have hcol : ∀ v : Fin d → ℤ, τ v 0 ≤ R :=
    fun v => (ENNReal.le_tsum (f := fun y => τ v y) 0).trans (hR v)
  have hinner : ∀ u : Fin d → ℤ, (∑' v, τ u v * τ v 0) ≤ R * R := by
    intro u
    calc ∑' v, τ u v * τ v 0
        ≤ ∑' v, τ u v * R := ENNReal.tsum_le_tsum fun v => by gcongr; exact hcol v
      _ = (∑' v, τ u v) * R := ENNReal.tsum_mul_right
      _ ≤ R * R := by gcongr; exact hR u
  calc openTriangleKernel τ 0 0
      = ∑' u, τ 0 u * (∑' v, τ u v * τ v 0) := by
        refine tsum_congr fun u => ?_
        rw [← ENNReal.tsum_mul_left]
        exact tsum_congr fun v => by rw [mul_assoc]
    _ ≤ ∑' u, τ 0 u * (R * R) := ENNReal.tsum_le_tsum fun u => by gcongr; exact hinner u
    _ = (∑' u, τ 0 u) * (R * R) := ENNReal.tsum_mul_right
    _ ≤ R * (R * R) := by gcongr; exact hR 0
    _ = R ^ 3 := by ring

/-! ### The autocorrelation (Gram) kernel of a profile -/

/-! **The autocorrelation kernel of a profile `f`**: `Γ_f(u,v) = ∑_z f z · f (z + v - u)`, the
translation-invariant Gram kernel `Q(v,w) = ⟨S 1_v, S 1_w⟩` of Kozma (2011), §2, for the profile
`f` acting as his square-root vector.  It is nonnegative whenever `f ≥ 0`, its diagonal is the
`ℓ²` mass of `f`, and it is a genuine square-root factorization: no entry of `Γ_f` is assumed
finite. -/



/-- The diagonal of the autocorrelation kernel is the `ℓ²` mass of the profile. -/
theorem gramKernel_self {f : (Fin d → ℤ) → ℝ} (hf0 : ∀ z, 0 ≤ f z) (u : Fin d → ℤ) :
    gramKernel f u u = ∑' z, ENNReal.ofReal (f z ^ 2) := by
  refine tsum_congr fun z => ?_
  show ENNReal.ofReal (f z) * ENNReal.ofReal (f (z + u - u)) = _
  rw [add_sub_cancel_right, ← ENNReal.ofReal_mul (hf0 z), pow_two]

/-- **The rows of the autocorrelation kernel have mass `(∑ f) ^ 2`**: the profile's `ℓ¹` mass is
squared by the convolution, which is the bound the row-sum criterion consumes. -/
theorem gramKernel_row_tsum_le {f : (Fin d → ℤ) → ℝ} (u : Fin d → ℤ) :
    ∑' v, gramKernel f u v ≤
      (∑' z, ENNReal.ofReal (f z)) * (∑' z, ENNReal.ofReal (f z)) := by
  have hstep : ∀ z : Fin d → ℤ,
      (∑' v : Fin d → ℤ, ENNReal.ofReal (f z) * ENNReal.ofReal (f (z + v - u)))
        = ENNReal.ofReal (f z) * (∑' z : Fin d → ℤ, ENNReal.ofReal (f z)) := by
    intro z
    rw [ENNReal.tsum_mul_left]
    congr 1
    calc ∑' v, ENNReal.ofReal (f (z + v - u))
        = ∑' v, ENNReal.ofReal (f (v + (z - u))) :=
          tsum_congr fun v => by rw [show z + v - u = v + (z - u) by abel]
      _ = ∑' w, ENNReal.ofReal (f w) := by
          simpa only [Equiv.coe_addRight] using
            (Equiv.tsum_eq (Equiv.addRight (z - u)) fun w : Fin d → ℤ => ENNReal.ofReal (f w))
  have hmain : ∑' v, gramKernel f u v =
      (∑' z, ENNReal.ofReal (f z)) * (∑' z, ENNReal.ofReal (f z)) := by
    calc ∑' v, gramKernel f u v
        = ∑' v, ∑' z, ENNReal.ofReal (f z) * ENNReal.ofReal (f (z + v - u)) := rfl
      _ = ∑' z, ∑' v, ENNReal.ofReal (f z) * ENNReal.ofReal (f (z + v - u)) := ENNReal.tsum_comm
      _ = ∑' z, ENNReal.ofReal (f z) * (∑' z, ENNReal.ofReal (f z)) := tsum_congr hstep
      _ = (∑' z, ENNReal.ofReal (f z)) * (∑' z, ENNReal.ofReal (f z)) :=
          ENNReal.tsum_mul_right (f := fun z => ENNReal.ofReal (f z))
            (a := ∑' z, ENNReal.ofReal (f z))
  exact le_of_eq hmain

/-! ### `hTri` from a summable normalized profile -/

/-- Monotonicity of the open triangle in the kernel. -/
theorem openTriangleKernel_mono {τ σ : (Fin d → ℤ) → (Fin d → ℤ) → ℝ≥0∞}
    (h : ∀ u v : Fin d → ℤ, τ u v ≤ σ u v) :
    openTriangleKernel τ 0 0 ≤ openTriangleKernel σ 0 0 := by
  refine ENNReal.tsum_le_tsum fun u => ENNReal.tsum_le_tsum fun v => ?_
  exact mul_le_mul (mul_le_mul (h 0 u) (h u v) zero_le zero_le) (h v 0) zero_le zero_le

/-- **The open-triangle self energy of the autocorrelation kernel is at most `(∑ f) ^ 6`.**  This is
the quantitative core: the row masses `(∑ f) ^ 2` of `Γ_f` feed the row-sum criterion. -/
theorem openTriangleKernel_gramKernel_le {f : (Fin d → ℤ) → ℝ} (hf0 : ∀ z, 0 ≤ f z)
    (hf : Summable f) :
    openTriangleKernel (gramKernel f) 0 0 ≤ ENNReal.ofReal ((∑' z, f z) ^ 6) := by
  have hL : (∑' z, ENNReal.ofReal (f z)) = ENNReal.ofReal (∑' z, f z) :=
    (ENNReal.ofReal_tsum_of_nonneg hf0 hf).symm
  have hrow : ∀ x : Fin d → ℤ, ∑' y, gramKernel f x y ≤
      (∑' z, ENNReal.ofReal (f z)) * (∑' z, ENNReal.ofReal (f z)) :=
    fun x => gramKernel_row_tsum_le x
  have hbound := openTriangleKernel_zero_le_of_rowSum_le (gramKernel f) hrow
  have hcube : ENNReal.ofReal ((∑' z, f z) ^ 6)
      = ((∑' z, ENNReal.ofReal (f z)) * (∑' z, ENNReal.ofReal (f z))) ^ 3 := by
    rw [show (∑' z, f z) ^ 6 = ((∑' z, f z) * (∑' z, f z)) ^ 3 by ring]
    rw [ENNReal.ofReal_pow (mul_nonneg (tsum_nonneg hf0) (tsum_nonneg hf0)),
      ENNReal.ofReal_mul (tsum_nonneg hf0), hL]
  rw [hcube]
  exact hbound

/-- **The triangle condition from a concrete autocorrelation profile.**  If the configured
two-point function is the autocorrelation kernel of a nonnegative summable profile `f`, then the
open-triangle self energy is at most `(∑_z f z) ^ 6`; in particular it is finite.

The identification hypothesis is the *pointwise* kernel identity, not a finiteness statement: the
boundedness of `∇_{β_c}` is derived here from the row masses of `Γ_f`. -/
theorem openTriangleSelf_le_of_gramProfile {J : Sym2 (Fin d → ℤ) → ℝ} {hJ : ∀ e, 0 ≤ J e}
    {β : NNReal} {f : (Fin d → ℤ) → ℝ} (hf0 : ∀ z, 0 ≤ f z) (hf : Summable f)
    (hident : ∀ u v : Fin d → ℤ, twoPointFunction J hJ β u v = gramKernel f u v) :
    openTriangleSelf J hJ β 0 ≤ ENNReal.ofReal ((∑' z, f z) ^ 6) := by
  have hEq : openTriangleSelf J hJ β 0 = openTriangleKernel (gramKernel f) 0 0 := by
    have h0 : openTriangleSelf J hJ β 0 = openTriangleKernel (twoPointFunction J hJ β) 0 0 := rfl
    rw [h0]
    exact tsum_congr fun u => tsum_congr fun v => by
      rw [hident 0 u, hident u v, hident v 0]
  rw [hEq]
  exact openTriangleKernel_gramKernel_le hf0 hf

/-- **`hTri` from a summable profile.** -/
theorem openTriangleSelf_lt_top_of_gramProfile {J : Sym2 (Fin d → ℤ) → ℝ} {hJ : ∀ e, 0 ≤ J e}
    {β : NNReal} {f : (Fin d → ℤ) → ℝ} (hf0 : ∀ z, 0 ≤ f z) (hf : Summable f)
    (hident : ∀ u v : Fin d → ℤ, twoPointFunction J hJ β u v = gramKernel f u v) :
    openTriangleSelf J hJ β 0 < ⊤ :=
  (openTriangleSelf_le_of_gramProfile hf0 hf hident).trans_lt ENNReal.ofReal_lt_top

/-- **`hTri` from domination by an autocorrelation kernel.**  It is enough that the two-point
function be bounded pointwise by `Γ_f` for a nonnegative summable profile `f` — the equality of
`openTriangleSelf_lt_top_of_gramProfile` is not needed. -/
theorem openTriangleSelf_le_of_gramDomination {J : Sym2 (Fin d → ℤ) → ℝ} {hJ : ∀ e, 0 ≤ J e}
    {β : NNReal} {f : (Fin d → ℤ) → ℝ} (hf0 : ∀ z, 0 ≤ f z) (hf : Summable f)
    (hle : ∀ u v : Fin d → ℤ, twoPointFunction J hJ β u v ≤ gramKernel f u v) :
    openTriangleSelf J hJ β 0 ≤ ENNReal.ofReal ((∑' z, f z) ^ 6) := by
  have hEq : openTriangleSelf J hJ β 0 = openTriangleKernel (twoPointFunction J hJ β) 0 0 := rfl
  rw [hEq]
  exact (openTriangleKernel_mono hle).trans (openTriangleKernel_gramKernel_le hf0 hf)

/-- **`hTri` from domination by an autocorrelation kernel.** -/
theorem openTriangleSelf_lt_top_of_gramDomination {J : Sym2 (Fin d → ℤ) → ℝ}
    {hJ : ∀ e, 0 ≤ J e} {β : NNReal} {f : (Fin d → ℤ) → ℝ} (hf0 : ∀ z, 0 ≤ f z)
    (hf : Summable f)
    (hle : ∀ u v : Fin d → ℤ, twoPointFunction J hJ β u v ≤ gramKernel f u v) :
    openTriangleSelf J hJ β 0 < ⊤ :=
  (openTriangleSelf_le_of_gramDomination hf0 hf hle).trans_lt ENNReal.ofReal_lt_top

/-- **Contrapositive form of the bridge.**  If the open-triangle self energy of `τ` is infinite,
then `τ` exceeds the autocorrelation kernel of every nonnegative summable profile somewhere. -/
theorem exists_lt_gramKernel_of_openTriangleKernel_eq_top
    {τ : (Fin d → ℤ) → (Fin d → ℤ) → ℝ≥0∞}
    (htop : openTriangleKernel τ 0 0 = ⊤)
    {f : (Fin d → ℤ) → ℝ} (hf0 : ∀ z, 0 ≤ f z) (hf : Summable f) :
    ∃ u v : Fin d → ℤ, gramKernel f u v < τ u v := by
  by_contra h
  simp only [not_exists, not_lt] at h
  have hle : ∀ u v : Fin d → ℤ, τ u v ≤ gramKernel f u v := fun u v => h u v
  have hfin := (openTriangleKernel_mono hle).trans (openTriangleKernel_gramKernel_le hf0 hf)
  rw [htop] at hfin
  exact absurd hfin (not_le.mpr ENNReal.ofReal_lt_top)

/-! ### Consistency of the profile hypothesis with the model's normalization -/

/-- The model's diagonal normalization `τ(x,x) = 1` (`twoPointFunction_self`) is *exactly* the
statement `∑_z f z ^ 2 = 1` for the profile: the autocorrelation identification forces the
profile to be an `ℓ²` unit vector. -/
theorem one_eq_tsum_sq_of_ident {J : Sym2 (Fin d → ℤ) → ℝ} {hJ : ∀ e, 0 ≤ J e} {β : NNReal}
    {f : (Fin d → ℤ) → ℝ} (hf0 : ∀ z, 0 ≤ f z)
    (hident : ∀ u v : Fin d → ℤ, twoPointFunction J hJ β u v = gramKernel f u v)
    (u : Fin d → ℤ) :
    ∑' z, ENNReal.ofReal (f z ^ 2) = 1 := by
  have h := hident u u
  rw [twoPointFunction_self] at h
  rw [gramKernel_self hf0 u] at h
  exact h.symm

/-! ### A computed non-vacuity witness -/

/-- The delta profile gives the identity (Kronecker) kernel. -/
theorem gramKernel_delta (u v : Fin d → ℤ) :
    gramKernel (fun z : Fin d → ℤ => if z = 0 then (1 : ℝ) else 0) u v =
      if u = v then 1 else 0 := by
  have hunfold : gramKernel (fun z : Fin d → ℤ => if z = 0 then (1 : ℝ) else 0) u v =
      ∑' b, ENNReal.ofReal (if b = 0 then (1 : ℝ) else 0) *
        ENNReal.ofReal (if b + v - u = 0 then (1 : ℝ) else 0) := rfl
  rw [hunfold, tsum_eq_single (0 : Fin d → ℤ)]
  · by_cases huv : u = v
    · subst huv
      simp
    · have hvu : v - u ≠ 0 := sub_ne_zero.mpr (Ne.symm huv)
      simp [hvu, huv]
  · intro b hb
    simp [hb]

/-! ### Structural properties of the autocorrelation kernel -/

/-- The autocorrelation kernel of a profile is translation invariant. -/
theorem gramKernel_translate (f : (Fin d → ℤ) → ℝ) (a u v : Fin d → ℤ) :
    gramKernel f (u + a) (v + a) = gramKernel f u v := by
  refine tsum_congr fun z => ?_
  rw [show z + (v + a) - (u + a) = z + v - u by abel]

/-- The autocorrelation kernel of a profile is symmetric. -/
theorem gramKernel_comm (f : (Fin d → ℤ) → ℝ) (u v : Fin d → ℤ) :
    gramKernel f u v = gramKernel f v u := by
  have hunfold : gramKernel f u v =
      ∑' z, ENNReal.ofReal (f z) * ENNReal.ofReal (f (z + v - u)) := rfl
  have hunfold2 : gramKernel f v u =
      ∑' z, ENNReal.ofReal (f z) * ENNReal.ofReal (f (z + u - v)) := rfl
  rw [hunfold, hunfold2, ← Equiv.tsum_eq (Equiv.addRight (v - u))
    (fun z => ENNReal.ofReal (f z) * ENNReal.ofReal (f (z + u - v)))]
  refine tsum_congr fun z => ?_
  simp only [Equiv.coe_addRight]
  rw [show z + (v - u) + u - v = z by abel, show z + (v - u) = z + v - u by abel]
  exact mul_comm _ _

/-- **A normalized profile gives a kernel bounded by `1`**, matching `twoPointFunction_le_one`:
AM--GM on the profile turns the kernel into half the sum of the two shifted `ℓ²` masses. -/
theorem gramKernel_le_one {f : (Fin d → ℤ) → ℝ} (hf0 : ∀ z, 0 ≤ f z)
    (hf2 : Summable fun z => f z ^ 2) (hnorm : ∑' z, f z ^ 2 = 1) (u v : Fin d → ℤ) :
    gramKernel f u v ≤ 1 := by
  have hshift : Summable fun z : Fin d → ℤ => f (z + v - u) ^ 2 := by
    have h0 := (Equiv.summable_iff (f := fun z : Fin d → ℤ => f z ^ 2)
      (Equiv.addRight (v - u))).mpr hf2
    have h : Summable fun z : Fin d → ℤ => f (z + (v - u)) ^ 2 := by
      simpa only [Equiv.coe_addRight, Function.comp_def] using h0
    simpa only [add_sub_assoc] using h
  have htsum_shift : (∑' z : Fin d → ℤ, f (z + v - u) ^ 2) = ∑' z : Fin d → ℤ, f z ^ 2 := by
    have h : (∑' c : Fin d → ℤ, f (c + (v - u)) ^ 2) = ∑' b : Fin d → ℤ, f b ^ 2 := by
      simpa only [Equiv.coe_addRight] using
        (Equiv.tsum_eq (Equiv.addRight (v - u)) fun z : Fin d → ℤ => f z ^ 2)
    simpa only [add_sub_assoc] using h
  have hpt : ∀ z : Fin d → ℤ, ENNReal.ofReal (f z) * ENNReal.ofReal (f (z + v - u)) ≤
      ENNReal.ofReal ((f z ^ 2 + f (z + v - u) ^ 2) / 2) := by
    intro z
    rw [← ENNReal.ofReal_mul (hf0 z)]
    refine ENNReal.ofReal_le_ofReal ?_
    nlinarith [sq_nonneg (f z - f (z + v - u))]
  have hsumm : Summable fun z : Fin d → ℤ => (f z ^ 2 + f (z + v - u) ^ 2) / 2 :=
    (hf2.add hshift).div_const 2
  have hnn : ∀ z : Fin d → ℤ, 0 ≤ (f z ^ 2 + f (z + v - u) ^ 2) / 2 := fun z => by positivity
  have hval : (∑' z : Fin d → ℤ, (f z ^ 2 + f (z + v - u) ^ 2) / 2) =
      ∑' z : Fin d → ℤ, f z ^ 2 := by
    rw [show (fun z : Fin d → ℤ => (f z ^ 2 + f (z + v - u) ^ 2) / 2) =
      fun z => (1 / 2) * (f z ^ 2 + f (z + v - u) ^ 2) from
      funext fun z => by ring]
    rw [tsum_mul_left, Summable.tsum_add hf2 hshift, htsum_shift]
    ring
  calc gramKernel f u v
      = ∑' z, ENNReal.ofReal (f z) * ENNReal.ofReal (f (z + v - u)) := rfl
    _ ≤ ∑' z, ENNReal.ofReal ((f z ^ 2 + f (z + v - u) ^ 2) / 2) := ENNReal.tsum_le_tsum hpt
    _ = ENNReal.ofReal (∑' z, (f z ^ 2 + f (z + v - u) ^ 2) / 2) :=
        (ENNReal.ofReal_tsum_of_nonneg hnn hsumm).symm
    _ = 1 := by rw [hval, hnorm, ENNReal.ofReal_one]

/-! The delta profile `δ 0 = 1`, `δ z = 0` for `z ≠ 0`. -/



/-- The witness kernel is the identity kernel: `Γ_δ(u,v) = [u = v]`. -/
theorem gramKernel_deltaProfile (u v : Fin d → ℤ) :
    gramKernel (deltaProfile d) u v = if u = v then 1 else 0 :=
  gramKernel_delta u v

/-- **The witness kernel has diagonal `1` and open-triangle self energy `1`.**  So the profile
hypothesis of `openTriangleSelf_lt_top_of_gramProfile` is inhabited by a kernel that meets the
model's normalization `τ(x,x) = 1`. -/
theorem openTriangleKernel_gramKernel_delta :
    openTriangleKernel (gramKernel (deltaProfile d)) 0 0 = 1 := by
  set f0 : (Fin d → ℤ) → ℝ := deltaProfile d with hf0
  have hK : ∀ a b : Fin d → ℤ, gramKernel f0 a b = if a = b then 1 else 0 := gramKernel_deltaProfile
  have hunfold : openTriangleKernel (gramKernel f0) 0 0 =
      ∑' u, ∑' v, gramKernel f0 0 u * gramKernel f0 u v * gramKernel f0 v 0 := rfl
  rw [hunfold]
  have hinner : ∀ u : Fin d → ℤ,
      (∑' v, gramKernel f0 0 u * gramKernel f0 u v * gramKernel f0 v 0) =
        if u = 0 then 1 else 0 := by
    intro u
    rw [tsum_eq_single u]
    · by_cases hu : u = 0
      · subst hu
        simp [hK]
      · have hu0 : ¬ (0 = u) := fun h => hu h.symm
        simp [hK, hu, hu0]
    · intro b hb
      have hub : ¬ (u = b) := Ne.symm hb
      rw [hK u b]
      simp [hub]
  rw [tsum_congr hinner, tsum_eq_single (0 : Fin d → ℤ)]
  · simp
  · intro b hb
    simp [hb]

/-- **The hypothesis set is inhabited in the model's own shape.**  The delta profile gives a kernel
with all four structural properties of the model's two-point function — unit diagonal
(`twoPointFunction_self`), the bound `1` (`twoPointFunction_le_one`), symmetry
(`twoPointFunction_comm`) and translation invariance — and finite open-triangle self energy. -/
theorem exists_kernel_model_properties_and_hTri :
    ∃ τ : (Fin d → ℤ) → (Fin d → ℤ) → ℝ≥0∞,
      (∀ x, τ x x = 1) ∧ (∀ x y, τ x y ≤ 1) ∧ (∀ x y, τ x y = τ y x) ∧
        (∀ (a x y : Fin d → ℤ), τ (x + a) (y + a) = τ x y) ∧ openTriangleKernel τ 0 0 < ⊤ := by
  refine ⟨gramKernel (deltaProfile d), ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    rw [gramKernel_deltaProfile]
    simp
  · intro x y
    rw [gramKernel_deltaProfile]
    split_ifs <;> norm_num
  · intro x y
    exact gramKernel_comm (deltaProfile d) x y
  · intro a x y
    exact gramKernel_translate (deltaProfile d) a x y
  · rw [openTriangleKernel_gramKernel_delta]
    exact ENNReal.one_lt_top

/-! ### The obstruction: diagonal normalization is not enough -/

/-- The constant kernel `τ ≡ 1` has open-triangle self energy `⊤`: the double sum of ones over the
infinite lattice diverges. -/
theorem openTriangleKernel_one_eq_top [Infinite (Fin d → ℤ)] :
    openTriangleKernel (d := d) (fun (_ : Fin d → ℤ) (_ : Fin d → ℤ) => (1 : ℝ≥0∞)) 0 0 = ⊤ := by
  have hunfold : openTriangleKernel (d := d)
      (fun (_ : Fin d → ℤ) (_ : Fin d → ℤ) => (1 : ℝ≥0∞)) 0 0
      = ∑' _u : Fin d → ℤ, ∑' _v : Fin d → ℤ, (1 : ℝ≥0∞) * 1 * 1 := rfl
  rw [hunfold]
  have hinner : ∀ _u : Fin d → ℤ, (∑' _v : Fin d → ℤ, (1 : ℝ≥0∞) * 1 * 1) = ⊤ := by
    intro _u
    rw [one_mul, one_mul]
    exact ENNReal.tsum_const_eq_top_of_ne_zero one_ne_zero
  rw [tsum_congr hinner]
  exact ENNReal.tsum_eq_top_of_eq_top ⟨0, rfl⟩

/-- **Diagonal `1`, the pointwise bound `1`, symmetry and translation invariance do not imply the
triangle condition.**  `τ ≡ 1` satisfies all four properties — compare `twoPointFunction_self`,
`twoPointFunction_le_one`, `twoPointFunction_comm` and translation invariance of the configured
kernel, and it is even the Gram matrix of the constant family
(`TriTail.constantKernel_psd_data`) — yet `∇(0,0) = ⊤`.  So no combination of the properties the
worktree proves about its own `twoPointFunction` can replace the summability of the profile in the
Gram representation. -/
theorem diagonal_one_translationInvariant_not_sufficient [Infinite (Fin d → ℤ)] :
    ¬ (∀ τ : (Fin d → ℤ) → (Fin d → ℤ) → ℝ≥0∞, (∀ x, τ x x = 1) →
        (∀ x y, τ x y ≤ 1) → (∀ x y, τ x y = τ y x) →
        (∀ (a x y : Fin d → ℤ), τ (x + a) (y + a) = τ x y) →
        openTriangleKernel τ 0 0 < ⊤) := by
  intro h
  have hdiag : ∀ x : Fin d → ℤ,
      (fun (_ : Fin d → ℤ) (_ : Fin d → ℤ) => (1 : ℝ≥0∞)) x x = 1 := fun _ => rfl
  have hle : ∀ x y : Fin d → ℤ,
      (fun (_ : Fin d → ℤ) (_ : Fin d → ℤ) => (1 : ℝ≥0∞)) x y ≤ 1 := fun _ _ => le_rfl
  have hsymm : ∀ x y : Fin d → ℤ,
      (fun (_ : Fin d → ℤ) (_ : Fin d → ℤ) => (1 : ℝ≥0∞)) x y =
        (fun (_ : Fin d → ℤ) (_ : Fin d → ℤ) => (1 : ℝ≥0∞)) y x := fun _ _ => rfl
  have hti : ∀ a x y : Fin d → ℤ,
      (fun (_ : Fin d → ℤ) (_ : Fin d → ℤ) => (1 : ℝ≥0∞)) (x + a) (y + a) =
        (fun (_ : Fin d → ℤ) (_ : Fin d → ℤ) => (1 : ℝ≥0∞)) x y := fun _ _ _ => rfl
  have := h (fun (_ : Fin d → ℤ) (_ : Fin d → ℤ) => 1) hdiag hle hsymm hti
  rw [openTriangleKernel_one_eq_top (d := d)] at this
  exact (lt_irrefl (⊤ : ℝ≥0∞)) this

/-! ### Toolbox for the missing tail step (`∇_r → 0`)

`hTri` above is finiteness at the origin.  The other §I.4.1 input is the vanishing of the tail,
`Tendsto (openTriangleTail J hJ β) atTop (𝓝 0)`.  Under the profile hypothesis this should follow
from `openTriangleTail_tendsto_of_sqrtKernel` with the *same* profile: `∇(0,·)` is the
autocorrelation of the triple convolution `f * f * f` (because `Γ_f³ = Γ_{f*f*f}`, i.e. `∇(0,x)` is
a 6-fold convolution).  The lattice convolution algebra needed for that identity is proved here
(`conv`, `refl`, `conv_comm`, `conv_assoc`); the remaining steps — the chain of `conv_assoc` /
`conv_comm` / `refl` rewrites giving `conv P (conv P P) = conv G (refl G)` for `P = F * F∨` and
`G = F * F * F`, and the `ofReal` conversion of a triple convolution — are *not* done, so the tail
is deliberately **not** claimed.

Convolution of `ℝ≥0∞`-valued functions on the lattice. -/



/-! Reflection `H∨(w) = H(-w)`. -/



/-- Convolution on the lattice is commutative (reindexing by `z ↦ w - z`); no summability is
needed in `ℝ≥0∞`. -/
theorem conv_comm (H K : (Fin d → ℤ) → ℝ≥0∞) : conv H K = conv K H := by
  funext w
  change (∑' z, H z * K (w - z)) = ∑' z, K z * H (w - z)
  rw [← Equiv.tsum_eq (Equiv.subLeft w) (fun z => K z * H (w - z))]
  refine tsum_congr fun z => ?_
  rw [Equiv.subLeft_apply, show w - (w - z) = z by abel]
  exact mul_comm _ _

/-- Convolution on the lattice is associative (Fubini for `ℝ≥0∞` sums plus the reindexing
`z ↦ y + t`). -/
theorem conv_assoc (H K L : (Fin d → ℤ) → ℝ≥0∞) :
    conv (conv H K) L = conv H (conv K L) := by
  funext w
  change (∑' z, (∑' y, H y * K (z - y)) * L (w - z)) =
    ∑' y, H y * ∑' t, K t * L (w - y - t)
  rw [← tsum_congr fun z =>
    ENNReal.tsum_mul_right (f := fun y => H y * K (z - y)) (a := L (w - z))]
  rw [ENNReal.tsum_comm (f := fun z y => H y * K (z - y) * L (w - z))]
  refine tsum_congr fun y => ?_
  rw [tsum_congr fun a => mul_assoc (H y) (K (a - y)) (L (w - a))]
  rw [ENNReal.tsum_mul_left]
  congr 1
  calc ∑' a, K (a - y) * L (w - a)
      = ∑' t, K (t + y - y) * L (w - (t + y)) :=
        (Equiv.tsum_eq (Equiv.addRight y) (fun a => K (a - y) * L (w - a))).symm
    _ = ∑' t, K t * L (w - y - t) := by
        refine tsum_congr fun t => ?_
        rw [show t + y - y = t by abel, show w - (t + y) = w - y - t by abel]

end PercLib.CriticalLRP.TriTail

/-! ### Handoff to the model -/

namespace PercLib.CriticalLRP

/-- **`hTri` for `SourceModelData` from a summable autocorrelation profile**, in the exact shape
the §I.4.18/§I.4.20 consumers require:
`TriTail.openTriangleSelf M.kernel M.kernel_nonneg M.betaCrit 0 < ⊤`. -/
theorem Orchestration.SourceModelData.openTriangleSelf_lt_top_of_gramProfile
    (M : Orchestration.SourceModelData) {f : M.V → ℝ} (hf0 : ∀ z, 0 ≤ f z)
    (hf : Summable f)
    (hident : ∀ u v : M.V,
      twoPointFunction M.kernel M.kernel_nonneg M.betaCrit u v = TriTail.gramKernel f u v) :
    TriTail.openTriangleSelf M.kernel M.kernel_nonneg M.betaCrit 0 < ⊤ :=
  TriTail.openTriangleSelf_lt_top_of_gramProfile (d := M.d) hf0 hf hident

/-- **`hTri` for `SourceModelData` from domination by a summable autocorrelation profile. -/
theorem Orchestration.SourceModelData.openTriangleSelf_lt_top_of_gramDomination
    (M : Orchestration.SourceModelData) {f : M.V → ℝ} (hf0 : ∀ z, 0 ≤ f z)
    (hf : Summable f)
    (hle : ∀ u v : M.V,
      twoPointFunction M.kernel M.kernel_nonneg M.betaCrit u v ≤ TriTail.gramKernel f u v) :
    TriTail.openTriangleSelf M.kernel M.kernel_nonneg M.betaCrit 0 < ⊤ :=
  TriTail.openTriangleSelf_lt_top_of_gramDomination (d := M.d) hf0 hf hle

end PercLib.CriticalLRP

/-! ### Axiom audit -/

set_option linter.style.longLine false

#print axioms PercLib.CriticalLRP.TriTail.openTriangleKernel_zero_le_of_rowSum_le
#print axioms PercLib.CriticalLRP.TriTail.gramKernel_self
#print axioms PercLib.CriticalLRP.TriTail.gramKernel_row_tsum_le
#print axioms PercLib.CriticalLRP.TriTail.openTriangleKernel_mono
#print axioms PercLib.CriticalLRP.TriTail.openTriangleKernel_gramKernel_le
#print axioms PercLib.CriticalLRP.TriTail.openTriangleSelf_le_of_gramProfile
#print axioms PercLib.CriticalLRP.TriTail.openTriangleSelf_le_of_gramDomination
#print axioms PercLib.CriticalLRP.TriTail.openTriangleSelf_lt_top_of_gramDomination
#print axioms PercLib.CriticalLRP.TriTail.openTriangleSelf_lt_top_of_gramProfile
#print axioms PercLib.CriticalLRP.TriTail.exists_lt_gramKernel_of_openTriangleKernel_eq_top
#print axioms PercLib.CriticalLRP.TriTail.one_eq_tsum_sq_of_ident
#print axioms PercLib.CriticalLRP.TriTail.conv_comm
#print axioms PercLib.CriticalLRP.TriTail.conv_assoc
#print axioms PercLib.CriticalLRP.TriTail.gramKernel_translate
#print axioms PercLib.CriticalLRP.TriTail.gramKernel_comm
#print axioms PercLib.CriticalLRP.TriTail.gramKernel_le_one
#print axioms PercLib.CriticalLRP.TriTail.exists_kernel_model_properties_and_hTri
#print axioms PercLib.CriticalLRP.TriTail.gramKernel_delta
#print axioms PercLib.CriticalLRP.TriTail.openTriangleKernel_gramKernel_delta
#print axioms PercLib.CriticalLRP.TriTail.openTriangleKernel_one_eq_top
#print axioms PercLib.CriticalLRP.TriTail.diagonal_one_translationInvariant_not_sufficient
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.openTriangleSelf_lt_top_of_gramProfile
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.openTriangleSelf_lt_top_of_gramDomination
