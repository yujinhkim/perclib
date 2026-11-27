/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

# Radial tail vanishing for the open triangle from a Gram (autocorrelation) profile

Integrated and independently rebuilt from accepted Ultramath `smwyq4kak`, member `m2`,
direction `d2`, at production base `860204bba022fa59110751d428c2bd8f123ad604`.
This is the analytic finite-summability route, independent of the
triple-convolution/reflection identity route in `TriTailConvolution.Main`.

It consumes the already integrated `gramKernel_row_tsum_le` and
`openTriangle_eq_openTriangleKernel` from `TriTailNormalization`.

## What is proved

The remaining §I.4.1 input after `hTri` is the *vanishing of the tail*,
`∇_r = sup_{‖x‖ ≥ r} ∇_{β_c}(0,x) → 0`.  The accepted `Main.lean` says explicitly that this
"should follow" from `Γ_f³ = Γ_{f*f*f}` and that the convolution-algebra steps are *not* done.
Here we obtain the same conclusion by a different and shorter route, without any of
`conv_assoc` / `conv_comm` / `refl` and without identifying `Γ_f³` with an autocorrelation
pointwise:

* `tsum_openTriangleKernel_gramKernel_le` — **the total-mass bound**
  `∑_x ∇_f(0,x) ≤ (∑_z f z)^6`, where `∇_f = openTriangleKernel (gramKernel f)`.
  It is two applications of the row-sum bound `gramKernel_row_tsum_le`
  (the rows of `Γ_f` all have mass `(∑ f)^2`) plus Tonelli:
  `∑_x ∇(0,x) = ∑_u ∑_v Γ(0,u) Γ(u,v) (∑_x Γ(v,x)) ≤ (∑f)² · (∑f)⁴ = (∑f)⁶`.
  This is the `ℓ¹`-operator-norm computation `⟨δ_0, τ³ 1⟩` at the constant vector `1`,
  valid with only `≤` in the middle — hence no associativity of convolution, no reflection
  `H∨`, and no `ofReal` conversion of a triple convolution is needed.

* `radialTailSup_eventually_lt`, `tendsto_radialTailSup_zero`,
  `tendsto_radialTailSup_toReal_zero` — **the abstract tail engine**: for *any* type `ι`,
  *any* real-valued `nrm : ι → ℝ` and any `a : ι → ℝ≥0∞` with finite total mass,
  `r ↦ ⨆ x, ⨆ (_ : r ≤ nrm x), a x` tends to `0` (both in `ℝ≥0∞` and after `.toReal`).
  The engine is deliberately *norm-agnostic*: the vanishing is a consequence of the total
  mass alone, so no comparison between the lattice sup-norm `FiniteVolume.latticeDist 0 ·`
  (used by `TriTail.openTriangleTail`) and the model's normalized norm `M.S.dist 0 ·`
  (used by `SourceModelData.nablaTail`) is required.  This is the explicit bridge the
  two tails need: they are two instances of one statement, not two statements.

* `openTriangleTail_tendsto_zero_of_gramProfile` / `..._of_gramDomination` — the tail of the
  configured model kernel vanishes when it *equals* (resp. is pointwise bounded by) the
  autocorrelation kernel `Γ_f` of a nonnegative summable profile.

* `SourceModelData.tendsto_nablaTail_zero_of_gramProfile` and its `.toReal` form — the exact
  shape `(M.nablaTail r).toReal → 0` consumed downstream.

## Scope and honesty

The profile hypothesis is the *same* one the accepted `hTri` bridge takes
(`openTriangleSelf_lt_top_of_gramProfile`), and it is a genuine restriction: `Γ_f ∈ ℓ¹`
forces the two-point function itself to be summable, which the critical long-range model's
`τ(0,x) ≍ |x|^{-d+α}` is not.  Nothing here derives `hTri` from `HD3`, nothing asserts a
uniform vanishing polygon factor, and no finite-critical model data is invented.  The
conclusion is conditional on the Gram representation, exactly as the accepted files are.

No `sorry`, no `admit`, no `native_decide`, no axioms beyond the standard three.
-/

module

public import PercLib.CriticalLRP.Analysis.TriTailNormalization.Main
public import PercLib.CriticalLRP.Analysis.Polygon.Defs

/-! # Finite-mass radial tails for Gram-dominated triangles -/

open scoped ENNReal Topology
open Filter

set_option linter.style.longLine false
set_option linter.hashCommand false
set_option linter.unusedSectionVars false

@[expose] public section

namespace PercLib.CriticalLRP.TriTail

variable {d : ℕ}

/-! ### The abstract tail engine -/

/-- **The finite-mass tail engine, eventual form.**
If `a : ι → ℝ≥0∞` has finite total mass, then for every `b ≠ 0` the radial tail supremum
`⨆ x, ⨆ (_ : r ≤ nrm x), a x` is eventually below `b`.  The norm `nrm` is arbitrary and
real-valued (only finitely many of its values can be `≤ r` when the mass is finite).

The proof is the only place where the total mass is used: taking `.toReal` of the mass gives a
summable real family, the sum over the complement of a finset tends to `0`
(`tendsto_tsum_compl_atTop_zero`), and then choosing `r` beyond the largest `nrm`-value on that
finset puts the whole tail inside the complement. -/
theorem radialTailSup_eventually_lt {ι : Type*} (a : ι → ℝ≥0∞) (nrm : ι → ℝ)
    (hS : (∑' x, a x) ≠ ⊤) {b : ℝ≥0∞} (hb : b ≠ 0) :
    ∀ᶠ r : ℝ in atTop, (⨆ x : ι, ⨆ (_ : r ≤ nrm x), a x) < b := by
  classical
  rcases eq_or_ne b ⊤ with hbt | hbt
  · subst hbt
    refine Filter.Eventually.of_forall fun r => ?_
    have hle : (⨆ x : ι, ⨆ (_ : r ≤ nrm x), a x) ≤ ∑' x, a x :=
      iSup_le fun x => iSup_le fun _ => ENNReal.le_tsum x
    exact lt_of_le_of_lt hle (lt_top_iff_ne_top.2 hS)
  · have hbpos : 0 < b := lt_of_le_of_ne zero_le (Ne.symm hb)
    have hbne' : b ≠ 0 := hb
    have hhalf : (0 : ℝ) < b.toReal / 2 := half_pos (ENNReal.toReal_pos hb hbt)
    set u : ι → ℝ := fun x => (a x).toReal with hudef
    have hsumm : Summable u := ENNReal.summable_toReal hS
    have hcompl : Tendsto (fun F : Finset ι => ∑' x : {x // x ∉ F}, u x) atTop (𝓝 0) :=
      tendsto_tsum_compl_atTop_zero u
    have hev : ∀ᶠ F : Finset ι in atTop, (∑' x : {x // x ∉ F}, u x) < b.toReal / 2 :=
      (tendsto_order.1 hcompl).2 _ hhalf
    obtain ⟨F, hF⟩ := Filter.eventually_atTop.1 hev
    refine Filter.eventually_atTop.2 ⟨F.sum (fun y => |nrm y|) + 1, fun r hr => ?_⟩
    have hout : ∀ x : ι, r ≤ nrm x → x ∉ F := by
      intro x hx hxF
      have h1 : |nrm x| ≤ F.sum (fun y => |nrm y|) :=
        Finset.single_le_sum (f := fun y => |nrm y|) (fun y _ => abs_nonneg (nrm y)) hxF
      have h2 : nrm x ≤ |nrm x| := le_abs_self (nrm x)
      linarith
    have hsmall : (∑' x : {x // x ∉ F}, u x) < b.toReal / 2 := hF F le_rfl
    have hbound : ∀ x : ι, r ≤ nrm x → a x ≤ ENNReal.ofReal (b.toReal / 2) := by
      intro x hx
      have hxF : x ∉ F := hout x hx
      have hsub : Summable (u ∘ Subtype.val : {y : ι // y ∉ F} → ℝ) := hsumm.subtype _
      have hle : u x ≤ ∑' y : {y : ι // y ∉ F}, u y := by
        simpa using hsub.le_tsum ⟨x, hxF⟩ (fun j _ => ENNReal.toReal_nonneg)
      have hcoe : ENNReal.ofReal (u x) = a x :=
        ENNReal.ofReal_toReal (ne_top_of_le_ne_top hS (ENNReal.le_tsum x))
      rw [← hcoe]
      exact ENNReal.ofReal_le_ofReal (le_of_lt (lt_of_le_of_lt hle hsmall))
    have hlt : ENNReal.ofReal (b.toReal / 2) < b := by
      have h' : ENNReal.ofReal (b.toReal / 2) < ENNReal.ofReal b.toReal :=
        (ENNReal.ofReal_lt_ofReal_iff (p := b.toReal / 2) (q := b.toReal)
          (ENNReal.toReal_pos hb hbt)).2 (by linarith)
      rwa [ENNReal.ofReal_toReal hbt] at h'
    exact lt_of_le_of_lt (iSup_le fun x => iSup_le fun hx => hbound x hx) hlt

/-- **The finite-mass tail engine**: a radial tail supremum of a finite-mass `ℝ≥0∞`-family
tends to `0`.  This is `Tendsto (radialTailSup nrm F) atTop (𝓝 0)` with the only hypothesis
being that the *total mass* of `F` is finite. -/
theorem tendsto_radialTailSup_zero {ι : Type*} (a : ι → ℝ≥0∞) (nrm : ι → ℝ)
    (hS : (∑' x, a x) ≠ ⊤) :
    Tendsto (fun r : ℝ => ⨆ x : ι, ⨆ (_ : r ≤ nrm x), a x) atTop (𝓝 0) := by
  refine tendsto_order.2 ⟨fun b hb => absurd hb (not_lt.2 zero_le), fun b hb => ?_⟩
  exact radialTailSup_eventually_lt a nrm hS (ne_of_gt hb)

/-- **The real-valued form of the engine.**  The same tail, taken in `ℝ` by `.toReal`,
tends to `0`; this is the shape `(M.nablaTail r).toReal → 0` used by the §I.4.18/§I.4.20
consumers.  It needs no finiteness of the tail values separately: the bound
`< ofReal b` produced by the engine already bounds the value away from `⊤`. -/
theorem tendsto_radialTailSup_toReal_zero {ι : Type*} (a : ι → ℝ≥0∞) (nrm : ι → ℝ)
    (hS : (∑' x, a x) ≠ ⊤) :
    Tendsto (fun r : ℝ => ((⨆ x : ι, ⨆ (_ : r ≤ nrm x), a x)).toReal) atTop (𝓝 0) := by
  refine tendsto_order.2 ⟨fun b _ => Filter.Eventually.of_forall
    fun r => lt_of_lt_of_le ‹b < 0› ENNReal.toReal_nonneg, fun b hb => ?_⟩
  have hbne : ENNReal.ofReal b ≠ 0 := (ENNReal.ofReal_ne_zero_iff).2 hb
  filter_upwards [radialTailSup_eventually_lt a nrm hS hbne] with r hr
  have htop : (⨆ x : ι, ⨆ (_ : r ≤ nrm x), a x) ≠ ⊤ := ne_top_of_lt hr
  calc ((⨆ x : ι, ⨆ (_ : r ≤ nrm x), a x)).toReal
      < (ENNReal.ofReal b).toReal :=
        (ENNReal.toReal_lt_toReal htop ENNReal.ofReal_ne_top).2 hr
    _ = b := ENNReal.toReal_ofReal hb.le

/-- **Domination form of the engine**: pointwise domination by a finite-mass family already
gives vanishing of the tail.  This is the form used for the two-point function, which is only
*compared* with `Γ_f`, never identified with it. -/
theorem tendsto_radialTailSup_zero_of_le {ι : Type*} {F A : ι → ℝ≥0∞} (nrm : ι → ℝ)
    (hle : ∀ x, F x ≤ A x) (hS : (∑' x, A x) ≠ ⊤) :
    Tendsto (fun r : ℝ => ⨆ x : ι, ⨆ (_ : r ≤ nrm x), F x) atTop (𝓝 0) := by
  refine tendsto_order.2 ⟨fun b hb => absurd hb (not_lt.2 zero_le), fun b hb => ?_⟩
  filter_upwards [radialTailSup_eventually_lt A nrm hS (ne_of_gt hb)] with r hr
  have hsup : (⨆ x : ι, ⨆ (_ : r ≤ nrm x), F x) ≤ ⨆ x : ι, ⨆ (_ : r ≤ nrm x), A x :=
    iSup_le fun x => iSup_le fun hx =>
      le_trans (hle x) (le_trans (le_iSup (fun _ : r ≤ nrm x => A x) hx)
        (le_iSup (fun y => ⨆ (_ : r ≤ nrm y), A y) x))
  exact lt_of_le_of_lt hsup hr

/-! ### The total mass of the open triangle of an autocorrelation kernel -/

/-- **Total-mass bound `∑_x ∇_f(0,x) ≤ (∑_z f z)^6`.**

This is the whole analytic content of the tail vanishing, and it uses only that every row of
`Γ_f` has mass at most `(∑ f)^2` (`gramKernel_row_tsum_le`, accepted): Tonelli moves the sum
over `x` inside, the innermost sum is a row of `Γ_f`, and the two outer sums are rows of `Γ_f`
again.  No convolution associativity, no reflection, no pointwise identity. -/
theorem tsum_openTriangleKernel_gramKernel_le {f : (Fin d → ℤ) → ℝ} (hf0 : ∀ z, 0 ≤ f z)
    (hf : Summable f) :
    (∑' x, openTriangleKernel (gramKernel f) 0 x) ≤ ENNReal.ofReal ((∑' z, f z) ^ 6) := by
  set C : ℝ≥0∞ := ∑' z, ENNReal.ofReal (f z) with hC
  have hrow : ∀ u : Fin d → ℤ, (∑' v, gramKernel f u v) ≤ C * C := fun u =>
    gramKernel_row_tsum_le u
  have hcube : ENNReal.ofReal ((∑' z, f z) ^ 6) = (C * C) ^ 3 := by
    have hL : C = ENNReal.ofReal (∑' z, f z) :=
      (ENNReal.ofReal_tsum_of_nonneg hf0 hf).symm
    rw [show (∑' z, f z) ^ 6 = ((∑' z, f z) * (∑' z, f z)) ^ 3 by ring]
    rw [ENNReal.ofReal_pow (mul_nonneg (tsum_nonneg hf0) (tsum_nonneg hf0)),
      ENNReal.ofReal_mul (tsum_nonneg hf0), hL]
  rw [hcube]
  calc (∑' x, openTriangleKernel (gramKernel f) 0 x)
      = ∑' x, ∑' u, ∑' v, (gramKernel f 0 u * gramKernel f u v * gramKernel f v x) := rfl
    _ = ∑' u, ∑' x, ∑' v, (gramKernel f 0 u * gramKernel f u v * gramKernel f v x) :=
        ENNReal.tsum_comm
    _ = ∑' u, ∑' v, ∑' x, (gramKernel f 0 u * gramKernel f u v * gramKernel f v x) := by
        refine tsum_congr fun u => ENNReal.tsum_comm
    _ = ∑' u, ∑' v, ((gramKernel f 0 u * gramKernel f u v) * (∑' x, gramKernel f v x)) := by
        refine tsum_congr fun u => tsum_congr fun v => ?_
        rw [ENNReal.tsum_mul_left]
    _ ≤ ∑' u, ∑' v, ((gramKernel f 0 u * gramKernel f u v) * (C * C)) := by
        refine ENNReal.tsum_le_tsum fun u => ENNReal.tsum_le_tsum fun v => ?_
        exact mul_le_mul_of_nonneg_left (hrow v) zero_le
    _ = (∑' u, gramKernel f 0 u * (∑' v, gramKernel f u v)) * (C * C) := by
        have hinner : ∀ u : Fin d → ℤ,
            (∑' v, ((gramKernel f 0 u * gramKernel f u v) * (C * C)))
              = gramKernel f 0 u * (∑' v, gramKernel f u v) * (C * C) := by
          intro u
          rw [ENNReal.tsum_mul_right, ENNReal.tsum_mul_left]
        rw [tsum_congr hinner, ENNReal.tsum_mul_right]
    _ ≤ ((C * C) * (C * C)) * (C * C) := by
        have h1 : (∑' u, gramKernel f 0 u * (∑' v, gramKernel f u v))
            ≤ (∑' u, gramKernel f 0 u * (C * C)) :=
          ENNReal.tsum_le_tsum fun u => mul_le_mul_of_nonneg_left (hrow u) zero_le
        have h2 : (∑' u, gramKernel f 0 u * (C * C)) ≤ (C * C) * (C * C) := by
          rw [ENNReal.tsum_mul_right]
          exact mul_le_mul_of_nonneg_right (hrow 0) zero_le
        exact (mul_le_mul_of_nonneg_right h1 zero_le).trans (mul_le_mul_of_nonneg_right h2 zero_le)
    _ = (C * C) ^ 3 := by ring

/-- The total mass is finite, hence every value `∇_f(0,x)` is finite and the tail engine
applies. -/
theorem tsum_openTriangleKernel_gramKernel_ne_top {f : (Fin d → ℤ) → ℝ}
    (hf0 : ∀ z, 0 ≤ f z) (hf : Summable f) :
    (∑' x, openTriangleKernel (gramKernel f) 0 x) ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top (tsum_openTriangleKernel_gramKernel_le hf0 hf)

/-! ### Specialising the kernel to the configured model -/

/-- The configured open triangle is the abstract one at the autocorrelation kernel, when the
two-point function *is* that kernel. -/
theorem openTriangle_eq_openTriangleKernel_gramKernel {J : Sym2 (Fin d → ℤ) → ℝ}
    {hJ : ∀ e, 0 ≤ J e} {β : NNReal} {f : (Fin d → ℤ) → ℝ}
    (hident : ∀ u v : Fin d → ℤ, twoPointFunction J hJ β u v = gramKernel f u v)
    (x y : Fin d → ℤ) :
    openTriangle J hJ β x y = openTriangleKernel (gramKernel f) x y := by
  rw [openTriangle_eq_openTriangleKernel]
  exact tsum_congr fun u => tsum_congr fun v => by
    rw [hident x u, hident u v, hident v y]

/-- **The total mass of the configured open triangle is finite** under the Gram-profile
hypothesis. -/
theorem tsum_openTriangle_ne_top_of_gramProfile {J : Sym2 (Fin d → ℤ) → ℝ}
    {hJ : ∀ e, 0 ≤ J e} {β : NNReal} {f : (Fin d → ℤ) → ℝ} (hf0 : ∀ z, 0 ≤ f z)
    (hf : Summable f)
    (hident : ∀ u v : Fin d → ℤ, twoPointFunction J hJ β u v = gramKernel f u v) :
    (∑' x, openTriangle J hJ β 0 x) ≠ ⊤ := by
  have hmass := tsum_openTriangleKernel_gramKernel_ne_top hf0 hf
  have hEq : (∑' x, openTriangle J hJ β 0 x)
      = ∑' x, openTriangleKernel (gramKernel f) 0 x :=
    tsum_congr fun x => openTriangle_eq_openTriangleKernel_gramKernel hident 0 x
  rw [hEq]
  exact hmass

/-- **The open-triangle tail vanishes** for a kernel that is the autocorrelation kernel of a
nonnegative summable profile.  This is the missing §I.4.1 statement
`Tendsto (TriTail.openTriangleTail M.kernel M.kernel_nonneg M.betaCrit) atTop (𝓝 0)`.

Note the norm: this is the lattice sup-norm `FiniteVolume.latticeDist 0 ·`; the engine is
norm-agnostic, so the statement is *not* weakened by the choice. -/
theorem openTriangleTail_tendsto_zero_of_gramProfile {J : Sym2 (Fin d → ℤ) → ℝ}
    {hJ : ∀ e, 0 ≤ J e} {β : NNReal} {f : (Fin d → ℤ) → ℝ} (hf0 : ∀ z, 0 ≤ f z)
    (hf : Summable f)
    (hident : ∀ u v : Fin d → ℤ, twoPointFunction J hJ β u v = gramKernel f u v) :
    Tendsto (openTriangleTail J hJ β) atTop (𝓝 0) := by
  have hmass := tsum_openTriangle_ne_top_of_gramProfile hf0 hf hident
  exact tendsto_radialTailSup_zero (fun x : Fin d → ℤ => openTriangle J hJ β 0 x)
    (fun x : Fin d → ℤ => FiniteVolume.latticeDist 0 x) hmass

/-- **The total mass is finite** under mere pointwise domination by `Γ_f`. -/
theorem tsum_openTriangle_ne_top_of_gramDomination {J : Sym2 (Fin d → ℤ) → ℝ}
    {hJ : ∀ e, 0 ≤ J e} {β : NNReal} {f : (Fin d → ℤ) → ℝ} (hf0 : ∀ z, 0 ≤ f z)
    (hf : Summable f)
    (hle : ∀ u v : Fin d → ℤ, twoPointFunction J hJ β u v ≤ gramKernel f u v) :
    (∑' x, openTriangle J hJ β 0 x) ≠ ⊤ := by
  have hmono : ∀ x, openTriangle J hJ β 0 x ≤ openTriangleKernel (gramKernel f) 0 x := by
    intro x
    rw [openTriangle_eq_openTriangleKernel]
    refine ENNReal.tsum_le_tsum fun u => ENNReal.tsum_le_tsum fun v => ?_
    exact mul_le_mul (mul_le_mul (hle 0 u) (hle u v) zero_le zero_le) (hle v x) zero_le
      zero_le
  refine ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    ((ENNReal.tsum_le_tsum hmono).trans (tsum_openTriangleKernel_gramKernel_le hf0 hf))

/-- **The open-triangle tail vanishes** under pointwise domination by the autocorrelation
kernel of a nonnegative summable profile (no equality needed). -/
theorem openTriangleTail_tendsto_zero_of_gramDomination {J : Sym2 (Fin d → ℤ) → ℝ}
    {hJ : ∀ e, 0 ≤ J e} {β : NNReal} {f : (Fin d → ℤ) → ℝ} (hf0 : ∀ z, 0 ≤ f z)
    (hf : Summable f)
    (hle : ∀ u v : Fin d → ℤ, twoPointFunction J hJ β u v ≤ gramKernel f u v) :
    Tendsto (openTriangleTail J hJ β) atTop (𝓝 0) := by
  have hmass := tsum_openTriangle_ne_top_of_gramDomination hf0 hf hle
  exact tendsto_radialTailSup_zero (fun x : Fin d → ℤ => openTriangle J hJ β 0 x)
    (fun x : Fin d → ℤ => FiniteVolume.latticeDist 0 x) hmass

/-- The *strict* (`>`) tail is dominated by the closed (`≥`) one, since
`{x | r < nrm x} ⊆ {x | r ≤ nrm x}`.  The production definitions keep the two objects separate
(`openTriangleTail` vs `openTriangleTailOpen`, Kozma's formulation); the engine covers both
because the vanishing only uses the total mass. -/
theorem openTriangleTailOpen_le_openTriangleTail {J : Sym2 (Fin d → ℤ) → ℝ}
    {hJ : ∀ e, 0 ≤ J e} {β : NNReal} (r : ℝ) :
    openTriangleTailOpen J hJ β r ≤ openTriangleTail J hJ β r := by
  refine iSup_le fun x => iSup_le fun hx =>
    le_trans (le_iSup (fun (_ : r ≤ FiniteVolume.latticeDist 0 x) =>
      openTriangle J hJ β 0 x) (le_of_lt hx))
      (le_iSup (fun y => ⨆ (_ : r ≤ FiniteVolume.latticeDist 0 y),
        openTriangle J hJ β 0 y) x)

/-- **The strict open-triangle tail vanishes** as well (Kozma's `w ∉ B(v,r)` formulation). -/
theorem openTriangleTailOpen_tendsto_zero_of_gramProfile {J : Sym2 (Fin d → ℤ) → ℝ}
    {hJ : ∀ e, 0 ≤ J e} {β : NNReal} {f : (Fin d → ℤ) → ℝ} (hf0 : ∀ z, 0 ≤ f z)
    (hf : Summable f)
    (hident : ∀ u v : Fin d → ℤ, twoPointFunction J hJ β u v = gramKernel f u v) :
    Tendsto (openTriangleTailOpen J hJ β) atTop (𝓝 0) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (openTriangleTail_tendsto_zero_of_gramProfile hf0 hf hident)
    (fun _ => zero_le) (fun r => openTriangleTailOpen_le_openTriangleTail r)

/-- The strict tail vanishes under pointwise domination by `Γ_f`. -/
theorem openTriangleTailOpen_tendsto_zero_of_gramDomination {J : Sym2 (Fin d → ℤ) → ℝ}
    {hJ : ∀ e, 0 ≤ J e} {β : NNReal} {f : (Fin d → ℤ) → ℝ} (hf0 : ∀ z, 0 ≤ f z)
    (hf : Summable f)
    (hle : ∀ u v : Fin d → ℤ, twoPointFunction J hJ β u v ≤ gramKernel f u v) :
    Tendsto (openTriangleTailOpen J hJ β) atTop (𝓝 0) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (openTriangleTail_tendsto_zero_of_gramDomination hf0 hf hle)
    (fun _ => zero_le) (fun r => openTriangleTailOpen_le_openTriangleTail r)

end PercLib.CriticalLRP.TriTail

/-! ### Handoff to the model: `M.nablaTail → 0` -/

namespace PercLib.CriticalLRP

/-- **The model's open-triangle tail vanishes** from the Gram-profile hypothesis, in the exact
`ℝ≥0∞` shape `Tendsto M.nablaTail atTop (𝓝 0)`.

`M.nablaTail` uses the model's normalized norm `M.S.dist 0 ·` rather than the lattice sup-norm;
the engine needs no comparison between them, which is the explicit normalization bridge. -/
theorem Orchestration.SourceModelData.tendsto_nablaTail_zero_of_gramProfile
    (M : Orchestration.SourceModelData) {f : M.V → ℝ} (hf0 : ∀ z, 0 ≤ f z)
    (hf : Summable f)
    (hident : ∀ u v : M.V,
      twoPointFunction M.kernel M.kernel_nonneg M.betaCrit u v = TriTail.gramKernel f u v) :
    Tendsto M.nablaTail atTop (𝓝 0) := by
  have hmass := TriTail.tsum_openTriangle_ne_top_of_gramProfile (d := M.d) hf0 hf hident
  exact TriTail.tendsto_radialTailSup_zero
    (fun x : M.V => TriTail.openTriangle M.kernel M.kernel_nonneg M.betaCrit 0 x)
    (fun x : M.V => M.S.dist 0 x) hmass

/-- **The real-valued form**: `(M.nablaTail r).toReal → 0`. -/
theorem Orchestration.SourceModelData.tendsto_nablaTail_toReal_zero_of_gramProfile
    (M : Orchestration.SourceModelData) {f : M.V → ℝ} (hf0 : ∀ z, 0 ≤ f z)
    (hf : Summable f)
    (hident : ∀ u v : M.V,
      twoPointFunction M.kernel M.kernel_nonneg M.betaCrit u v = TriTail.gramKernel f u v) :
    Tendsto (fun r : ℝ => (M.nablaTail r).toReal) atTop (𝓝 0) := by
  have hmass := TriTail.tsum_openTriangle_ne_top_of_gramProfile (d := M.d) hf0 hf hident
  exact TriTail.tendsto_radialTailSup_toReal_zero
    (fun x : M.V => TriTail.openTriangle M.kernel M.kernel_nonneg M.betaCrit 0 x)
    (fun x : M.V => M.S.dist 0 x) hmass

/-- **The model's open-triangle tail vanishes under domination**, in `ℝ≥0∞` shape. -/
theorem Orchestration.SourceModelData.tendsto_nablaTail_zero_of_gramDomination
    (M : Orchestration.SourceModelData) {f : M.V → ℝ} (hf0 : ∀ z, 0 ≤ f z)
    (hf : Summable f)
    (hle : ∀ u v : M.V,
      twoPointFunction M.kernel M.kernel_nonneg M.betaCrit u v ≤ TriTail.gramKernel f u v) :
    Tendsto M.nablaTail atTop (𝓝 0) := by
  have hmass := TriTail.tsum_openTriangle_ne_top_of_gramDomination (d := M.d) hf0 hf hle
  exact TriTail.tendsto_radialTailSup_zero
    (fun x : M.V => TriTail.openTriangle M.kernel M.kernel_nonneg M.betaCrit 0 x)
    (fun x : M.V => M.S.dist 0 x) hmass

/-- **The model's open-triangle tail vanishes under domination** by an autocorrelation
kernel. -/
theorem Orchestration.SourceModelData.tendsto_nablaTail_toReal_zero_of_gramDomination
    (M : Orchestration.SourceModelData) {f : M.V → ℝ} (hf0 : ∀ z, 0 ≤ f z)
    (hf : Summable f)
    (hle : ∀ u v : M.V,
      twoPointFunction M.kernel M.kernel_nonneg M.betaCrit u v ≤ TriTail.gramKernel f u v) :
    Tendsto (fun r : ℝ => (M.nablaTail r).toReal) atTop (𝓝 0) := by
  have hmass := TriTail.tsum_openTriangle_ne_top_of_gramDomination (d := M.d) hf0 hf hle
  exact TriTail.tendsto_radialTailSup_toReal_zero
    (fun x : M.V => TriTail.openTriangle M.kernel M.kernel_nonneg M.betaCrit 0 x)
    (fun x : M.V => M.S.dist 0 x) hmass

end PercLib.CriticalLRP

/-! ### Non-vacuity of the profile hypothesis -/

namespace PercLib.CriticalLRP.TriTail

variable {d : ℕ}

/-! ### Sharpness: the finite-mass hypothesis of the engine is essential -/

/-- With `nrm k = k` on `ℕ`, the radial set `{k | r ≤ k}` is never empty, so the tail
supremum of the constant family `1` is `1` at every radius. -/
theorem iSup_one_of_le_nat (r : ℝ) :
    (⨆ k : ℕ, ⨆ (_hk : r ≤ (k : ℝ)), (1 : ℝ≥0∞)) = 1 := by
  refine le_antisymm (iSup_le fun k => iSup_le fun _hk => le_rfl) ?_
  obtain ⟨k, hk⟩ := exists_nat_ge r
  have hpos : (⨆ (_hk : r ≤ (k : ℝ)), (1 : ℝ≥0∞)) = 1 := iSup_pos hk
  calc (1 : ℝ≥0∞) = ⨆ (_hk : r ≤ (k : ℝ)), (1 : ℝ≥0∞) := hpos.symm
    _ ≤ ⨆ k : ℕ, ⨆ (_hk : r ≤ (k : ℝ)), (1 : ℝ≥0∞) :=
        le_iSup (fun k : ℕ => ⨆ (_hk : r ≤ (k : ℝ)), (1 : ℝ≥0∞)) k

/-- **The finite-mass hypothesis cannot be dropped.**  The constant family `a ≡ 1` on `ℕ`
has infinite total mass, and with `nrm k = k` its radial tail equals `1` at every radius, so
it does not tend to `0`.  Thus `tsum ≠ ⊤` in `tendsto_radialTailSup_zero` is doing real work,
and the vanishing is a genuine consequence of summability rather than of the shape of `nrm`. -/
theorem not_tendsto_radialTailSup_zero_const :
    ¬ Tendsto (fun r : ℝ => ⨆ k : ℕ, ⨆ (_hk : r ≤ (k : ℝ)), (1 : ℝ≥0∞)) atTop (𝓝 0) := by
  intro h
  have hev : ∀ᶠ r : ℝ in atTop,
      (⨆ k : ℕ, ⨆ (_hk : r ≤ (k : ℝ)), (1 : ℝ≥0∞)) < 1 :=
    (tendsto_order.1 h).2 1 zero_lt_one
  obtain ⟨r, hr⟩ := hev.exists
  rw [iSup_one_of_le_nat r] at hr
  exact lt_irrefl 1 hr


/-- The delta profile is nonnegative. -/
theorem deltaProfile_nonneg (z : Fin d → ℤ) : 0 ≤ deltaProfile d z := by
  unfold deltaProfile
  by_cases h : z = 0 <;> simp [h]

/-- The delta profile is summable (unit `ℓ¹` mass). -/
theorem summable_deltaProfile : Summable (deltaProfile d) := by
  have h : HasSum (fun z : Fin d → ℤ => if z = 0 then (1 : ℝ) else 0) 1 := by
    simpa using hasSum_ite_eq (0 : Fin d → ℤ) (1 : ℝ)
  exact h.summable

/-- `∑_z δ_0(z) = 1`. -/
theorem tsum_deltaProfile : (∑' z : Fin d → ℤ, deltaProfile d z) = 1 := by
  rw [tsum_eq_single (0 : Fin d → ℤ)]
  · simp [deltaProfile]
  · intro b hb
    simp [deltaProfile, hb]

/-- The delta profile is a nonnegative summable profile, so the Gram-profile hypotheses of the
tail theorems above are inhabited. -/
theorem exists_summable_nonneg_profile :
    ∃ f : (Fin d → ℤ) → ℝ, (∀ z, 0 ≤ f z) ∧ Summable f ∧
      (∑' x, openTriangleKernel (gramKernel f) 0 x) ≠ ⊤ :=
  ⟨deltaProfile d, deltaProfile_nonneg, summable_deltaProfile,
    tsum_openTriangleKernel_gramKernel_ne_top deltaProfile_nonneg summable_deltaProfile⟩

/-- **The total-mass bound is attained by the delta profile**: `∑_x ∇_δ(0,x) = 1 = (∑ δ)^6`,
matching the accepted computed witness `openTriangleKernel_gramKernel_delta`.  So the mass
hypothesis is not vacuous and the constant `(∑ f)^6` is sharp at this witness. -/
theorem tsum_openTriangleKernel_gramKernel_delta :
    (∑' x, openTriangleKernel (gramKernel (deltaProfile d)) 0 x) = 1 := by
  refine le_antisymm ?_ ?_
  · have hmass := tsum_openTriangleKernel_gramKernel_le (d := d) deltaProfile_nonneg
      summable_deltaProfile
    simpa [tsum_deltaProfile] using hmass
  · calc (1 : ℝ≥0∞) = openTriangleKernel (gramKernel (deltaProfile d)) 0 0 :=
        (openTriangleKernel_gramKernel_delta (d := d)).symm
      _ ≤ ∑' x, openTriangleKernel (gramKernel (deltaProfile d)) 0 x := ENNReal.le_tsum 0

end PercLib.CriticalLRP.TriTail

/-! ### Axiom audit -/

#print axioms PercLib.CriticalLRP.TriTail.radialTailSup_eventually_lt
#print axioms PercLib.CriticalLRP.TriTail.tendsto_radialTailSup_zero
#print axioms PercLib.CriticalLRP.TriTail.tendsto_radialTailSup_toReal_zero
#print axioms PercLib.CriticalLRP.TriTail.tendsto_radialTailSup_zero_of_le
#print axioms PercLib.CriticalLRP.TriTail.tsum_openTriangleKernel_gramKernel_le
#print axioms PercLib.CriticalLRP.TriTail.tsum_openTriangleKernel_gramKernel_ne_top
#print axioms PercLib.CriticalLRP.TriTail.openTriangle_eq_openTriangleKernel_gramKernel
#print axioms PercLib.CriticalLRP.TriTail.tsum_openTriangle_ne_top_of_gramProfile
#print axioms PercLib.CriticalLRP.TriTail.openTriangleTail_tendsto_zero_of_gramProfile
#print axioms PercLib.CriticalLRP.TriTail.tsum_openTriangle_ne_top_of_gramDomination
#print axioms PercLib.CriticalLRP.TriTail.openTriangleTail_tendsto_zero_of_gramDomination
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.tendsto_nablaTail_zero_of_gramProfile
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.tendsto_nablaTail_toReal_zero_of_gramProfile
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.tendsto_nablaTail_toReal_zero_of_gramDomination
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.tendsto_nablaTail_zero_of_gramDomination
#print axioms PercLib.CriticalLRP.TriTail.openTriangleTailOpen_le_openTriangleTail
#print axioms PercLib.CriticalLRP.TriTail.openTriangleTailOpen_tendsto_zero_of_gramProfile
#print axioms PercLib.CriticalLRP.TriTail.openTriangleTailOpen_tendsto_zero_of_gramDomination
#print axioms PercLib.CriticalLRP.TriTail.iSup_one_of_le_nat
#print axioms PercLib.CriticalLRP.TriTail.not_tendsto_radialTailSup_zero_const
#print axioms PercLib.CriticalLRP.TriTail.deltaProfile_nonneg
#print axioms PercLib.CriticalLRP.TriTail.summable_deltaProfile
#print axioms PercLib.CriticalLRP.TriTail.tsum_deltaProfile
#print axioms PercLib.CriticalLRP.TriTail.exists_summable_nonneg_profile
#print axioms PercLib.CriticalLRP.TriTail.tsum_openTriangleKernel_gramKernel_delta
