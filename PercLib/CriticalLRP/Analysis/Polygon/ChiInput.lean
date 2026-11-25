/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PercLib contributors

Uniform lower comparison and finiteness of source cutoff moments.
-/
module

public import PercLib.CriticalLRP.Analysis.Polygon.Consumer
public import PercLib.CriticalLRP.MomentMonotonicity.SourceModelCutoffLimit

set_option autoImplicit false
set_option linter.unusedSectionVars false

open MeasureTheory Filter Topology Asymptotics
open scoped ENNReal NNReal Topology BigOperators Asymptotics

@[expose] public section

namespace PercLib.CriticalLRP.I418C.ChiInput

open PercLib.CriticalLRP Orchestration
open PercLib.CriticalLRP.KernelPower

variable (M : SourceModelData)

/-! ## Finiteness of the cutoff mass from the first-moment lower comparison -/

/-- `(⊤ : ℝ≥0∞).toReal = 0`, so a *positive* lower bound on `(M.cutMassAt r 0).toReal`
already rules out `M.cutMassAt r 0 = ⊤`: `hχ` and `hχfin` are not independent, and `hχfin` is
not an extra source hypothesis. -/
theorem cutMassAt_ne_top_of_le_toReal {r c₀ : ℝ} (hc₀ : 0 < c₀) (hr : 0 < r)
    (h : c₀ * r ^ M.α ≤ (M.cutMassAt r 0).toReal) : M.cutMassAt r 0 ≠ ⊤ := by
  rintro htop
  rw [htop, ENNReal.toReal_top] at h
  have hpos : 0 < c₀ * r ^ M.α := mul_pos hc₀ (Real.rpow_pos_of_pos hr M.α)
  linarith

/-- For `α > 0`, `r ↦ r ^ α` is unbounded above on `[1, ∞)`. -/
theorem exists_lt_rpow_of_pos {α : ℝ} (hα : 0 < α) (B : ℝ) :
    ∃ r : ℝ, 1 ≤ r ∧ B < r ^ α := by
  have ht : Tendsto (fun r : ℝ => r ^ α) atTop atTop := tendsto_rpow_atTop hα
  have hev : ∀ᶠ r : ℝ in atTop, B + 1 ≤ r ^ α := tendsto_atTop.1 ht (B + 1)
  obtain ⟨r₀, hr₀⟩ := eventually_atTop.1 hev
  refine ⟨max r₀ 1, le_max_right _ _, ?_⟩
  have h := hr₀ (max r₀ 1) (le_max_left _ _)
  linarith

/-! ## Proposition I.4.2 ⟹ the uniform first-moment lower comparison

The paper's Lemma I.4.18 proof uses `E_{β_c,r}|K| ⪰ r^α`, the *lower half* of Proposition
I.4.2's `E_{β_c,r}|K| ∼ (α/β_c) r^α`.  Everything below takes that asymptotic, in one of its
shapes, as the only first-moment input. -/

/-- **Weakest sufficient first-moment input: an eventual lower bound `c r^α ≤ χ(r)` gives a
single `c₀ > 0` with `c₀ r^α ≤ χ(r)` for every `r > 0`.**

Above the threshold the constant stays `c`; below it, `χ(r) ≥ 1` (which holds unconditionally:
`T(0,0) = 1`, so the cluster mass is at least `1`) absorbs the deficit with `R ^ (-α)`, and
monotonicity of `χ` propagates finiteness downwards.  This is what makes the source's
`∀ r > 0` claim reachable from an `r → ∞` asymptotic. -/
theorem exists_chi_lower_uniform_of_eventually {c : ℝ} (hc : 0 < c)
    (h : ∀ᶠ r : ℝ in atTop, c * r ^ M.α ≤ (M.cutMassAt r 0).toReal) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ r : ℝ, 0 < r → c₀ * r ^ M.α ≤ (M.cutMassAt r 0).toReal := by
  obtain ⟨r₁, hr₁⟩ := eventually_atTop.1 h
  set R : ℝ := max r₁ 1 with hRdef
  have hR1 : 1 ≤ R := le_max_right _ _
  have hRpos : 0 < R := lt_of_lt_of_le one_pos hR1
  have habove : ∀ r : ℝ, R ≤ r → c * r ^ M.α ≤ (M.cutMassAt r 0).toReal :=
    fun r hr => hr₁ r (le_trans (le_max_left _ _) hr)
  have hRfin : M.cutMassAt R 0 ≠ ⊤ :=
    cutMassAt_ne_top_of_le_toReal M hc hRpos (habove R le_rfl)
  refine ⟨min c (R ^ (-M.α)), lt_min hc (Real.rpow_pos_of_pos hRpos _), ?_⟩
  intro r hrpos
  have hcle : min c (R ^ (-M.α)) ≤ c := min_le_left _ _
  have hcle' : min c (R ^ (-M.α)) ≤ R ^ (-M.α) := min_le_right _ _
  have hrpow : 0 < r ^ M.α := Real.rpow_pos_of_pos hrpos M.α
  rcases le_or_gt R r with hRr | hrR
  · exact le_trans (mul_le_mul_of_nonneg_right hcle (le_of_lt hrpow)) (habove r hRr)
  · -- `r < R`: `R ^ (-α) * r ^ α ≤ 1 ≤ χ(r)`
    have hmono : M.cutMassAt r 0 ≤ M.cutMassAt R 0 := by
      rw [M.cutMassAt_zero_eq_cutMoment r, M.cutMassAt_zero_eq_cutMoment R]
      exact M.cutMoment_monotone 1 (le_of_lt hrR)
    have hrfin : M.cutMassAt r 0 ≠ ⊤ := ne_top_of_le_ne_top hRfin hmono
    have h1le : (1 : ℝ) ≤ (M.cutMassAt r 0).toReal := by
      have h1 : (1 : ℝ≥0∞) ≤ M.cutMassAt r 0 := by
        rw [M.cutMassAt_zero_eq_cutMoment r]
        exact M.one_le_cutMoment_one r
      have h2 := ENNReal.toReal_mono hrfin h1
      simpa using h2
    have hpow : r ^ M.α ≤ R ^ M.α :=
      Real.rpow_le_rpow (le_of_lt hrpos) (le_of_lt hrR) M.hα.le
    have hinv : R ^ (-M.α) * R ^ M.α = 1 := by
      rw [← Real.rpow_add hRpos, neg_add_cancel, Real.rpow_zero]
    have hkey : R ^ (-M.α) * r ^ M.α ≤ 1 := by
      have h3 := mul_le_mul_of_nonneg_left hpow
        (le_of_lt (Real.rpow_pos_of_pos hRpos (-M.α)))
      linarith [hinv, h3]
    calc min c (R ^ (-M.α)) * r ^ M.α
        ≤ R ^ (-M.α) * r ^ M.α := mul_le_mul_of_nonneg_right hcle' (le_of_lt hrpow)
      _ ≤ 1 := hkey
      _ ≤ (M.cutMassAt r 0).toReal := h1le

/-- **General-constant form of the limit hypothesis: `χ(r) / (c r^α) → 1` with `c > 0` gives the
uniform first-moment lower comparison.**

Stated separately from the `c = α/β_c` instance below because `0 < β_c` is *not* a field of
`SourceModelData`: when the constant is supplied directly, no hypothesis on `β_c` is needed. -/
theorem exists_chi_lower_uniform_of_tendsto_div {c : ℝ} (hc : 0 < c)
    (hP : Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal / (c * r ^ M.α)) atTop (𝓝 1)) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ r : ℝ, 0 < r → c₀ * r ^ M.α ≤ (M.cutMassAt r 0).toReal := by
  have hc2 : 0 < c / 2 := by linarith
  refine exists_chi_lower_uniform_of_eventually M hc2 ?_
  filter_upwards [hP.eventually (eventually_gt_nhds (by norm_num : (1 : ℝ) / 2 < 1)),
    eventually_gt_atTop (0 : ℝ)] with r hr hr0
  have hden : 0 < c * r ^ M.α := mul_pos hc (Real.rpow_pos_of_pos hr0 M.α)
  rw [lt_div_iff₀ hden] at hr
  calc c / 2 * r ^ M.α = (1 / 2 : ℝ) * (c * r ^ M.α) := by ring
    _ ≤ (M.cutMassAt r 0).toReal := le_of_lt hr

/-- **Proposition I.4.2's displayed asymptotic implies the source's `E|K| ⪰ r^α`, uniformly
in `r`.**  Hypothesis: `(M.cutMassAt r 0).toReal / ((α/β_c) * r^α) → 1`. -/
theorem exists_chi_lower_uniform
    (hβ : 0 < (M.betaCrit : ℝ))
    (hP : Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal
      / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) atTop (𝓝 1)) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ r : ℝ, 0 < r → c₀ * r ^ M.α ≤ (M.cutMassAt r 0).toReal :=
  exists_chi_lower_uniform_of_tendsto_div M (div_pos M.hα hβ) hP

/-- **The source's `∼` in the repository's `~[atTop]` notation** (`SourceModelData.ball_count`
uses the same notation for Lemma I.4.6): `χ(r) ~[atTop] (α/β_c) r^α` gives the uniform
first-moment lower comparison. -/
theorem exists_chi_lower_uniform_of_isEquivalent
    (hβ : 0 < (M.betaCrit : ℝ))
    (hP : (fun r : ℝ => (M.cutMassAt r 0).toReal) ~[atTop]
      (fun r : ℝ => (M.α / (M.betaCrit : ℝ)) * r ^ M.α)) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ r : ℝ, 0 < r → c₀ * r ^ M.α ≤ (M.cutMassAt r 0).toReal := by
  have hA : 0 < M.α / (M.betaCrit : ℝ) := div_pos M.hα hβ
  refine exists_chi_lower_uniform M hβ ?_
  have hz : ∀ᶠ r : ℝ in atTop,
      (fun r : ℝ => (M.α / (M.betaCrit : ℝ)) * r ^ M.α) r ≠ 0 := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
    exact ne_of_gt (mul_pos hA (Real.rpow_pos_of_pos hr M.α))
  exact (isEquivalent_iff_tendsto_one (u := fun r : ℝ => (M.cutMassAt r 0).toReal)
    (v := fun r : ℝ => (M.α / (M.betaCrit : ℝ)) * r ^ M.α) hz).mp hP

/-- The two consumer-side hypotheses together, both derived from Proposition I.4.2:
the lower comparison at every `r > 0` and, consequently, its finiteness. -/
theorem exists_chi_lower_uniform_and_finite
    (hβ : 0 < (M.betaCrit : ℝ))
    (hP : Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal
      / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) atTop (𝓝 1)) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ r : ℝ, 0 < r →
      c₀ * r ^ M.α ≤ (M.cutMassAt r 0).toReal ∧ M.cutMassAt r 0 ≠ ⊤ := by
  obtain ⟨c₀, hc₀, hχ⟩ := exists_chi_lower_uniform M hβ hP
  exact ⟨c₀, hc₀, fun r hr =>
    ⟨hχ r hr, cutMassAt_ne_top_of_le_toReal M hc₀ hr (hχ r hr)⟩⟩

/-! ## The Lemma I.4.18 assembly with `hχfin` discharged -/

/-- **Lemma I.4.18, `ℓ ≥ 4`, with the finiteness of `χ` no longer assumed.**

Identical to `Polygon.Consumer.source_polygon_bound_of_cutoff_data` except that
`hχfin : M.cutMassAt r 0 ≠ ⊤` is replaced by the *uniform* first-moment comparison
`∀ r' > 0, c₀ * r'^α ≤ (M.cutMassAt r' 0).toReal`, from which it follows at `r` (`1 ≤ r`).
The uniform form is the shape Proposition I.4.2 delivers, and it is what the source uses:
its `c` and `C` do not depend on `r`. -/
theorem source_polygon_bound_of_uniform_chi
    (r R trc : ℝ) (s : Finset M.V) {c₀ K cc : ℝ}
    (hr : 1 ≤ r) (hc₀ : 0 < c₀) (hK : 0 ≤ K)
    (hχu : ∀ r' : ℝ, 0 < r' → c₀ * r' ^ M.α ≤ (M.cutMassAt r' 0).toReal)
    (hTri : PercLib.CriticalLRP.TriTail.openTriangleSelf M.kernel M.kernel_nonneg M.betaCrit 0
      < ⊤)
    (hB2 : ∀ u : M.V, Summable (fun v => M.twoPoint M.betaCrit 0 v * M.twoPoint M.betaCrit v u))
    (hB3 : ∀ y : M.V,
      Summable (fun u => (∑' v, M.twoPoint M.betaCrit 0 v * M.twoPoint M.betaCrit v u)
        * M.twoPoint M.betaCrit u y))
    (hlink : ∀ y : M.V, polyK (M.twoPoint M.betaCrit) 3 0 y ≤ M.triPoint 0 y)
    {ell : ℕ} (hell : 4 ≤ ell)
    (hct : cc = M.α / (4 * (M.d : ℝ)))
    (hfar : ∀ y : M.V, y ∉ s → R ≤ M.S.dist 0 y)
    (htailc : ∀ y : M.V, r ^ cc ≤ M.S.dist 0 y → M.triPoint 0 y ≤ trc)
    (htrc : 0 ≤ trc)
    (hcard : (s.card : ℝ) ≤ K * R ^ (M.d : ℝ))
    (hR : R = r ^ (M.α / (2 * (M.d : ℝ)))) :
    ∀ x : M.V, polyK (M.cutTwoPoint r) ell 0 x
      ≤ max 1 (M.triSelf * K / c₀) * (trc + r ^ (-cc)) *
        ((M.cutMassAt r 0).toReal) ^ (ell - 3) := by
  have hrpos : 0 < r := lt_of_lt_of_le one_pos hr
  exact source_polygon_bound_of_cutoff_data M r R trc s hr hc₀ hK
    (cutMassAt_ne_top_of_le_toReal M hc₀ hrpos (hχu r hrpos))
    hTri hB2 hB3 hlink hell hct hfar htailc htrc hcard hR (hχu r hrpos)

/-- **Source-facing form: Lemma I.4.18 for `ℓ ≥ 4`, with the first-moment constant produced by
Proposition I.4.2 and no first-moment hypothesis left.**

There is `c₀ > 0` — namely `min ((α/β_c)/2) (R₁^{-α})` with `R₁ = max r₁ 1`, `r₁` the threshold
of the limit, so it depends only on `α`, `β_c` and that limit — such that for every `r ≥ 1` and
every admissible
near/far/ball/tail datum, the polygon diagram is bounded by

  `max 1 (∇_{β_c} K / c₀) * (∇_{r^c} + r^{-c}) * χ^{ℓ-3}`,

with `C = max 1 (∇_{β_c} K / c₀)` independent of `r` and `ℓ`.  The remaining hypotheses are
the ball/tail data of the source theorem — `∇_{r^c}` is an input to that statement too, and
`K, cc` encode the ball-count bound and the choice `c = α/(4d)` — together with the uncut
threefold comparison data.  None of them mentions `χ`. -/
theorem exists_c0_source_polygon_bound
    (hβ : 0 < (M.betaCrit : ℝ))
    (hP : Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal
      / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) atTop (𝓝 1))
    (hTri : PercLib.CriticalLRP.TriTail.openTriangleSelf M.kernel M.kernel_nonneg M.betaCrit 0
      < ⊤)
    (hB2 : ∀ u : M.V, Summable (fun v => M.twoPoint M.betaCrit 0 v * M.twoPoint M.betaCrit v u))
    (hB3 : ∀ y : M.V,
      Summable (fun u => (∑' v, M.twoPoint M.betaCrit 0 v * M.twoPoint M.betaCrit v u)
        * M.twoPoint M.betaCrit u y))
    (hlink : ∀ y : M.V, polyK (M.twoPoint M.betaCrit) 3 0 y ≤ M.triPoint 0 y) :
    ∃ c₀ : ℝ, 0 < c₀ ∧
      ∀ (r R trc : ℝ) (s : Finset M.V) (K cc : ℝ) (ell : ℕ),
        1 ≤ r → 0 ≤ K → 4 ≤ ell → cc = M.α / (4 * (M.d : ℝ)) →
        (∀ y : M.V, y ∉ s → R ≤ M.S.dist 0 y) →
        (∀ y : M.V, r ^ cc ≤ M.S.dist 0 y → M.triPoint 0 y ≤ trc) →
        0 ≤ trc → (s.card : ℝ) ≤ K * R ^ (M.d : ℝ) →
        R = r ^ (M.α / (2 * (M.d : ℝ))) →
        ∀ x : M.V, polyK (M.cutTwoPoint r) ell 0 x
          ≤ max 1 (M.triSelf * K / c₀) * (trc + r ^ (-cc)) *
            ((M.cutMassAt r 0).toReal) ^ (ell - 3) := by
  obtain ⟨c₀, hc₀, hχu⟩ := exists_chi_lower_uniform M hβ hP
  exact ⟨c₀, hc₀, fun r R trc s K cc ell hr hK hell hct hfar htailc htrc hcard hR =>
    source_polygon_bound_of_uniform_chi M r R trc s hr hc₀ hK hχu hTri hB2 hB3 hlink
      hell hct hfar htailc htrc hcard hR⟩

/-! ## `hχ` is not a finiteness assumption

The uniform first-moment comparison pushes `χ(r)` above `c₀ r^α` for all `r`, while `χ(r)` is
bounded above by the *uncut* critical first moment.  Hence `hχ` forces that uncut moment to be
`⊤`: it is incompatible with a finite critical susceptibility.  This is exactly why it cannot
be obtained from `χ_{β_c} < ∞`, and why no route to it is circular in the source's sense. -/

/-- **`E|K| ⪰ r^α` at `β_c,r` forces the uncut critical first moment to be infinite.**

So the first-moment lower comparison of Lemma I.4.18 is not a disguised finiteness hypothesis:
any derivation of it must be compatible with `E_{β_c}|K_0| = ⊤`; conversely, a finite
`E_{β_c}|K_0|` refutes the uniform comparison for every `c₀ > 0`. -/
theorem uncut_firstMoment_eq_top_of_chi_lower {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hχu : ∀ r : ℝ, 0 < r → c₀ * r ^ M.α ≤ (M.cutMassAt r 0).toReal) :
    ∫⁻ ω, clusterVol ω (0 : M.V) ∂(M.law M.betaCrit) = ⊤ := by
  by_contra hne
  have hbound : ∀ r : ℝ, 0 < r →
      c₀ * r ^ M.α ≤ (∫⁻ ω, clusterVol ω (0 : M.V) ∂(M.law M.betaCrit)).toReal := by
    intro r hr
    refine le_trans (hχu r hr) ?_
    rw [M.cutMassAt_zero_eq_cutMoment r]
    have h2 : M.cutMoment 1 r
        ≤ ∫⁻ ω, clusterVol ω (0 : M.V) ∂(M.law M.betaCrit) := by
      simpa using M.cutMoment_le_uncut 1 r
    exact ENNReal.toReal_mono hne h2
  -- `r ^ α` is unbounded above, so some `r ≥ 1` violates the bound
  obtain ⟨r, hr1, hrbig⟩ := exists_lt_rpow_of_pos M.hα
    ((∫⁻ ω, clusterVol ω (0 : M.V) ∂(M.law M.betaCrit)).toReal / c₀)
  have hrpos : 0 < r := lt_of_lt_of_le one_pos hr1
  have hbig : (∫⁻ ω, clusterVol ω (0 : M.V) ∂(M.law M.betaCrit)).toReal < c₀ * r ^ M.α := by
    rw [div_lt_iff₀ hc₀] at hrbig
    linarith [hrbig]
  linarith [hbound r hrpos, hbig]


/-- If the model's cutoff first-moment ratio converges to `1`, the critical parameter is
positive. In the zero-parameter case the denominator of that ratio is identically zero,
so uniqueness of limits contradicts convergence to `1`. -/
theorem betaCrit_pos_of_tendsto_chi_div
    (hP : Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal
      / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) atTop (𝓝 1)) :
    0 < (M.betaCrit : ℝ) := by
  have hbne : (M.betaCrit : ℝ) ≠ 0 := by
    intro hbzero
    simp [hbzero] at hP
  exact lt_of_le_of_ne M.betaCrit.coe_nonneg (Ne.symm hbne)

end PercLib.CriticalLRP.I418C.ChiInput
