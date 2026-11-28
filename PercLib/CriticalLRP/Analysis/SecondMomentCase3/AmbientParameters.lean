/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Accepted and independently rebuilt from Ultramath `smwzlje3f`.
Production base `a59bc6c22aba42e69160666c17feac870d4cb887`; reviewed scratch source `.ultramath/smwzlje3f/m2/AmbientParameters.lean`.

Ultramath swarm `smwzlje3f`, member `m2`.

# Ambient parameters of the Case-3 chain are not independent inputs

Two kinds of inputs of the Case-3 wrappers are derivable rather than assumed:

* On the I.4.15 side, `hα : 0 < M.α` is the structure field `SourceModelData.hα`, and
  `hβ : (M.betaCrit : ℝ) ≠ 0` follows from the first-moment normalisation `hP`: at
  `β_c = 0` the normalising constant `α/β_c` is `0`, so the quotient in `hP` is the
  constant `0` and cannot tend to `1`.
* On the I.4.20 side, `hαd : M.α < M.d` follows from the high-dimensional alternative
  `hHD3`, and `hβ : 0 < M.betaCrit` follows from the lower two-point bound `hlow` and the
  `β = 0` law (`longRangeMeasure_zero`: at `β = 0` no edge is open, so distinct vertices
  are not connected).

Further reductions proved here:

* `regularlyVaryingAtTop_of_tendsto_div_rpow` converts the *conclusion* of the product-gap
  Case-3 theorem (`(M.cutMoment 2 r).toReal / r ^ (3α) → A > 0`) into the `hRV2` input of
  the I.4.20 Case-3 consumers.
* `measurable_cutMoment_toReal_of_monotone` proves `r ↦ (M.cutMoment p r).toReal`
  measurable unconditionally (production's version needs finiteness at every radius), which
  removes `hmommeas1`/`hmommeas2` from those consumers.
* `case3_moment_three_bound_of_source_p21` is the I.4.19 cubic-bound consumer with seven
  consumer-side inputs *derived*: `hRV2` from the proved `(2,1)` product-gap theorem,
  `hRV1` from `hP` (`momOf_one_regularlyVarying`), `hmommeas1`/`hmommeas2` from the
  unconditional measurability lemma, `hαd` from `hHD3`, `hβ` from `hlow`, and `hfin` from
  `hP`.

The finiteness side condition `hfin : ∀ᶠ r, M.cutMassAt r 0 ≠ ⊤` of the I.4.20 consumers is
also not independent: `eventually_cutMassAt_ne_top_of_hP` derives it from `hP`, because
`(⊤ : ℝ≥0∞).toReal = 0` makes the normalised quotient `0`.

The source statements used are Proposition I.4.2 (`E_{β_c,r}|K| ∼ (α/β_c) r^α`, which is
exactly the normalisation assumed in `hP`), Proposition I.4.15 (regular variation of
`E_{β_c,r}|K|²` of index `3α`, and `E|K|² ∼ A r^{3α}` under logarithmic integrability of the
error), and Proposition I.4.20 (`E|K|^p ∼ (2p-3)!! (E|K|²/E|K|)^{p-1} E|K|`), from
Hutchcroft, *Critical long-range percolation I*, pp. 33–47.

No `sorry`, no `admit`, no `native_decide`, no custom axioms.
-/
module

public import PercLib.CriticalLRP.Analysis.MomentRegularVariation
public import PercLib.CriticalLRP.Analysis.SecondMomentCase3.ProductGap.SourceConsumer
public import PercLib.CriticalLRP.VolumeMoments.HigherMoments.I420Case3.Scope.Main
public import PercLib.CriticalLRP.VolumeMoments.HigherMoments.I420Case3.RatioInduction.Handoff

@[expose] public section

open MeasureTheory Measure ProbabilityTheory unitInterval Filter Topology Set
open scoped ENNReal NNReal Topology
open PercLib.CriticalLRP.VolumeMoments.HigherMoments

namespace PercLib.CriticalLRP.Analysis

/-- **A positive power-law limit gives regular variation of that index.**
If `f r / r ^ a → A > 0`, then `f (l r) / f r → l ^ a` for every `l > 0`, and `f` is
eventually nonzero. -/
theorem regularlyVaryingAtTop_of_tendsto_div_rpow {f : ℝ → ℝ} {a A : ℝ} (hA : 0 < A)
    (h : Tendsto (fun r : ℝ => f r / r ^ a) atTop (𝓝 A)) :
    RegularlyVaryingAtTop f a := by
  have hnorm : Tendsto (fun r : ℝ => f r / (A * r ^ a)) atTop (𝓝 1) := by
    have hdiv : Tendsto (fun r : ℝ => (f r / r ^ a) / A) atTop (𝓝 (A / A)) :=
      h.div_const A
    rw [div_self hA.ne'] at hdiv
    refine hdiv.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
    have hra : r ^ a ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hr _)
    have hA0 : A ≠ 0 := ne_of_gt hA
    field_simp
  exact Analysis.regularlyVaryingAtTop_of_tendsto_div hA.ne' hnorm

end PercLib.CriticalLRP.Analysis

namespace PercLib.CriticalLRP.Orchestration.SourceModelData

variable (M : SourceModelData)

/-! ## `β_c ≠ 0` and `κ = α/β_c > 0` follow from the first-moment normalisation -/

/-- **`hβ` is implied by `hP`.** The normalising constant of the first-moment asymptotic is
`κ = α / β_c`; at `β_c = 0` the quotient in `hP` is identically zero, so it cannot tend to
`1`. -/
theorem betaCrit_ne_zero_of_hP
    (hP : Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal
      / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) atTop (𝓝 1)) :
    (M.betaCrit : ℝ) ≠ 0 := by
  intro h0
  have hconst : (fun r : ℝ => (M.cutMassAt r 0).toReal
      / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) = fun _ => (0 : ℝ) := by
    funext r
    simp [h0]
  rw [hconst] at hP
  have h10 : (1 : ℝ) = 0 := tendsto_nhds_unique hP tendsto_const_nhds
  exact one_ne_zero h10

/-- Positivity of the model's `β_c` from its nonvanishing, using `β_c : ℝ≥0`. -/
theorem betaCrit_pos_of_ne_zero (hβ : (M.betaCrit : ℝ) ≠ 0) : 0 < (M.betaCrit : ℝ) :=
  lt_of_le_of_ne (NNReal.coe_nonneg _) (Ne.symm hβ)

/-- **`hκ` is implied by `hP`**: the normalising constant `α / β_c` is positive. -/
theorem kappa_pos_of_hP
    (hP : Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal
      / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) atTop (𝓝 1)) :
    0 < M.α / (M.betaCrit : ℝ) :=
  div_pos M.hα (M.betaCrit_pos_of_ne_zero (M.betaCrit_ne_zero_of_hP hP))

/-- `hκ` from an explicitly assumed `β_c ≠ 0` (the form in which `κ > 0` appears in the
Case-1 and measurability consumers). -/
theorem kappa_pos_of_betaCrit_ne_zero (hβ : (M.betaCrit : ℝ) ≠ 0) :
    0 < M.α / (M.betaCrit : ℝ) :=
  div_pos M.hα (M.betaCrit_pos_of_ne_zero hβ)

/-- **Measurability of the real cutoff moments.** `r ↦ M.cutMoment p r` is monotone into
`ℝ≥0∞`, hence measurable, and `ENNReal.toReal` is measurable.  In particular `hmommeas1`
and `hmommeas2` of the I.4.20 consumers are not inputs. -/
theorem measurable_cutMoment_toReal_of_monotone (p : ℕ) :
    Measurable (fun r : ℝ => (M.cutMoment p r).toReal) :=
  ENNReal.measurable_toReal.comp (M.cutMoment_monotone p).measurable

/-- **Finiteness of the first cutoff moment is implied by `hP`.** If `cutMassAt r 0 = ⊤`
then its `toReal` is `0`, so the normalised quotient in `hP` is `0`; a sequence tending to
`1` is eventually `> 1/2`.  Hence `hfin` of the I.4.20 Case-3 consumers is not independent
of the first-moment normalisation. -/
theorem eventually_cutMassAt_ne_top_of_hP
    (hP : Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal
      / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) atTop (𝓝 1)) :
    ∀ᶠ r : ℝ in atTop, M.cutMassAt r 0 ≠ ⊤ := by
  have hev : ∀ᶠ r : ℝ in atTop,
      (1 / 2 : ℝ) < (M.cutMassAt r 0).toReal
        / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α) :=
    hP.eventually (lt_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1))
  filter_upwards [hev] with r hr htop
  rw [htop, ENNReal.toReal_top, zero_div] at hr
  linarith

/-! ## The Case-3 exports without `hα` and `hβ` -/

/-- **Proposition I.4.15, Case 3, with the ambient parameters discharged.** Same conclusion
and same remaining source inputs as `secondMoment_asymptotic_case3_of_source_p21`, but
`hα` is taken from the model structure and `hβ` is derived from `hP`. -/
theorem secondMoment_asymptotic_case3_of_source_p21_paramFree {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hac : ∀ R : ℝ, r₀ ≤ R → AbsolutelyContinuousOnInterval
      (fun r : ℝ => (M.cutMoment 2 r).toReal) r₀ R)
    (hae : ∀ᵐ t ∂(volume.restrict (Ici r₀)),
      HasDerivAt (fun r : ℝ => (M.cutMoment 2 r).toReal) (M.rhsScalarTwo t) t)
    (h1 : ∀ t : ℝ, r₀ ≤ t → M.cutMoment 1 t ≠ ⊤)
    (h2 : ∀ t : ℝ, r₀ ≤ t → M.cutMoment 2 t ≠ ⊤)
    (hP : Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal
      / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) atTop (𝓝 1))
    (hTri : TriTail.openTriangleSelf M.kernel M.kernel_nonneg M.betaCrit 0 < ⊤)
    {C₀ p : ℝ} (hC₀ : 0 ≤ C₀) (hp : 1 < p)
    (hF : Analysis.LogRadialBound (fun y : M.V => M.S.dist (0 : M.V) y)
      (fun y : M.V => TriTail.openTriangle M.kernel M.kernel_nonneg M.betaCrit 0 y) C₀ p)
    (hmeasE2 : Measurable M.p2ExclError) (hmeasEbar : Measurable M.p2Ebar)
    (hlogH : Analysis.LogarithmicallyIntegrable M.p2H)
    (hlogE0 : Analysis.LogarithmicallyIntegrable (PivotFlux.cutE0 M))
    {c3 : ℝ} (hc3 : 0 < c3)
    (hgm : ∀ᶠ r : ℝ in atTop, c3 * (M.cutMassAt r 0).toReal ^ 3 ≤ (M.cutMoment 2 r).toReal) :
    ∃ A : ℝ, 0 < A ∧ Tendsto
      (fun r : ℝ => (M.cutMoment 2 r).toReal / r ^ (3 * M.α)) atTop (𝓝 A) :=
  M.secondMoment_asymptotic_case3_of_source_p21 M.hα hr₀
    (M.betaCrit_ne_zero_of_hP hP) hac hae h1 h2 hP hTri hC₀ hp hF hmeasE2 hmeasEbar
    hlogH hlogE0 hc3 hgm

/-- **Proposition I.4.15, Case 3, in regularly-varying form, with the ambient parameters
discharged.** -/
theorem regularlyVarying_two_of_source_p21_paramFree {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hac : ∀ R : ℝ, r₀ ≤ R → AbsolutelyContinuousOnInterval
      (fun r : ℝ => (M.cutMoment 2 r).toReal) r₀ R)
    (hmR : Measurable M.rhsScalarTwo)
    (hae : ∀ᵐ t ∂(volume.restrict (Ici r₀)),
      HasDerivAt (fun r : ℝ => (M.cutMoment 2 r).toReal) (M.rhsScalarTwo t) t)
    (h1 : ∀ t : ℝ, r₀ ≤ t → M.cutMoment 1 t ≠ ⊤)
    (h2 : ∀ t : ℝ, r₀ ≤ t → M.cutMoment 2 t ≠ ⊤)
    (hP : Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal
      / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) atTop (𝓝 1))
    (hTri : TriTail.openTriangleSelf M.kernel M.kernel_nonneg M.betaCrit 0 < ⊤)
    {C₀ p : ℝ} (hC₀ : 0 ≤ C₀) (hp : 1 < p)
    (hF : Analysis.LogRadialBound (fun y : M.V => M.S.dist (0 : M.V) y)
      (fun y : M.V => TriTail.openTriangle M.kernel M.kernel_nonneg M.betaCrit 0 y) C₀ p)
    {c3 : ℝ} (hc3 : 0 < c3)
    (hgm : ∀ᶠ r : ℝ in atTop, c3 * (M.cutMassAt r 0).toReal ^ 3 ≤ (M.cutMoment 2 r).toReal) :
    Analysis.RegularlyVaryingAtTop (fun r : ℝ => (M.cutMoment 2 r).toReal) (3 * M.α) :=
  M.regularlyVarying_two_of_source_p21 M.hα hr₀
    (M.betaCrit_ne_zero_of_hP hP) hac hmR hae h1 h2 hP hTri hC₀ hp hF hc3 hgm

end PercLib.CriticalLRP.Orchestration.SourceModelData

namespace PercLib.CriticalLRP.Orchestration.SourceModelData

variable (M : SourceModelData)

/-! ## The honest `β = 0` law and `β_c > 0` from the lower two-point bound -/

/-- At `β = 0` the law is the point mass at the empty configuration, so distinct vertices are
not connected: `twoPoint 0 x y = 0`. -/
theorem twoPoint_zero_of_ne {x y : M.V} (hxy : x ≠ y) : M.twoPoint 0 x y = 0 := by
  have hlaw : M.law 0 = Measure.dirac (∅ : Config M.V) :=
    longRangeMeasure_zero M.kernel M.kernel_nonneg
  have hnot : (∅ : Config M.V) ∉ {ω : Config M.V | Connects ω x y} := by
    simp only [Set.mem_ofPred_eq, Connects, PercLib.Percolation.Bond.openGraph_empty,
      SimpleGraph.reachable_bot]
    exact hxy
  change (M.law 0).real {ω : Config M.V | Connects ω x y} = 0
  rw [hlaw, Measure.dirac_real_apply, Set.indicator_of_notMem hnot]

/-- A nonzero vertex of the lattice `Fin M.d → ℤ`. -/
theorem exists_ne_zero_vertex : ∃ x : M.V, x ≠ 0 := by
  refine ⟨fun i => if i = (⟨0, M.hd⟩ : Fin M.d) then (1 : ℤ) else 0, ?_⟩
  intro hzero
  have h1 := congrFun hzero (⟨0, M.hd⟩ : Fin M.d)
  simp at h1

/-- **`0 < β_c` from a positive lower bound on the two-point function.** If `β_c` were `0`,
the lower bound would compare a positive number with `twoPoint 0 0 x = 0`. -/
theorem betaCrit_pos_of_twoPoint_lower {c : ℝ} (hc : 0 < c) {x : M.V} (hx : x ≠ 0)
    (hlow : c * (M.S.dist 0 x) ^ (-(M.d : ℝ) + M.α) ≤ M.twoPoint M.betaCrit 0 x) :
    0 < (M.betaCrit : ℝ) := by
  rcases eq_or_lt_of_le (NNReal.coe_nonneg M.betaCrit) with h0 | hpos
  · exfalso
    have hbc0 : M.betaCrit = 0 := NNReal.coe_eq_zero.mp h0.symm
    have hz : M.twoPoint (0 : ℝ≥0) (0 : M.V) x = 0 := M.twoPoint_zero_of_ne (Ne.symm hx)
    rw [hbc0, hz] at hlow
    have hp : 0 < (M.S.dist 0 x) ^ (-(M.d : ℝ) + M.α) :=
      Real.rpow_pos_of_pos (M.S.dist_pos (Ne.symm hx)) _
    have hpos' : 0 < c * (M.S.dist 0 x) ^ (-(M.d : ℝ) + M.α) := mul_pos hc hp
    linarith
  · exact hpos

end PercLib.CriticalLRP.Orchestration.SourceModelData



namespace PercLib.CriticalLRP.I420Case3

open PercLib.CriticalLRP Orchestration
open PercLib.CriticalLRP.VolumeMoments.HigherMoments

/-- **The cubic (I.4.19) upper moment bound with the ambient parameters discharged.**
`hαd` and `hβ` are derived: the first from `hHD3`, the second from `hlow` and the `β = 0`
law. -/
theorem case3_moment_three_bound_of_HD_case3_paramFree (M : SourceModelData)
    (hHD3 : M.d = 6 ∧ M.α = 2 ∧ ∃ C : ℝ, 0 < C ∧ ∀ x y : M.V, x ≠ y →
      M.twoPoint M.betaCrit x y ≤ C * (Real.log (M.S.ρ (toVec (x - y))))⁻¹ *
        (M.S.ρ (toVec (x - y))) ^ (-(M.d : ℝ) + 2))
    (hTri : TriTail.openTriangleSelf M.kernel M.kernel_nonneg M.betaCrit 0 < ⊤)
    {f' h : ℝ → ℝ} {c C r₀ : ℝ} (hc : 0 < c)
    (hlow : ∀ x : M.V, x ≠ 0 →
      c * (M.S.dist 0 x) ^ (-(M.d : ℝ) + M.α) ≤ M.twoPoint M.betaCrit 0 x)
    (hfin : ∀ᶠ r : ℝ in atTop, M.cutMassAt r 0 ≠ ⊤)
    (hr₀ : 0 < r₀)
    (hderiv : ∀ t, r₀ ≤ t →
      HasDerivAt (fun r => (M.cutMassAt r 0).toReal) (f' t) t)
    (hpos : ∀ t, r₀ ≤ t → 0 < (M.cutMassAt t 0).toReal)
    (hode : ∀ t, r₀ ≤ t →
      f' t = (M.betaCrit : ℝ) * (1 - h t) * t ^ (-M.α - 1) *
        ((M.cutMassAt t 0).toReal) ^ 2)
    (hmeas : Measurable h) (hhedge : ∀ t, r₀ ≤ t → |h t| ≤ C)
    (h0 : Tendsto h atTop (𝓝 0))
    (𝓔 : ℕ → Finset (Sym2 M.V)) (h𝓔mono : Monotone 𝓔)
    (h𝓔 : ∀ e : Sym2 M.V, ∃ n, e ∈ 𝓔 n)
    {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hMa : ∀ (r : ℝ), 1 ≤ r → ∀ ℓ : ℕ, ℓ ≤ 3 →
      I420Case1.powMomentAt (M.cutProb r) (ℓ + 1) (0 : M.V) ≠ ⊤)
    {c3 : ℝ} (hc3 : 0 < c3)
    (hgm : ∀ᶠ r in atTop, c3 * momOf (fun r => M.cutProb r) (0 : M.V) 1 r ^ 3
      ≤ momOf (fun r => M.cutProb r) (0 : M.V) 2 r)
    (hmommeas1 : Measurable (fun r =>
      momOf (fun r => M.cutProb r) (0 : M.V) 1 r))
    (hmommeas2 : Measurable (fun r =>
      momOf (fun r => M.cutProb r) (0 : M.V) 2 r))
    (hRV1 : Analysis.RegularlyVaryingAtTop
      (fun r => momOf (fun r => M.cutProb r) (0 : M.V) 1 r) M.α)
    (hRV2 : Analysis.RegularlyVaryingAtTop
      (fun r => momOf (fun r => M.cutProb r) (0 : M.V) 2 r) (3 * M.α))
    {cr : ℝ → ℝ} (hcr0 : ∀ r, 0 < r → 0 ≤ cr r)
    (hderivId : ∀ r : ℝ, 0 < r → HasDerivAt
      (fun s => momOf (fun s => M.cutProb s) (0 : M.V) 3 s)
      (cr r * ∑ ℓ ∈ Finset.range 3, ((Nat.choose 3 ℓ : ℕ) : ℝ) *
        I420Case1.mixedExclR (M.cutProb r) (0 : M.V) (ℓ + 1) (3 - ℓ)
          (BallAverage.ball_finite M r).toFinset) r)
    (hcnorm : ∀ ε > 0, ∀ᶠ r in atTop,
      cr r * I420Case3.ballCard (fun r =>
          (BallAverage.ball_finite M r).toFinset) r *
        momOf (fun r => M.cutProb r) (0 : M.V) 1 r * r ≤ (1 + ε) * M.α) :
    ∀ ε > 0, ∀ᶠ r in atTop,
      momOf (fun r => M.cutProb r) (0 : M.V) 3 r ≤
        (1 + ε) * mixedMoment 3 (fun m r =>
          momOf (fun r => M.cutProb r) (0 : M.V) m r) r := by
  have hαd : M.α < (M.d : ℝ) := by
    rw [hHD3.1, hHD3.2.1]
    norm_num
  have hβ : (0 : ℝ) < M.betaCrit := by
    obtain ⟨x, hx⟩ := M.exists_ne_zero_vertex
    exact M.betaCrit_pos_of_twoPoint_lower hc hx (hlow x hx)
  exact case3_moment_three_bound_of_HD_case3 M hHD3 hTri hc hαd hlow hfin hβ hr₀ hderiv
    hpos hode hmeas hhedge h0 𝓔 h𝓔mono h𝓔 hθ0 hθ1 hMa hc3 hgm hmommeas1 hmommeas2 hRV1 hRV2
    hcr0 hderivId hcnorm

/-- **The normalised `(I.4.21)` Case-3 form with the ambient parameters discharged.**
`hαd` from `hHD3`; `hβ` from `hlow` and the `β = 0` law. -/
theorem case3_i421_cutPoly_source_of_HD_case3_paramFree (M : SourceModelData)
    (hHD3 : M.d = 6 ∧ M.α = 2 ∧ ∃ C : ℝ, 0 < C ∧ ∀ x y : M.V, x ≠ y →
      M.twoPoint M.betaCrit x y ≤ C * (Real.log (M.S.ρ (toVec (x - y))))⁻¹ *
        (M.S.ρ (toVec (x - y))) ^ (-(M.d : ℝ) + 2))
    (hTri : TriTail.openTriangleSelf M.kernel M.kernel_nonneg M.betaCrit 0 < ⊤)
    {f' h : ℝ → ℝ} {c C r₀ : ℝ} (hc : 0 < c)
    (hlow : ∀ x : M.V, x ≠ 0 →
      c * (M.S.dist 0 x) ^ (-(M.d : ℝ) + M.α) ≤ M.twoPoint M.betaCrit 0 x)
    (hfin : ∀ᶠ r : ℝ in atTop, M.cutMassAt r 0 ≠ ⊤)
    (hr₀ : 0 < r₀)
    (hderiv : ∀ t, r₀ ≤ t →
      HasDerivAt (fun r => (M.cutMassAt r 0).toReal) (f' t) t)
    (hpos : ∀ t, r₀ ≤ t → 0 < (M.cutMassAt t 0).toReal)
    (hode : ∀ t, r₀ ≤ t →
      f' t = (M.betaCrit : ℝ) * (1 - h t) * t ^ (-M.α - 1) *
        ((M.cutMassAt t 0).toReal) ^ 2)
    (hmeas : Measurable h) (hhedge : ∀ t, r₀ ≤ t → |h t| ≤ C)
    (h0 : Tendsto h atTop (𝓝 0))
    (𝓔 : ℕ → Finset (Sym2 M.V)) (h𝓔mono : Monotone 𝓔)
    (h𝓔 : ∀ e : Sym2 M.V, ∃ n, e ∈ 𝓔 n) (p ℓ : ℕ) (hp : 1 ≤ p) (hℓ : ℓ + 1 ≤ p)
    {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hmom : ∀ r : ℝ, 1 ≤ r → ∀ m : ℕ, 1 ≤ m → m ≤ p + 1 →
      I420Case1.powMomentAt (M.cutProb r) m (0 : M.V) ≠ ⊤)
    {c3 : ℝ} (hc3 : 0 < c3)
    (hgm : ∀ᶠ r in atTop, c3 * momOf (fun r => M.cutProb r) (0 : M.V) 1 r ^ 3
      ≤ momOf (fun r => M.cutProb r) (0 : M.V) 2 r) :
    ∃ c₁ C₁ : ℝ, 0 < c₁ ∧ 0 < C₁ ∧
      Tendsto (fun r => discR (M.cutProb r) (0 : M.V) (ℓ + 1) (p - ℓ)
          (BallAverage.ball_finite M r).toFinset /
        biasTarget (momOf (fun r => M.cutProb r) (0 : M.V) 1 r)
          (momOf (fun r => M.cutProb r) (0 : M.V) 2 r) p) atTop (𝓝 0) := by
  have hαd : M.α < (M.d : ℝ) := by
    rw [hHD3.1, hHD3.2.1]
    norm_num
  have hβ : (0 : ℝ) < M.betaCrit := by
    obtain ⟨x, hx⟩ := M.exists_ne_zero_vertex
    exact M.betaCrit_pos_of_twoPoint_lower hc hx (hlow x hx)
  exact case3_i421_cutPoly_source_of_HD_case3 M hHD3 hTri hc hαd hlow hfin hβ hr₀ hderiv
    hpos hode hmeas hhedge h0 𝓔 h𝓔mono h𝓔 p ℓ hp hℓ hθ0 hθ1 hmom hc3 hgm

/-- **The two normalised `(I.4.20)` Case-3 limits with the ambient parameters discharged.**
`hαd` is derived from `hHD3` and `hβ : 0 < β_c` from `hlow` and the `β = 0` law; `hfin` is
retained because this statement has no `hP`. -/
theorem case3_hAend_hAmid_cutPoly_source_of_HD_case3_paramFree (M : SourceModelData)
    (hHD3 : M.d = 6 ∧ M.α = 2 ∧ ∃ C : ℝ, 0 < C ∧ ∀ x y : M.V, x ≠ y →
      M.twoPoint M.betaCrit x y ≤ C * (Real.log (M.S.ρ (toVec (x - y))))⁻¹ *
        (M.S.ρ (toVec (x - y))) ^ (-(M.d : ℝ) + 2))
    (hTri : TriTail.openTriangleSelf M.kernel M.kernel_nonneg M.betaCrit 0 < ⊤)
    {f' h : ℝ → ℝ} {c C r₀ : ℝ} (hc : 0 < c)
    (hlow : ∀ x : M.V, x ≠ 0 →
      c * (M.S.dist 0 x) ^ (-(M.d : ℝ) + M.α) ≤ M.twoPoint M.betaCrit 0 x)
    (hfin : ∀ᶠ r : ℝ in atTop, M.cutMassAt r 0 ≠ ⊤)
    (hr₀ : 0 < r₀)
    (hderiv : ∀ t, r₀ ≤ t →
      HasDerivAt (fun r => (M.cutMassAt r 0).toReal) (f' t) t)
    (hpos : ∀ t, r₀ ≤ t → 0 < (M.cutMassAt t 0).toReal)
    (hode : ∀ t, r₀ ≤ t →
      f' t = (M.betaCrit : ℝ) * (1 - h t) * t ^ (-M.α - 1) *
        ((M.cutMassAt t 0).toReal) ^ 2)
    (hmeas : Measurable h) (hhedge : ∀ t, r₀ ≤ t → |h t| ≤ C)
    (h0 : Tendsto h atTop (𝓝 0))
    (𝓔 : ℕ → Finset (Sym2 M.V)) (h𝓔mono : Monotone 𝓔)
    (h𝓔 : ∀ e : Sym2 M.V, ∃ n, e ∈ 𝓔 n) (p : ℕ) (hp : 3 ≤ p)
    {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hMa : ∀ (r : ℝ), 1 ≤ r → ∀ ℓ : ℕ, ℓ ≤ p →
      I420Case1.powMomentAt (M.cutProb r) (ℓ + 1) (0 : M.V) ≠ ⊤)
    {c3 : ℝ} (hc3 : 0 < c3)
    (hgm : ∀ᶠ r in atTop, c3 * momOf (fun r => M.cutProb r) (0 : M.V) 1 r ^ 3
      ≤ momOf (fun r => M.cutProb r) (0 : M.V) 2 r) :
    Tendsto (fun r => I420Case1.mixedExclR (M.cutProb r) (0 : M.V) 1 p
          (BallAverage.ball_finite M r).toFinset /
        (ballCard (fun r => (BallAverage.ball_finite M r).toFinset) r *
          (momOf (fun r => M.cutProb r) (0 : M.V) 1 r *
            momOf (fun r => M.cutProb r) (0 : M.V) p r))) atTop (𝓝 1) ∧
      ∀ ℓ, 1 ≤ ℓ → ℓ ≤ p - 2 → Tendsto
        (fun r => I420Case1.mixedExclR (M.cutProb r) (0 : M.V) (ℓ + 1) (p - ℓ)
            (BallAverage.ball_finite M r).toFinset /
          (ballCard (fun r => (BallAverage.ball_finite M r).toFinset) r *
            (momOf (fun r => M.cutProb r) (0 : M.V) (ℓ + 1) r *
              momOf (fun r => M.cutProb r) (0 : M.V) (p - ℓ) r))) atTop (𝓝 1) := by
  have hαd : M.α < (M.d : ℝ) := by
    rw [hHD3.1, hHD3.2.1]
    norm_num
  have hβ : (0 : ℝ) < M.betaCrit := by
    obtain ⟨x, hx⟩ := M.exists_ne_zero_vertex
    exact M.betaCrit_pos_of_twoPoint_lower hc hx (hlow x hx)
  exact case3_hAend_hAmid_cutPoly_source_of_HD_case3 M hHD3 hTri hc hαd hlow hfin hβ hr₀
    hderiv hpos hode hmeas hhedge h0 𝓔 h𝓔mono h𝓔 p hp hθ0 hθ1 hMa hc3 hgm

end PercLib.CriticalLRP.I420Case3

namespace PercLib.CriticalLRP.I420Case3

open PercLib.CriticalLRP Orchestration
open PercLib.CriticalLRP.VolumeMoments.HigherMoments

/-- **The cubic (I.4.19) upper moment bound from the Case-3 source inputs**, with `hRV2`
derived from the product-gap second-moment theorem and `hαd`, `hβ` derived internally. -/
theorem case3_moment_three_bound_of_source_p21 (M : SourceModelData)
    (hHD3 : M.d = 6 ∧ M.α = 2 ∧ ∃ C : ℝ, 0 < C ∧ ∀ x y : M.V, x ≠ y →
      M.twoPoint M.betaCrit x y ≤ C * (Real.log (M.S.ρ (toVec (x - y))))⁻¹ *
        (M.S.ρ (toVec (x - y))) ^ (-(M.d : ℝ) + 2))
    (hTri : TriTail.openTriangleSelf M.kernel M.kernel_nonneg M.betaCrit 0 < ⊤)
    {f' h : ℝ → ℝ} {c C r₀ : ℝ} (hc : 0 < c)
    (hlow : ∀ x : M.V, x ≠ 0 →
      c * (M.S.dist 0 x) ^ (-(M.d : ℝ) + M.α) ≤ M.twoPoint M.betaCrit 0 x)
    (hr₀ : 0 < r₀)
    (hderiv : ∀ t, r₀ ≤ t →
      HasDerivAt (fun r => (M.cutMassAt r 0).toReal) (f' t) t)
    (hpos : ∀ t, r₀ ≤ t → 0 < (M.cutMassAt t 0).toReal)
    (hode : ∀ t, r₀ ≤ t →
      f' t = (M.betaCrit : ℝ) * (1 - h t) * t ^ (-M.α - 1) *
        ((M.cutMassAt t 0).toReal) ^ 2)
    (hmeas : Measurable h) (hhedge : ∀ t, r₀ ≤ t → |h t| ≤ C)
    (h0 : Tendsto h atTop (𝓝 0))
    (𝓔 : ℕ → Finset (Sym2 M.V)) (h𝓔mono : Monotone 𝓔)
    (h𝓔 : ∀ e : Sym2 M.V, ∃ n, e ∈ 𝓔 n)
    {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hMa : ∀ (r : ℝ), 1 ≤ r → ∀ ℓ : ℕ, ℓ ≤ 3 →
      I420Case1.powMomentAt (M.cutProb r) (ℓ + 1) (0 : M.V) ≠ ⊤)
    {c3 : ℝ} (hc3 : 0 < c3)
    (hgm : ∀ᶠ r in atTop, c3 * momOf (fun r => M.cutProb r) (0 : M.V) 1 r ^ 3
      ≤ momOf (fun r => M.cutProb r) (0 : M.V) 2 r)
    (hac : ∀ R : ℝ, r₀ ≤ R → AbsolutelyContinuousOnInterval
      (fun r : ℝ => (M.cutMoment 2 r).toReal) r₀ R)
    (hae : ∀ᵐ t ∂(volume.restrict (Ici r₀)),
      HasDerivAt (fun r : ℝ => (M.cutMoment 2 r).toReal) (M.rhsScalarTwo t) t)
    (h1 : ∀ t : ℝ, r₀ ≤ t → M.cutMoment 1 t ≠ ⊤)
    (h2 : ∀ t : ℝ, r₀ ≤ t → M.cutMoment 2 t ≠ ⊤)
    (hP : Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal
      / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) atTop (𝓝 1))
    {C₀ pF : ℝ} (hC₀ : 0 ≤ C₀) (hpF : 1 < pF)
    (hF : Analysis.LogRadialBound (fun y : M.V => M.S.dist (0 : M.V) y)
      (fun y : M.V => TriTail.openTriangle M.kernel M.kernel_nonneg M.betaCrit 0 y) C₀ pF)
    (hmeasE2 : Measurable M.p2ExclError) (hmeasEbar : Measurable M.p2Ebar)
    (hlogH : Analysis.LogarithmicallyIntegrable M.p2H)
    (hlogE0 : Analysis.LogarithmicallyIntegrable (PivotFlux.cutE0 M))
    {cr : ℝ → ℝ} (hcr0 : ∀ r, 0 < r → 0 ≤ cr r)
    (hderivId : ∀ r : ℝ, 0 < r → HasDerivAt
      (fun s => momOf (fun s => M.cutProb s) (0 : M.V) 3 s)
      (cr r * ∑ ℓ ∈ Finset.range 3, ((Nat.choose 3 ℓ : ℕ) : ℝ) *
        I420Case1.mixedExclR (M.cutProb r) (0 : M.V) (ℓ + 1) (3 - ℓ)
          (BallAverage.ball_finite M r).toFinset) r)
    (hcnorm : ∀ ε > 0, ∀ᶠ r in atTop,
      cr r * I420Case3.ballCard (fun r =>
          (BallAverage.ball_finite M r).toFinset) r *
        momOf (fun r => M.cutProb r) (0 : M.V) 1 r * r ≤ (1 + ε) * M.α) :
    ∀ ε > 0, ∀ᶠ r in atTop,
      momOf (fun r => M.cutProb r) (0 : M.V) 3 r ≤
        (1 + ε) * mixedMoment 3 (fun m r =>
          momOf (fun r => M.cutProb r) (0 : M.V) m r) r := by
  have hαd : M.α < (M.d : ℝ) := by
    rw [hHD3.1, hHD3.2.1]
    norm_num
  have hβ : (0 : ℝ) < M.betaCrit := by
    obtain ⟨x, hx⟩ := M.exists_ne_zero_vertex
    exact M.betaCrit_pos_of_twoPoint_lower hc hx (hlow x hx)
  have hfin : ∀ᶠ r : ℝ in atTop, M.cutMassAt r 0 ≠ ⊤ :=
    M.eventually_cutMassAt_ne_top_of_hP hP
  have hgm' : ∀ᶠ r : ℝ in atTop,
      c3 * (M.cutMassAt r 0).toReal ^ 3 ≤ (M.cutMoment 2 r).toReal := by
    filter_upwards [hgm] with r hr
    simpa [momOf_cutProb_eq_toReal_cutMoment, SourceModelData.cutMassAt_zero_eq_cutMoment]
      using hr
  obtain ⟨A, hA0, hA⟩ := M.secondMoment_asymptotic_case3_of_source_p21 M.hα hr₀
    (M.betaCrit_ne_zero_of_hP hP) hac hae h1 h2 hP hTri hC₀ hpF hF hmeasE2 hmeasEbar
    hlogH hlogE0 hc3 hgm'
  have hRV2 : Analysis.RegularlyVaryingAtTop
      (fun r => momOf (fun r => M.cutProb r) (0 : M.V) 2 r) (3 * M.α) := by
    have hrv := Analysis.regularlyVaryingAtTop_of_tendsto_div_rpow hA0 hA
    simpa only [momOf_cutProb_eq_toReal_cutMoment] using hrv
  have hRV1 : Analysis.RegularlyVaryingAtTop
      (fun r => momOf (fun r => M.cutProb r) (0 : M.V) 1 r) M.α :=
    M.momOf_one_regularlyVarying M.hα (M.betaCrit_ne_zero_of_hP hP) hP
  have hmommeas1 : Measurable (fun r =>
      momOf (fun r => M.cutProb r) (0 : M.V) 1 r) := by
    simpa only [momOf_cutProb_eq_toReal_cutMoment] using M.measurable_cutMoment_toReal_of_monotone 1
  have hmommeas2 : Measurable (fun r =>
      momOf (fun r => M.cutProb r) (0 : M.V) 2 r) := by
    simpa only [momOf_cutProb_eq_toReal_cutMoment] using M.measurable_cutMoment_toReal_of_monotone 2
  exact case3_moment_three_bound_of_HD_case3 M hHD3 hTri hc hαd hlow hfin hβ hr₀ hderiv
    hpos hode hmeas hhedge h0 𝓔 h𝓔mono h𝓔 hθ0 hθ1 hMa hc3 hgm hmommeas1 hmommeas2 hRV1 hRV2
    hcr0 hderivId hcnorm

end PercLib.CriticalLRP.I420Case3

set_option linter.hashCommand false
set_option linter.style.longLine false

#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.betaCrit_ne_zero_of_hP
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.betaCrit_pos_of_ne_zero
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.kappa_pos_of_hP
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.kappa_pos_of_betaCrit_ne_zero
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.measurable_cutMoment_toReal_of_monotone
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.eventually_cutMassAt_ne_top_of_hP
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.twoPoint_zero_of_ne
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.exists_ne_zero_vertex
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.betaCrit_pos_of_twoPoint_lower
#print axioms PercLib.CriticalLRP.Analysis.regularlyVaryingAtTop_of_tendsto_div_rpow
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.secondMoment_asymptotic_case3_of_source_p21_paramFree
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.regularlyVarying_two_of_source_p21_paramFree
#print axioms PercLib.CriticalLRP.I420Case3.case3_moment_three_bound_of_HD_case3_paramFree
#print axioms PercLib.CriticalLRP.I420Case3.case3_hAend_hAmid_cutPoly_source_of_HD_case3_paramFree
#print axioms PercLib.CriticalLRP.I420Case3.case3_i421_cutPoly_source_of_HD_case3_paramFree
#print axioms PercLib.CriticalLRP.I420Case3.case3_moment_three_bound_of_source_p21
