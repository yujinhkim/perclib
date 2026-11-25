/-
# Sum-before-differentiate: the `y`-interchange for the cut-mass flux without a per-vertex majorant

Accepted from swarm `smwtvrwnn`, member `m4`, direction D1B.

The campaign's route to the off-corner derivative of the cut mass `χ(r) = M.cutMassReal r`
(`Analysis/Cutoff/Deriv.lean`) writes `χ = ∑_y T_r(0,y)` and differentiates the `y`-series
termwise.  That needs a *single* `u : V → ℝ` with `|flux_y r| ≤ u y` for **every** radius `r` in a
window and `∑_y u y < ∞` (`hasDerivAt_cutMassReal_of_summableMajorant`), and no such `u` is known:
the only bound the existing machinery gives is `|flux_y r| ≤ 2·1·D_r·E_r|K_0|`
(`sMomentWeight_le_of_sharpness` with `A = {y}`, `q = 1`), which is the same number for every `y`
and hence not summable in `y`.

This file takes the opposite order.  Instead of differentiating the `y`-series, it **integrates in
`r` first** and then passes to the `y`-limit by monotone convergence:

* `lintegral_iSup_ofReal_eq_ofReal_of_tendsto_intervalIntegral` (pure Mathlib): if `f'_n ≥ 0` are
  pointwise increasing on `Ioc a b`, interval integrable, and their interval integrals converge to
  `I`, then the `ℝ≥0∞`-integral of the pointwise supremum of `ofReal (f'_n)` is `ofReal I`.
* `lintegral_tsum_sMomentInfFlux_eq_ofReal_sub` (model level): on a window `I` that meets no corner
  radius, the `ℝ≥0∞`-integral over `Ioc a b` of the **`y`-sum of the per-vertex pivotal fluxes**
  equals `ofReal (χ b - χ a)`.

No radius-uniform summable majorant `u`, no summability of the `y`-series at any radius, and no
statement about the size of `χ'` enters: the exact identity is the monotone limit of the
*finite-`A`* fundamental theorem of calculus, whose derivative form is the already-landed
`hasDerivAt_finset_sum_cutTwoPoint`.

What is *not* proved (see the closing section): the pointwise derivative `HasDerivAt χ (∑'_y flux_y)`
needs in addition that the `y`-sum of fluxes is *continuous* at the radius, or summable there; both
are strictly weaker than the radius-uniform majorant but neither is derived here.
-/
module

public import PercLib.CriticalLRP.Analysis.Cutoff.Deriv

/-!
An alternate cutoff-mass Russo interchange: integrate in the radius before taking the vertex
limit, avoiding the old radius-uniform summable per-vertex majorant.
-/

@[expose] public section

noncomputable section

set_option linter.style.longLine false

open MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP.Orchestration

/-! ## 1. The monotone-convergence engine -/

/-- **Monotone convergence for interval integrals, in `ℝ≥0∞` form.**

For a family `f' : ℕ → ℝ → ℝ` that is nonnegative and pointwise increasing on `Ioc a b`, each
member interval integrable, whose interval integrals tend to `I`, the `ℝ≥0∞`-integral of the
pointwise supremum of `ENNReal.ofReal (f' n)` is `ENNReal.ofReal I`.

No domination of `f'` by an integrable function is used: this *is* the monotone convergence
theorem, and the finiteness is recovered at the end from the finiteness of `I`. -/
theorem lintegral_iSup_ofReal_eq_ofReal_of_tendsto_intervalIntegral
    {f' : ℕ → ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) {I : ℝ}
    (hint : ∀ n, IntervalIntegrable (f' n) volume a b)
    (hnn : ∀ n, ∀ x ∈ Set.Ioc a b, 0 ≤ f' n x)
    (hmono : ∀ x ∈ Set.Ioc a b, Monotone fun n => f' n x)
    (hconv : Tendsto (fun n => ∫ x in a..b, f' n x) atTop (𝓝 I)) :
    ∫⁻ x in Set.Ioc a b, (⨆ n, ENNReal.ofReal (f' n x)) = ENNReal.ofReal I := by
  have hmeas : ∀ n, AEMeasurable (fun x => ENNReal.ofReal (f' n x))
      (volume.restrict (Set.Ioc a b)) := fun n =>
    ((hint n).1.aestronglyMeasurable.aemeasurable).ennreal_ofReal
  have heq : ∀ n, ∫⁻ x in Set.Ioc a b, ENNReal.ofReal (f' n x)
      = ENNReal.ofReal (∫ x in a..b, f' n x) := by
    intro n
    have hnn' : ∀ᵐ x ∂(volume.restrict (Set.Ioc a b)), 0 ≤ f' n x := by
      rw [ae_restrict_iff' measurableSet_Ioc]
      exact Eventually.of_forall fun x hx => hnn n x hx
    have h := ofReal_integral_eq_lintegral_ofReal (μ := volume.restrict (Set.Ioc a b))
      (f := f' n) (hint n).1 hnn'
    rw [← h, ← intervalIntegral.integral_of_le hab]
  have h1 : Tendsto (fun n => ∫⁻ x in Set.Ioc a b, ENNReal.ofReal (f' n x)) atTop
      (𝓝 (∫⁻ x in Set.Ioc a b, (⨆ n, ENNReal.ofReal (f' n x)))) := by
    refine lintegral_tendsto_of_tendsto_of_monotone hmeas ?_ ?_
    · rw [ae_restrict_iff' measurableSet_Ioc]
      exact Eventually.of_forall fun x hx n m hnm => ENNReal.ofReal_le_ofReal (hmono x hx hnm)
    · rw [ae_restrict_iff' measurableSet_Ioc]
      exact Eventually.of_forall fun x hx =>
        tendsto_atTop_iSup fun n m hnm => ENNReal.ofReal_le_ofReal (hmono x hx hnm)
  have h2 : Tendsto (fun n => ∫⁻ x in Set.Ioc a b, ENNReal.ofReal (f' n x)) atTop
      (𝓝 (ENNReal.ofReal I)) := by
    have hc : Tendsto (fun n => ENNReal.ofReal (∫ x in a..b, f' n x)) atTop
        (𝓝 (ENNReal.ofReal I)) := ENNReal.continuous_ofReal.tendsto I |> fun h => h.comp hconv
    simpa only [heq] using hc
  exact tendsto_nhds_unique h1 h2

end PercLib.CriticalLRP.Orchestration

namespace PercLib.CriticalLRP.Orchestration

namespace SourceModelData

variable (M : SourceModelData)

/-! ## 2. The `y`-interchange for the integrated flux -/

/-- **The integrated `y`-interchange for the cut-mass flux.**

Let `I` be an open window of radii meeting **no corner radius** (`r ∉ M.cornerRadii`), let
`T : ℕ → Finset M.V` be a monotone exhaustion of the vertex set, and let `S` be an edge
exhaustion.  Assume

* the per-edge domination and the per-vertex parameter regularity of the existing off-corner
  two-point derivative (`hdom`, `hboundint`, `hmeasK`, `hmeasinf`, `hcontinf`, literally those of
  `hasDerivAt_finset_sum_cutTwoPoint`),
* finiteness of the cut-off first moment on `Icc a b` (`hfin`),
* interval integrability in `r` of every single-vertex flux (`hfluxint`) and its nonnegativity on
  `Ioc a b` (`hfluxnn`).

Then the `ℝ≥0∞`-integral over `Ioc a b` of the whole `y`-series of per-vertex fluxes equals
`ENNReal.ofReal (χ b - χ a)`.

The proof is monotone convergence applied to the finite-`A` identity
`∫ r in a..b, ∑_{y∈T N} flux_y r = ∑_{y∈T N} T_b(0,y) - ∑_{y∈T N} T_a(0,y)`
(=`hasDerivAt_finset_sum_cutTwoPoint` plus the fundamental theorem of calculus), followed by the
identification of the `y`-series with the supremum of its finite partial sums on the exhaustion. -/
theorem lintegral_tsum_sMomentInfFlux_eq_ofReal_sub
    (T : ℕ → Finset M.V) (hTmono : Monotone T) (hT : ∀ y : M.V, ∃ n, y ∈ T n)
    (S : ℕ → Finset (Sym2 M.V)) (hSmono : Monotone S) (hS : ∀ e : Sym2 M.V, ∃ n, e ∈ S n)
    {I : Set ℝ} (hI : IsOpen I) {a b : ℝ} (hab : a ≤ b) (hsub : Set.uIcc a b ⊆ I)
    (hoff : ∀ r ∈ I, r ∉ M.cornerRadii)
    (hKd : ∀ r ∈ I, DifferentiableAt ℝ M.K r)
    (hdom : ∀ r ∈ I, Summable fun e : Sym2 M.V =>
      |M.cutEdgeDeriv r e| * (2 * (M.cutLaw r).real {ω : Config M.V | e ∈ touchSet ω (0 : M.V)}))
    (hboundint : ∀ y : M.V, ∀ a' ∈ I, ∀ b' ∈ I, IntervalIntegrable
      (sMomentWeight (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv) volume a' b')
    (hmeasK : ∀ y : M.V, ∀ k : ℕ, AEStronglyMeasurable (windowFluxOf (0 : M.V)
      (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) {y}) S M.cutProb M.cutEdgeDeriv k) volume)
    (hmeasinf : ∀ y : M.V, ∀ r ∈ I, StronglyMeasurableAtFilter
      (sMomentInfFlux (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv) (𝓝 r) volume)
    (hcontinf : ∀ y : M.V, ∀ r ∈ I, ContinuousAt
      (sMomentInfFlux (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv) r)
    (hfin : ∀ r ∈ Set.uIcc a b, M.cutMassAt r 0 ≠ ⊤)
    (hfluxint : ∀ y : M.V, IntervalIntegrable (fun r =>
      sMomentInfFlux (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv r) volume a b)
    (hfluxnn : ∀ y : M.V, ∀ r ∈ Set.Ioc a b, 0 ≤
      sMomentInfFlux (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv r) :
    ∫⁻ r in Set.Ioc a b, (∑' y : M.V, ENNReal.ofReal
        (sMomentInfFlux (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv r))
      = ENNReal.ofReal (M.cutMassReal b - M.cutMassReal a) := by
  classical
  -- the exhaustion is cofinal for finite vertex sets
  have hTfin : ∀ s : Finset M.V, ∃ n, s ⊆ T n := by
    intro s
    induction s using Finset.induction with
    | empty => exact ⟨0, Finset.empty_subset _⟩
    | insert y s _ ih =>
      obtain ⟨n₁, h₁⟩ := hT y
      obtain ⟨n₂, h₂⟩ := ih
      refine ⟨max n₁ n₂, ?_⟩
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hTmono (le_max_left _ _) h₁
      · exact hTmono (le_max_right _ _) (h₂ hx)
  have htendT : Tendsto T atTop atTop := tendsto_atTop_atTop.mpr fun s => by
    obtain ⟨n, hn⟩ := hTfin s
    exact ⟨n, fun m hm => hn.trans (hTmono hm)⟩
  have hsum_int : ∀ A : Finset M.V, IntervalIntegrable (fun r => ∑ y ∈ A,
      sMomentInfFlux (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv r) volume a b := by
    intro A
    have h := IntervalIntegrable.sum A (f := fun y r =>
      sMomentInfFlux (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv r)
      (fun y _ => hfluxint y)
    have hfun : (∑ i ∈ A, (fun r =>
        sMomentInfFlux (0 : M.V) {i} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv r))
        = fun r => ∑ i ∈ A,
            sMomentInfFlux (0 : M.V) {i} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv r := by
      funext r
      rw [Finset.sum_apply]
    rw [hfun] at h
    exact h
  -- the finite-`A` fundamental theorem of calculus
  have hIdN : ∀ N : ℕ, ∫ r in a..b,
      (∑ y ∈ T N, sMomentInfFlux (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv r)
      = (∑ y ∈ T N, M.cutTwoPoint b 0 y) - (∑ y ∈ T N, M.cutTwoPoint a 0 y) := by
    intro N
    have hderiv : ∀ r ∈ Set.uIcc a b, HasDerivAt
        (fun r' => ∑ y ∈ T N, M.cutTwoPoint r' 0 y)
        (∑ y ∈ T N, sMomentInfFlux (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv r) r :=
      fun r hr => M.hasDerivAt_finset_sum_cutTwoPoint (T N) S hSmono hS hI (hsub hr)
        (fun r' hr' => hoff r' hr') (fun r' hr' => hKd r' hr') (fun r' hr' => hdom r' hr')
        (fun y a' ha' b' hb' => hboundint y a' ha' b' hb') (fun y k => hmeasK y k)
        (fun y => hmeasinf y r (hsub hr)) (fun y => hcontinf y r (hsub hr))
    have hint : IntervalIntegrable
        (fun r => ∑ y ∈ T N, sMomentInfFlux (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv r)
        volume a b :=
      hsum_int (T N)
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  -- the two endpoint limits
  have hlim : ∀ r : ℝ, r ∈ Set.uIcc a b →
      Tendsto (fun N => ∑ y ∈ T N, M.cutTwoPoint r 0 y) atTop (𝓝 (M.cutMassReal r)) := by
    intro r hr
    have hsumm := M.summable_cutTwoPoint_of_finite (hfin r hr)
    have h := hsumm.hasSum.comp htendT
    rw [← M.cutMassReal_eq_tsum_cutTwoPoint (hfin r hr)] at h
    exact h
  have hconv : Tendsto (fun N => ∫ r in a..b,
      (∑ y ∈ T N, sMomentInfFlux (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv r))
      atTop (𝓝 (M.cutMassReal b - M.cutMassReal a)) := by
    have hsub' : Tendsto (fun N => (∑ y ∈ T N, M.cutTwoPoint b 0 y) - (∑ y ∈ T N, M.cutTwoPoint a 0 y))
        atTop (𝓝 (M.cutMassReal b - M.cutMassReal a)) :=
      (hlim b Set.right_mem_uIcc).sub (hlim a Set.left_mem_uIcc)
    simpa only [hIdN] using hsub'
  -- monotone convergence
  have hmain := lintegral_iSup_ofReal_eq_ofReal_of_tendsto_intervalIntegral (f' := fun N r =>
      ∑ y ∈ T N, sMomentInfFlux (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv r)
    hab (fun N => hsum_int (T N))
    (fun N x hx => Finset.sum_nonneg fun y _ => hfluxnn y x hx)
    (fun x hx => monotone_nat_of_le_succ fun N => by
      refine Finset.sum_le_sum_of_subset_of_nonneg (hTmono (Nat.le_succ N)) ?_
      intro y _ _
      exact hfluxnn y x hx)
    hconv
  -- identify the supremum with the `y`-series
  have hstep : ∀ r ∈ Set.Ioc a b, (⨆ N, ENNReal.ofReal (∑ y ∈ T N,
      sMomentInfFlux (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv r))
      = ∑' y : M.V, ENNReal.ofReal
          (sMomentInfFlux (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv r) := by
    intro r hr
    have h1 : ∀ N, ENNReal.ofReal (∑ y ∈ T N,
        sMomentInfFlux (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv r)
        = ∑ y ∈ T N, ENNReal.ofReal
            (sMomentInfFlux (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv r) :=
      fun N => ENNReal.ofReal_sum_of_nonneg (fun y _ => hfluxnn y r hr)
    simp only [h1]
    rw [ENNReal.tsum_eq_iSup_sum]
    refine le_antisymm (iSup_le fun N => le_iSup (fun s : Finset M.V => ∑ y ∈ s,
      ENNReal.ofReal (sMomentInfFlux (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv r))
      (T N)) (iSup_le fun s => ?_)
    obtain ⟨N, hNs⟩ := hTfin s
    exact le_iSup_of_le N (Finset.sum_le_sum_of_subset_of_nonneg hNs fun y _ _ => zero_le)
  have hfin' : ∫⁻ r in Set.Ioc a b, (⨆ N, ENNReal.ofReal (∑ y ∈ T N,
      sMomentInfFlux (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv r))
      = ∫⁻ r in Set.Ioc a b, (∑' y : M.V, ENNReal.ofReal
          (sMomentInfFlux (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv r)) := by
    refine lintegral_congr_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    exact hstep r hr
  rw [← hfin']
  exact hmain


/-- **The infinite pivotal flux is dominated by the total pivotal weight**, pointwise in the
parameter.

This is the per-vertex domination `|sMomentInfFlux o A q π c r| ≤ sMomentWeight o A q π c r`: it
turns interval integrability of the pivotal weight (`hboundint`) into interval integrability of each
single-vertex flux (the hypothesis `hfluxint`/`hfluxintW` of the theorems below), and it is *also*
the precise reason why the dominant of the per-`y` flux cannot be summable in `y`: at `A = {y}`,
`q = 1` the right-hand side is `2 D_r E_r|K_o|`, independent of `y`. -/
theorem abs_sMomentInfFlux_le (o : M.V) (A : Finset M.V) (q : M.V → ℝ) {r : ℝ}
    (hdom : Summable fun e : Sym2 M.V => |M.cutEdgeDeriv r e| *
      (2 * max (∑ x ∈ A, |q x|) 0 * (M.cutLaw r).real {ω : Config M.V | e ∈ touchSet ω o})) :
    |sMomentInfFlux o A q M.cutProb M.cutEdgeDeriv r|
      ≤ sMomentWeight o A q M.cutProb M.cutEdgeDeriv r := by
  classical
  have hterm : ∀ e : Sym2 M.V, |M.cutEdgeDeriv r e *
      pivotalFlux (edgeMeasure (M.cutProb r)) (sMomentTrunc q o A) e|
      ≤ |M.cutEdgeDeriv r e| * (2 * max (∑ x ∈ A, |q x|) 0 *
          (M.cutLaw r).real {ω : Config M.V | e ∈ touchSet ω o}) := by
    intro e
    rw [abs_mul]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    exact abs_pivotalFlux_le (o := o) (edgeMeasure (M.cutProb r)) (le_max_right _ _)
      (fun ω => (abs_sMomentTrunc_le q o A ω).trans (le_max_left _ _))
      (measurable_sMomentTrunc q o A) (sMomentTrunc_dep q o A) e
  have habs : Summable fun e : Sym2 M.V => |M.cutEdgeDeriv r e *
      pivotalFlux (edgeMeasure (M.cutProb r)) (sMomentTrunc q o A) e| :=
    hdom.of_nonneg_of_le (fun e => abs_nonneg _) hterm
  calc |sMomentInfFlux o A q M.cutProb M.cutEdgeDeriv r|
      = ‖∑' e : Sym2 M.V, M.cutEdgeDeriv r e *
          pivotalFlux (edgeMeasure (M.cutProb r)) (sMomentTrunc q o A) e‖ := by
        rw [sMomentInfFlux, infFluxOf, Real.norm_eq_abs]
    _ ≤ ∑' e : Sym2 M.V, ‖M.cutEdgeDeriv r e *
          pivotalFlux (edgeMeasure (M.cutProb r)) (sMomentTrunc q o A) e‖ :=
        norm_tsum_le_tsum_norm habs
    _ = ∑' e : Sym2 M.V, |M.cutEdgeDeriv r e *
          pivotalFlux (edgeMeasure (M.cutProb r)) (sMomentTrunc q o A) e| :=
        tsum_congr fun e => Real.norm_eq_abs _
    _ ≤ ∑' e : Sym2 M.V, |M.cutEdgeDeriv r e| * (2 * max (∑ x ∈ A, |q x|) 0 *
          (M.cutLaw r).real {ω : Config M.V | e ∈ touchSet ω o}) :=
        Summable.tsum_le_tsum hterm habs hdom
    _ = sMomentWeight o A q M.cutProb M.cutEdgeDeriv r := rfl

/-- **Real-valued form: the cut mass is the integral of its `y`-summed flux.**

With the hypotheses of `lintegral_tsum_sMomentInfFlux_eq_ofReal_sub` plus

* `ha0 : 0 < a` (so that `χ` is monotone on `[a,b]` and `χ b - χ a ≥ 0`),
* `hsummable` — pointwise summability in `y` of the per-vertex fluxes (this is the *only* new
  input, and it is pointwise in `r`: no uniformity in `r`, no summable majorant),

the exact fundamental-theorem-of-calculus identity holds in real arithmetic:
`∫ r in a..b, ∑'_y flux_y r = χ b - χ a`.

Measurability of the summed flux is *derived* here from the per-vertex continuity `hcontinf`, so it
is not an extra hypothesis. -/
theorem intervalIntegral_tsum_sMomentInfFlux_eq_sub
    (T : ℕ → Finset M.V) (hTmono : Monotone T) (hT : ∀ y : M.V, ∃ n, y ∈ T n)
    (S : ℕ → Finset (Sym2 M.V)) (hSmono : Monotone S) (hS : ∀ e : Sym2 M.V, ∃ n, e ∈ S n)
    {I : Set ℝ} (hI : IsOpen I) {a b : ℝ} (hab : a ≤ b) (hsub : Set.uIcc a b ⊆ I)
    (ha0 : 0 < a)
    (hoff : ∀ r ∈ I, r ∉ M.cornerRadii)
    (hKd : ∀ r ∈ I, DifferentiableAt ℝ M.K r)
    (hdom : ∀ r ∈ I, Summable fun e : Sym2 M.V =>
      |M.cutEdgeDeriv r e| * (2 * (M.cutLaw r).real {ω : Config M.V | e ∈ touchSet ω (0 : M.V)}))
    (hboundint : ∀ y : M.V, ∀ a' ∈ I, ∀ b' ∈ I, IntervalIntegrable
      (sMomentWeight (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv) volume a' b')
    (hmeasK : ∀ y : M.V, ∀ k : ℕ, AEStronglyMeasurable (windowFluxOf (0 : M.V)
      (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) {y}) S M.cutProb M.cutEdgeDeriv k) volume)
    (hmeasinf : ∀ y : M.V, ∀ r ∈ I, StronglyMeasurableAtFilter
      (sMomentInfFlux (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv) (𝓝 r) volume)
    (hcontinf : ∀ y : M.V, ∀ r ∈ I, ContinuousAt
      (sMomentInfFlux (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv) r)
    (hfin : ∀ r ∈ Set.uIcc a b, M.cutMassAt r 0 ≠ ⊤)
    (hfluxint : ∀ y : M.V, IntervalIntegrable (fun r =>
      sMomentInfFlux (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv r) volume a b)
    (hfluxnn : ∀ y : M.V, ∀ r ∈ Set.Ioc a b, 0 ≤
      sMomentInfFlux (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv r)
    (hsummable : ∀ r ∈ Set.Ioc a b, Summable fun y : M.V =>
      sMomentInfFlux (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv r) :
    ∫ r in a..b, (∑' y : M.V,
        sMomentInfFlux (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv r)
      = M.cutMassReal b - M.cutMassReal a := by
  classical
  have hLin := M.lintegral_tsum_sMomentInfFlux_eq_ofReal_sub T hTmono hT S hSmono hS hI hab hsub
    hoff hKd hdom hboundint hmeasK hmeasinf hcontinf hfin hfluxint hfluxnn
  have hstep : ∀ r ∈ Set.Ioc a b, ENNReal.ofReal (∑' y : M.V,
        sMomentInfFlux (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv r)
      = ∑' y : M.V, ENNReal.ofReal
        (sMomentInfFlux (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv r) :=
    fun r hr => ENNReal.ofReal_tsum_of_nonneg (fun y => hfluxnn y r hr) (hsummable r hr)
  have hcongr : ∫⁻ r in Set.Ioc a b, ENNReal.ofReal ((∑' y : M.V,
        sMomentInfFlux (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv r))
      = ENNReal.ofReal (M.cutMassReal b - M.cutMassReal a) := by
    rw [← hLin]
    refine lintegral_congr_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    exact hstep r hr
  have hnonneg : ∀ᵐ r ∂(volume.restrict (Set.Ioc a b)), 0 ≤ (∑' y : M.V,
      sMomentInfFlux (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv r) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    exact tsum_nonneg fun y => hfluxnn y r hr
  have hmeas : AEStronglyMeasurable (fun r => ∑' y : M.V,
      sMomentInfFlux (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv r)
      (volume.restrict (Set.Ioc a b)) := by
    refine AEStronglyMeasurable.tsum fun y => ?_
    have hcontI : ContinuousOn (fun r =>
        sMomentInfFlux (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv r) I :=
      fun r hr => (hcontinf y r hr).continuousWithinAt
    exact (hcontI.mono fun r hr => hsub (Set.Icc_subset_uIcc (Set.Ioc_subset_Icc_self hr)))
      |>.aestronglyMeasurable measurableSet_Ioc
  have hmono : M.cutMassReal a ≤ M.cutMassReal b :=
    M.cutMassReal_le_of_le ha0 hab (hfin b Set.right_mem_uIcc)
  calc ∫ r in a..b, (∑' y : M.V,
        sMomentInfFlux (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv r)
      = ∫ r, (∑' y : M.V,
          sMomentInfFlux (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv r)
          ∂(volume.restrict (Set.Ioc a b)) := by
        rw [intervalIntegral.integral_of_le hab]
    _ = (∫⁻ r in Set.Ioc a b, ENNReal.ofReal ((∑' y : M.V,
          sMomentInfFlux (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv r))).toReal := by
        rw [integral_eq_lintegral_of_nonneg_ae hnonneg hmeas]
    _ = (ENNReal.ofReal (M.cutMassReal b - M.cutMassReal a)).toReal := by rw [hcongr]
    _ = M.cutMassReal b - M.cutMassReal a := ENNReal.toReal_ofReal (sub_nonneg.mpr hmono)

/-- **Pointwise off-corner derivative of the cut mass from continuity of the summed flux.**

The hypotheses are those of `intervalIntegral_tsum_sMomentInfFlux_eq_sub`, taken on an explicit open
window `Ioo α β` containing `r0` (so that `0 < α` gives positivity and the window is
interval-convex), together with

* `hsummable` — pointwise-in-`r` summability of the per-vertex fluxes on the window,
* `hGcont` — **continuity on the window of the summed flux** `G r = ∑'_y flux_y r`,
* `hfluxintW` — interval integrability of each single-vertex flux on every subinterval.

Note what is *not* assumed: no majorant `u : V → ℝ` with `|flux_y r| ≤ u y` uniform in `r` and
`∑_y u y < ∞`, no differentiability of `χ` at any radius, and no growth bound on `χ'`.  This is
exactly the residual shape that replaces the radius-uniform per-vertex majorant: a statement about
the *sum*, locally in `r`, at one radius at a time.

The proof composes the integrated identity with the fundamental theorem of calculus for the
integral function `r ↦ ∫_{r0}^r G`: on `Ioo α β` we have `χ r - χ r0 = ∫_{r0}^r G r' dr'`, and the
integral function has derivative `G r0` at `r0` because `G` is continuous there. -/
theorem hasDerivAt_cutMassReal_tsum_sMomentInfFlux
    (T : ℕ → Finset M.V) (hTmono : Monotone T) (hT : ∀ y : M.V, ∃ n, y ∈ T n)
    (S : ℕ → Finset (Sym2 M.V)) (hSmono : Monotone S) (hS : ∀ e : Sym2 M.V, ∃ n, e ∈ S n)
    {α β r0 : ℝ} (hα0 : 0 < α) (hαr0 : α < r0) (hr0β : r0 < β)
    (hoff : ∀ r ∈ Set.Ioo α β, r ∉ M.cornerRadii)
    (hKd : ∀ r ∈ Set.Ioo α β, DifferentiableAt ℝ M.K r)
    (hdom : ∀ r ∈ Set.Ioo α β, Summable fun e : Sym2 M.V =>
      |M.cutEdgeDeriv r e| * (2 * (M.cutLaw r).real {ω : Config M.V | e ∈ touchSet ω (0 : M.V)}))
    (hboundint : ∀ y : M.V, ∀ a' ∈ Set.Ioo α β, ∀ b' ∈ Set.Ioo α β, IntervalIntegrable
      (sMomentWeight (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv) volume a' b')
    (hmeasK : ∀ y : M.V, ∀ k : ℕ, AEStronglyMeasurable (windowFluxOf (0 : M.V)
      (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) {y}) S M.cutProb M.cutEdgeDeriv k) volume)
    (hmeasinf : ∀ y : M.V, ∀ r ∈ Set.Ioo α β, StronglyMeasurableAtFilter
      (sMomentInfFlux (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv) (𝓝 r) volume)
    (hcontinf : ∀ y : M.V, ∀ r ∈ Set.Ioo α β, ContinuousAt
      (sMomentInfFlux (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv) r)
    (hfin : ∀ r ∈ Set.Ioo α β, M.cutMassAt r 0 ≠ ⊤)
    (hfluxnn : ∀ y : M.V, ∀ r ∈ Set.Ioo α β, 0 ≤
      sMomentInfFlux (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv r)
    (hsummable : ∀ r ∈ Set.Ioo α β, Summable fun y : M.V =>
      sMomentInfFlux (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv r)
    (hfluxintW : ∀ y : M.V, ∀ a' ∈ Set.Ioo α β, ∀ b' ∈ Set.Ioo α β, IntervalIntegrable (fun r =>
      sMomentInfFlux (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv r) volume a' b')
    (hGcont : ∀ r ∈ Set.Ioo α β, ContinuousAt (fun r' => ∑' y : M.V,
      sMomentInfFlux (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv r') r) :
    HasDerivAt M.cutMassReal (∑' y : M.V,
      sMomentInfFlux (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv r0) r0 := by
  classical
  have hconv : ∀ a ∈ Set.Ioo α β, ∀ b ∈ Set.Ioo α β, Set.uIcc a b ⊆ Set.Ioo α β := by
    intro a ha b hb t ht
    rw [Set.mem_uIcc] at ht
    rcases ht with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨lt_of_lt_of_le ha.1 h1, lt_of_le_of_lt h2 hb.2⟩
    · exact ⟨lt_of_lt_of_le hb.1 h1, lt_of_le_of_lt h2 ha.2⟩
  have hId : ∀ a ∈ Set.Ioo α β, ∀ b ∈ Set.Ioo α β, a ≤ b →
      ∫ r in a..b, (∑' y : M.V,
        sMomentInfFlux (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv r)
        = M.cutMassReal b - M.cutMassReal a := by
    intro a ha b hb hab
    have hsubab := hconv a ha b hb
    have hIoc : Set.Ioc a b ⊆ Set.Ioo α β := fun r hr =>
      hsubab (Set.Icc_subset_uIcc (Set.Ioc_subset_Icc_self hr))
    exact M.intervalIntegral_tsum_sMomentInfFlux_eq_sub (I := Set.Ioo α β)
      T hTmono hT S hSmono hS isOpen_Ioo hab hsubab (lt_trans hα0 ha.1)
      hoff hKd hdom (fun y a' ha' b' hb' => hboundint y a' ha' b' hb') hmeasK hmeasinf hcontinf
      (fun r hr => hfin r (hsubab hr)) (fun y => hfluxintW y a ha b hb)
      (fun y r hr => hfluxnn y r (hIoc hr)) (fun r hr => hsummable r (hIoc hr))
  have hr0 : r0 ∈ Set.Ioo α β := ⟨hαr0, hr0β⟩
  -- the integrated identity as an eventual equality at `r0`
  have heq : (fun r => ∫ x in r0..r, (∑' y : M.V,
        sMomentInfFlux (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv x))
      =ᶠ[𝓝 r0] fun r => M.cutMassReal r - M.cutMassReal r0 := by
    filter_upwards [isOpen_Ioo.mem_nhds hr0] with r hr
    rcases lt_trichotomy r r0 with hlt | heq0 | hgt
    · have h1 := hId r hr r0 hr0 hlt.le
      rw [intervalIntegral.integral_symm]
      linarith
    · subst heq0
      rw [intervalIntegral.integral_same, sub_self]
    · have h1 := hId r0 hr0 r hr hgt.le
      linarith
  have hderiv : HasDerivAt (fun r => ∫ x in r0..r, (∑' y : M.V,
      sMomentInfFlux (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv x))
      (∑' y : M.V,
        sMomentInfFlux (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv r0) r0 :=
    intervalIntegral.integral_hasDerivAt_right (by simp [IntervalIntegrable])
      (ContinuousAt.stronglyMeasurableAtFilter (s := Set.Ioo α β) isOpen_Ioo hGcont r0 hr0)
      (hGcont r0 hr0)
  have h2 : HasDerivAt (fun r => M.cutMassReal r - M.cutMassReal r0)
      (∑' y : M.V,
        sMomentInfFlux (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv r0) r0 :=
    hderiv.congr_of_eventuallyEq heq.symm
  have h3 := h2.add_const (M.cutMassReal r0)
  simpa only [sub_add_cancel] using h3

end SourceModelData

end PercLib.CriticalLRP.Orchestration

/-! ## Axiom audit

Every declaration of this file is checked to depend only on `propext`, `Classical.choice` and
`Quot.sound`; no `sorry`, `admit`, `native_decide` or custom axiom is used anywhere above. -/

set_option linter.hashCommand false

#print axioms PercLib.CriticalLRP.Orchestration.lintegral_iSup_ofReal_eq_ofReal_of_tendsto_intervalIntegral
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.abs_sMomentInfFlux_le
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.lintegral_tsum_sMomentInfFlux_eq_ofReal_sub
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.intervalIntegral_tsum_sMomentInfFlux_eq_sub
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.hasDerivAt_cutMassReal_tsum_sMomentInfFlux
