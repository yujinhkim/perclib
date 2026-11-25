module

public import PercLib.CriticalLRP.Analysis.Cutoff.OffCorner.RadiusSummedFlux
public import PercLib.CriticalLRP.CylinderRusso
public import PercLib.CriticalLRP.RussoInf.Exchange

/-!
# Frozen-window continuity: cylinder (finite-edge) base case and the uniform-approximation transfer

The landed reduction `RadiusSummedFlux.continuousAt_exclScalar_iff_frozenWindow` identifies the
excluded-mass scalar at a positive off-corner radius `r₀` with the continuity at `r₀` of one
frozen-window moment in the cutoff law,

`r ↦ (∫⁻ ω, |K_0| ∑_{y ∈ B_{r₀}} 1(y ∉ K_0) |K_y| ∂(cutLaw r)).toReal`.

This file supplies the two pieces of that continuity which do not involve the moving window:

* **Cylinder base case.** For a finite edge set `S` and an observable `g` that depends only on the
  edges in `S`, the map `r ↦ ∫ ω, g (S.restrict ω) ∂(cutLaw r)` is continuous at every `r₀ > 0`.
  The proof is the cylinder formula `CylinderRusso.integral_edgeMeasure_cylinder` (the infinite
  product law restricted to `S` is the finite product of Bernoullis) together with continuity of
  the finite polynomial `expectation p X` in the open probabilities `p`, and
  `Continuity.continuousAt_cutProb` for `r ↦ (cutProb r e : ℝ)`.
* **Uniform-approximation transfer.** A real function which is uniformly approximated near `r₀`
  by functions continuous at `r₀` is continuous at `r₀` (`continuousAt_of_uniform_approx`), and
  the frozen-window moment is exactly of that shape once it is approximated by cylinder
  observables whose integrals agree with it to `ε` *uniformly in `r` near `r₀`
  (`continuousAt_toReal_lintegral_of_cylinder_approx`).

The passage from a pointwise cluster estimate to that uniform `ε`-closeness is **not** proved
here; it is the single remaining analytic input, stated as the explicit hypothesis `h` of
`continuousAt_toReal_lintegral_of_cylinder_approx` and of
`continuousAt_exclScalar_of_cylinderApprox`.  What *is* proved about it is the domination and the
moment it consumes: the frozen integrand is pointwise at most the `pairMass` integrand
(`frozenWindow_integrand_le_pairMass`), hence the frozen moment is finite at any radius at which
the *second* cutoff moment is finite (`frozenWindow_lintegral_ne_top`), while `pairMass` itself is
bounded by `|B_r| χ(r)² + connMass` (`E1Sign.pairMass_le`).  So the missing tail estimate is a
consequence of a finite second endpoint moment plus the shrinking of the escape sets
`SourceModelData.markEscape`; no annulus or moving-window estimate is involved.

The proofs use only the standard foundational axioms.
-/

set_option autoImplicit false
set_option linter.hashCommand false
set_option linter.style.longLine false
-- the cylinder lemma below carries `[DecidableEq V]` only to consume the finite-product
-- machinery of `CylinderRusso`; it is an implicit instance argument there, not a type-class
-- hypothesis visible in the statement.
set_option linter.unusedDecidableInType false

noncomputable section

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP.Orchestration

/-! ## 1. The uniform-approximation criterion -/

/-- **A function uniformly approximable near `r₀` by functions continuous at `r₀` is continuous
at `r₀`.**  The approximant may depend on `ε`, and only has to be `ε`-close on a
`δ`-neighbourhood of `r₀`; this is the shape produced by an `ε`-splitting argument over a
truncation parameter. -/
theorem continuousAt_of_uniform_approx {g : ℝ → ℝ} {r₀ : ℝ}
    (h : ∀ ε > 0, ∃ (h' : ℝ → ℝ) (δ : ℝ), 0 < δ ∧ ContinuousAt h' r₀ ∧
      ∀ r, |r - r₀| < δ → |g r - h' r| ≤ ε) :
    ContinuousAt g r₀ := by
  rw [Metric.continuousAt_iff]
  intro ε hε
  obtain ⟨h', δ, hδ, hcont, happ⟩ := h (ε / 3) (by linarith)
  rw [Metric.continuousAt_iff] at hcont
  obtain ⟨δ', hδ', hspec⟩ := hcont (ε / 3) (by linarith)
  refine ⟨min δ δ', lt_min hδ hδ', fun r hr => ?_⟩
  rw [Real.dist_eq] at hr ⊢
  have hrmem : |r - r₀| < δ := lt_of_lt_of_le hr (min_le_left δ δ')
  have h1 : |g r - h' r| ≤ ε / 3 := happ r hrmem
  have h2 : |h' r - h' r₀| < ε / 3 := by
    simpa only [Real.dist_eq] using hspec (show dist r r₀ < δ' by
      rw [Real.dist_eq]; exact lt_of_lt_of_le hr (min_le_right δ δ'))
  have h3 : |g r₀ - h' r₀| ≤ ε / 3 := happ r₀ (by rw [sub_self, abs_zero]; exact hδ)
  have h4 : |h' r₀ - g r₀| ≤ ε / 3 := by
    rw [abs_sub_comm]; exact h3
  calc |g r - g r₀|
      = |(g r - h' r) + (h' r - h' r₀) + (h' r₀ - g r₀)| := by ring_nf
    _ ≤ |g r - h' r| + |h' r - h' r₀| + |h' r₀ - g r₀| := abs_add_three _ _ _
    _ < ε := by linarith

end PercLib.CriticalLRP.Orchestration

namespace PercLib.CriticalLRP

/-! ## 2. The finite-Bernoulli expectation is continuous in the open probabilities -/

/-- The finite-configuration weight `configurationLaw` is continuous in the open probabilities. -/
theorem continuous_configurationLaw {E : Type*} [Fintype E] [DecidableEq E]
    (s : Configuration E) :
    Continuous fun p : E → ℝ => configurationLaw p s := by
  unfold configurationLaw
  refine continuous_finsetProd _ fun e _ => ?_
  by_cases he : e ∈ s
  · simpa [he] using (continuous_apply e : Continuous fun p : E → ℝ => p e)
  · have h : Continuous fun p : E → ℝ => (1 : ℝ) - p e :=
      continuous_const.sub (continuous_apply e)
    simpa [he, Pi.sub_apply] using h

/-- The finite-volume expectation `expectation p X` is continuous in the open probabilities `p`:
it is a finite sum of products of the coordinates. -/
theorem continuous_expectation {E : Type*} [Fintype E] [DecidableEq E]
    (X : Configuration E → ℝ) :
    Continuous fun p : E → ℝ => expectation p X := by
  unfold expectation
  refine continuous_finsetSum _ fun s _ => ?_
  exact (continuous_configurationLaw s).mul continuous_const

/-- Continuity of the same expectation along a radius, when every edge probability is continuous
in the radius. -/
theorem continuousAt_expectation {E : Type*} [Fintype E] [DecidableEq E]
    {p : ℝ → E → ℝ} {r₀ : ℝ} (hp : ∀ e, ContinuousAt (fun r => p r e) r₀)
    (X : Configuration E → ℝ) :
    ContinuousAt (fun r => expectation (p r) X) r₀ :=
  (continuous_expectation X).continuousAt.comp (continuousAt_pi.mpr hp)

/-! ## 3. Cylinder observables under the cutoff law: continuity in the cutoff radius -/

variable {V : Type*} [Countable V] [DecidableEq V]

/-- **Cylinder integrals are continuous in a continuously varying family of edge
probabilities.**  General form, for an arbitrary family `π : ℝ → Sym2 V → unitInterval` of open
probabilities. -/
theorem continuousAt_integral_edgeMeasure_cylinder
    (π : ℝ → Sym2 V → unitInterval) (S : Finset (Sym2 V)) (g : (↥S → Prop) → ℝ)
    {r₀ : ℝ} (hπ : ∀ e : Sym2 V, ContinuousAt (fun r => ((π r e : unitInterval) : ℝ)) r₀) :
    ContinuousAt (fun r => ∫ ω : Config V, g (S.restrict ω) ∂(edgeMeasure (π r))) r₀ := by
  have hEq : ∀ r : ℝ, (∫ ω : Config V, g (S.restrict ω) ∂(edgeMeasure (π r)))
      = expectation (fun e : ↥S => ((π r (e : Sym2 V) : unitInterval) : ℝ))
          (fun c => g (fun e => e ∈ c)) :=
    fun r => integral_edgeMeasure_cylinder (π r) S g
  simp only [hEq]
  exact continuousAt_expectation
    (p := fun r (e : ↥S) => ((π r (e : Sym2 V) : unitInterval) : ℝ))
    (fun e => hπ (e : Sym2 V)) _

end PercLib.CriticalLRP

namespace PercLib.CriticalLRP.Orchestration

namespace SourceModelData

variable (M : SourceModelData)

/-- **Cylinder observables are continuous in the cutoff radius at every `r₀ > 0`.**  The edge
probabilities `r ↦ (cutProb r e : ℝ)` are continuous (`Continuity.continuousAt_cutProb`), and a
cylinder observable has an expectation which is a finite polynomial in them. -/
theorem continuousAt_integral_cutLaw_cylinder (S : Finset (Sym2 M.V))
    (g : (↥S → Prop) → ℝ) {r₀ : ℝ} (hr₀ : 0 < r₀) :
    ContinuousAt (fun r => ∫ ω, g (S.restrict ω) ∂(M.cutLaw r)) r₀ := by
  have hlaw : ∀ r : ℝ, M.cutLaw r = PercLib.CriticalLRP.edgeMeasure (M.cutProb r) :=
    fun r => E1Sign.cutLaw_eq M r
  simp only [hlaw]
  exact continuousAt_integral_edgeMeasure_cylinder M.cutProb S g
    (fun e => M.continuousAt_cutProb r₀ hr₀ e)

/-! ## 4. The same statement for nonnegative ENNReal-valued cylinder integrands -/

/-- A nonnegative cylinder observable, written through `ENNReal.ofReal`, has a `toReal` moment
which is continuous in the cutoff radius.  The `toReal` is legitimate: the cylinder integrand
takes finitely many values and the cutoff law is a probability measure, so its `lintegral` is the
`ofReal` of an honest finite real integral. -/
theorem continuousAt_toReal_lintegral_cutLaw_cylinder (S : Finset (Sym2 M.V))
    (g : (↥S → Prop) → ℝ) (hg : 0 ≤ g) {r₀ : ℝ} (hr₀ : 0 < r₀) :
    ContinuousAt (fun r => (∫⁻ ω, ENNReal.ofReal (g (S.restrict ω)) ∂(M.cutLaw r)).toReal)
      r₀ := by
  have hcont := M.continuousAt_integral_cutLaw_cylinder S g hr₀
  have hEq : ∀ r : ℝ, (∫⁻ ω, ENNReal.ofReal (g (S.restrict ω)) ∂(M.cutLaw r)).toReal
      = ∫ ω, g (S.restrict ω) ∂(M.cutLaw r) := by
    intro r
    have hmeas : AEStronglyMeasurable (fun ω : Config M.V => g (S.restrict ω))
        (M.cutLaw r) :=
      ((measurable_of_finite g).comp (Finset.measurable_restrict S)).aestronglyMeasurable
    have hint : Integrable (fun ω : Config M.V => g (S.restrict ω)) (M.cutLaw r) := by
      refine Integrable.of_bound hmeas (∑ c : ↥S → Prop, |g c|) ?_
      refine Filter.Eventually.of_forall fun ω => ?_
      rw [Real.norm_eq_abs]
      exact Finset.single_le_sum (f := fun c : ↥S → Prop => |g c|)
        (fun c _ => abs_nonneg _) (Finset.mem_univ _)
    have hnn : 0 ≤ᵐ[M.cutLaw r] fun ω : Config M.V => g (S.restrict ω) :=
      Filter.Eventually.of_forall fun ω => hg _
    have hconv : ENNReal.ofReal (∫ ω : Config M.V, g (S.restrict ω) ∂(M.cutLaw r))
        = ∫⁻ ω, ENNReal.ofReal (g (S.restrict ω)) ∂(M.cutLaw r) :=
      ofReal_integral_eq_lintegral_ofReal hint hnn
    exact (congrArg ENNReal.toReal hconv).symm.trans
      (ENNReal.toReal_ofReal (integral_nonneg
        (f := fun ω : Config M.V => g (S.restrict ω)) fun ω => hg (S.restrict ω)))
  exact hcont.congr (Filter.Eventually.of_forall fun r => (hEq r).symm)

/-! ## 5. The uniform-approximation transfer for moments in the cutoff law -/

/-- **A moment in the cutoff law is continuous as soon as it is uniformly approximated near
`r₀` by cylinder moments.**  The cylinder moments are continuous at `r₀` by §4, so the whole
content is the `ε`-splitting: an approximation which is only valid at each fixed radius is *not*
enough, and this is where the two-sided tail estimate has to be spent. -/
theorem continuousAt_toReal_lintegral_of_cylinder_approx
    (F : Config M.V → ℝ≥0∞) {r₀ : ℝ} (hr₀ : 0 < r₀)
    (h : ∀ ε > 0, ∃ (S : Finset (Sym2 M.V)) (g : (↥S → Prop) → ℝ), 0 ≤ g ∧ ∃ δ > 0,
      ∀ r, |r - r₀| < δ →
        |(∫⁻ ω, F ω ∂(M.cutLaw r)).toReal
          - (∫⁻ ω, ENNReal.ofReal (g (S.restrict ω)) ∂(M.cutLaw r)).toReal| ≤ ε) :
    ContinuousAt (fun r => (∫⁻ ω, F ω ∂(M.cutLaw r)).toReal) r₀ :=
  continuousAt_of_uniform_approx fun ε hε => by
    obtain ⟨S, g, hg, δ, hδ, hspec⟩ := h ε hε
    exact ⟨fun r => (∫⁻ ω, ENNReal.ofReal (g (S.restrict ω)) ∂(M.cutLaw r)).toReal,
      δ, hδ, M.continuousAt_toReal_lintegral_cutLaw_cylinder S g hg hr₀, hspec⟩

/-! ## 6. The frozen-window moment of the excluded mass

The exact integrand of `RadiusSummedFlux.continuousAt_exclScalar_iff_frozenWindow`, with the
window frozen at `r₀`. -/

/-- **The frozen-window integrand is dominated by the `pairMass` integrand.**  Dropping the
excluded indicator can only increase the integrand. -/
theorem frozenWindow_integrand_le_pairMass (r₀ : ℝ) (ω : Config M.V) :
    clusterVol ω (0 : M.V) * ∑ y ∈ E1Sign.ballF M r₀,
        ((cluster ω (0 : M.V))ᶜ).indicator (fun _ => (1 : ℝ≥0∞)) y * clusterVol ω y
      ≤ clusterVol ω (0 : M.V) * ∑ y ∈ E1Sign.ballF M r₀, clusterVol ω y := by
  classical
  have hsum : (∑ y ∈ E1Sign.ballF M r₀,
        ((cluster ω (0 : M.V))ᶜ).indicator (fun _ => (1 : ℝ≥0∞)) y * clusterVol ω y)
      ≤ ∑ y ∈ E1Sign.ballF M r₀, clusterVol ω y := by
    refine Finset.sum_le_sum fun y _ => ?_
    rw [Set.indicator_apply]
    split_ifs with hy
    · simp
    · simp
  gcongr

/-- **The frozen-window moment is finite from the second cutoff moment.**  This is the finiteness
input the `toReal` in `continuousAt_exclScalar_iff_frozenWindow` needs, and it is *not* an
`ENNReal.toReal` identity: the frozen integrand is pointwise dominated by the `pairMass`
integrand on the frozen window, and `pairMass` is finite as soon as `cutMoment 2` is. -/
theorem frozenWindow_lintegral_ne_top {r₀ r : ℝ}
    (hB : E1Sign.ballF M r = E1Sign.ballF M r₀) (h2 : M.cutMoment 2 r ≠ ⊤) :
    (∫⁻ ω, clusterVol ω (0 : M.V) * ∑ y ∈ E1Sign.ballF M r₀,
        ((cluster ω (0 : M.V))ᶜ).indicator (fun _ => (1 : ℝ≥0∞)) y * clusterVol ω y
      ∂(M.cutLaw r)) ≠ ⊤ := by
  refine ne_top_of_le_ne_top ?_ (lintegral_mono (M.frozenWindow_integrand_le_pairMass r₀))
  have hpair : (∫⁻ ω, clusterVol ω (0 : M.V) * ∑ y ∈ E1Sign.ballF M r₀,
        clusterVol ω y ∂(M.cutLaw r)) = E1Sign.pairMass M r := by
    rw [E1Sign.pairMass, hB]
  rw [hpair]
  exact E1Sign.pairMass_ne_top M r h2

/-! ### The escape tail of the frozen-window moment

The first half of the missing uniform tail estimate: the frozen-window moment sitting on the event
that the cluster of the origin leaves the lattice ball of radius `n` tends to `0`.  This is the
vanishing of a fixed integrable function on a decreasing family of sets whose intersection is
null (`tendsto_setLIntegral_toReal_of_antitone`), the finiteness being supplied by the second
cutoff moment through `frozenWindow_lintegral_ne_top`. -/

/-- **The frozen-window moment of the escape event vanishes.**  The event is
`{ω | ∃ x ∉ B_n, Connects ω 0 x}`; its intersection over `n` is contained in
`{clusterVol ω 0 = ⊤}`, which is null because the first cutoff moment is finite. -/
theorem tendsto_frozenWindow_escape {r₀ r : ℝ}
    (hB : E1Sign.ballF M r = E1Sign.ballF M r₀) (h2 : M.cutMoment 2 r ≠ ⊤) :
    Tendsto (fun n : ℕ => (∫⁻ ω in {ω : Config M.V | ∃ x : M.V,
        x ∉ M.ball (n : ℝ) ∧ Connects ω (0 : M.V) x},
        clusterVol ω (0 : M.V) * ∑ y ∈ E1Sign.ballF M r₀,
          ((cluster ω (0 : M.V))ᶜ).indicator (fun _ => (1 : ℝ≥0∞)) y * clusterVol ω y
        ∂(M.cutLaw r)).toReal) atTop (𝓝 0) := by
  classical
  have hFmeas : Measurable fun ω : Config M.V => clusterVol ω (0 : M.V) *
      ∑ y ∈ E1Sign.ballF M r₀,
        ((cluster ω (0 : M.V))ᶜ).indicator (fun _ => (1 : ℝ≥0∞)) y * clusterVol ω y :=
    (measurable_clusterVol (0 : M.V)).mul (Finset.measurable_sum _ fun y _ =>
      (Measurable.indicator measurable_const (measurableSet_cluster_mem (0 : M.V) y).compl).mul
        (measurable_clusterVol y))
  have hfin : (∫⁻ ω, clusterVol ω (0 : M.V) * ∑ y ∈ E1Sign.ballF M r₀,
      ((cluster ω (0 : M.V))ᶜ).indicator (fun _ => (1 : ℝ≥0∞)) y * clusterVol ω y
      ∂(M.cutLaw r)) ≠ ⊤ := M.frozenWindow_lintegral_ne_top hB h2
  have hsetmeas : ∀ n : ℕ, MeasurableSet {ω : Config M.V | ∃ x : M.V,
      x ∉ M.ball (n : ℝ) ∧ Connects ω (0 : M.V) x} := by
    intro n
    have hset : {ω : Config M.V | ∃ x : M.V, x ∉ M.ball (n : ℝ) ∧ Connects ω (0 : M.V) x}
        = ⋃ (x : M.V), ⋃ (_ : x ∉ M.ball (n : ℝ)),
            {ω : Config M.V | Connects ω (0 : M.V) x} := by
      ext ω
      simp only [Set.mem_iUnion]
      exact ⟨fun ⟨x, hx, hc⟩ => ⟨x, hx, hc⟩, fun ⟨x, hx, hc⟩ => ⟨x, hx, hc⟩⟩
    rw [hset]
    exact MeasurableSet.iUnion fun x => MeasurableSet.iUnion fun _ =>
      measurableSet_cluster_mem (0 : M.V) x
  have hanti : Antitone fun n : ℕ => {ω : Config M.V | ∃ x : M.V,
      x ∉ M.ball (n : ℝ) ∧ Connects ω (0 : M.V) x} := by
    intro n m hnm ω hω
    obtain ⟨x, hx, hc⟩ := hω
    exact ⟨x, fun hmem => hx (PercLib.CriticalLRP.BallAverage.ball_mono M
      (by exact_mod_cast hnm) hmem), hc⟩
  have hnull : (M.cutLaw r) {ω : Config M.V | clusterVol ω (0 : M.V) = ⊤} = 0 := by
    have h1 : (∫⁻ ω, clusterVol ω (0 : M.V) ∂(M.cutLaw r)) ≠ ⊤ := by
      have h := M.cutMoment_one_ne_top_of_two h2
      simpa [SourceModelData.cutMoment] using h
    refine measure_eq_zero_iff_ae_notMem.mpr ?_
    filter_upwards [ae_lt_top (measurable_clusterVol (0 : M.V)) h1] with ω hω hmem
    exact absurd hmem (ne_of_lt hω)
  have hinter : (M.cutLaw r) (⋂ n : ℕ, {ω : Config M.V | ∃ x : M.V,
      x ∉ M.ball (n : ℝ) ∧ Connects ω (0 : M.V) x}) = 0 := by
    refine measure_mono_null ?_ hnull
    intro ω hω
    have hinf : (cluster ω (0 : M.V)).Infinite := by
      intro hfin
      obtain ⟨N, hN⟩ := M.exists_ball_subset_of_finite hfin
      obtain ⟨x, hx, hconn⟩ := Set.mem_iInter.mp hω N
      exact hx (hN (mem_cluster_iff.mpr hconn))
    change clusterVol ω (0 : M.V) = ⊤
    simpa only [InInfiniteCluster] using (inInfiniteCluster_iff ω (0 : M.V)).mpr hinf
  exact PercLib.CriticalLRP.tendsto_setLIntegral_toReal_of_antitone hFmeas hfin
    hsetmeas hanti hinter

/-- **Continuity of the excluded-mass scalar from a uniform cylinder approximation of the frozen
window moment.**  This deletes the frozen-window hypothesis of
`RadiusSummedFlux.hGcont_of_frozenWindow` in favour of the explicit approximation datum `h`; the
derivation of `h` from the cluster escapes is *not* carried out here. -/
theorem continuousAt_exclScalar_of_cylinderApprox {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hoff : r₀ ∉ M.attainedRadii)
    (h : ∀ ε > 0, ∃ (S : Finset (Sym2 M.V)) (g : (↥S → Prop) → ℝ), 0 ≤ g ∧ ∃ δ > 0,
      ∀ r, |r - r₀| < δ →
        |(∫⁻ ω, clusterVol ω (0 : M.V) * ∑ y ∈ E1Sign.ballF M r₀,
            ((cluster ω (0 : M.V))ᶜ).indicator (fun _ => (1 : ℝ≥0∞)) y * clusterVol ω y
              ∂(M.cutLaw r)).toReal
          - (∫⁻ ω, ENNReal.ofReal (g (S.restrict ω)) ∂(M.cutLaw r)).toReal| ≤ ε) :
    ContinuousAt M.exclScalar r₀ :=
  (M.continuousAt_exclScalar_iff_frozenWindow hr₀ hoff).mpr
    (M.continuousAt_toReal_lintegral_of_cylinder_approx _ hr₀ h)

/-! ## 7. The endpoint derivative theorem with the frozen-window premise replaced -/

/-- `hGcont` in its consumed shape, with the frozen-window continuity supplied by the explicit
cylinder-approximation datum rather than assumed. -/
theorem hGcont_of_cylinderApprox {α β : ℝ} (hα0 : 0 < α)
    (h2β : M.cutMoment 2 β ≠ ⊤) (hoff : ∀ r ∈ Set.Ioo α β, r ∉ M.cornerRadii)
    (hK : ∀ r ∈ Set.Ioo α β, ContinuousAt (fun r' => deriv M.K r') r)
    (hcyl : ∀ r ∈ Set.Ioo α β, ∀ ε > 0,
      ∃ (S : Finset (Sym2 M.V)) (g : (↥S → Prop) → ℝ), 0 ≤ g ∧ ∃ δ > 0,
      ∀ s, |s - r| < δ →
        |(∫⁻ ω, clusterVol ω (0 : M.V) * ∑ y ∈ E1Sign.ballF M r,
            ((cluster ω (0 : M.V))ᶜ).indicator (fun _ => (1 : ℝ≥0∞)) y * clusterVol ω y
              ∂(M.cutLaw s)).toReal
          - (∫⁻ ω, ENNReal.ofReal (g (S.restrict ω)) ∂(M.cutLaw s)).toReal| ≤ ε) :
    ∀ r ∈ Set.Ioo α β, ContinuousAt (fun r' => ∑' y : M.V,
      sMomentInfFlux (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv r') r :=
  M.hGcont_of_scalar_continuity hα0 h2β hoff hK fun r hr =>
    M.continuousAt_exclScalar_of_cylinderApprox (hα0.trans hr.1)
      (by rw [M.attainedRadii_eq_cornerRadii]; exact hoff r hr) (hcyl r hr)

/-- **The off-corner endpoint derivative of the cutoff mass**, with the opaque frozen-window
continuity premise of `RadiusSummedFlux.hasDerivAt_cutMassReal_rhsScalar_of_endpoint_of_envelope_of_frozenWindow`
replaced by the explicit cylinder-approximation datum.  Every remaining hypothesis is visible: the
window, the moment, the per-vertex continuity and the approximation itself. -/
theorem hasDerivAt_cutMassReal_rhsScalar_of_endpoint_of_envelope_of_cylinderApprox
    (T : ℕ → Finset M.V) (hTmono : Monotone T) (hT : ∀ y : M.V, ∃ n, y ∈ T n)
    (S : ℕ → Finset (Sym2 M.V)) (hSmono : Monotone S) (hS : ∀ e : Sym2 M.V, ∃ n, e ∈ S n)
    {α β r0 C : ℝ} (hα0 : 0 < α) (hαr0 : α < r0) (hr0β : r0 < β)
    (hoff : ∀ r ∈ Set.Ioo α β, r ∉ M.cornerRadii)
    (hKd : ∀ r ∈ Set.Ioo α β, DifferentiableAt ℝ M.K r)
    (h2β : M.cutMoment 2 β ≠ ⊤)
    (hC0 : 0 ≤ C) (hCb : ∀ r ∈ Set.Ioo α β, -(deriv M.K r) ≤ C)
    (hKβ : deriv M.K β < 0)
    (hcontinf : ∀ y : M.V, ∀ r ∈ Set.Ioo α β, ContinuousAt
      (sMomentInfFlux (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv) r)
    (hK : ∀ r ∈ Set.Ioo α β, ContinuousAt (fun r' => deriv M.K r') r)
    (hcyl : ∀ r ∈ Set.Ioo α β, ∀ ε > 0,
      ∃ (S' : Finset (Sym2 M.V)) (g : (↥S' → Prop) → ℝ), 0 ≤ g ∧ ∃ δ > 0,
      ∀ s, |s - r| < δ →
        |(∫⁻ ω, clusterVol ω (0 : M.V) * ∑ y ∈ E1Sign.ballF M r,
            ((cluster ω (0 : M.V))ᶜ).indicator (fun _ => (1 : ℝ≥0∞)) y * clusterVol ω y
              ∂(M.cutLaw s)).toReal
          - (∫⁻ ω, ENNReal.ofReal (g (S'.restrict ω)) ∂(M.cutLaw s)).toReal| ≤ ε) :
    HasDerivAt M.cutMassReal (M.rhsScalar r0) r0 :=
  M.hasDerivAt_cutMassReal_rhsScalar_of_endpoint_of_envelope_of_scalar T hTmono hT S hSmono hS
    hα0 hαr0 hr0β hoff hKd h2β hC0 hCb hKβ hcontinf hK fun r hr =>
      M.continuousAt_exclScalar_of_cylinderApprox (hα0.trans hr.1)
        (by rw [M.attainedRadii_eq_cornerRadii]; exact hoff r hr) (hcyl r hr)

/-- **Window functionals `cutFun` are continuous in the cutoff radius.**  `cutFun S g` is a
cylinder observable (`RussoInf.Exchange.cutFun_eq_restrict`), so this is
`continuousAt_integral_cutLaw_cylinder` in the vocabulary of the infinite-volume Russo tower
(`RussoInf/Exchange`).  This is the form in which the finite-window expectations of that tower
carry their `r`-dependence. -/
theorem continuousAt_integral_cutFun_cutLaw (S : Finset (Sym2 M.V)) (g : Config M.V → ℝ)
    {r₀ : ℝ} (hr₀ : 0 < r₀) :
    ContinuousAt (fun r => ∫ ω, PercLib.CriticalLRP.cutFun S g ω ∂(M.cutLaw r)) r₀ := by
  obtain ⟨G, -, hG⟩ := PercLib.CriticalLRP.cutFun_eq_restrict S g
  have hEq : ∀ r : ℝ, (∫ ω, PercLib.CriticalLRP.cutFun S g ω ∂(M.cutLaw r))
      = ∫ ω, G (S.restrict ω) ∂(M.cutLaw r) := fun r =>
    integral_congr_ae (Filter.Eventually.of_forall fun ω => hG ω)
  exact (M.continuousAt_integral_cutLaw_cylinder S G hr₀).congr
    (Filter.Eventually.of_forall fun r => (hEq r).symm)

end SourceModelData

end PercLib.CriticalLRP.Orchestration

/-! ## Axiom audit -/

open PercLib.CriticalLRP.Orchestration.SourceModelData

#print axioms PercLib.CriticalLRP.Orchestration.continuousAt_of_uniform_approx
#print axioms PercLib.CriticalLRP.continuous_configurationLaw
#print axioms PercLib.CriticalLRP.continuous_expectation
#print axioms PercLib.CriticalLRP.continuousAt_expectation
#print axioms PercLib.CriticalLRP.continuousAt_integral_edgeMeasure_cylinder
#print axioms continuousAt_integral_cutLaw_cylinder
#print axioms continuousAt_toReal_lintegral_cutLaw_cylinder
#print axioms continuousAt_toReal_lintegral_of_cylinder_approx
#print axioms frozenWindow_integrand_le_pairMass
#print axioms frozenWindow_lintegral_ne_top
#print axioms tendsto_frozenWindow_escape
#print axioms continuousAt_exclScalar_of_cylinderApprox
#print axioms continuousAt_integral_cutFun_cutLaw
#print axioms hGcont_of_cylinderApprox
#print axioms hasDerivAt_cutMassReal_rhsScalar_of_endpoint_of_envelope_of_cylinderApprox
