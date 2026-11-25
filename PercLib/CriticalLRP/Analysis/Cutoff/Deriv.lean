/-
Candidate packet for swarm `smwttizjk`, member `m8`, direction D1A
(infinite-volume off-corner mass derivative).

Content: the `r`-derivative of the *actual* source cut-off edge probability
`q_e(r) = 1 - exp(-β_c J_r(e))` at a radius not in `M.cornerRadii`, for the model's own norm
`M.S.ρ` and with the source's own slope `deriv M.K r` (no constant-slope restriction), together
with the induced derivative of every finite-window cut-law expectation.

Nothing here asserts differentiability of the infinite-volume cut mass; that is the residual
obligation of D1A and is stated at the end as an explicit hypothesis.
-/
module

public import PercLib.CriticalLRP.RussoInf.CutoffFlux
public import PercLib.CriticalLRP.Analysis.Cutoff.Deriv.Defs
public import PercLib.CriticalLRP.CutoffRusso
public import PercLib.CriticalLRP.RussoInf.SpatialDominated
public import PercLib.CriticalLRP.Analysis.Cutoff.IntervalAC.Defs
public import PercLib.CriticalLRP.Analysis.Cutoff.LocalAC.Interface
public import PercLib.CriticalLRP.Analysis.Cutoff.CornerRadii
public import PercLib.CriticalLRP.Analysis.Cutoff.Continuity

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP.Orchestration

namespace SourceModelData

variable (M : SourceModelData)

@[simp] theorem cutEdgeDeriv_mk (r : ℝ) (x y : M.V) :
    M.cutEdgeDeriv r s(x, y) =
      (if x = y then 0 else
        (if M.S.dist x y ≤ r then
          (M.betaCrit : ℝ) * (-(deriv M.K r)) *
            Real.exp (-((M.betaCrit : ℝ) *
              FiniteVolume.cutoffProfile M.K r (M.S.dist x y)))
         else 0)) := rfl

/-- The cut-off edge probability of the actual model, written as `1 - exp(-β_c J_r(e))`. -/
theorem cutProb_coe_eq (r : ℝ) (e : Sym2 M.V) :
    ((M.cutProb r e : unitInterval) : ℝ)
      = 1 - Real.exp (-((M.betaCrit : ℝ) * M.cutKernel r e)) :=
  bernoulliEdgeProb_coe _ _ _ e

/-- The kernel value of a non-loop edge is the cut-off profile of its `M.S.dist` length, and the
kernel value of a loop edge is `0`. -/
theorem cutKernel_mk (r : ℝ) (x y : M.V) :
    M.cutKernel r s(x, y) =
      (if x = y then 0 else
        FiniteVolume.cutoffProfile M.K r (M.S.dist x y)) :=
  radialSym_mk M.S (FiniteVolume.cutoffProfile M.K r) x y

/-- **The `r`-derivative of the source cut-off edge probability, off the corner set.**

At a radius `r` at which `M.K` is differentiable and which is not realised as `M.S.dist x y` for
distinct `x y`, the edge probability `r' ↦ q_e(r')` of every edge is differentiable, with the
weight `M.cutEdgeDeriv r e` of the Russo formula.

The `ℓ^∞`-only restriction of the existing `RussoInf` instantiation is absent: the length is
`M.S.dist`, an arbitrary normalised norm, and the slope is the source's `deriv M.K r`. -/
theorem hasDerivAt_cutProb_off {r : ℝ} (hoff : r ∉ M.cornerRadii)
    (hKd : DifferentiableAt ℝ M.K r) (e : Sym2 M.V) :
    HasDerivAt (fun r' => ((M.cutProb r' e : unitInterval) : ℝ)) (M.cutEdgeDeriv r e) r := by
  induction e using Sym2.ind with
  | h x y =>
    rw [M.cutEdgeDeriv_mk]
    by_cases hxy : x = y
    · -- loop edge: the kernel value is `0` for every radius, so the probability is constant `0`
      subst hxy
      rw [ite_eq_left rfl]
      have hzero : ∀ r' : ℝ, ((M.cutProb r' s(x, x) : unitInterval) : ℝ) = 0 := by
        intro r'
        rw [M.cutProb_coe_eq, M.cutKernel_mk, ite_eq_left rfl]
        simp
      rw [show (fun r' => ((M.cutProb r' s(x, x) : unitInterval) : ℝ)) = fun _ => (0 : ℝ) from
        funext hzero]
      exact hasDerivAt_const (x := r) (c := (0 : ℝ))
    · -- genuine edge: apply the general one-dimensional computation
      rw [ite_eq_right hxy]
      have hne : M.S.dist x y ≠ r := fun h => hoff ⟨x, y, hxy, h⟩
      have hfun : (fun r' => ((M.cutProb r' s(x, y) : unitInterval) : ℝ))
          = fun r' => longRangeEdgeProbability (M.betaCrit : ℝ)
              (FiniteVolume.cutoffProfile M.K r' (M.S.dist x y)) := by
        funext r'
        rw [M.cutProb_coe_eq, M.cutKernel_mk, ite_eq_right hxy]
        rfl
      rw [hfun]
      exact FiniteVolume.hasDerivAt_cutoffEdgeProbability_if (K := M.K)
        (K' := -(deriv M.K r)) (r := r) (s := M.S.dist x y) hne
        (by simpa using hKd.hasDerivAt) (β := (M.betaCrit : ℝ))


/-- The off-corner derivative of the source cut-off edge probability, with differentiability of
`M.K` at the radius obtained from the model's own `K_diff` field (valid on `Ioi 0`). -/
theorem hasDerivAt_cutProb_off_of_pos {r : ℝ} (hr : 0 < r) (hoff : r ∉ M.cornerRadii)
    (e : Sym2 M.V) :
    HasDerivAt (fun r' => ((M.cutProb r' e : unitInterval) : ℝ)) (M.cutEdgeDeriv r e) r :=
  M.hasDerivAt_cutProb_off hoff (M.K_diff.differentiableAt (isOpen_Ioi.mem_nhds hr)) e

/-- The cut-off law is the independent edge law of the cut-off edge probabilities (definitional). -/
theorem cutLaw_eq_edgeMeasure (r : ℝ) : M.cutLaw r = edgeMeasure (M.cutProb r) := rfl

/-- **Finite-window Russo identity at the actual model.**

For every finite edge set `S` and every functional `g` of the configuration, the expectation of
`g` under the window-restricted cut-off law is differentiable in the radius at every off-corner
radius at which `M.K` is differentiable, with derivative the finite pivotal sum.

This is unconditional: no moment, domination or convergence hypothesis enters, because the window
is finite. The edge derivative is `M.hasDerivAt_cutProb_off`, i.e. the model's own `deriv M.K r`
and the model's own norm `M.S.ρ`. -/
theorem hasDerivAt_integral_cutFun_cutLaw (S : Finset (Sym2 M.V)) (g : Config M.V → ℝ)
    {r : ℝ} (hoff : r ∉ M.cornerRadii) (hKd : DifferentiableAt ℝ M.K r) :
    HasDerivAt (fun r' => ∫ ω, cutFun S g ω ∂(M.cutLaw r'))
      (∑ e ∈ S, M.cutEdgeDeriv r e * pivotalFlux (M.cutLaw r) (cutFun S g) e) r := by
  have hgen := hasDerivAt_integral_cutFun (V := M.V) (πt := M.cutProb)
    (π' := M.cutEdgeDeriv r) S g (fun e => M.hasDerivAt_cutProb_off hoff hKd e)
  have hfun : (fun r' => ∫ ω : Config M.V, cutFun S g ω ∂(edgeMeasure (M.cutProb r')))
      = fun r' => ∫ ω : Config M.V, cutFun S g ω ∂(M.cutLaw r') := by
    funext r'
    rw [M.cutLaw_eq_edgeMeasure]
  rw [hfun] at hgen
  refine hgen.congr_deriv ?_
  rw [← M.cutLaw_eq_edgeMeasure r,
    Finset.sum_coe_sort S (fun e => M.cutEdgeDeriv r e *
      pivotalFlux (M.cutLaw r) (cutFun S g) e)]

/-- The truncated spatial moment at a singleton set with unit weight is the cluster indicator. -/
theorem sMomentTrunc_singleton (y : M.V) (ω : Config M.V) :
    sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) {y} ω
      = (cluster ω (0 : M.V)).indicator (fun _ => (1 : ℝ)) y := by
  rw [sMomentTrunc, Finset.sum_singleton]

/-- **The cut-off two-point function is the expectation of the truncated spatial moment** at the
singleton `{y}` with unit weight. -/
theorem integral_sMomentTrunc_singleton (r : ℝ) (y : M.V) :
    ∫ ω, sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) {y} ω ∂(M.cutLaw r)
      = M.cutTwoPoint r 0 y := by
  have hpt : ∀ ω : Config M.V, sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) {y} ω
      = {ω' : Config M.V | y ∈ cluster ω' (0 : M.V)}.indicator (1 : Config M.V → ℝ) ω := by
    intro ω
    rw [sMomentTrunc_singleton]
    by_cases h : y ∈ cluster ω (0 : M.V)
    · have h' : ω ∈ {ω' : Config M.V | y ∈ cluster ω' (0 : M.V)} := h
      rw [Set.indicator_of_mem h, Set.indicator_of_mem h']
      rfl
    · have h' : ω ∉ {ω' : Config M.V | y ∈ cluster ω' (0 : M.V)} := h
      rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h']
  rw [show (fun ω => sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) {y} ω)
      = {ω' : Config M.V | y ∈ cluster ω' (0 : M.V)}.indicator (1 : Config M.V → ℝ) from
    funext hpt]
  rw [integral_indicator_one (measurableSet_cluster_mem (0 : M.V) y)]
  have hset : {ω : Config M.V | y ∈ cluster ω (0 : M.V)}
      = {ω : Config M.V | Connects ω (0 : M.V) y} := by
    ext ω
    exact mem_cluster_iff
  rw [hset]
  rfl

end SourceModelData

end PercLib.CriticalLRP.Orchestration

namespace PercLib.CriticalLRP.Orchestration

namespace SourceModelData

variable (M : SourceModelData)

/-- **Off-corner derivative of a source two-point function.**

At an off-corner radius `r0` at which `M.K` is differentiable, the two-point function
`r ↦ M.cutTwoPoint r 0 y` of the actual model is differentiable with derivative the infinite
pivotal flux of the cluster indicator `1{y ∈ K_0}`, i.e.
`∑'_e c_{r0}(e) · pivot_{r0}(1{y ∈ K_0}) e` with `c = M.cutEdgeDeriv`.

Hypotheses retained explicitly (all model-level, none involving a finite-window derivative):

* `hdeg` — the per-vertex mass bound `D` of the derivative weights (the paper's `β|J'|(2⌈r⌉₊+1)^d`
  for the `ℓ^∞` model; here an arbitrary function `D` of the radius),
* `hvol` — finiteness of the cut-off first moment on the parameter window,
* `hboundint` — interval integrability in `r` of the total pivotal weight,
* `hmeasK`, `hmeasinf`, `hcontinf` — parameter measurability/continuity of the window fluxes and of
  the limiting flux.

The conclusion is a *pointwise* derivative of a source object; it is the `y`-th summand of the
cut-mass derivative assembled in `hasDerivAt_cutMassReal_of_summableMajorant`. -/
theorem hasDerivAt_cutTwoPoint_off (y : M.V) (S : ℕ → Finset (Sym2 M.V))
    (hSmono : Monotone S) (hS : ∀ e : Sym2 M.V, ∃ n, e ∈ S n)
    {I : Set ℝ} (hI : IsOpen I) {r0 : ℝ} (hr0 : r0 ∈ I)
    (hoff : ∀ r ∈ I, r ∉ M.cornerRadii)
    (hKd : ∀ r ∈ I, DifferentiableAt ℝ M.K r)
    (hdom : ∀ r ∈ I, Summable fun e : Sym2 M.V =>
      |M.cutEdgeDeriv r e| * (2 * (M.cutLaw r).real {ω : Config M.V | e ∈ touchSet ω (0 : M.V)}))
    (hboundint : ∀ a ∈ I, ∀ b ∈ I, IntervalIntegrable
      (sMomentWeight (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv) volume a b)
    (hmeasK : ∀ k, AEStronglyMeasurable (windowFluxOf (0 : M.V)
      (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) {y}) S M.cutProb M.cutEdgeDeriv k) volume)
    (hmeasinf : StronglyMeasurableAtFilter
      (sMomentInfFlux (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv) (𝓝 r0) volume)
    (hcontinf : ContinuousAt
      (sMomentInfFlux (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv) r0) :
    HasDerivAt (fun r => M.cutTwoPoint r 0 y)
      (sMomentInfFlux (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv r0) r0 := by
  have hmain := hasDerivAt_integral_sMomentTrunc_of_dominated (V := M.V)
    (o := (0 : M.V)) (A := {y}) (q := fun _ => (1 : ℝ)) (S := S) hSmono hS
    (π := M.cutProb) (c := M.cutEdgeDeriv) hI hr0
    (fun e r hr => M.hasDerivAt_cutProb_off (hoff r hr) (hKd r hr) e)
    (fun r hr => by
      have h := hdom r hr
      rw [M.cutLaw_eq_edgeMeasure r] at h
      simpa [Finset.sum_singleton] using h)
    hboundint hmeasK hmeasinf hcontinf
  have hfun : (fun r => ∫ ω : Config M.V,
        sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) {y} ω ∂(edgeMeasure (M.cutProb r)))
      = fun r => M.cutTwoPoint r 0 y := by
    funext r
    rw [← M.cutLaw_eq_edgeMeasure r, M.integral_sMomentTrunc_singleton]
  rw [hfun] at hmain
  exact hmain

/-- Summability of the two-point function over the vertex set, from finiteness of the cut-off
first moment. -/
theorem summable_cutTwoPoint_of_finite {r : ℝ} (hfin : M.cutMassAt r 0 ≠ ⊤) :
    Summable fun y : M.V => M.cutTwoPoint r 0 y := by
  have hsum := tsum_ofReal_cutTwoPoint_eq_cutMoment M r
  have hne : ∑' y : M.V, ENNReal.ofReal (M.cutTwoPoint r 0 y) ≠ ⊤ := by
    rw [hsum]; rw [← cutMassAt_zero_eq_cutMoment]; exact hfin
  have h := ENNReal.summable_toReal hne
  refine h.congr fun y => ?_
  exact ENNReal.toReal_ofReal (cutTwoPoint_nonneg M r 0 y)

/-- **The cut mass is the sum of the two-point functions**, in real arithmetic, as soon as the
cut-off first moment is finite. -/
theorem cutMassReal_eq_tsum_cutTwoPoint {r : ℝ} (hfin : M.cutMassAt r 0 ≠ ⊤) :
    M.cutMassReal r = ∑' y : M.V, M.cutTwoPoint r 0 y := by
  have hsum := tsum_ofReal_cutTwoPoint_eq_cutMoment M r
  have hsumm : Summable fun y : M.V => M.cutTwoPoint r 0 y :=
    M.summable_cutTwoPoint_of_finite hfin
  have hof : M.cutMassAt r 0
      = ENNReal.ofReal (∑' y : M.V, M.cutTwoPoint r 0 y) := by
    rw [cutMassAt_zero_eq_cutMoment, ← hsum,
      ENNReal.ofReal_tsum_of_nonneg (fun y => cutTwoPoint_nonneg M r 0 y) hsumm]
  rw [cutMassReal, hof, ENNReal.toReal_ofReal (tsum_nonneg fun y => cutTwoPoint_nonneg M r 0 y)]

end SourceModelData

end PercLib.CriticalLRP.Orchestration

namespace PercLib.CriticalLRP.Orchestration

namespace SourceModelData

variable (M : SourceModelData)

/-- **Off-corner derivative of the cut mass, from a summable-in-`y` majorant.**

The cut mass `χ(r) = M.cutMassReal r = (M.cutMassAt r 0).toReal` is the sum over `y` of the
two-point functions `M.cutTwoPoint r 0 y` (as soon as the cut-off first moment is finite).  Each
summand is differentiable off the corner set with derivative the infinite pivotal flux of the
cluster indicator (`M.hasDerivAt_cutTwoPoint_off`).  If the pivotal fluxes admit a single
majorant `u : V → ℝ` which is summable **and uniform in the radius**, Mathlib's
`hasDerivAt_tsum_of_isPreconnected` lets the `y`-sum be differentiated termwise.

The residual premise isolated here is exactly `hub`: a summable-in-`y`, locally-uniform-in-`r`
bound on the per-`y` pivotal flux `∑'_e |c_r(e)| · 2 P_r(e ∈ touchSet · 0)`.  It is *not*
available from the pinned total pivotal mass `2 D E_r|K_0|` of `sMomentWeight_le_of_sharpness`,
which is a bound on the sum over `y` and not on each `y` separately; obtaining it is the
remaining mass-transport/interchange obstruction of D1A. -/
theorem hasDerivAt_cutMassReal_of_summableMajorant
    (S : ℕ → Finset (Sym2 M.V)) (hSmono : Monotone S) (hS : ∀ e : Sym2 M.V, ∃ n, e ∈ S n)
    {a b : ℝ} {r0 : ℝ} (hr0 : r0 ∈ Set.Ioo a b)
    (hoff : ∀ r ∈ Set.Ioo a b, r ∉ M.cornerRadii)
    (hKd : ∀ r ∈ Set.Ioo a b, DifferentiableAt ℝ M.K r)
    (hdom : ∀ r ∈ Set.Ioo a b, Summable fun e : Sym2 M.V =>
      |M.cutEdgeDeriv r e| * (2 * (M.cutLaw r).real {ω : Config M.V | e ∈ touchSet ω (0 : M.V)}))
    (hboundint : ∀ y : M.V, ∀ a' ∈ Set.Ioo a b, ∀ b' ∈ Set.Ioo a b,
      IntervalIntegrable
        (sMomentWeight (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv) volume a' b')
    (hmeasK : ∀ y : M.V, ∀ k : ℕ, AEStronglyMeasurable (windowFluxOf (0 : M.V)
      (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) {y}) S M.cutProb M.cutEdgeDeriv k) volume)
    (hmeasinf : ∀ y : M.V, ∀ r ∈ Set.Ioo a b, StronglyMeasurableAtFilter
      (sMomentInfFlux (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv) (𝓝 r) volume)
    (hcontinf : ∀ y : M.V, ∀ r ∈ Set.Ioo a b, ContinuousAt
      (sMomentInfFlux (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv) r)
    (hfin : ∀ r ∈ Set.Ioo a b, M.cutMassAt r 0 ≠ ⊤)
    (u : M.V → ℝ) (hu : Summable u)
    (hub : ∀ y : M.V, ∀ r ∈ Set.Ioo a b,
      |sMomentInfFlux (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv r| ≤ u y) :
    HasDerivAt M.cutMassReal
      (∑' y : M.V,
        sMomentInfFlux (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv r0) r0 := by
  have hpt : ∀ (y : M.V) (r : ℝ), r ∈ Set.Ioo a b →
      HasDerivAt (fun z => M.cutTwoPoint z 0 y)
        (sMomentInfFlux (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv r) r :=
    fun y r hr => M.hasDerivAt_cutTwoPoint_off y S hSmono hS isOpen_Ioo hr
      (fun r' hr' => hoff r' hr') (fun r' hr' => hKd r' hr')
      (fun r' hr' => hdom r' hr') (fun a' ha' b' hb' => hboundint y a' ha' b' hb')
      (fun k => hmeasK y k) (hmeasinf y r hr) (hcontinf y r hr)
  have htsum : HasDerivAt (fun z => ∑' y : M.V, M.cutTwoPoint z 0 y)
      (∑' y : M.V,
        sMomentInfFlux (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv r0) r0 :=
    hasDerivAt_tsum_of_isPreconnected (α := M.V) (𝕜 := ℝ) (F := ℝ)
      (u := u) (g := fun y z => M.cutTwoPoint z 0 y)
      (g' := fun y z =>
        sMomentInfFlux (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv z)
      (t := Set.Ioo a b) (y₀ := r0) (y := r0) hu isOpen_Ioo isPreconnected_Ioo
      hpt (fun y r hr => by rw [Real.norm_eq_abs]; exact hub y r hr)
      hr0 (M.summable_cutTwoPoint_of_finite (hfin r0 hr0)) hr0
  refine htsum.congr_of_eventuallyEq ?_
  filter_upwards [isOpen_Ioo.mem_nhds hr0] with r hr
  exact M.cutMassReal_eq_tsum_cutTwoPoint (hfin r hr)

end SourceModelData

end PercLib.CriticalLRP.Orchestration

namespace PercLib.CriticalLRP.Orchestration

namespace SourceModelData

variable (M : SourceModelData)

/-- **Off-corner derivative and derivative bound for the cut mass.**

Pointwise form of `hasDerivAt_cutMassReal_of_summableMajorant`: at every off-corner radius of the
window the cut mass is differentiable, and the derivative is bounded by the total mass `∑' u` of
the summable majorant.  This is the `hgood` shape consumed by
`M.cutMassReal_abs_sub_le_integral_of_continuousOn_interior` / the `LocalAC` interface. -/
theorem cutMassReal_offCorner_deriv_bound
    (S : ℕ → Finset (Sym2 M.V)) (hSmono : Monotone S) (hS : ∀ e : Sym2 M.V, ∃ n, e ∈ S n)
    {a b : ℝ}
    (hoff : ∀ r ∈ Set.Ioo a b, r ∉ M.cornerRadii)
    (hKd : ∀ r ∈ Set.Ioo a b, DifferentiableAt ℝ M.K r)
    (hdom : ∀ r ∈ Set.Ioo a b, Summable fun e : Sym2 M.V =>
      |M.cutEdgeDeriv r e| * (2 * (M.cutLaw r).real {ω : Config M.V | e ∈ touchSet ω (0 : M.V)}))
    (hboundint : ∀ y : M.V, ∀ a' ∈ Set.Ioo a b, ∀ b' ∈ Set.Ioo a b,
      IntervalIntegrable
        (sMomentWeight (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv) volume a' b')
    (hmeasK : ∀ y : M.V, ∀ k : ℕ, AEStronglyMeasurable (windowFluxOf (0 : M.V)
      (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) {y}) S M.cutProb M.cutEdgeDeriv k) volume)
    (hmeasinf : ∀ y : M.V, ∀ r ∈ Set.Ioo a b, StronglyMeasurableAtFilter
      (sMomentInfFlux (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv) (𝓝 r) volume)
    (hcontinf : ∀ y : M.V, ∀ r ∈ Set.Ioo a b, ContinuousAt
      (sMomentInfFlux (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv) r)
    (hfin : ∀ r ∈ Set.Ioo a b, M.cutMassAt r 0 ≠ ⊤)
    (u : M.V → ℝ) (hu : Summable u)
    (hub : ∀ y : M.V, ∀ r ∈ Set.Ioo a b,
      |sMomentInfFlux (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv r| ≤ u y) :
    ∀ r ∈ Set.Ioo a b, r ∉ M.cornerRadii →
      DifferentiableAt ℝ M.cutMassReal r ∧ |deriv M.cutMassReal r| ≤ ∑' y : M.V, u y := by
  intro r hr _
  have hderiv := M.hasDerivAt_cutMassReal_of_summableMajorant S hSmono hS hr hoff hKd hdom
    hboundint hmeasK hmeasinf hcontinf hfin u hu hub
  refine ⟨hderiv.differentiableAt, ?_⟩
  rw [hderiv.deriv]
  have habs : Summable fun y : M.V =>
      |sMomentInfFlux (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv r| :=
    hu.of_nonneg_of_le (fun y => abs_nonneg _) (fun y => hub y r hr)
  calc |∑' y : M.V,
        sMomentInfFlux (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv r|
      = ‖∑' y : M.V,
        sMomentInfFlux (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv r‖ :=
        (Real.norm_eq_abs _).symm
    _ ≤ ∑' y : M.V,
        ‖sMomentInfFlux (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv r‖ :=
        norm_tsum_le_tsum_norm habs
    _ = ∑' y : M.V,
        |sMomentInfFlux (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv r| :=
        tsum_congr fun y => Real.norm_eq_abs _
    _ ≤ ∑' y : M.V, u y :=
        Summable.tsum_le_tsum (fun y => hub y r hr) habs hu

/-- **Absolute continuity and the fundamental theorem of calculus for the cut mass**, from a
summable-in-`y`, radius-uniform majorant of the per-`y` pivotal fluxes.

This assembles the new pointwise off-corner derivative with three landed results:

* `M.finite_cornerRadii_inter_Ioo` (local finiteness of the corner set),
* `M.continuousAt_cutMassReal` (two-sided continuity from a finite larger cut-off moment),
* `M.cutMassReal_absolutelyContinuousOn_of_continuousOn_interior` (`LocalAC/Interface`).

The majorant is the constant `∑' u`, which is continuous and interval integrable on any window, so
the conclusion is `AbsolutelyContinuousOnInterval M.cutMassReal a b` plus the exact fundamental
theorem of calculus statement. -/
theorem cutMassReal_absolutelyContinuousOn_of_summableMajorant
    (S : ℕ → Finset (Sym2 M.V)) (hSmono : Monotone S) (hS : ∀ e : Sym2 M.V, ∃ n, e ∈ S n)
    {a b : ℝ} (hab : a ≤ b) (ha : 0 < a) {r1 : ℝ} (hb1 : b < r1)
    (hfin1 : M.cutMassAt r1 0 ≠ ⊤)
    (hoff : ∀ r ∈ Set.Ioo a b, r ∉ M.cornerRadii)
    (hKd : ∀ r ∈ Set.Ioo a b, DifferentiableAt ℝ M.K r)
    (hdom : ∀ r ∈ Set.Ioo a b, Summable fun e : Sym2 M.V =>
      |M.cutEdgeDeriv r e| * (2 * (M.cutLaw r).real {ω : Config M.V | e ∈ touchSet ω (0 : M.V)}))
    (hboundint : ∀ y : M.V, ∀ a' ∈ Set.Ioo a b, ∀ b' ∈ Set.Ioo a b,
      IntervalIntegrable
        (sMomentWeight (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv) volume a' b')
    (hmeasK : ∀ y : M.V, ∀ k : ℕ, AEStronglyMeasurable (windowFluxOf (0 : M.V)
      (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) {y}) S M.cutProb M.cutEdgeDeriv k) volume)
    (hmeasinf : ∀ y : M.V, ∀ r ∈ Set.Ioo a b, StronglyMeasurableAtFilter
      (sMomentInfFlux (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv) (𝓝 r) volume)
    (hcontinf : ∀ y : M.V, ∀ r ∈ Set.Ioo a b, ContinuousAt
      (sMomentInfFlux (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv) r)
    (hfin : ∀ r ∈ Set.Ioo a b, M.cutMassAt r 0 ≠ ⊤)
    (u : M.V → ℝ) (hu : Summable u)
    (hub : ∀ y : M.V, ∀ r ∈ Set.Ioo a b,
      |sMomentInfFlux (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv r| ≤ u y) :
    AbsolutelyContinuousOnInterval M.cutMassReal a b ∧
      ∫ t in a..b, deriv M.cutMassReal t = M.cutMassReal b - M.cutMassReal a := by
  have hcont : ContinuousOn M.cutMassReal (Set.Icc a b) := by
    intro r hr
    exact (M.continuousAt_cutMassReal r (lt_of_lt_of_le ha hr.1)
      (lt_of_le_of_lt hr.2 hb1) hfin1).continuousWithinAt
  have hgood := M.cutMassReal_offCorner_deriv_bound S hSmono hS hoff hKd hdom hboundint
    hmeasK hmeasinf hcontinf hfin u hu hub
  have hC : IntervalIntegrable (fun _ : ℝ => ∑' y : M.V, u y) volume a b :=
    intervalIntegrable_const
  have hCcont : ContinuousOn (fun _ : ℝ => ∑' y : M.V, u y) (Set.Ioo a b) :=
    continuous_const.continuousOn
  have hDfin : (M.cornerRadii ∩ Set.Ioo a b).Finite := M.finite_cornerRadii_inter_Ioo a b
  refine ⟨M.cutMassReal_absolutelyContinuousOn_of_continuousOn_interior hab hcont hC hCcont
    hDfin hgood, ?_⟩
  exact M.cutMassReal_intervalIntegral_deriv_of_continuousOn_interior hab hcont hC hCcont
    hDfin hgood

/-- **The finitely-truncated mass is differentiable off the corner set.**

For every *finite* vertex set `A ⊆ V`, the partial mass `r ↦ ∑_{y ∈ A} M.cutTwoPoint r 0 y` is
differentiable at every off-corner radius of the window, with derivative the finite sum of the
infinite pivotal fluxes.  No finiteness of the cut-off moment and no summable-in-`y` majorant is
required: the only residuals are the per-edge domination `hdom` and the parameter regularity of the
window fluxes, exactly as in `hasDerivAt_cutTwoPoint_off`.

This isolates the obstruction in the infinite-volume mass derivative: passing from finite `A` to
`V` is precisely the `y`-interchange controlled by the majorant `u` of
`hasDerivAt_cutMassReal_of_summableMajorant`. -/
theorem hasDerivAt_finset_sum_cutTwoPoint (A : Finset M.V) (S : ℕ → Finset (Sym2 M.V))
    (hSmono : Monotone S) (hS : ∀ e : Sym2 M.V, ∃ n, e ∈ S n)
    {I : Set ℝ} (hI : IsOpen I) {r0 : ℝ} (hr0 : r0 ∈ I)
    (hoff : ∀ r ∈ I, r ∉ M.cornerRadii)
    (hKd : ∀ r ∈ I, DifferentiableAt ℝ M.K r)
    (hdom : ∀ r ∈ I, Summable fun e : Sym2 M.V =>
      |M.cutEdgeDeriv r e| * (2 * (M.cutLaw r).real {ω : Config M.V | e ∈ touchSet ω (0 : M.V)}))
    (hboundint : ∀ y : M.V, ∀ a' ∈ I, ∀ b' ∈ I,
      IntervalIntegrable
        (sMomentWeight (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv) volume a' b')
    (hmeasK : ∀ y : M.V, ∀ k : ℕ, AEStronglyMeasurable (windowFluxOf (0 : M.V)
      (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) {y}) S M.cutProb M.cutEdgeDeriv k) volume)
    (hmeasinf : ∀ y : M.V, StronglyMeasurableAtFilter
      (sMomentInfFlux (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv) (𝓝 r0) volume)
    (hcontinf : ∀ y : M.V, ContinuousAt
      (sMomentInfFlux (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv) r0) :
    HasDerivAt (fun r => ∑ y ∈ A, M.cutTwoPoint r 0 y)
      (∑ y ∈ A,
        sMomentInfFlux (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv r0) r0 := by
  have h := HasDerivAt.fun_sum (u := A)
    (A := fun y r => M.cutTwoPoint r 0 y)
    (A' := fun y => sMomentInfFlux (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb
      M.cutEdgeDeriv r0)
    (fun y _ => M.hasDerivAt_cutTwoPoint_off y S hSmono hS hI hr0
      hoff hKd hdom (fun a' ha' b' hb' => hboundint y a' ha' b' hb') (fun k => hmeasK y k)
      (hmeasinf y) (hcontinf y))
  simpa only [Finset.sum_apply] using h

end SourceModelData

end PercLib.CriticalLRP.Orchestration

/-! ## Axiom audit

Every declaration of this packet is checked to depend only on `propext`, `Classical.choice` and
`Quot.sound`. -/

set_option linter.hashCommand false
set_option linter.style.longLine false

#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.cutEdgeDeriv
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.cutEdgeDeriv_mk
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.cutProb_coe_eq
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.cutKernel_mk
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.hasDerivAt_cutProb_off
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.hasDerivAt_cutProb_off_of_pos
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.cutLaw_eq_edgeMeasure
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.hasDerivAt_integral_cutFun_cutLaw
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.sMomentTrunc_singleton
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.integral_sMomentTrunc_singleton
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.hasDerivAt_cutTwoPoint_off
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.summable_cutTwoPoint_of_finite
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.cutMassReal_eq_tsum_cutTwoPoint
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.hasDerivAt_cutMassReal_of_summableMajorant
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.cutMassReal_offCorner_deriv_bound
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.hasDerivAt_finset_sum_cutTwoPoint
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.cutMassReal_absolutelyContinuousOn_of_summableMajorant
