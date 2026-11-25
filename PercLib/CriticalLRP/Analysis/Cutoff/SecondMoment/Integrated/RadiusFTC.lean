/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Swarm `smwvgnqju`, member `m2`, direction `d2`.

# The `p = 2` radius derivative without `hfluxMono`, and the exact comparison that fails

The landed off-corner radius derivative `SourceModelData.hasDerivAt_cutMomentReal_two` is produced
from the integrated identity `∫ t in a..x, M.rhsScalarTwo t = M.cutMomentReal 2 x - M.cutMomentReal 2 a`
via the monotone convergence core `intervalIntegral_eq_of_monotone_window`, which consumes the
window-index monotonicity of the finite window fluxes

`hfluxMono : ∀ n t, M.windowFlux (S n) t ≤ M.windowFlux (S (n + 1)) t`.

Observable domination alone does not justify that hypothesis (`Integrated/WindowFlux.lean`,
section 5). This file replaces it by one explicit *uniform-in-window majorant* of the flux.
It does not assert a completed source-witness refutation of monotonicity.

## What is proved here

* `integral_rhsScalarTwo_eq_sub_of_window_majorant` — the integrated radius identity, with
  `hfluxMono`, `hmomMono`, `hmomNN` dropped and replaced by
  `hfluxMaj : ∀ n, ∀ t ∈ (a, b], M.windowFlux (S n) t ≤ G t` for one radius function `G` with
  `IntegrableOn G (Ioc a b)`; the window family need not be monotone or exhausting;
* `hasDerivAt_cutMomentReal_two_of_window_majorant` — the pointwise off-corner radius derivative,
  from the landed fixed-base FTC `hasDerivAt_of_integral_from_base`;
* `hasDerivAt_cutMomentReal_two_of_envelope` — the same with `G` written as an edge sum
  `t ↦ ∑' e, Env e t`, i.e. the interface that a summable ghost envelope has to meet;
* `partialLimitFlux_le_rhsScalarTwo` — the truncated *untruncated*-pivotal sums are dominated by the
  accepted right-hand side, from the landed fixed-radius FLUX identity and the nonnegativity of the
  edge terms: `M.partialLimitFlux S r ≤ M.rhsScalarTwo r`;
* `cutFun_clusterVolSqReal_le_self_of_ne_top`, `ae_cutFun_clusterVolSqReal_le_self` — the windowed
  square is dominated by the untruncated square at every finite-cluster configuration, hence almost
  surely under the cut-off law (`PivotFlux.ae_clusterVol_ne_top`);
* `integrable_flipDiff_cutFun_clusterVolSqReal` — the windowed flip difference is integrable with no
  moment hypothesis (finite-window bound);
* `sub_le_sub_false` — the arithmetic obstruction of section 1.

## The exact comparison that fails

The natural candidate majorant is the accepted right-hand side itself: it would be enough to prove

`M.windowFlux S r ≤ M.rhsScalarTwo r`,  equivalently  `M.windowFlux S r ≤ M.partialLimitFlux S r`,

because the second inequality only needs, edge by edge (`e` in the exact support `inSupport M r`),

`pivotalFlux (M.cutLaw r) (cutFun S M.clusterVolSqReal) e ≤ pivotalFlux (M.cutLaw r)
  M.clusterVolSqReal e`

and `cutEdgeDeriv r e ≥ 0`.  **That per-edge comparison is not derivable from the domination of the
observables.**  `flipDiff g e ω = g (forceOn {e} {e} ω) - g (forceOn {e} ∅ ω)` is *not* monotone
in `g`: the closed argument `forceOn {e} ∅ ω` enters with a negative sign, so raising the functional
at the closed configuration lowers the flip difference (`sub_le_sub_false`).  Concretely, from
`g ≤ h` one only gets `g (F_e) ≤ h (F_e)` and `g (F_∅) ≤ h (F_∅)`, which give the wrong sign for
the second term.  The two-sided requirement

`g (F_e) ≤ h (F_e)` **and** `h (F_∅) ≤ g (F_∅)`

is what would be needed at the level of functions, but it is not supplied by observable
domination.  The obstruction is not merely the `⊤ ↦ 0` convention for `toReal` (finite-cluster
configurations are handled by `ae_cutFun_clusterVolSqReal_le_self`): it is the sign of the closed
term inside the pivotal (Russo) derivative.  This is an obstruction to that particular proof,
not a proof that the desired one-sided flux bound is false.

The remaining route to the majorant is therefore the one through the *closed ghosts*: the landed
per-edge identities `cutEdgeClosedWeight_mul_pivotalFlux_eq` and
`cutEdgeClosedWeight_mul_pivotalFlux_cutFun_eq` express both pivotal fluxes as integrals of the
nonnegative `ℝ≥0∞` merge weights `quadEdgeWeight`, and what has to be compared is
`quadEdgeWeight (cutConfig S ω) ≤ quadEdgeWeight ω` (junk-free in `ℝ≥0∞`, since cutting shrinks the
origin cluster and the `y`-cluster).  That comparison is a candidate, not a theorem of this file: neither its truth nor its negation is
established here. No integrable majorant is constructed, and `hfluxMaj` and `hfluxConv` remain
explicit hypotheses of the derivative interface.
-/
module

public import PercLib.CriticalLRP.Analysis.Cutoff.SecondMoment.Integrated.Exchange
public import PercLib.CriticalLRP.Analysis.Cutoff.SecondMoment.Integrated.Main
public import PercLib.CriticalLRP.Analysis.Cutoff.SecondMoment.FluxConv.Main
public import PercLib.CriticalLRP.Analysis.Cutoff.SecondMoment.Integrated.WindowFlux
public import PercLib.CriticalLRP.Analysis.Cutoff.FluxSupport
public import PercLib.CriticalLRP.RussoInf.FluxTruncation.Main

/-!
# The radius identity and derivative, without window-index monotonicity of the flux
-/

set_option autoImplicit false
set_option linter.hashCommand false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP.Orchestration

namespace SourceModelData

variable (M : SourceModelData)

/-! ## 1. Why the naive domination of the pivotal flux does not follow from domination of the observable -/

/-- **The ordering that a naive domination argument would need is false.**  If `g ≤ h` pointwise
then the flip differences `flipDiff g e ω = g (forceOn {e} {e} ω) - g (forceOn {e} ∅ ω)` and
`flipDiff h e ω = h (forceOn {e} {e} ω) - h (forceOn {e} ∅ ω)` are *not* ordered: the closed
argument enters with a negative sign, so raising the functional at the closed configuration lowers
the flip difference.

The arithmetic content is that `a ≤ a'` and `b ≤ b'` do not imply `a - b ≤ a' - b'`; this lemma
records the counterexample `a = a' = 1`, `b = 0`, `b' = 5`.  Consequently

`pivotalFlux (M.cutLaw r) (cutFun S M.clusterVolSqReal) e ≤ pivotalFlux (M.cutLaw r)
  M.clusterVolSqReal e`

is **not** a consequence of `cutFun S M.clusterVolSqReal ≤ M.clusterVolSqReal`, and the one-sided
majorant `M.windowFlux S r ≤ M.rhsScalarTwo r` cannot be obtained from the pointwise domination of
the windowed square at the level of pivotal fluxes.  (At the level of the *closed ghosts* — the
nonnegative `ENNReal` merge weights — the corresponding comparison is junk-free; see the module
report.) -/
theorem sub_le_sub_false : ¬ ∀ a b a' b' : ℝ, a ≤ a' → b ≤ b' → a - b ≤ a' - b' := by
  intro h
  have hc := h 1 0 1 5 le_rfl (by norm_num)
  norm_num at hc

/-! ## 2. The windowed square lies below the untruncated square, on finite clusters -/

/-- **The windowed square of the origin cluster is dominated by the untruncated one, at every
configuration whose origin cluster is finite.**

Cutting to a finite edge window can only shrink the cluster of the origin, so on a finite cluster
the two `ℝ≥0∞ → ℝ` conversions are order preserving and the squares are ordered.

The finiteness hypothesis is *not* removable pointwise: at a configuration with an infinite origin
cluster the untruncated functional takes the junk value `|K₀|² = 0` while the windowed cluster can
be nonempty, so the inequality reverses there.  It is, however, removable almost surely under
`M.cutLaw r`, since `PivotFlux.ae_clusterVol_ne_top` gives `∀ᵐ ω, ∀ v, clusterVol ω v ≠ ⊤`. -/
theorem cutFun_clusterVolSqReal_le_self_of_ne_top (S : Finset (Sym2 M.V)) {ω : Config M.V}
    (hfin : clusterVol ω (0 : M.V) ≠ ⊤) :
    cutFun S M.clusterVolSqReal ω ≤ M.clusterVolSqReal ω := by
  have hle : clusterVol (cutConfig S ω) (0 : M.V) ≤ clusterVol ω (0 : M.V) :=
    clusterVol_mono (fun e he => he.1) 0
  simp only [cutFun, M.clusterVolSqReal_apply]
  have h2 : (clusterVol (cutConfig S ω) (0 : M.V)).toReal
      ≤ (clusterVol ω (0 : M.V)).toReal :=
    ENNReal.toReal_mono hfin hle
  exact pow_le_pow_left₀ ENNReal.toReal_nonneg h2 2

/-- **The windowed square is dominated by the untruncated one almost surely**, under the finite
first cutoff moment.  `PivotFlux.ae_clusterVol_ne_top` gives almost sure finiteness of *every*
cluster volume, so the finite-cluster comparison applies almost surely.

This shows that the pointwise domination of the observables is available; what fails is the
passage to the pivotal fluxes (section 1). -/
theorem ae_cutFun_clusterVolSqReal_le_self (S : Finset (Sym2 M.V)) {r : ℝ}
    (h1 : M.cutMassAt r (0 : M.V) ≠ ⊤) :
    ∀ᵐ ω ∂(M.cutLaw r), cutFun S M.clusterVolSqReal ω ≤ M.clusterVolSqReal ω := by
  filter_upwards [PivotFlux.ae_clusterVol_ne_top M r h1] with ω hω
  exact M.cutFun_clusterVolSqReal_le_self_of_ne_top S (hω 0)

/-! ## 3. The windowed flip difference is integrable -/

/-- **The windowed flip difference is integrable.**  It is bounded by twice the finite-window
constant `((insert 0 (edgeVertices S)).card)^2` of `cutFun_clusterVolSqReal_le`, and the cut-off
law is a probability measure.  No moment hypothesis is used. -/
theorem integrable_flipDiff_cutFun_clusterVolSqReal (S : Finset (Sym2 M.V)) (r : ℝ)
    (e : Sym2 M.V) :
    Integrable (flipDiff (cutFun S M.clusterVolSqReal) e) (M.cutLaw r) := by
  have hmeas : AEStronglyMeasurable (flipDiff (cutFun S M.clusterVolSqReal) e) (M.cutLaw r) :=
    (measurable_flipDiff (measurable_cutFun M.measurable_clusterVolSqReal) e).aestronglyMeasurable
  refine Integrable.of_bound hmeas (2 * ((insert (0 : M.V) (edgeVertices S)).card : ℝ) ^ 2)
    (Eventually.of_forall fun ω => ?_)
  have hb1 := M.cutFun_clusterVolSqReal_le S
    (forceOn ({e} : Set (Sym2 M.V)) ({e} : Config M.V) ω)
  have hb2 := M.cutFun_clusterVolSqReal_le S
    (forceOn ({e} : Set (Sym2 M.V)) (∅ : Config M.V) ω)
  have hn1 := M.cutFun_clusterVolSqReal_nonneg S
    (forceOn ({e} : Set (Sym2 M.V)) ({e} : Config M.V) ω)
  have hn2 := M.cutFun_clusterVolSqReal_nonneg S
    (forceOn ({e} : Set (Sym2 M.V)) (∅ : Config M.V) ω)
  rw [Real.norm_eq_abs, flipDiff, abs_le]
  constructor <;> linarith

/-! ## 4. A partial sum of the untruncated pivotal flux is below the accepted right-hand side -/

/-- **The truncated untruncated-pivotal sum is at most the accepted right-hand side.**  All edge
terms are nonnegative at positive radius, so a finite sum is at most the `tsum`, and the `tsum` is
the accepted `p = 2` right-hand side by the landed fixed-radius FLUX identity. -/
theorem partialLimitFlux_le_rhsScalarTwo {r : ℝ} (hr : 0 < r)
    (h1 : M.cutMassAt r (0 : M.V) ≠ ⊤) (hp2 : M.p2RHS r ≠ ⊤) (S : Finset (Sym2 M.V)) :
    M.partialLimitFlux S r ≤ M.rhsScalarTwo r := by
  have hnn : ∀ e : Sym2 M.V, 0 ≤ M.cutEdgeDeriv r e *
      pivotalFlux (M.cutLaw r) M.clusterVolSqReal e := fun e =>
    mul_nonneg (M.cutEdgeDeriv_nonneg (M.neg_deriv_K_nonneg hr) e)
      (M.pivotalFlux_clusterVolSqReal_nonneg r h1 e)
  have hsumm : Summable fun e : Sym2 M.V =>
      M.cutEdgeDeriv r e * pivotalFlux (M.cutLaw r) M.clusterVolSqReal e :=
    M.summable_cutEdgeDeriv_mul_pivotalFlux h1 hp2
  have hmem := Summable.sum_le_tsum S (fun e _ => hnn e) hsumm
  have hg : M.clusterVolSqReal
      = fun ω : Config M.V => (clusterVol ω (0 : M.V)).toReal ^ 2 :=
    funext fun ω => M.clusterVolSqReal_apply ω
  rw [SourceModelData.partialLimitFlux]
  calc ∑ e ∈ S, M.cutEdgeDeriv r e * pivotalFlux (M.cutLaw r) M.clusterVolSqReal e
      ≤ ∑' e : Sym2 M.V,
          M.cutEdgeDeriv r e * pivotalFlux (M.cutLaw r) M.clusterVolSqReal e := hmem
    _ = M.rhsScalarTwo r := by
        rw [hg]
        exact M.tsum_cutEdgeDeriv_mul_pivotalFlux_eq_rhsScalarTwo r h1 hp2

/-! ## 5. The integrated radius identity from a uniform-in-window majorant -/

/-- **The integrated `p = 2` radius identity, from a uniform-in-window majorant of the flux.**

Compared with the landed `integral_rhsScalarTwo_eq_sub_of_window` this

* drops the flux monotonicity `hfluxMono : ∀ n t, M.windowFlux (S n) t ≤ M.windowFlux (S (n + 1)) t`
  and replaces it by the one-sided majorant `hfluxMaj : ∀ n, ∀ t ∈ (a, b], M.windowFlux (S n) t ≤ G t`
  by a single radius function `G` with finite interval integral;
* drops the moment monotonicity `hmommono` and the nonnegativity of the moment increments
  `hmomnn` (dominated convergence identifies the limit of the integral, so no monotone convergence
  of the moment increments is needed);
* does not require the window family `S` to be monotone or exhausting;
* keeps the pointwise-in-radius convergence `hfluxConv` (the fixed-radius insertion problem).

The analytic input is exactly the dominated-convergence exchange
`intervalIntegral_eq_of_majorant_window` of `Exchange.lean`; the finite-window part is the
unconditional FTC `integral_windowFlux_eq_sub`.  Measurability in the radius, nonnegativity of the
flux and interval integrability of each window flux are not hypotheses: they are the landed
`measurable_windowFlux`, `windowFlux_nonneg` and `intervalIntegrable_windowFlux`. -/
theorem integral_rhsScalarTwo_eq_sub_of_window_majorant {a b : ℝ}
    (hwin : M.IsOffCornerWindow a b) (S : ℕ → Finset (Sym2 M.V))
    {G : ℝ → ℝ} (hfluxMaj : ∀ n, ∀ t ∈ Set.Ioc a b, M.windowFlux (S n) t ≤ G t)
    (hG : IntegrableOn G (Set.Ioc a b) volume)
    (hfluxConv : ∀ t, Tendsto (fun n => M.windowFlux (S n) t) atTop (𝓝 (M.rhsScalarTwo t)))
    (hmoment : ∀ x ∈ Set.Icc a b,
      Tendsto (fun n => M.windowMoment (S n) x - M.windowMoment (S n) a) atTop
        (𝓝 (M.cutMomentReal 2 x - M.cutMomentReal 2 a))) :
    ∀ x ∈ Set.Icc a b,
      ∫ t in a..x, M.rhsScalarTwo t = M.cutMomentReal 2 x - M.cutMomentReal 2 a := by
  obtain ⟨ha, _, hoff⟩ := hwin
  intro x hx
  have hwin' : M.IsOffCornerWindow a x :=
    ⟨ha, hx.1, fun r hr => hoff r (Set.Icc_subset_Icc_right hx.2 hr)⟩
  have hGx : IntervalIntegrable G volume a x :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hx.1).mpr
      (hG.mono_set (Set.Ioc_subset_Ioc le_rfl hx.2))
  refine intervalIntegral_eq_of_majorant_window (F := fun n => M.windowFlux (S n))
    (Flim := fun t => M.rhsScalarTwo t)
    (p := fun n => M.windowMoment (S n) x - M.windowMoment (S n) a)
    (G := G) (L := M.cutMomentReal 2 x - M.cutMomentReal 2 a) hx.1
    (fun n t => M.windowFlux_nonneg (S n) t)
    (fun n => (M.measurable_windowFlux (S n)).aestronglyMeasurable) ?_ hGx hfluxConv
    (fun n => M.integral_windowFlux_eq_sub (S n) hwin'
      (M.intervalIntegrable_windowFlux (S n) hwin')) (hmoment x hx)
  intro n t ht
  exact hfluxMaj n t (Set.Ioc_subset_Ioc le_rfl hx.2 ht)

/-! ## 6. The off-corner radius derivative without `hfluxMono` -/

/-- **The `p = 2` off-corner radius derivative, with `hfluxMono` replaced by a uniform-in-window
majorant.**

Fix an off-corner window `[a, b]` containing `r0` in its interior.  Suppose

* `hfluxMaj` — all window fluxes are dominated on `(a, b]` by a single radius function `G` whose
  interval integral on `[a, b]` is finite.  This is the exact replacement for `hfluxMono`: it is
  a bound by a *fixed* function of the radius, so it does not order the windows among themselves,
  and it does not require the window family to be nested;
* `hfluxConv` — the window fluxes converge pointwise in the radius to `M.rhsScalarTwo` (the
  fixed-radius insertion problem, direction `d1`);
* `hmoment` — the window moment increments converge to the increments of `M.cutMomentReal 2`;
* `hrhsCont`, `hrhsInt` — continuity at `r0` and interval integrability of `M.rhsScalarTwo` on the
  window, for the fixed-base fundamental theorem of calculus.

Then `HasDerivAt (fun r => M.cutMomentReal 2 r) (M.rhsScalarTwo r0) r0`.

`hfluxMeas`, `hfluxNN`, `hfluxInt` of the landed statement are not hypotheses here: they are the
landed theorems `measurable_windowFlux`, `windowFlux_nonneg` and `intervalIntegrable_windowFlux`.
`hmomMono` and `hmomNN` are not needed at all.  Neither is any monotonicity in the window index. -/
theorem hasDerivAt_cutMomentReal_two_of_window_majorant {a b r0 : ℝ}
    (hwin : M.IsOffCornerWindow a b) (S : ℕ → Finset (Sym2 M.V))
    (har : a < r0) (hrb : r0 < b)
    {G : ℝ → ℝ} (hfluxMaj : ∀ n, ∀ t ∈ Set.Ioc a b, M.windowFlux (S n) t ≤ G t)
    (hG : IntervalIntegrable G volume a b)
    (hfluxConv : ∀ t, Tendsto (fun n => M.windowFlux (S n) t) atTop (𝓝 (M.rhsScalarTwo t)))
    (hmoment : ∀ x ∈ Set.Icc a b,
      Tendsto (fun n => M.windowMoment (S n) x - M.windowMoment (S n) a) atTop
        (𝓝 (M.cutMomentReal 2 x - M.cutMomentReal 2 a)))
    (hrhsCont : ContinuousAt (fun t => M.rhsScalarTwo t) r0)
    (hrhsInt : IntervalIntegrable (fun t => M.rhsScalarTwo t) volume a b) :
    HasDerivAt (fun r => M.cutMomentReal 2 r) (M.rhsScalarTwo r0) r0 := by
  have hab : a ≤ b := hwin.2.1
  have hOn : IntegrableOn (fun t => M.rhsScalarTwo t) (Set.Ioc a b) volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp hrhsInt
  have hGon : IntegrableOn G (Set.Ioc a b) volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp hG
  have hbase := M.integral_rhsScalarTwo_eq_sub_of_window_majorant hwin S hfluxMaj hGon
    hfluxConv hmoment
  have hmeas : Measurable fun t => M.rhsScalarTwo t := by
    have hlim : (fun t => M.rhsScalarTwo t)
        = fun t => liminf (fun n => M.windowFlux (S n) t) atTop := by
      funext t
      exact (hfluxConv t).liminf_eq.symm
    rw [hlim]
    exact Measurable.liminf fun n => M.measurable_windowFlux (S n)
  have hint : IntervalIntegrable (fun t => M.rhsScalarTwo t) volume a r0 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (le_of_lt har)).mpr
      (hOn.mono_set (Set.Ioc_subset_Ioc le_rfl (le_of_lt hrb)))
  refine hasDerivAt_of_integral_from_base (f := fun r => M.cutMomentReal 2 r)
    (g := fun t => M.rhsScalarTwo t) (a := a) hint hmeas hrhsCont ?_
  filter_upwards [isOpen_Ioo.mem_nhds (show r0 ∈ Set.Ioo a b from ⟨har, hrb⟩)] with x hx
  exact hbase x (Set.Ioo_subset_Icc_self hx)

/-- **The radius derivative from an explicit edge envelope.**

The majorant `G` of `hasDerivAt_cutMomentReal_two_of_window_majorant` is taken to be the edge sum
`t ↦ ∑' e, Env e t` of a per-edge envelope.  This is the exact interface expected from the
summable ghost envelope of direction `d1`: that direction has to produce `Env` with (i) the
pointwise bound on the window fluxes and (ii) `IntervalIntegrable (∑' e, Env · e)` on the radius
window; everything else is discharged here and in
`hasDerivAt_cutMomentReal_two_of_window_majorant`. -/
theorem hasDerivAt_cutMomentReal_two_of_envelope {a b r0 : ℝ}
    (hwin : M.IsOffCornerWindow a b) (S : ℕ → Finset (Sym2 M.V))
    (har : a < r0) (hrb : r0 < b) (Env : Sym2 M.V → ℝ → ℝ)
    (hfluxLe : ∀ n, ∀ t ∈ Set.Ioc a b, M.windowFlux (S n) t ≤ ∑' e : Sym2 M.V, Env e t)
    (hEnv : IntervalIntegrable (fun t => ∑' e : Sym2 M.V, Env e t) volume a b)
    (hfluxConv : ∀ t, Tendsto (fun n => M.windowFlux (S n) t) atTop (𝓝 (M.rhsScalarTwo t)))
    (hmoment : ∀ x ∈ Set.Icc a b,
      Tendsto (fun n => M.windowMoment (S n) x - M.windowMoment (S n) a) atTop
        (𝓝 (M.cutMomentReal 2 x - M.cutMomentReal 2 a)))
    (hrhsCont : ContinuousAt (fun t => M.rhsScalarTwo t) r0)
    (hrhsInt : IntervalIntegrable (fun t => M.rhsScalarTwo t) volume a b) :
    HasDerivAt (fun r => M.cutMomentReal 2 r) (M.rhsScalarTwo r0) r0 :=
  M.hasDerivAt_cutMomentReal_two_of_window_majorant hwin S har hrb hfluxLe hEnv hfluxConv
    hmoment hrhsCont hrhsInt

/-- **The radius derivative from a uniform constant in the landed finite-window flux bound.**

The landed finite-window bound `abs_windowFlux_le` reads

`|M.windowFlux S r| ≤ c S * |deriv M.K r|`,  `c S = |S| * (β_c * 2 * |V_S|²)`.

`|deriv M.K|` is interval integrable on every positive radius window
(`intervalIntegrable_deriv_K`), so the majorant hypothesis of
`hasDerivAt_cutMomentReal_two_of_window_majorant` is met with `G = C * |deriv M.K|` as soon as the
landed constants `c (S n)` are bounded along the window family by one number `C`.

This is the concrete form of the replacement for `hfluxMono`: instead of the (false) ordering of
the fluxes among themselves, one needs the *uniformity in the window index* of the constant in the
already landed per-window bound.  For an exhausting family the constant `c (S n)` grows with the
window, so this corollary is not a discharge of `hfluxMono` either; it isolates the remaining gap
as a single number. -/
theorem hasDerivAt_cutMomentReal_two_of_uniform_flux_bound {a b r0 : ℝ}
    (hwin : M.IsOffCornerWindow a b) (S : ℕ → Finset (Sym2 M.V))
    (har : a < r0) (hrb : r0 < b) {C : ℝ}
    (hC : ∀ n : ℕ, (S n).card * ((M.betaCrit : ℝ) *
      (2 * ((insert (0 : M.V) (edgeVertices (S n))).card : ℝ) ^ 2)) ≤ C)
    (hfluxConv : ∀ t, Tendsto (fun n => M.windowFlux (S n) t) atTop (𝓝 (M.rhsScalarTwo t)))
    (hmoment : ∀ x ∈ Set.Icc a b,
      Tendsto (fun n => M.windowMoment (S n) x - M.windowMoment (S n) a) atTop
        (𝓝 (M.cutMomentReal 2 x - M.cutMomentReal 2 a)))
    (hrhsCont : ContinuousAt (fun t => M.rhsScalarTwo t) r0)
    (hrhsInt : IntervalIntegrable (fun t => M.rhsScalarTwo t) volume a b) :
    HasDerivAt (fun r => M.cutMomentReal 2 r) (M.rhsScalarTwo r0) r0 := by
  have ha : 0 < a := hwin.1
  have hab : a ≤ b := hwin.2.1
  have hK : IntervalIntegrable (fun r => |deriv M.K r|) volume a b :=
    (M.intervalIntegrable_deriv_K ha hab).abs
  have hG : IntervalIntegrable (fun r => C * |deriv M.K r|) volume a b := hK.const_mul C
  refine M.hasDerivAt_cutMomentReal_two_of_window_majorant hwin S har hrb ?_ hG hfluxConv
    hmoment hrhsCont hrhsInt
  intro n t ht
  have h0 : (0 : ℝ) ≤ |deriv M.K t| := abs_nonneg _
  calc M.windowFlux (S n) t ≤ |M.windowFlux (S n) t| := le_abs_self _
    _ ≤ ((S n).card * ((M.betaCrit : ℝ) *
           (2 * ((insert (0 : M.V) (edgeVertices (S n))).card : ℝ) ^ 2))) * |deriv M.K t| :=
        M.abs_windowFlux_le (S n) t
    _ ≤ C * |deriv M.K t| := by
        exact mul_le_mul_of_nonneg_right (hC n) h0

end SourceModelData

end PercLib.CriticalLRP.Orchestration

end

/-! ## Axiom audit -/

#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.sub_le_sub_false
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.cutFun_clusterVolSqReal_le_self_of_ne_top
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.ae_cutFun_clusterVolSqReal_le_self
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.integrable_flipDiff_cutFun_clusterVolSqReal
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.partialLimitFlux_le_rhsScalarTwo
#print axioms
  PercLib.CriticalLRP.Orchestration.SourceModelData.integral_rhsScalarTwo_eq_sub_of_window_majorant
#print axioms
  PercLib.CriticalLRP.Orchestration.SourceModelData.hasDerivAt_cutMomentReal_two_of_window_majorant
#print axioms
  PercLib.CriticalLRP.Orchestration.SourceModelData.hasDerivAt_cutMomentReal_two_of_envelope
#print axioms
  PercLib.CriticalLRP.Orchestration.SourceModelData.hasDerivAt_cutMomentReal_two_of_uniform_flux_bound
