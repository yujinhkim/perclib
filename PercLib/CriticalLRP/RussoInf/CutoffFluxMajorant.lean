/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
-/

module

/-
Member `m3`, swarm `smwj39frb` — direction (B): the *real* `r`-derivative of the
cutoff first moment, taken at the level of the pivotal flux of the Definition
I.1.5 cutoff law.

Hutchcroft, *Critical long-range percolation I*, arXiv:2508.18807v1, Lemma I.4.1.

## What is proved here (sorry-free, no new axioms)

`RussoInf/RussoDominated.lean` reduces the infinite-volume Russo identity for the
capped cluster volume to a **dominator**: a summable `W : Sym2 V → ℝ` with

  `|c r e| · 2 max m' 0 · P_r(e ∈ touchSet · o) ≤ W e`   for all `r ∈ I`, `e`,

together with continuity/measurability in the parameter.  The point of this file
is that for the cutoff model the dominator is *free*: the cutoff laws increase in
`r`, and `{ω | e ∈ touchSet ω o}` is an increasing event, so `P_r(e ∈ touchSet · o)`
increases in `r`.  Taking the majorant at the **right endpoint** `b` of the
parameter interval therefore dominates every `r < b`, and summability at `b` is
exactly the existing per-vertex degree bound (`sum_activeWeight_incident_le`)
plus finiteness of `E_{β,b}|K_o|` (`summable_abs_weight_touch`).

Nothing here assumes uniformity in the window index, and no sharpness estimate
beyond finiteness of the expected cluster volume at the single parameter `b` is
used.

Uniformity in `e` is never used either, and the derivative scale is the paper's *r-dependent*
`|J'(r)|`, kept as `K' : ℝ → ℝ` with only a bound `K' r ≤ M` on the parameter set.

## Declarations

* `mem_touchSet_mono`, `isIncreasing_touchSet_mem`, `real_touchSet_mono` —
  `{ω | e ∈ touchSet ω o}` is an increasing event, so its probability is monotone in the edge law.
* `cutoffPiFamily_mono`, `cutoff_real_touchSet_mono` — the Definition I.1.5 edge laws and the
  probabilities `P_r(e ∈ touchSet · o)` increase in the cutoff radius `r`.
* `majorant_arith` — the scalar domination step.
* `summable_cutoffFluxMajorant` — the right-endpoint dominating sequence is summable, from the
  per-vertex degree bound `(2⌈b⌉₊+1)^d` and finiteness of `E_{β}|K_o|`.
* `cutoffFluxMajorant_le` — the pointwise inequality `flux weight at r ≤ W` for `r ≤ b`.
* `hasDerivAt_cutoffClusterVol_of_majorant` — **the main theorem**: the `r`-derivative of
  `r ↦ E_{β,r}[cappedClusterVol]` is the infinite pivotal flux, with `hunif` *and* the uniform mass
  bound removed.
* `cutoff_fluxWeight_le` — the same majorant makes the total pivotal mass uniformly bounded on the
  parameter set, i.e. it discharges `hmass` of `hasDerivAt_integral_cappedClusterVol_of_uniformMass`.
* `edgeLen_loop`, `modelProfile_hprof_fails` — a faithfulness caveat of the existing
  `cutoffPiFamily` interface (see below).

## What is *not* proved here

1. **`hvol`** — finiteness of `E_{β,b}|K_o|` at the single parameter `b`.  This is the genuine
   sharpness input of the paper and is *not* derived here (in particular not from
   `cutoffProfile_dominated`: that comparison of first moments is a different direction).
2. **`hcontterm`, `hmeas`** — continuity in the parameter of each individual pivotal-flux term and
   measurability in the parameter of the finite-window fluxes.  Both concern the single trajectory
   `r ↦ P_r`, not uniformity in the window index, which is what `hunif` asked for.  They are not
   discharged here: for the *full* `cappedClusterVol` the term `pivotalFlux (P_r) g e` depends on
   infinitely many coordinates, so its continuity in `r` is not a finite-dimensional statement.
   (The corresponding statement for the *window* functionals `cutFun S g` is finite-dimensional and
   should follow from `pivotalFlux_cutFun`; that is not carried out here.)

## Faithfulness caveat (property of the existing interface)

`Config (Fin d → ℤ) = Set (Sym2 (Fin d → ℤ))` contains the loops `s(x,x)`, and
`edgeLen s(x,x) = 0`.  The hypothesis `hprof` of `cutoffPiFamily` — `0 ≤ cutoffProfile K r (edgeLen e)`
for **every** `e` — therefore fails for the model profile `r ↦ r^{-(d+α)}`, because
`cutoffProfile K r 0 = K 0 − K r = −K r < 0` for `r > 0` (`modelProfile_hprof_fails`).  The interface
needs a loop-free edge set, or edge probabilities vanishing on loops as `cutoffKernel`/`radialKernel`
does.  The theorems of this file do not depend on this beyond inheriting exactly the `hprof` that
`hasDerivAt_integral_cappedClusterVol_cutoff` already assumes.
-/
public import PercLib.CriticalLRP.RussoInf.RussoDominated
public import PercLib.CriticalLRP.CutoffRusso

set_option autoImplicit true

open MeasureTheory Measure Filter Finset
open scoped ENNReal NNReal Topology

@[expose] public section

namespace PercLib.CriticalLRP

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Countable V]

/-! ## The touch set is increasing, and monotone in the law -/

/-- Growing the configuration can only enlarge the cluster, hence the touch set. -/
theorem mem_touchSet_mono {ω ω' : Config V} {o : V} {e : Sym2 V}
    (hsub : ω ⊆ ω') (he : e ∈ touchSet ω o) : e ∈ touchSet ω' o := by
  obtain ⟨v, hv, hcv⟩ := mem_touchSet.mp he
  exact mem_touchSet.mpr ⟨v, hv, cluster_mono (fun e' he' => hsub he') o hcv⟩

/-- `{ω | e ∈ touchSet ω o}` is an increasing event. -/
theorem isIncreasing_touchSet_mem (o : V) (e : Sym2 V) :
    IsIncreasing {ω : Config V | e ∈ touchSet ω o} := by
  intro a b hab ha
  exact mem_touchSet_mono hab ha

/-- Monotonicity in the edge law of the probability that a fixed edge touches the cluster of `o`. -/
theorem real_touchSet_mono {p q : Sym2 V → unitInterval} (hpq : ∀ e, p e ≤ q e) (o : V)
    (e : Sym2 V) :
    (edgeMeasure p).real {ω : Config V | e ∈ touchSet ω o}
      ≤ (edgeMeasure q).real {ω : Config V | e ∈ touchSet ω o} := by
  have hle := edgeMeasure_mono_of_le hpq (measurableSet_touchSet_mem e) (isIncreasing_touchSet_mem o e)
  have htop : (edgeMeasure q) {ω : Config V | e ∈ touchSet ω o} ≠ ⊤ := measure_ne_top _ _
  show ((edgeMeasure p) _).toReal ≤ ((edgeMeasure q) _).toReal
  exact ENNReal.toReal_mono htop hle


/-! ## Monotonicity in the cutoff parameter -/

variable {d : ℕ}

/-- The Definition I.1.5 edge probabilities increase when the cutoff parameter increases,
whenever the profile does (for an antitone profile this is
`FiniteVolume.cutoffProfile_mono_r`). -/
theorem cutoffPiFamily_mono {β : ℝ} (hβ : 0 ≤ β) {K : ℝ → ℝ}
    (hprof : ∀ (r : ℝ) (e : Sym2 (Fin d → ℤ)),
      0 ≤ FiniteVolume.cutoffProfile K r (FiniteVolume.edgeLen e))
    {a b : ℝ}
    (hmono : ∀ e : Sym2 (Fin d → ℤ),
      FiniteVolume.cutoffProfile K a (FiniteVolume.edgeLen e)
        ≤ FiniteVolume.cutoffProfile K b (FiniteVolume.edgeLen e)) :
    ∀ e : Sym2 (Fin d → ℤ),
      cutoffPiFamily (d := d) β K hβ hprof a e ≤ cutoffPiFamily (d := d) β K hβ hprof b e := by
  intro e
  have h := FiniteVolume.longRangeEdgeProbability_mono_J (β := β) hβ (hmono e)
  show ((cutoffPiFamily (d := d) β K hβ hprof a e : unitInterval) : ℝ)
      ≤ ((cutoffPiFamily (d := d) β K hβ hprof b e : unitInterval) : ℝ)
  rw [cutoffPiFamily_coe, cutoffPiFamily_coe]
  exact h

/-- The probability that a fixed edge touches the cluster of `o` is increasing in the cutoff
parameter.  This is the only place where the monotone coupling enters, and it is what makes the
*right endpoint* of a parameter interval a valid dominator for the pivotal flux. -/
theorem cutoff_real_touchSet_mono {β : ℝ} (hβ : 0 ≤ β) {K : ℝ → ℝ}
    (hprof : ∀ (r : ℝ) (e : Sym2 (Fin d → ℤ)),
      0 ≤ FiniteVolume.cutoffProfile K r (FiniteVolume.edgeLen e))
    {a b : ℝ}
    (hmono : ∀ e : Sym2 (Fin d → ℤ),
      FiniteVolume.cutoffProfile K a (FiniteVolume.edgeLen e)
        ≤ FiniteVolume.cutoffProfile K b (FiniteVolume.edgeLen e))
    (o : Fin d → ℤ) (e : Sym2 (Fin d → ℤ)) :
    (edgeMeasure (cutoffPiFamily (d := d) β K hβ hprof a)).real
        {ω : Config (Fin d → ℤ) | e ∈ touchSet ω o}
      ≤ (edgeMeasure (cutoffPiFamily (d := d) β K hβ hprof b)).real
        {ω : Config (Fin d → ℤ) | e ∈ touchSet ω o} :=
  real_touchSet_mono (cutoffPiFamily_mono hβ hprof hmono) o e

/-! ## The right-endpoint majorant of the cutoff pivotal flux -/

/-- Scalar form of the right-endpoint domination. -/
theorem majorant_arith {A M B q q' P Q : ℝ} (hA : 0 ≤ A) (hM : 0 ≤ M)
    (hBle : B ≤ A * q) (hq0 : 0 ≤ q) (hqq' : q ≤ q') (hP0 : 0 ≤ P) (hPQ : P ≤ Q) :
    B * (M * P) ≤ A * M * (q' * Q) := by
  have hq'0 : 0 ≤ q' := le_trans hq0 hqq'
  have h1 : B * (M * P) ≤ (A * q) * (M * P) :=
    mul_le_mul_of_nonneg_right hBle (mul_nonneg hM hP0)
  have h2 : (A * q) * (M * P) ≤ (A * q') * (M * Q) :=
    mul_le_mul (mul_le_mul_of_nonneg_left hqq' hA) (mul_le_mul_of_nonneg_left hPQ hM)
      (mul_nonneg hM hP0) (mul_nonneg hA hq'0)
  calc B * (M * P) ≤ (A * q) * (M * P) := h1
    _ ≤ (A * q') * (M * Q) := h2
    _ = A * M * (q' * Q) := by ring

/-- **The cutoff pivotal-flux majorant.**  On a parameter interval whose right endpoint is `b`, the
flux weight `|c_r(e)| · 2 max m' 0 · P_r(e touches K_o)` is dominated by its value at `b`
restricted to the edges of length at most `b`, summed against an arbitrary law `π` at `b`.

Summability of that dominating sequence is the paper's finite-pivotal-flux input at the single
parameter `b`: the per-vertex degree bound `(2⌈b⌉₊+1)^d` of the cutoff graph together with
`E_{β,b}|K_o| < ∞`. -/
theorem summable_cutoffFluxMajorant (o : Fin d → ℤ) {β K' b : ℝ} (hβ : 0 ≤ β) (hK' : 0 ≤ K')
    (π : Sym2 (Fin d → ℤ) → unitInterval) (m' : ℝ)
    (hvol : ∫⁻ ω : Config (Fin d → ℤ), clusterVol ω o ∂(edgeMeasure π) ≠ ⊤) :
    Summable fun e : Sym2 (Fin d → ℤ) =>
      β * K' * (2 * max m' 0) *
        (if (FiniteVolume.edgeLen e : ℝ) ≤ b then
          (edgeMeasure π).real {ω : Config (Fin d → ℤ) | e ∈ touchSet ω o} else 0) := by
  classical
  set c : Sym2 (Fin d → ℤ) → ℝ :=
    fun e => β * K' * (if (FiniteVolume.edgeLen e : ℝ) ≤ b then (1 : ℝ) else 0) with hcdef
  have hc0 : ∀ e, 0 ≤ c e := by
    intro e
    refine mul_nonneg (mul_nonneg hβ hK') ?_
    split_ifs <;> norm_num
  have hs : Summable fun e : Sym2 (Fin d → ℤ) =>
      |c e| * (edgeMeasure π).real {ω : Config (Fin d → ℤ) | e ∈ touchSet ω o} := by
    refine summable_abs_weight_touch (o := o) (edgeMeasure π) c
      (D := β * K' * ((2 * ⌈b⌉₊ + 1) ^ d : ℕ))
      (mul_nonneg (mul_nonneg hβ hK') (by positivity)) ?_ hvol
    intro x u
    have h :=
      FiniteVolume.sum_activeWeight_incident_le (d := d) x b (β * K') (mul_nonneg hβ hK') u
    refine (le_of_eq ?_).trans h
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [abs_of_nonneg (hc0 e), hcdef]
    exact congrArg
      (fun t => (β * K' * (if (FiniteVolume.edgeLen e : ℝ) ≤ b then (1 : ℝ) else 0)) * t)
      (CutoffFlux.ite_inst_irrel _ _ (1 : ℝ) 0)
  refine (hs.mul_left (2 * max m' 0)).congr fun e => ?_
  rw [abs_of_nonneg (hc0 e)]
  by_cases h : (FiniteVolume.edgeLen e : ℝ) ≤ b
  · simp only [hcdef, ite_eq_left h]; ring
  · simp only [hcdef, ite_eq_right h]; ring

/-- The pointwise domination used by `hasDerivAt_cutoffClusterVol_of_majorant`.

The derivative scale `K' : ℝ → ℝ` is the *r-dependent* `|J'(r)|` of the paper; only a bound
`K' r ≤ M` on the parameter set is needed. -/
theorem cutoffFluxMajorant_le {β r b M : ℝ} (hβ : 0 ≤ β) {K K' : ℝ → ℝ}
    (hprof : ∀ (s : ℝ) (e : Sym2 (Fin d → ℤ)),
      0 ≤ FiniteVolume.cutoffProfile K s (FiniteVolume.edgeLen e))
    {o : Fin d → ℤ} (e : Sym2 (Fin d → ℤ)) (hrb : r ≤ b)
    (hK'0 : 0 ≤ K' r) (hK'M : K' r ≤ M) (m' : ℝ)
    (hPmono : (edgeMeasure (cutoffPiFamily (d := d) β K hβ hprof r)).real
        {ω : Config (Fin d → ℤ) | e ∈ touchSet ω o}
      ≤ (edgeMeasure (cutoffPiFamily (d := d) β K hβ hprof b)).real
        {ω : Config (Fin d → ℤ) | e ∈ touchSet ω o}) :
    |(if (FiniteVolume.edgeLen e : ℝ) ≤ r then
          β * K' r * (1 - longRangeEdgeProbability β
            (FiniteVolume.cutoffProfile K r (FiniteVolume.edgeLen e)))
        else 0)| *
        (2 * max m' 0 *
          (edgeMeasure (cutoffPiFamily (d := d) β K hβ hprof r)).real
            {ω : Config (Fin d → ℤ) | e ∈ touchSet ω o})
      ≤ β * M * (2 * max m' 0) *
        (if (FiniteVolume.edgeLen e : ℝ) ≤ b then
          (edgeMeasure (cutoffPiFamily (d := d) β K hβ hprof b)).real
            {ω : Config (Fin d → ℤ) | e ∈ touchSet ω o} else 0) := by
  have hq0 : 0 ≤ longRangeEdgeProbability β (FiniteVolume.cutoffProfile K r (FiniteVolume.edgeLen e)) :=
    longRangeEdgeProbability_nonneg hβ (hprof r e)
  have hq1 : longRangeEdgeProbability β (FiniteVolume.cutoffProfile K r (FiniteVolume.edgeLen e)) ≤ 1 :=
    longRangeEdgeProbability_le_one hβ (hprof r e)
  have hBle : |(if (FiniteVolume.edgeLen e : ℝ) ≤ r then
        β * K' r * (1 - longRangeEdgeProbability β
          (FiniteVolume.cutoffProfile K r (FiniteVolume.edgeLen e)))
      else 0)|
      ≤ β * M * (if (FiniteVolume.edgeLen e : ℝ) ≤ r then (1 : ℝ) else 0) := by
    by_cases h : (FiniteVolume.edgeLen e : ℝ) ≤ r
    · rw [ite_eq_left h, ite_eq_left h, abs_of_nonneg]
      · refine mul_le_mul (mul_le_mul_of_nonneg_left hK'M hβ) (by linarith) (by linarith)
          (mul_nonneg hβ (le_trans hK'0 hK'M))
      · exact mul_nonneg (mul_nonneg hβ hK'0) (by linarith)
    · rw [ite_eq_right h, ite_eq_right h, abs_zero, mul_zero]
  have hqq' : (if (FiniteVolume.edgeLen e : ℝ) ≤ r then (1 : ℝ) else 0)
      ≤ (if (FiniteVolume.edgeLen e : ℝ) ≤ b then (1 : ℝ) else 0) := by
    by_cases h : (FiniteVolume.edgeLen e : ℝ) ≤ r
    · rw [ite_eq_left h, ite_eq_left (le_trans h hrb)]
    · rw [ite_eq_right h]
      split_ifs <;> norm_num
  have hM : (0 : ℝ) ≤ 2 * max m' 0 := by positivity
  have h := majorant_arith (A := β * M) (M := 2 * max m' 0)
    (B := |(if (FiniteVolume.edgeLen e : ℝ) ≤ r then
        β * K' r * (1 - longRangeEdgeProbability β
          (FiniteVolume.cutoffProfile K r (FiniteVolume.edgeLen e)))
      else 0)|)
    (q := if (FiniteVolume.edgeLen e : ℝ) ≤ r then (1 : ℝ) else 0)
    (q' := if (FiniteVolume.edgeLen e : ℝ) ≤ b then (1 : ℝ) else 0)
    (P := (edgeMeasure (cutoffPiFamily (d := d) β K hβ hprof r)).real
      {ω : Config (Fin d → ℤ) | e ∈ touchSet ω o})
    (Q := (edgeMeasure (cutoffPiFamily (d := d) β K hβ hprof b)).real
      {ω : Config (Fin d → ℤ) | e ∈ touchSet ω o})
    (mul_nonneg hβ (le_trans hK'0 hK'M)) hM hBle (by split_ifs <;> norm_num) hqq'
    measureReal_nonneg hPmono
  refine h.trans_eq ?_
  by_cases hb : (FiniteVolume.edgeLen e : ℝ) ≤ b
  · rw [ite_eq_left hb, ite_eq_left hb]; ring
  · rw [ite_eq_right hb, ite_eq_right hb]; ring

/-! ## Assembly: the cutoff Russo identity without any uniformity hypothesis -/

/-- The derivative scale `K' : ℝ → ℝ` is the paper's `|J'(r)|`; the theorem only needs it
nonnegative and bounded by `M` on the parameter set.

Compare `hasDerivAt_integral_cappedClusterVol_cutoff` (`RussoInf/Exchange.lean`), whose remaining
input is the local *uniform* convergence `hunif` of the finite-window pivotal fluxes, and
`hasDerivAt_integral_cappedClusterVol_of_uniformMass` (`RussoInf/RussoDominated.lean`), whose
remaining input is a bound `B` on the total pivotal mass *uniform* in the parameter.

Here neither is a hypothesis.  The parameter interval only has to lie below a finite `b`: on it the
flux weight is dominated, by the monotone coupling, by its value at `b` restricted to the edges of
length at most `b`, and that dominating sequence is summable as soon as `E_{β,b}|K_o| < ∞` (the
per-vertex degree bound `(2⌈b⌉₊+1)^d` is the repository's `sum_activeWeight_incident_le`).

What remains, and is *named*, is
* `hvol` — finiteness of the expected cluster volume at the single parameter `b` (the genuine
  sharpness input of the paper; nothing about it is assumed uniform in `r` or in the window),
* `hcontterm` — continuity in the parameter of each individual pivotal-flux term,
* `hmeas` — measurability in the parameter of the finite-window fluxes.

The last two are statements about the single trajectory `r ↦ P_r`; neither is uniformity in the
window index, which is what `hunif` asked for. -/
theorem hasDerivAt_cutoffClusterVol_of_majorant
    (o : Fin d → ℤ) (p : ℕ) (n' m' : ℝ) (hm' : 0 ≤ m')
    (S : ℕ → Finset (Sym2 (Fin d → ℤ))) (hSmono : Monotone S)
    (hS : ∀ e : Sym2 (Fin d → ℤ), ∃ n, e ∈ S n)
    {β M : ℝ} (hβ : 0 ≤ β) (hM : 0 ≤ M) {K K' : ℝ → ℝ}
    (hprof : ∀ (r : ℝ) (e : Sym2 (Fin d → ℤ)),
      0 ≤ FiniteVolume.cutoffProfile K r (FiniteVolume.edgeLen e))
    (hprofr : ∀ ⦃a b : ℝ⦄, a ≤ b → ∀ e : Sym2 (Fin d → ℤ),
      FiniteVolume.cutoffProfile K a (FiniteVolume.edgeLen e)
        ≤ FiniteVolume.cutoffProfile K b (FiniteVolume.edgeLen e))
    {I : Set ℝ} (hI : IsOpen I) {r0 : ℝ} (hr0 : r0 ∈ I) {b : ℝ} (hIb : ∀ r ∈ I, r ≤ b)
    (hK'0 : ∀ r ∈ I, 0 ≤ K' r) (hK'M : ∀ r ∈ I, K' r ≤ M)
    (hderivK : ∀ r ∈ I, HasDerivAt K (-(K' r)) r)
    (hne : ∀ r ∈ I, ∀ e : Sym2 (Fin d → ℤ), (FiniteVolume.edgeLen e : ℝ) ≠ r)
    (hvol : ∫⁻ ω : Config (Fin d → ℤ), clusterVol ω o
      ∂(edgeMeasure (cutoffPiFamily (d := d) β K hβ hprof b)) ≠ ⊤)
    (hcontterm : ∀ e : Sym2 (Fin d → ℤ), ∀ r ∈ I,
      ContinuousAt (fun r' => (if (FiniteVolume.edgeLen e : ℝ) ≤ r' then
          β * K' r' * (1 - longRangeEdgeProbability β
            (FiniteVolume.cutoffProfile K r' (FiniteVolume.edgeLen e))) else 0) *
        pivotalFlux (edgeMeasure (cutoffPiFamily (d := d) β K hβ hprof r'))
          (cappedClusterVol o p n' m') e) r)
    (hmeas : ∀ k : ℕ, AEStronglyMeasurable
      (windowPivotalFlux o p n' m' S (cutoffPiFamily (d := d) β K hβ hprof)
        (fun s e => if (FiniteVolume.edgeLen e : ℝ) ≤ s then
          β * K' s * (1 - longRangeEdgeProbability β
            (FiniteVolume.cutoffProfile K s (FiniteVolume.edgeLen e))) else 0) k) volume) :
    HasDerivAt
      (fun r : ℝ => ∫ ω : Config (Fin d → ℤ), cappedClusterVol o p n' m' ω
        ∂(edgeMeasure (cutoffPiFamily (d := d) β K hβ hprof r)))
      (infPivotalFlux o p n' m' (cutoffPiFamily (d := d) β K hβ hprof)
        (fun s e => if (FiniteVolume.edgeLen e : ℝ) ≤ s then
          β * K' s * (1 - longRangeEdgeProbability β
            (FiniteVolume.cutoffProfile K s (FiniteVolume.edgeLen e))) else 0) r0) r0 := by
  classical
  set c : ℝ → Sym2 (Fin d → ℤ) → ℝ := fun s e =>
    if (FiniteVolume.edgeLen e : ℝ) ≤ s then
      β * K' s * (1 - longRangeEdgeProbability β
        (FiniteVolume.cutoffProfile K s (FiniteVolume.edgeLen e))) else 0 with hcdef
  set W : Sym2 (Fin d → ℤ) → ℝ := fun e => β * M * (2 * max m' 0) *
    (if (FiniteVolume.edgeLen e : ℝ) ≤ b then
      (edgeMeasure (cutoffPiFamily (d := d) β K hβ hprof b)).real
        {ω : Config (Fin d → ℤ) | e ∈ touchSet ω o} else 0) with hWdef
  refine hasDerivAt_integral_cappedClusterVol_of_majorant o p n' m' hm' S hSmono hS
    (cutoffPiFamily (d := d) β K hβ hprof) c hI hr0 ?_ W ?_ ?_ ?_ ?_
  · -- the edge derivative, from the rate identity of the proof of Lemma I.4.1
    intro e r hr
    have h := FiniteVolume.hasDerivAt_cutoffEdgeProbability_if (K := K) (K' := K' r)
      (r := r) (s := (FiniteVolume.edgeLen e : ℝ)) (hne r hr e) (hderivK r hr) β
    simp only [hcdef]
    refine h.congr_deriv ?_
    by_cases hs : (FiniteVolume.edgeLen e : ℝ) ≤ r
    · rw [ite_eq_left hs, ite_eq_left hs]
      simp only [longRangeEdgeProbability]
      ring
    · rw [ite_eq_right hs, ite_eq_right hs]
  · -- summability of the right-endpoint majorant
    rw [hWdef]
    exact summable_cutoffFluxMajorant (d := d) o hβ hM _ m' hvol
  · -- pointwise domination of the flux weight
    intro r hr e
    rw [hWdef]
    refine cutoffFluxMajorant_le (d := d) hβ hprof e (hIb r hr) (hK'0 r hr) (hK'M r hr) m' ?_
    exact cutoff_real_touchSet_mono hβ hprof (hprofr (hIb r hr)) o e
  · -- continuity of each pivotal-flux term (named input)
    intro e r hr
    simpa only [hcdef] using hcontterm e r hr
  · -- measurability of the window fluxes (named input)
    intro k
    simpa only [hcdef] using hmeas k

/-! ## The same majorant gives the uniform total pivotal mass for free -/

/-- **The total pivotal mass of the cutoff model is bounded by its value at the right endpoint.**

`fluxWeight o m' π c r` is the total mass `∑'_e |c_r(e)| · 2 max m' 0 · P_r(e ∈ touchSet · o)`.
On a parameter set bounded above by `b` it is at most its value at `b` on the edges of length at
most `b`, whose `tsum` is finite by `summable_cutoffFluxMajorant`.

This is *verbatim* the hypothesis `hmass` of
`hasDerivAt_integral_cappedClusterVol_of_uniformMass` (up to the `K'`-versus-`M` constant), with
`B := ∑' e, W e`.  That hypothesis is therefore not an extra sharpness input: monotonicity of `P_r`
in `r` supplies it, and only `E_{β,b}|K_o| < ∞` is used. -/
theorem cutoff_fluxWeight_le (o : Fin d → ℤ) {β M : ℝ} (hβ : 0 ≤ β) (hM : 0 ≤ M)
    {K K' : ℝ → ℝ}
    (hprof : ∀ (r : ℝ) (e : Sym2 (Fin d → ℤ)),
      0 ≤ FiniteVolume.cutoffProfile K r (FiniteVolume.edgeLen e))
    (hprofr : ∀ ⦃a b : ℝ⦄, a ≤ b → ∀ e : Sym2 (Fin d → ℤ),
      FiniteVolume.cutoffProfile K a (FiniteVolume.edgeLen e)
        ≤ FiniteVolume.cutoffProfile K b (FiniteVolume.edgeLen e))
    {I : Set ℝ} {b : ℝ} (hIb : ∀ r ∈ I, r ≤ b) (m' : ℝ) {r : ℝ} (hr : r ∈ I)
    (hK'0 : 0 ≤ K' r) (hK'M : K' r ≤ M)
    (hvol : ∫⁻ ω : Config (Fin d → ℤ), clusterVol ω o
      ∂(edgeMeasure (cutoffPiFamily (d := d) β K hβ hprof b)) ≠ ⊤) :
    fluxWeight o m' (cutoffPiFamily (d := d) β K hβ hprof)
        (fun s e => if (FiniteVolume.edgeLen e : ℝ) ≤ s then
          β * K' s * (1 - longRangeEdgeProbability β
            (FiniteVolume.cutoffProfile K s (FiniteVolume.edgeLen e))) else 0) r
      ≤ ∑' e : Sym2 (Fin d → ℤ), β * M * (2 * max m' 0) *
          (if (FiniteVolume.edgeLen e : ℝ) ≤ b then
            (edgeMeasure (cutoffPiFamily (d := d) β K hβ hprof b)).real
              {ω : Config (Fin d → ℤ) | e ∈ touchSet ω o} else 0) := by
  classical
  have hW : Summable fun e : Sym2 (Fin d → ℤ) => β * M * (2 * max m' 0) *
      (if (FiniteVolume.edgeLen e : ℝ) ≤ b then
        (edgeMeasure (cutoffPiFamily (d := d) β K hβ hprof b)).real
          {ω : Config (Fin d → ℤ) | e ∈ touchSet ω o} else 0) :=
    summable_cutoffFluxMajorant (d := d) o hβ hM _ m' hvol
  have hnn : ∀ e : Sym2 (Fin d → ℤ),
      0 ≤ |(if (FiniteVolume.edgeLen e : ℝ) ≤ r then
          β * K' r * (1 - longRangeEdgeProbability β
            (FiniteVolume.cutoffProfile K r (FiniteVolume.edgeLen e))) else 0)| *
        (2 * max m' 0 * (edgeMeasure (cutoffPiFamily (d := d) β K hβ hprof r)).real
          {ω : Config (Fin d → ℤ) | e ∈ touchSet ω o}) := fun e =>
    mul_nonneg (abs_nonneg _) (mul_nonneg (by positivity) measureReal_nonneg)
  have hterm : ∀ e : Sym2 (Fin d → ℤ),
      |(if (FiniteVolume.edgeLen e : ℝ) ≤ r then
          β * K' r * (1 - longRangeEdgeProbability β
            (FiniteVolume.cutoffProfile K r (FiniteVolume.edgeLen e))) else 0)| *
        (2 * max m' 0 * (edgeMeasure (cutoffPiFamily (d := d) β K hβ hprof r)).real
          {ω : Config (Fin d → ℤ) | e ∈ touchSet ω o})
      ≤ β * M * (2 * max m' 0) *
          (if (FiniteVolume.edgeLen e : ℝ) ≤ b then
            (edgeMeasure (cutoffPiFamily (d := d) β K hβ hprof b)).real
              {ω : Config (Fin d → ℤ) | e ∈ touchSet ω o} else 0) := fun e =>
    cutoffFluxMajorant_le (d := d) hβ hprof e (hIb r hr) hK'0 hK'M m'
      (cutoff_real_touchSet_mono hβ hprof (hprofr (hIb r hr)) o e)
  have hsum : Summable fun e : Sym2 (Fin d → ℤ) =>
      |(if (FiniteVolume.edgeLen e : ℝ) ≤ r then
          β * K' r * (1 - longRangeEdgeProbability β
            (FiniteVolume.cutoffProfile K r (FiniteVolume.edgeLen e))) else 0)| *
        (2 * max m' 0 * (edgeMeasure (cutoffPiFamily (d := d) β K hβ hprof r)).real
          {ω : Config (Fin d → ℤ) | e ∈ touchSet ω o}) :=
    Summable.of_nonneg_of_le hnn hterm hW
  simpa only [fluxWeight] using (Summable.tsum_le_tsum hterm hsum hW)

/-! ## A faithfulness caveat of the existing cutoff interface -/

/-- `Sym2` contains the loops `s(x,x)`, and the `‖·‖_∞`-length of a loop is `0`. -/
theorem edgeLen_loop {d : ℕ} (x : Fin d → ℤ) : FiniteVolume.edgeLen (s(x, x)) = 0 := by
  rw [FiniteVolume.edgeLen_mk, sub_self]
  simp [FiniteVolume.linfNorm]

/-- **Obstruction.**  The model profile `r ↦ r^{-(d+α)}` (Definition I.1.3, `FiniteVolume.modelProfile`)
does *not* satisfy the nonnegativity hypothesis `hprof` required by `cutoffPiFamily`.  At the loop
`s(x,x)` the length is `0`, and the cutoff profile there is `K 0 − K r = −K r < 0` for `r > 0`.

So `cutoffPiFamily` is not literally the cut-off law of Definition I.1.5 on the loop-carrying
configuration space `Config (Fin d → ℤ) = Set (Sym2 (Fin d → ℤ))`: the interface needs either a loop-free
edge set or an edge probability that vanishes on loops (as `FiniteVolume.cutoffKernel`/`radialKernel`
does).  This is a property of the existing interface, not of the theorems above; their `hprof`
hypothesis is verbatim the one assumed by `hasDerivAt_integral_cappedClusterVol_cutoff` in
`RussoInf/Exchange.lean`. -/
theorem modelProfile_hprof_fails (d : ℕ) :
    ¬ (∀ (r : ℝ) (e : Sym2 (Fin d → ℤ)),
      0 ≤ FiniteVolume.cutoffProfile (FiniteVolume.modelProfile d 1) r (FiniteVolume.edgeLen e)) := by
  intro h
  have hloop := h 1 (s((0 : Fin d → ℤ), (0 : Fin d → ℤ)))
  have hlen : ((FiniteVolume.edgeLen (s((0 : Fin d → ℤ), (0 : Fin d → ℤ))) : ℕ) : ℝ) = 0 := by
    rw [edgeLen_loop]; norm_num
  rw [hlen, FiniteVolume.cutoffProfile_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hloop
  have hexp : (-(d : ℝ) - 1) ≠ 0 := by
    have := Nat.cast_nonneg (α := ℝ) d
    intro hc
    linarith
  have h0 : FiniteVolume.modelProfile d 1 (0 : ℝ) = 0 := by
    simp only [FiniteVolume.modelProfile]
    exact Real.zero_rpow hexp
  have h1 : FiniteVolume.modelProfile d 1 (1 : ℝ) = 1 := by
    simp [FiniteVolume.modelProfile]
  rw [h0, h1] at hloop
  norm_num at hloop

end PercLib.CriticalLRP

/-! ## Axiom audit -/

#print axioms PercLib.CriticalLRP.mem_touchSet_mono
#print axioms PercLib.CriticalLRP.isIncreasing_touchSet_mem
#print axioms PercLib.CriticalLRP.real_touchSet_mono
#print axioms PercLib.CriticalLRP.cutoffPiFamily_mono
#print axioms PercLib.CriticalLRP.cutoff_real_touchSet_mono
#print axioms PercLib.CriticalLRP.majorant_arith
#print axioms PercLib.CriticalLRP.summable_cutoffFluxMajorant
#print axioms PercLib.CriticalLRP.cutoffFluxMajorant_le
#print axioms PercLib.CriticalLRP.hasDerivAt_cutoffClusterVol_of_majorant
#print axioms PercLib.CriticalLRP.cutoff_fluxWeight_le
#print axioms PercLib.CriticalLRP.modelProfile_hprof_fails
