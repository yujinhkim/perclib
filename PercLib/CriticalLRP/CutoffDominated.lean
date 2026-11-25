/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
-/

/-
# Definition I.1.5, the subcritical domination, and the transfer of cluster moments

Source: Tom Hutchcroft, *Critical long-range percolation I: High effective dimension*,
arXiv:2508.18807v1, Definition I.1.5 and p. 7:

  "for every `r < ∞` there exists `ε = ε(r) > 0` such that `J_r(x,y) ≤ (1 − ε)J(x,y)`
   for every `x ≠ y`, so that `P_{β_c,r}` is stochastically dominated by the
   subcritical measure `P_{(1−ε)β_c}`."

`KernelGeometry.cutoffProfile_dominated` proves the one-point inequality
`cutoffProfile K r s ≤ (1 − K r / K 1) * K s` for `s ≥ 1`, and
`LatticeGeometry.cutoffKernel_lattice_dominated` instantiates it for `cutoffKernel`
and `radialKernel` as functions `V → V → ℝ`.  What is missing — and what this file
supplies — is the whole chain from that pointwise scalar fact to the *law* and to the
*cluster moments*:

* `uncutKernel_shift` — the uncut lattice kernel is translation invariant;
* `cutoffCoefficient_mem` — `ε = K r / K 1` is in `(0,1]` and `1 − ε < 1`, so the
  parameter `β(1 − ε)` is *strictly* smaller than `β` when `β > 0`;
* `cutoffSymKernel_le_scaled` — the edge-by-edge inequality for the genuine loop-safe
  kernel `CutoffKernel.cutoffSymKernel` on `Sym2 (ℤ^d)` against the genuine uncut
  kernel `kernelJ (K ∘ ‖·‖_∞)`, for **every** edge of `Sym2 (ℤ^d)` (loops included);
* `bernoulliEdgeProb_cutoff_le_scaled` — the resulting per-edge comparison of open
  probabilities at parameter `β` versus `β(1 − ε)`;
* `longRangeMeasure_cutoff_dominated` — stochastic domination on increasing events,
  `P_{β,r} ⪯ P_{β(1−ε)}`;
* `infiniteClusterProb_cutoff_le`, `…_eq_zero` — the literal conclusion "`P_{β,r}` is
  dominated by a subcritical measure": if the uncut law at `β(1−ε)` has no percolation,
  neither does `P_{β,r}`;
* `lintegral_clusterVol_cutoff_le` and `…_ne_top` — the first cluster moment of the
  cutoff law is bounded by, and finite whenever finite for, the uncut first moment at
  the reduced parameter `β(1−ε)`;
* `uncutKernel_rootIndependent` — root-independence of the uncut first moment, free
  from translation invariance, so that the only upstream input is finiteness at one
  point;
* `cutoff_clusterVol_sq_ne_top` and `cutoff_joint_windowMoment_ne_top` — the finite
  first moment at `β(1−ε)` gives the cutoff second and joint window moments, through
  `CountableProduct/MonotoneMoments`.

## Why the loop-safe kernel matters

`Config (Fin d → ℤ) = Set (Sym2 (Fin d → ℤ))` contains the loops `s(x,x)`.  The
existing `RussoInf.Exchange.cutoffPiFamily` assigns the loop `s(x,x)` the probability
`1 − exp(−β (K 0 − K r))`, whose profile `K 0 − K r` is negative for the model profile
(`CutoffFluxMajorant.modelProfile_hprof_fails`), so that interface is vacuous at the
source's own kernel unless a positivity hypothesis the source does not satisfy is
assumed.  `CutoffKernel.cutoffSymKernel` instead vanishes on loops, exactly as the
paper's factor `1(x ≠ y)` requires, and `K 0 = 0` makes the uncut kernel agree with it
there; every statement below is stated for `cutoffSymKernel` and is non-vacuous for
`r ↦ r^{-(d+α)}`.

## Not claimed

This is a *dominance* construction.  It does **not** prove finiteness of any uncut
first moment: the premise `hfin` of the moment-transfer theorems is exactly "the uncut
mean at the reduced parameter `β(1−ε)` is finite", i.e. subcritical finiteness of the
mean, and nothing here manufactures it.  In particular this file does not discharge
the `hvol` input of `CutoffFluxMajorant`.

No new definitions, no `sorry`, no `admit`, no `native_decide`, no custom axioms.
-/
module

public import PercLib.CriticalLRP.CutoffLimit
public import PercLib.CriticalLRP.CountableProduct.MonotoneMoments

set_option autoImplicit true

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

@[expose] public section

open MeasureTheory Measure ProbabilityTheory unitInterval
open scoped ENNReal

namespace PercLib.CriticalLRP.CutoffDominated

open PercLib.CriticalLRP.FiniteVolume CutoffKernel CutoffLimit TreeExpansion

variable {d : ℕ} {K : ℝ → ℝ}

/-! ## Translation invariance of the uncut lattice kernel -/

/-- The uncut lattice kernel `J(x,y) = K(‖y − x‖_∞)` of a radial profile is
translation invariant. -/
theorem uncutKernel_shift (K : ℝ → ℝ) (a : Fin d → ℤ) (e : Sym2 (Fin d → ℤ)) :
    kernelJ (fun y : Fin d → ℤ => K ((linfNorm y : ℕ) : ℝ)) (profile_even K)
        (Sym2.map (fun x => x + a) e)
      = kernelJ (fun y : Fin d → ℤ => K ((linfNorm y : ℕ) : ℝ)) (profile_even K) e := by
  induction e using Sym2.ind with
  | _ x y =>
    rw [Sym2.map_mk]
    show K ((linfNorm ((y + a) - (x + a)) : ℕ) : ℝ) = K ((linfNorm (y - x) : ℕ) : ℝ)
    rw [show (y + a) - (x + a) = y - x by abel]

/-! ## The coefficient `1 − K r / K 1` -/

/-- **The coefficient of Definition I.1.5**: for an antitone positive profile and
`r ≥ 1`, `ε = K r / K 1` is positive, so `1 − ε ∈ [0,1)` is an admissible rescaling of
the parameter. -/
theorem cutoffCoefficient_mem (hK : AntitoneOn K (Set.Ioi 0)) {r : ℝ} (hr : 1 ≤ r)
    (hKr : 0 < K r) (hK1 : 0 < K 1) :
    0 ≤ 1 - K r / K 1 ∧ 1 - K r / K 1 < 1 ∧ K r / K 1 ≤ 1 := by
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hKr1 : K r ≤ K 1 := hK (Set.mem_Ioi.mpr zero_lt_one) (Set.mem_Ioi.mpr hr0) hr
  have hεpos : 0 < K r / K 1 := div_pos hKr hK1
  have hε1 : K r / K 1 ≤ 1 := by rw [div_le_one hK1]; exact hKr1
  constructor
  · linarith
  · constructor <;> linarith

/-- The rescaling coefficient as a nonnegative real. -/
theorem cutoffCoefficient_nonneg (hK : AntitoneOn K (Set.Ioi 0)) {r : ℝ} (hr : 1 ≤ r)
    (hKr : 0 < K r) (hK1 : 0 < K 1) : 0 ≤ 1 - K r / K 1 :=
  (cutoffCoefficient_mem hK hr hKr hK1).1

/-- **The reduced parameter is strictly smaller.**  Because `ε = K r / K 1 > 0`, the
parameter `β(1 − ε)` of the dominating law is strictly less than `β` whenever `β > 0`.
This is what makes the domination of Definition I.1.5 *subcritical* rather than trivial
at the same parameter. -/
theorem cutoff_parameter_lt (hK : AntitoneOn K (Set.Ioi 0)) {r : ℝ} (hr : 1 ≤ r)
    (hKr : 0 < K r) (hK1 : 0 < K 1) {β : NNReal} (hβ : 0 < β) :
    β * NNReal.mk (1 - K r / K 1) (cutoffCoefficient_nonneg hK hr hKr hK1) < β := by
  have hc : (NNReal.mk (1 - K r / K 1) (cutoffCoefficient_nonneg hK hr hKr hK1) : NNReal) < 1 := by
    rw [← NNReal.coe_lt_coe, NNReal.coe_mk, NNReal.coe_one]
    exact (cutoffCoefficient_mem hK hr hKr hK1).2.1
  simpa using mul_lt_mul_of_pos_left hc hβ

/-! ## Edge-by-edge domination of the loop-safe cut-off kernel -/

/-- **Definition I.1.5, edge by edge, for the loop-safe kernel.**
For `r ≥ 1` the cut-off kernel `J_r` of Definition I.1.5 is dominated by
`(1 − K r / K 1) J` on **every** unordered pair of `ℤ^d`, loops included.

The content is the lattice fact `1 ≤ ‖x − y‖_∞` for `x ≠ y`
(`LatticeGeometry.one_le_latticeDist`), which supplies the hypothesis `1 ≤ s` of
`KernelGeometry.cutoffProfile_dominated`; on loops both kernels vanish, which uses
`K 0 = 0`. -/
theorem cutoffSymKernel_le_scaled (hK : AntitoneOn K (Set.Ioi 0))
    (hKnn : ∀ t, 0 < t → 0 ≤ K t) (hK0 : K 0 = 0)
    {r : ℝ} (hr : 1 ≤ r) (hKr : 0 < K r) (hK1 : 0 < K 1) (e : Sym2 (Fin d → ℤ)) :
    cutoffSymKernel K d r e
      ≤ (1 - K r / K 1) * kernelJ (fun y : Fin d → ℤ => K ((linfNorm y : ℕ) : ℝ))
          (profile_even K) e := by
  induction e using Sym2.ind with
  | _ x y =>
    show cutoffSymKernel K d r s(x, y)
      ≤ (1 - K r / K 1) * K ((linfNorm (y - x) : ℕ) : ℝ)
    rw [show ((linfNorm (y - x) : ℕ) : ℝ) = latticeDist x y from by
      unfold latticeDist
      rw [show y - x = -(x - y) by abel, linfNorm_neg]]
    rw [cutoffSymKernel_mk]
    by_cases hxy : x = y
    · rw [ite_eq_left hxy]
      have hzero : latticeDist x y = 0 := by subst hxy; exact latticeDist_self x
      rw [hzero, hK0]
      simp
    · rw [ite_eq_right hxy]
      exact cutoffProfile_dominated hK hKnn (one_le_latticeDist hxy) hr hKr hK1

/-! ## The comparison of open probabilities -/

/-- `1 − e^{−β J} ≤ 1 − e^{−β' J'}` as soon as `β J ≤ β' J'`. -/
theorem bernoulliEdgeProb_le_of_mul_le {V : Type*} [Countable V] {J J' : Sym2 V → ℝ}
    (hJ : ∀ e, 0 ≤ J e) (hJ' : ∀ e, 0 ≤ J' e) {β β' : NNReal} {e : Sym2 V}
    (h : (β : ℝ) * J e ≤ (β' : ℝ) * J' e) :
    bernoulliEdgeProb J hJ β e ≤ bernoulliEdgeProb J' hJ' β' e := by
  rw [← Subtype.coe_le_coe, bernoulliEdgeProb_coe, bernoulliEdgeProb_coe]
  have hexp : Real.exp (-((β' : ℝ) * J' e)) ≤ Real.exp (-((β : ℝ) * J e)) :=
    Real.exp_le_exp.mpr (by linarith)
  linarith

/-- **The per-edge comparison of the paper**: the cut-off open probability at parameter
`β` is at most the uncut open probability at the reduced parameter `β(1 − K r / K 1)`. -/
theorem bernoulliEdgeProb_cutoff_le_scaled (hK : AntitoneOn K (Set.Ioi 0))
    (hKnn : ∀ t, 0 < t → 0 ≤ K t) (hK0 : K 0 = 0)
    {r : ℝ} (hr : 1 ≤ r) (hKr : 0 < K r) (hK1 : 0 < K 1) (β : NNReal)
    (e : Sym2 (Fin d → ℤ)) :
    bernoulliEdgeProb (cutoffSymKernel K d r) (cutoffSymKernel_nonneg' hK d r) β e
      ≤ bernoulliEdgeProb
          (kernelJ (fun y : Fin d → ℤ => K ((linfNorm y : ℕ) : ℝ)) (profile_even K))
          (uncutKernel_nonneg hKnn hK0 d)
          (β * NNReal.mk (1 - K r / K 1) (cutoffCoefficient_nonneg hK hr hKr hK1)) e := by
  refine bernoulliEdgeProb_le_of_mul_le (cutoffSymKernel_nonneg' hK d r)
    (uncutKernel_nonneg hKnn hK0 d) ?_
  have hdom := cutoffSymKernel_le_scaled hK hKnn hK0 hr hKr hK1 e
  have hcoef : ((β * NNReal.mk (1 - K r / K 1) (cutoffCoefficient_nonneg hK hr hKr hK1) : NNReal) : ℝ)
      = (β : ℝ) * (1 - K r / K 1) := by
    simp only [NNReal.coe_mul, NNReal.coe_mk]
  rw [hcoef]
  have hβ : (0 : ℝ) ≤ (β : ℝ) := β.2
  nlinarith [hdom, hβ]

/-- **The exact pointwise edge comparison used by every transfer below**, as a single
`∀ e` statement (so the comparison at each edge/site is the same named term): the
cut-off open probability at parameter `β` is dominated, edge by edge, by the uncut open
probability at the reduced parameter `β(1 − K r / K 1)`. -/
theorem cutoff_edgeComparison (hK : AntitoneOn K (Set.Ioi 0))
    (hKnn : ∀ t, 0 < t → 0 ≤ K t) (hK0 : K 0 = 0)
    {r : ℝ} (hr : 1 ≤ r) (hKr : 0 < K r) (hK1 : 0 < K 1) (β : NNReal) :
    ∀ e : Sym2 (Fin d → ℤ),
      bernoulliEdgeProb (cutoffSymKernel K d r) (cutoffSymKernel_nonneg' hK d r) β e
        ≤ bernoulliEdgeProb
            (kernelJ (fun y : Fin d → ℤ => K ((linfNorm y : ℕ) : ℝ)) (profile_even K))
            (uncutKernel_nonneg hKnn hK0 d)
            (β * NNReal.mk (1 - K r / K 1) (cutoffCoefficient_nonneg hK hr hKr hK1)) e :=
  fun e => bernoulliEdgeProb_cutoff_le_scaled hK hKnn hK0 hr hKr hK1 β e

/-! ## Stochastic domination of the laws -/

/-- **`P_{β,r} ⪯ P_{β(1−ε)}`**: every increasing measurable event is at least as likely
under the uncut law at the reduced parameter `β(1 − K r / K 1)` as under the cut-off law
at parameter `β`. -/
theorem longRangeMeasure_cutoff_dominated (hK : AntitoneOn K (Set.Ioi 0))
    (hKnn : ∀ t, 0 < t → 0 ≤ K t) (hK0 : K 0 = 0)
    {r : ℝ} (hr : 1 ≤ r) (hKr : 0 < K r) (hK1 : 0 < K 1) (β : NNReal)
    {A : Set (Config (Fin d → ℤ))} (hA : MeasurableSet A) (hinc : IsIncreasing A) :
    longRangeMeasure (cutoffSymKernel K d r) (cutoffSymKernel_nonneg' hK d r) β A
      ≤ longRangeMeasure
          (kernelJ (fun y : Fin d → ℤ => K ((linfNorm y : ℕ) : ℝ)) (profile_even K))
          (uncutKernel_nonneg hKnn hK0 d)
          (β * NNReal.mk (1 - K r / K 1) (cutoffCoefficient_nonneg hK hr hKr hK1)) A :=
  edgeMeasure_mono_of_le
    (fun e => bernoulliEdgeProb_cutoff_le_scaled hK hKnn hK0 hr hKr hK1 β e) hA hinc

/-- **The cut-off law is dominated by a subcritical law.**  If the uncut law at the
reduced parameter `β(1 − K r / K 1)` has no infinite cluster, neither does `P_{β,r}`.
This is the literal conclusion drawn on p. 7 of the paper. -/
theorem infiniteClusterProb_cutoff_le (hK : AntitoneOn K (Set.Ioi 0))
    (hKnn : ∀ t, 0 < t → 0 ≤ K t) (hK0 : K 0 = 0)
    {r : ℝ} (hr : 1 ≤ r) (hKr : 0 < K r) (hK1 : 0 < K 1) (β : NNReal) :
    infiniteClusterProb (cutoffSymKernel K d r) (cutoffSymKernel_nonneg' hK d r) β
      ≤ infiniteClusterProb
          (kernelJ (fun y : Fin d → ℤ => K ((linfNorm y : ℕ) : ℝ)) (profile_even K))
          (uncutKernel_nonneg hKnn hK0 d)
          (β * NNReal.mk (1 - K r / K 1) (cutoffCoefficient_nonneg hK hr hKr hK1)) :=
  longRangeMeasure_cutoff_dominated hK hKnn hK0 hr hKr hK1 β
    measurableSet_existsInfiniteCluster isIncreasing_existsInfiniteCluster

/-- **No percolation above cutoff**: if the uncut law at `β(1 − ε)` has no infinite
cluster, then `P_{β,r}` has none. -/
theorem infiniteClusterProb_cutoff_eq_zero (hK : AntitoneOn K (Set.Ioi 0))
    (hKnn : ∀ t, 0 < t → 0 ≤ K t) (hK0 : K 0 = 0)
    {r : ℝ} (hr : 1 ≤ r) (hKr : 0 < K r) (hK1 : 0 < K 1) (β : NNReal)
    (hsub : infiniteClusterProb
          (kernelJ (fun y : Fin d → ℤ => K ((linfNorm y : ℕ) : ℝ)) (profile_even K))
          (uncutKernel_nonneg hKnn hK0 d)
          (β * NNReal.mk (1 - K r / K 1) (cutoffCoefficient_nonneg hK hr hKr hK1)) = 0) :
    infiniteClusterProb (cutoffSymKernel K d r) (cutoffSymKernel_nonneg' hK d r) β = 0 :=
  le_antisymm (by rw [← hsub]; exact infiniteClusterProb_cutoff_le hK hKnn hK0 hr hKr hK1 β)
    zero_le

/-! ## Transfer of the first cluster moment -/

/-- **The cut-off first moment is bounded by the uncut first moment at the reduced
parameter.** -/
theorem lintegral_clusterVol_cutoff_le (hK : AntitoneOn K (Set.Ioi 0))
    (hKnn : ∀ t, 0 < t → 0 ≤ K t) (hK0 : K 0 = 0)
    {r : ℝ} (hr : 1 ≤ r) (hKr : 0 < K r) (hK1 : 0 < K 1) (β : NNReal)
    (o : Fin d → ℤ) :
    (∫⁻ ω, clusterVol ω o ∂(longRangeMeasure (cutoffSymKernel K d r)
        (cutoffSymKernel_nonneg' hK d r) β))
      ≤ ∫⁻ ω, clusterVol ω o ∂(longRangeMeasure
          (kernelJ (fun y : Fin d → ℤ => K ((linfNorm y : ℕ) : ℝ)) (profile_even K))
          (uncutKernel_nonneg hKnn hK0 d)
          (β * NNReal.mk (1 - K r / K 1) (cutoffCoefficient_nonneg hK hr hKr hK1))) :=
  lintegral_clusterVol_mono_of_le
    (fun e => bernoulliEdgeProb_cutoff_le_scaled hK hKnn hK0 hr hKr hK1 β e) o

/-- **The only upstream input.**  If the uncut law at the reduced parameter
`β(1 − K r / K 1)` has finite expected cluster volume, then the cut-off first moment at
parameter `β` is finite. -/
theorem lintegral_clusterVol_cutoff_ne_top (hK : AntitoneOn K (Set.Ioi 0))
    (hKnn : ∀ t, 0 < t → 0 ≤ K t) (hK0 : K 0 = 0)
    {r : ℝ} (hr : 1 ≤ r) (hKr : 0 < K r) (hK1 : 0 < K 1) (β : NNReal)
    (o : Fin d → ℤ)
    (hfin : (∫⁻ ω, clusterVol ω o ∂(longRangeMeasure
          (kernelJ (fun y : Fin d → ℤ => K ((linfNorm y : ℕ) : ℝ)) (profile_even K))
          (uncutKernel_nonneg hKnn hK0 d)
          (β * NNReal.mk (1 - K r / K 1) (cutoffCoefficient_nonneg hK hr hKr hK1)))) ≠ ∞) :
    (∫⁻ ω, clusterVol ω o ∂(longRangeMeasure (cutoffSymKernel K d r)
        (cutoffSymKernel_nonneg' hK d r) β)) ≠ ∞ :=
  ne_top_of_le_ne_top hfin
    (lintegral_clusterVol_cutoff_le hK hKnn hK0 hr hKr hK1 β o)

/-! ## Root-independence of the uncut first moment -/

/-- The uncut first moment is independent of the base point: this is where translation
invariance of `K ∘ ‖·‖_∞` is used, so that finiteness at one point is finiteness at
every point. -/
theorem uncutKernel_rootIndependent (hKnn : ∀ t, 0 < t → 0 ≤ K t) (hK0 : K 0 = 0)
    (β : NNReal) (a o : Fin d → ℤ) :
    (∫⁻ ω, clusterVol ω a ∂(edgeMeasure (bernoulliEdgeProb
        (kernelJ (fun y : Fin d → ℤ => K ((linfNorm y : ℕ) : ℝ)) (profile_even K))
        (uncutKernel_nonneg hKnn hK0 d) β)))
      = ∫⁻ ω, clusterVol ω o ∂(edgeMeasure (bernoulliEdgeProb
          (kernelJ (fun y : Fin d → ℤ => K ((linfNorm y : ℕ) : ℝ)) (profile_even K))
          (uncutKernel_nonneg hKnn hK0 d) β)) := by
  have hinv := bernoulliEdgeProb_shift (uncutKernel_shift K)
    (uncutKernel_nonneg hKnn hK0 d) β
  rw [lintegral_clusterVol_shift_invariant _ hinv a,
    lintegral_clusterVol_shift_invariant _ hinv o]

/-- **The root comparison in `≤` form** (not an equality hypothesis): the dominating
uncut first moment at `a` is bounded by its value at the labelled root `o`.  This is a
*theorem*, derived from translation invariance, so no uniform-in-the-root finiteness is
ever assumed. -/
theorem uncutKernel_rootComparison (hKnn : ∀ t, 0 < t → 0 ≤ K t) (hK0 : K 0 = 0)
    (β : NNReal) (o : Fin d → ℤ) :
    ∀ a : Fin d → ℤ,
      (∫⁻ ω, clusterVol ω a ∂(edgeMeasure (bernoulliEdgeProb
        (kernelJ (fun y : Fin d → ℤ => K ((linfNorm y : ℕ) : ℝ)) (profile_even K))
        (uncutKernel_nonneg hKnn hK0 d) β)))
        ≤ ∫⁻ ω, clusterVol ω o ∂(edgeMeasure (bernoulliEdgeProb
          (kernelJ (fun y : Fin d → ℤ => K ((linfNorm y : ℕ) : ℝ)) (profile_even K))
          (uncutKernel_nonneg hKnn hK0 d) β)) :=
  fun a => le_of_eq (uncutKernel_rootIndependent hKnn hK0 β a o)

/-- The root comparison **at every pair of sites**, still in `≤` form: this is what the
joint window moment consumes, once for each `y` in the window. -/
theorem uncutKernel_rootComparison_any (hKnn : ∀ t, 0 < t → 0 ≤ K t) (hK0 : K 0 = 0)
    (β : NNReal) :
    ∀ a b : Fin d → ℤ,
      (∫⁻ ω, clusterVol ω a ∂(edgeMeasure (bernoulliEdgeProb
        (kernelJ (fun y : Fin d → ℤ => K ((linfNorm y : ℕ) : ℝ)) (profile_even K))
        (uncutKernel_nonneg hKnn hK0 d) β)))
        ≤ ∫⁻ ω, clusterVol ω b ∂(edgeMeasure (bernoulliEdgeProb
          (kernelJ (fun y : Fin d → ℤ => K ((linfNorm y : ℕ) : ℝ)) (profile_even K))
          (uncutKernel_nonneg hKnn hK0 d) β)) :=
  fun a b => le_of_eq (uncutKernel_rootIndependent hKnn hK0 β a b)

/-! ## Transfer of the second and joint window moments

The reductions below use **only the `≤`-form root comparison**
`∀ a, E_κ|K_a| ≤ E_κ|K_o|` (the `hpq` root comparison at the labelled root `o`), not an
equality hypothesis, and they consume the pointwise edge comparison `hpq` explicitly.
The finite mean at the labelled root is `hfin`; no uniform-in-the-root finiteness is
assumed, because the cubic bound is applied to the dominating law at each root that
appears, using the root comparison at that site. -/

/-- **Isolated monotonicity comparison for the second cluster moment**: pointwise
domination of the edge laws gives, at a fixed root, domination of the second moment. -/
theorem lintegral_clusterVol_sq_le_of_pointwise {V : Type*} [Countable V]
    {π κ : Sym2 V → unitInterval} (hpq : ∀ e, π e ≤ κ e) (o : V) :
    (∫⁻ ω, clusterVol ω o * clusterVol ω o ∂(edgeMeasure π))
      ≤ ∫⁻ ω, clusterVol ω o * clusterVol ω o ∂(edgeMeasure κ) :=
  lintegral_clusterVol_sq_mono_of_le hpq o

/-- **Second moment transfer, fixed root, `≤`-form root comparison only.**
`hpq` is the pointwise edge comparison; `hroot` is the root comparison *at the labelled
root* `o`; `hfin` is finiteness of the dominating first moment at `o`.  The bound is
`E_π|K_o|² ≤ E_κ|K_o|² ≤ (E_κ|K_o|)³`, so the cubic bound is applied to the dominating
law at `o` and nowhere else. -/
theorem lintegral_clusterVol_sq_ne_top_of_pointwise {V : Type*} [Countable V]
    {π κ : Sym2 V → unitInterval} (hpq : ∀ e, π e ≤ κ e) (hκ : ∀ e, κ e < 1) (o : V)
    (hroot : ∀ a : V, (∫⁻ ω, clusterVol ω a ∂(edgeMeasure κ))
      ≤ ∫⁻ ω, clusterVol ω o ∂(edgeMeasure κ))
    (hfin : (∫⁻ ω, clusterVol ω o ∂(edgeMeasure κ)) ≠ ⊤) :
    (∫⁻ ω, clusterVol ω o * clusterVol ω o ∂(edgeMeasure π)) ≠ ⊤ := by
  have hcube : (∫⁻ ω, clusterVol ω o * clusterVol ω o ∂(edgeMeasure κ))
      ≤ (∫⁻ ω, clusterVol ω o ∂(edgeMeasure κ))
          * (∫⁻ ω, clusterVol ω o ∂(edgeMeasure κ))
          * (∫⁻ ω, clusterVol ω o ∂(edgeMeasure κ)) :=
    lintegral_clusterVol_sq_le_cube κ hκ o hroot
  refine ne_top_of_le_ne_top ?_ ((lintegral_clusterVol_sq_le_of_pointwise hpq o).trans hcube)
  exact ENNReal.mul_ne_top (ENNReal.mul_ne_top hfin hfin) hfin

/-- **Joint window moment transfer, fixed root.**  `hrootAny` is the root comparison
*at each site* `y ∈ B` (and at `o`), used to apply the cubic bound to the dominating law
at every root that occurs; `hfin` is finiteness at the labelled root `o` only. -/
theorem joint_windowMoment_ne_top_of_pointwise {V : Type*} [Countable V]
    {π κ : Sym2 V → unitInterval} (hpq : ∀ e, π e ≤ κ e) (hκ : ∀ e, κ e < 1) (o : V)
    (B : Finset V)
    (hrootAny : ∀ a b : V, (∫⁻ ω, clusterVol ω a ∂(edgeMeasure κ))
      ≤ ∫⁻ ω, clusterVol ω b ∂(edgeMeasure κ))
    (hfin : (∫⁻ ω, clusterVol ω o ∂(edgeMeasure κ)) ≠ ⊤) :
    (∫⁻ ω, clusterVol ω o * ∑ y ∈ B, clusterVol ω y ∂(edgeMeasure π)) ≠ ⊤ := by
  have h1 : ∀ a : V, (∫⁻ ω, clusterVol ω a ∂(edgeMeasure κ)) ≠ ⊤ := fun a =>
    ne_top_of_le_ne_top hfin (hrootAny a o)
  have hsecond : ∀ a : V,
      (∫⁻ ω, clusterVol ω a * clusterVol ω a ∂(edgeMeasure κ)) ≠ ⊤ := by
    intro a
    refine ne_top_of_le_ne_top ?_ (lintegral_clusterVol_sq_le_cube κ hκ a (hrootAny · a))
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (h1 a) (h1 a)) (h1 a)
  have hdom : (∫⁻ ω, clusterVol ω o * ∑ y ∈ B, clusterVol ω y ∂(edgeMeasure π))
      ≤ ∑ y ∈ B, ((∫⁻ ω, clusterVol ω o * clusterVol ω o ∂(edgeMeasure κ)) +
        ∫⁻ ω, clusterVol ω y * clusterVol ω y ∂(edgeMeasure κ)) := by
    have hb := (joint_windowMoment_le_sum_second_moments π o B).trans
      (Finset.sum_le_sum fun y _ => by
        have h0 : (∫⁻ ω, Percolation.cardFun (cluster ω o) *
            Percolation.cardFun (cluster ω o) ∂(edgeMeasure π)) ≤
            ∫⁻ ω, clusterVol ω o * clusterVol ω o ∂(edgeMeasure κ) := by
          simpa only [Percolation.cardFun_eq_encard] using
            lintegral_clusterVol_sq_le_of_pointwise hpq o
        have hy : (∫⁻ ω, Percolation.cardFun (cluster ω y) *
            Percolation.cardFun (cluster ω y) ∂(edgeMeasure π)) ≤
            ∫⁻ ω, clusterVol ω y * clusterVol ω y ∂(edgeMeasure κ) := by
          simpa only [Percolation.cardFun_eq_encard] using
            lintegral_clusterVol_sq_le_of_pointwise hpq y
        exact add_le_add h0 hy)
    simpa only [Percolation.cardFun_eq_encard] using hb
  refine ne_top_of_le_ne_top ?_ hdom
  rw [ENNReal.sum_ne_top]
  intro y _
  exact ENNReal.add_ne_top.mpr ⟨hsecond o, hsecond y⟩

/-- **Second cluster moment of the cut-off law**, from the finite uncut first moment at
the reduced parameter only, via the `≤`-form root comparison and the cubic bound on the
dominating law. -/
theorem cutoff_clusterVol_sq_ne_top (hK : AntitoneOn K (Set.Ioi 0))
    (hKnn : ∀ t, 0 < t → 0 ≤ K t) (hK0 : K 0 = 0)
    {r : ℝ} (hr : 1 ≤ r) (hKr : 0 < K r) (hK1 : 0 < K 1) (β : NNReal)
    (o : Fin d → ℤ)
    (hfin : (∫⁻ ω, clusterVol ω o ∂(longRangeMeasure
          (kernelJ (fun y : Fin d → ℤ => K ((linfNorm y : ℕ) : ℝ)) (profile_even K))
          (uncutKernel_nonneg hKnn hK0 d)
          (β * NNReal.mk (1 - K r / K 1) (cutoffCoefficient_nonneg hK hr hKr hK1)))) ≠ ∞) :
    (∫⁻ ω, clusterVol ω o * clusterVol ω o ∂(longRangeMeasure (cutoffSymKernel K d r)
        (cutoffSymKernel_nonneg' hK d r) β)) ≠ ∞ := by
  simp only [longRangeMeasure] at hfin ⊢
  exact lintegral_clusterVol_sq_ne_top_of_pointwise
    (cutoff_edgeComparison hK hKnn hK0 hr hKr hK1 β)
    (fun e => bernoulliEdgeProb_lt_one _ _ e) o
    (uncutKernel_rootComparison hKnn hK0 _ o) hfin

/-- **Joint window moment of the cut-off law**, under the same premise, with the root
comparison displayed at each site. -/
theorem cutoff_joint_windowMoment_ne_top (hK : AntitoneOn K (Set.Ioi 0))
    (hKnn : ∀ t, 0 < t → 0 ≤ K t) (hK0 : K 0 = 0)
    {r : ℝ} (hr : 1 ≤ r) (hKr : 0 < K r) (hK1 : 0 < K 1) (β : NNReal)
    (o : Fin d → ℤ) (B : Finset (Fin d → ℤ))
    (hfin : (∫⁻ ω, clusterVol ω o ∂(longRangeMeasure
          (kernelJ (fun y : Fin d → ℤ => K ((linfNorm y : ℕ) : ℝ)) (profile_even K))
          (uncutKernel_nonneg hKnn hK0 d)
          (β * NNReal.mk (1 - K r / K 1) (cutoffCoefficient_nonneg hK hr hKr hK1)))) ≠ ∞) :
    (∫⁻ ω, clusterVol ω o * ∑ y ∈ B, clusterVol ω y ∂(longRangeMeasure
        (cutoffSymKernel K d r) (cutoffSymKernel_nonneg' hK d r) β)) ≠ ∞ := by
  simp only [longRangeMeasure] at hfin ⊢
  exact joint_windowMoment_ne_top_of_pointwise
    (cutoff_edgeComparison hK hKnn hK0 hr hKr hK1 β)
    (fun e => bernoulliEdgeProb_lt_one _ _ e) o B
    (uncutKernel_rootComparison_any hKnn hK0 _) hfin

/-! ## Compatibility with the `V → V → ℝ` kernels of `KernelGeometry` -/

/-- The loop-safe `Sym2`-kernel `cutoffSymKernel` and the two-variable kernel
`FiniteVolume.cutoffKernel` agree on every non-loop edge of `ℤ^d`.  This is the exact
sense in which the edge-by-edge comparison above is the `Sym2` form of
`KernelGeometry.cutoffKernel_le_radialKernel`; on loops both are `0`. -/
theorem cutoffSymKernel_eq_cutoffKernel (K : ℝ → ℝ) (r : ℝ) (x y : Fin d → ℤ)
    (hxy : x ≠ y) :
    cutoffSymKernel K d r s(x, y) = cutoffKernel K (latticeDist (d := d)) r x y := by
  rw [cutoffSymKernel_mk, ite_eq_right hxy, cutoffKernel_eq_of_ne K _ r hxy]
  rfl

/-- The uncut `Sym2`-kernel `kernelJ (K ∘ ‖·‖_∞)` and the two-variable kernel
`FiniteVolume.radialKernel` agree on every non-loop edge of `ℤ^d`. -/
theorem kernelJ_eq_radialKernel (K : ℝ → ℝ) (x y : Fin d → ℤ) (hxy : x ≠ y) :
    kernelJ (fun y : Fin d → ℤ => K ((linfNorm y : ℕ) : ℝ)) (profile_even K) s(x, y)
      = radialKernel K (latticeDist (d := d)) x y := by
  show K ((linfNorm (y - x) : ℕ) : ℝ) = radialKernel K (latticeDist (d := d)) x y
  rw [radialKernel_eq_of_ne K _ hxy,
    show latticeDist x y = ((linfNorm (y - x) : ℕ) : ℝ) from by
      unfold latticeDist
      rw [show x - y = -(y - x) by abel, linfNorm_neg]]

/-- The cut-off kernel vanishes on loops, which is the paper's factor `1(x ≠ y)` and
the reason the loop-safe kernel needs no separate positivity hypothesis. -/
theorem cutoffSymKernel_loop (K : ℝ → ℝ) (r : ℝ) (x : Fin d → ℤ) :
    cutoffSymKernel K d r s(x, x) = 0 := by
  rw [cutoffSymKernel_mk, ite_eq_left rfl]

/-- With `K 0 = 0` the uncut kernel vanishes on loops too, so the two kernels differ
only through the factor `1 − K r / K 1` of Definition I.1.5. -/
theorem kernelJ_loop {K : ℝ → ℝ} (hK0 : K 0 = 0) (x : Fin d → ℤ) :
    kernelJ (fun y : Fin d → ℤ => K ((linfNorm y : ℕ) : ℝ)) (profile_even K) s(x, x) = 0 := by
  show K ((linfNorm (x - x) : ℕ) : ℝ) = 0
  rw [sub_self, show linfNorm (0 : Fin d → ℤ) = 0 from linfNorm_eq_zero_iff.mpr rfl]
  simp [hK0]

/-! ## Subcriticality: the premise discharged at a smaller parameter -/

/-- **The form in which the paper uses the domination**: if the uncut first moment is
finite at every parameter up to `β₀` (subcritical finiteness of the mean) and the
reduced parameter `β(1 − K r / K 1)` is at most `β₀`, then the cut-off first moment at
parameter `β` is finite. -/
theorem lintegral_clusterVol_cutoff_ne_top_of_subcritical (hK : AntitoneOn K (Set.Ioi 0))
    (hKnn : ∀ t, 0 < t → 0 ≤ K t) (hK0 : K 0 = 0)
    {r : ℝ} (hr : 1 ≤ r) (hKr : 0 < K r) (hK1 : 0 < K 1) (β : NNReal)
    (o : Fin d → ℤ) (β₀ : NNReal)
    (hle : β * NNReal.mk (1 - K r / K 1) (cutoffCoefficient_nonneg hK hr hKr hK1) ≤ β₀)
    (hsub : ∀ b : NNReal, b ≤ β₀ →
      (∫⁻ ω, clusterVol ω o ∂(longRangeMeasure
        (kernelJ (fun y : Fin d → ℤ => K ((linfNorm y : ℕ) : ℝ)) (profile_even K))
        (uncutKernel_nonneg hKnn hK0 d) b)) ≠ ∞) :
    (∫⁻ ω, clusterVol ω o ∂(longRangeMeasure (cutoffSymKernel K d r)
        (cutoffSymKernel_nonneg' hK d r) β)) ≠ ∞ :=
  lintegral_clusterVol_cutoff_ne_top hK hKnn hK0 hr hKr hK1 β o (hsub _ hle)

/-! ## Non-vacuity at the paper's own profile `r ↦ r^{-(d+α)}` -/

/-- For the model profile, `K 1 = 1`, so the coefficient of Definition I.1.5 is
`ε(r) = r^{-(d+α)}` and `1 − ε(r) = 1 − r^{-(d+α)}`. -/
theorem modelProfile_coefficient (d : ℕ) (α r : ℝ) :
    1 - modelProfile d α r / modelProfile d α 1 = 1 - modelProfile d α r := by
  rw [modelProfile_one, div_one]

/-- `ε(r) = r^{-(d+α)} > 0`, so for `r ≥ 1` the reduced parameter `(1 − ε)β` is
*strictly* smaller than `β`. -/
theorem modelProfile_coefficient_lt_one {d : ℕ} {α : ℝ} {r : ℝ} (hr : 1 ≤ r) :
    1 - modelProfile d α r < 1 := by
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hpos : 0 < modelProfile d α r := modelProfile_pos hr0
  linarith

/-- `1 − r^{-(d+α)} ≥ 0` for `r ≥ 1`, `α > 0`: the coefficient of Definition I.1.5 is
an admissible `NNReal` at the source's own profile. -/
theorem modelProfile_coefficient_nonneg {d : ℕ} {α : ℝ} (hα : 0 < α) {r : ℝ}
    (hr : 1 ≤ r) : 0 ≤ 1 - modelProfile d α r := by
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hαd : (0 : ℝ) ≤ (d : ℝ) + α := by
    have h : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
    linarith
  have hle : modelProfile d α r ≤ modelProfile d α 1 :=
    modelProfile_antitoneOn d hαd (Set.mem_Ioi.mpr zero_lt_one) (Set.mem_Ioi.mpr hr0) hr
  rw [modelProfile_one] at hle
  linarith

/-- **Definition I.1.5 at the source's own kernel, edge by edge.**  For the power-law
profile `r ↦ r^{-(d+α)}` with `α > 0` and `r ≥ 1` the cut-off kernel is dominated by
`(1 − r^{-(d+α)}) J` on **every** edge of `Sym2 (ℤ^d)`. -/
theorem modelProfile_cutoffSymKernel_le_scaled {d : ℕ} {α : ℝ} (hα : 0 < α) {r : ℝ}
    (hr : 1 ≤ r) (e : Sym2 (Fin d → ℤ)) :
    cutoffSymKernel (modelProfile d α) d r e
      ≤ (1 - modelProfile d α r) *
          kernelJ (fun y : Fin d → ℤ => modelProfile d α ((linfNorm y : ℕ) : ℝ))
            (profile_even (modelProfile d α)) e := by
  have hαd : (0 : ℝ) ≤ (d : ℝ) + α := by
    have h : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
    linarith
  have hanti : AntitoneOn (modelProfile d α) (Set.Ioi 0) := modelProfile_antitoneOn d hαd
  have hKnn : ∀ t : ℝ, 0 < t → 0 ≤ modelProfile d α t :=
    fun t ht => (modelProfile_pos ht).le
  have hK0 : modelProfile d α 0 = 0 := modelProfile_zero (by linarith)
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hKr : 0 < modelProfile d α r := modelProfile_pos hr0
  have hK1 : 0 < modelProfile d α 1 := by rw [modelProfile_one]; norm_num
  refine le_trans (cutoffSymKernel_le_scaled hanti hKnn hK0 hr hKr hK1 e) ?_
  rw [modelProfile_coefficient d α r]

/-- **Definition I.1.5 at the source's own kernel, on the law**: for the power-law
profile with `α > 0` and every `r ≥ 1`, every increasing measurable event is at least as
likely under the uncut law at parameter `β(1 − r^{-(d+α)})` as under the cut-off law
`P_{β,r}`.  This is a compiled witness that the interface of
`longRangeMeasure_cutoff_dominated` is inhabited by the profile of Definition I.1.3. -/
theorem modelProfile_longRangeMeasure_cutoff_dominated {d : ℕ} {α : ℝ} (hα : 0 < α)
    {r : ℝ} (hr : 1 ≤ r) (β : NNReal)
    {A : Set (Config (Fin d → ℤ))} (hA : MeasurableSet A) (hInc : IsIncreasing A) :
    longRangeMeasure (cutoffSymKernel (modelProfile d α) d r)
        (fun e => cutoffSymKernel_nonneg' (modelProfile_antitoneOn d (by
          have h : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
          linarith)) d r e) β A
      ≤ longRangeMeasure
          (kernelJ (fun y : Fin d → ℤ => modelProfile d α ((linfNorm y : ℕ) : ℝ))
            (profile_even (modelProfile d α)))
          (fun e => uncutKernel_nonneg (fun t ht => (modelProfile_pos ht).le)
            (modelProfile_zero (by
              have h : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
              linarith)) d e)
          (β * NNReal.mk (1 - modelProfile d α r) (modelProfile_coefficient_nonneg hα hr)) A := by
  refine edgeMeasure_mono_of_le (fun e => ?_) hA hInc
  refine bernoulliEdgeProb_le_of_mul_le _ _ ?_
  have hcoef : ((β * NNReal.mk (1 - modelProfile d α r)
      (modelProfile_coefficient_nonneg hα hr) : NNReal) : ℝ)
      = (β : ℝ) * (1 - modelProfile d α r) := by
    simp only [NNReal.coe_mul, NNReal.coe_mk]
  rw [hcoef]
  have hdom := modelProfile_cutoffSymKernel_le_scaled hα hr e
  have hβ : (0 : ℝ) ≤ (β : ℝ) := β.2
  nlinarith [hdom, hβ]

end PercLib.CriticalLRP.CutoffDominated

/-! ## Axiom audit -/

#print axioms PercLib.CriticalLRP.CutoffDominated.uncutKernel_shift
#print axioms PercLib.CriticalLRP.CutoffDominated.cutoffCoefficient_mem
#print axioms PercLib.CriticalLRP.CutoffDominated.cutoffSymKernel_le_scaled
#print axioms PercLib.CriticalLRP.CutoffDominated.bernoulliEdgeProb_le_of_mul_le
#print axioms PercLib.CriticalLRP.CutoffDominated.bernoulliEdgeProb_cutoff_le_scaled
#print axioms PercLib.CriticalLRP.CutoffDominated.longRangeMeasure_cutoff_dominated
#print axioms PercLib.CriticalLRP.CutoffDominated.infiniteClusterProb_cutoff_le
#print axioms PercLib.CriticalLRP.CutoffDominated.infiniteClusterProb_cutoff_eq_zero
#print axioms PercLib.CriticalLRP.CutoffDominated.lintegral_clusterVol_cutoff_le
#print axioms PercLib.CriticalLRP.CutoffDominated.lintegral_clusterVol_cutoff_ne_top
#print axioms PercLib.CriticalLRP.CutoffDominated.uncutKernel_rootIndependent
#print axioms PercLib.CriticalLRP.CutoffDominated.cutoff_clusterVol_sq_ne_top
#print axioms PercLib.CriticalLRP.CutoffDominated.cutoff_joint_windowMoment_ne_top
#print axioms PercLib.CriticalLRP.CutoffDominated.cutoffSymKernel_eq_cutoffKernel
#print axioms PercLib.CriticalLRP.CutoffDominated.kernelJ_eq_radialKernel
#print axioms PercLib.CriticalLRP.CutoffDominated.cutoffSymKernel_loop
#print axioms PercLib.CriticalLRP.CutoffDominated.kernelJ_loop
#print axioms PercLib.CriticalLRP.CutoffDominated.lintegral_clusterVol_cutoff_ne_top_of_subcritical
#print axioms PercLib.CriticalLRP.CutoffDominated.modelProfile_coefficient
#print axioms PercLib.CriticalLRP.CutoffDominated.modelProfile_coefficient_lt_one
#print axioms PercLib.CriticalLRP.CutoffDominated.modelProfile_coefficient_nonneg
#print axioms PercLib.CriticalLRP.CutoffDominated.modelProfile_cutoffSymKernel_le_scaled
#print axioms PercLib.CriticalLRP.CutoffDominated.modelProfile_longRangeMeasure_cutoff_dominated
#print axioms PercLib.CriticalLRP.CutoffDominated.cutoff_parameter_lt

#print axioms PercLib.CriticalLRP.CutoffDominated.cutoff_edgeComparison
#print axioms PercLib.CriticalLRP.CutoffDominated.uncutKernel_rootComparison
#print axioms PercLib.CriticalLRP.CutoffDominated.uncutKernel_rootComparison_any
#print axioms PercLib.CriticalLRP.CutoffDominated.lintegral_clusterVol_sq_le_of_pointwise
#print axioms PercLib.CriticalLRP.CutoffDominated.lintegral_clusterVol_sq_ne_top_of_pointwise
#print axioms PercLib.CriticalLRP.CutoffDominated.joint_windowMoment_ne_top_of_pointwise
