/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

# Interval absolute continuity of the cut-off mass for the explicit power-law model

Integrated from Ultramath `smwv4hzkh`, member `m8`, direction C5, and independently rebuilt.
The per-vertex continuity helper is reused from `PowerLawContinuity`, and the first-moment
integral wrapper uses the exact source-kernel moment transfer.

## What this file does

The landed off-corner endpoint derivative theorems
(`Analysis/Cutoff/OffCorner/RadiusPivotalWeight.lean`,
`.../RadiusExcludedMass.lean`, `.../RadiusMeasurability/Main.lean`) all consume

* a pair of *existential* exhaustions `T : ℕ → Finset M.V`, `S : ℕ → Finset (Sym2 M.V)`,
* the per-vertex flux continuity `hcontinf`,
* the excluded-mass continuity `hex`, and (in the measurability route) the dominator
  interval-integrability `hboundint`.

For the literal model `sourceModelWitness d hd α hα` this file removes all of them:

* `exists_monotone_finset_exhaustion`: a countable inhabited type has a monotone exhaustive
  sequence of finite sets (`Encodable`); `SourceModelData.exists_monotone_finset_exhaustion` and
  `exists_monotone_finset_exhaustion_sym2_sourceModelWitness` instantiate it at `M.V = Fin d → ℤ`
  and at `Sym2 M.V`.  These `T`, `S` are *constructed*, not assumed.
* `sourceModelWitness_intervalIntegrable_pivotalWeight`: `hboundint` on a window `Ioo a b` from a
  finite *first* cutoff moment at the right endpoint `b`, the explicit kernel and
  `intervalIntegrable_pivotalWeight_of_envelope`.
* `sourceModelWitness_hcontinf_of_moment_two`: `hcontinf` on `Ioo a b` from off-corner radii and a
  finite *second* moment at `b`, via `continuousAt_normalizedPivotMass` (the a807474 capstone) and
  `sourceModelWitness_hcontinf`.
* `sourceModelWitness_continuousAt_exclScalar_of_moments`: `hex` from off-corner radii and finite
  second and third moments at `b`.
* `sourceModelWitness_hasDerivAt_cutMassReal_rhsScalar_of_endpoint`: the off-corner endpoint
  derivative with `T`, `S`, `hcontinf`, `hex` **eliminated**.
* `sourceModelWitness_continuousOn_cutMassReal`: `χ` is continuous on the *closed* window `Icc a b`
  — at interior points by `continuousAt_cutMassReal` (whose strictly larger radius is `b` itself),
  at `b` by the left continuity `tendsto_cutMassReal_nhdsLT`, since within `Icc a b` the only
  approach to `b` is from the left.  So no finite moment above `b` is needed.
* `sourceModelWitness_cutMassReal_absolutelyContinuousOn_Icc`,
  `sourceModelWitness_cutMassReal_abs_sub_le_integral_Icc`,
  `sourceModelWitness_cutMassReal_intervalIntegral_deriv_Icc` and
  `sourceModelWitness_cutMassReal_ae_differentiableAt_Icc`: Lemma I.4.1 in integrated form on the
  whole window `[a,b]` — the cut mass is absolutely continuous in the radius, its increment is
  bounded by the integral of the explicit constant majorant, the integral of its radial derivative
  is its increment, and it is a.e. differentiable.  No derivative is claimed *at* a corner radius.

## What is *not* claimed

Nothing is claimed at a radius at which an edge length is attained (a "corner"), and no
differentiability of `χ` is claimed from the left or right at such a radius.  The statements are
for the *literal* model `sourceModelWitness d hd α hα` with `1 ≤ d` and `α > 0`; no abstract
`SourceModelData` is treated, and no moment, critical-parameter (`β_c ≠ 0`) or percolation
statement is derived.  In particular the three hypotheses `0 < a`, `a < b`, `r₀ ∈ Ioo a b` and the
finite moments `cutMoment 2 b ≠ ⊤`, `cutMoment 3 b ≠ ⊤` remain visible and are not uniform in `b`.
The majorant used is the *constant* supplied by `SourceModelData.abs_rhsScalar_le_of_window`
(excluded mass bounded by `|B_b| (cutMoment 2 b)²` times `β_c a ^ (-(d) - α - 1)`); no uniformity of
any radius-local quantity is asserted, in contrast with the false radius-local-uniform bound on
`stdDegree` recorded in `OffCorner/UniformObstruction.lean`.
-/
module

public import PercLib.CriticalLRP.Analysis.Cutoff.OffCorner.TwoPoint.Capstone
public import PercLib.CriticalLRP.Analysis.Cutoff.OffCorner.PowerLawDeriv
public import PercLib.CriticalLRP.Analysis.Cutoff.OffCorner.RadiusPivotalWeight
public import PercLib.CriticalLRP.Analysis.Cutoff.OffCorner.RadiusExcludedMass
public import PercLib.CriticalLRP.Analysis.Cutoff.CornerRadii
public import PercLib.CriticalLRP.Analysis.Cutoff.Continuity
public import PercLib.CriticalLRP.Analysis.Cutoff.OffCorner.PowerLawContinuity

/-!
# Local absolute continuity of the power-law cutoff mass

The finite-moment, off-corner derivative of the explicit source model is combined with
its constant local derivative majorant. Closed-window continuity, absolute continuity,
and the radial fundamental-theorem identity follow. Pointwise derivative claims remain
restricted to off-corner radii; the finite first cutoff moment is not constructed.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.hashCommand false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal Topology Interval

namespace PercLib.CriticalLRP.Orchestration

/-! ## 1. Exhaustions are constructible, not an extra input -/

/-- **A countable inhabited type has a monotone exhaustive sequence of finite sets.**  The finite
set at `n` is the image of `{0, …, n}` under `Encodable.decode`.  This is the existence content of
the hypothesis `∃ T, Monotone T ∧ ∀ y, ∃ n, y ∈ T n` that the off-corner endpoint wrappers carry. -/
theorem exists_monotone_finset_exhaustion_of_encodable (ι : Type) [Encodable ι] [Inhabited ι] :
    ∃ T : ℕ → Finset ι, Monotone T ∧ ∀ x : ι, ∃ n, x ∈ T n := by
  classical
  refine ⟨fun n => (Finset.range (n + 1)).image (fun k => (Encodable.decode k).getD default),
    ?_, ?_⟩
  · intro n m hnm
    exact Finset.image_mono _ (by intro k hk; simp only [Finset.mem_range] at hk ⊢; omega)
  · intro x
    exact ⟨Encodable.encode x, Finset.mem_image.mpr
      ⟨Encodable.encode x, Finset.mem_range.mpr (Nat.lt_succ_self _), by
        simp [Encodable.encodek]⟩⟩

namespace SourceModelData

/-- **The vertex exhaustion `T` of the off-corner wrappers exists** for every source model, with no
hypothesis: `M.V = Fin M.d → ℤ` is countable and inhabited. -/
theorem exists_monotone_finset_exhaustion (M : SourceModelData) :
    ∃ T : ℕ → Finset M.V, Monotone T ∧ ∀ y : M.V, ∃ n, y ∈ T n :=
  exists_monotone_finset_exhaustion_of_encodable M.V

end SourceModelData

/-- **The edge exhaustion `S` of the off-corner wrappers exists**, built from a vertex exhaustion by
the product construction `S n = (T n) × (T n)` read through `Sym2.mk`.  No countability of
`Sym2 ι` is needed. -/
theorem exists_monotone_finset_exhaustion_sym2 {ι : Type}
    {T : ℕ → Finset ι} (hTmono : Monotone T) (hT : ∀ x : ι, ∃ n, x ∈ T n) :
    ∃ S : ℕ → Finset (Sym2 ι), Monotone S ∧ ∀ e : Sym2 ι, ∃ n, e ∈ S n := by
  classical
  refine ⟨fun n => (T n ×ˢ T n).image (fun p : ι × ι => Sym2.mk p.1 p.2), ?_, ?_⟩
  · intro n m hnm
    refine Finset.image_mono _ ?_
    exact Finset.product_subset_product (hTmono hnm) (hTmono hnm)
  · intro e
    obtain ⟨p, hp⟩ := Sym2.mk_surjective e
    obtain ⟨x, y⟩ := p
    obtain ⟨nx, hx⟩ := hT x
    obtain ⟨ny, hy⟩ := hT y
    refine ⟨max nx ny, Finset.mem_image.mpr ⟨(x, y), ?_, hp⟩⟩
    exact Finset.mk_mem_product (hTmono (le_max_left _ _) hx)
      (hTmono (le_max_right _ _) hy)

end PercLib.CriticalLRP.Orchestration

namespace PercLib.CriticalLRP.Orchestration.Witness

open PercLib.CriticalLRP.Orchestration

/-! ## 2. The literal model: `hboundint` from one finite first moment -/

/-- **`hboundint` for the explicit power-law model.**  On the off-corner window `Ioo a b` the total
pivotal weight `r ↦ sMomentWeight 0 {y} 1` is interval integrable over every subinterval with
endpoints in `Ioo a b`, from a finite *first* cutoff moment at `b`.  The dominator is the
interior-scale envelope of `intervalIntegrable_pivotalWeight_of_envelope` at `ρ = b` with
`C = a ^ (-(d) - α - 1)`, which the explicit kernel supplies on the whole window. -/
theorem sourceModelWitness_intervalIntegrable_pivotalWeight (d : ℕ) (hd : 1 ≤ d) (α : ℝ)
    (hα : 0 < α) {a b : ℝ} (ha : 0 < a)
    (h1b : (sourceModelWitness d hd α hα).cutMoment 1 b ≠ ⊤) :
    ∀ y : (sourceModelWitness d hd α hα).V, ∀ a' ∈ Set.Ioo a b, ∀ b' ∈ Set.Ioo a b,
      IntervalIntegrable
        (sMomentWeight (0 : (sourceModelWitness d hd α hα).V)
          ({y} : Finset (sourceModelWitness d hd α hα).V) (fun _ => (1 : ℝ))
          (sourceModelWitness d hd α hα).cutProb
          (sourceModelWitness d hd α hα).cutEdgeDeriv) volume a' b' := by
  intro y a' ha' b' hb'
  have hab : a < b := lt_trans ha'.1 ha'.2
  have hβ0 : 0 < b := lt_trans ha hab
  have hCb : ∀ r ∈ Set.Ioo a b, -(deriv (sourceModelWitness d hd α hα).K r) ≤
      a ^ (-(d : ℝ) - α - 1) :=
    fun r hr => sourceModelWitness_hCb d hd α hα a b ha r hr
  have hKβ : deriv (sourceModelWitness d hd α hα).K b < 0 :=
    sourceModelWitness_hKβ d hd α hα hβ0
  rcases le_total a' b' with hab' | hb'a'
  · exact SourceModelData.intervalIntegrable_pivotalWeight_of_envelope
      (sourceModelWitness d hd α hα) (lt_trans ha ha'.1) hab' hb'.2.le
      (fun r hr => hCb r ⟨lt_of_lt_of_le ha'.1 hr.1, lt_of_le_of_lt hr.2 hb'.2⟩)
      (Real.rpow_nonneg ha.le _) hKβ hβ0 h1b y
  · exact (SourceModelData.intervalIntegrable_pivotalWeight_of_envelope
      (sourceModelWitness d hd α hα) (lt_trans ha hb'.1) hb'a' ha'.2.le
      (fun r hr => hCb r ⟨lt_of_lt_of_le hb'.1 hr.1, lt_of_le_of_lt hr.2 ha'.2⟩)
      (Real.rpow_nonneg ha.le _) hKβ hβ0 h1b y).symm

/-!
Per-vertex continuity is supplied by the landed `PowerLawContinuity`: its proved
`sourceModelWitness_hcontinf_of_moment_two` is shared, rather than redeclared here.
-/

/-! ## 4. The literal model: excluded-mass continuity from second and third moments -/

/-- **`hex` for the explicit power-law model**: the excluded-mass scalar is continuous at every
off-corner radius of the window, from finite second and third cutoff moments at `b`.  Off the
corner set the norm sphere at `r` carries no lattice point
(`SourceModelData.noSphere_of_cornerRadii`), which is exactly what
`SourceModelData.continuousAt_exclScalar` needs. -/
theorem sourceModelWitness_continuousAt_exclScalar_of_moments (d : ℕ) (hd : 1 ≤ d) (α : ℝ)
    (hα : 0 < α) {a b : ℝ} (ha : 0 < a)
    (hoff : ∀ r ∈ Set.Ioo a b, r ∉ (sourceModelWitness d hd α hα).cornerRadii)
    (h2b : (sourceModelWitness d hd α hα).cutMoment 2 b ≠ ⊤)
    (h3b : (sourceModelWitness d hd α hα).cutMoment 3 b ≠ ⊤) :
    ∀ r ∈ Set.Ioo a b, ContinuousAt (sourceModelWitness d hd α hα).exclScalar r := by
  intro r hr
  exact SourceModelData.continuousAt_exclScalar (M := sourceModelWitness d hd α hα)
    (ha.trans hr.1)
    (SourceModelData.noSphere_of_cornerRadii (M := sourceModelWitness d hd α hα)
      (ha.trans hr.1) (hoff r hr)) hr.2 h2b h3b

end PercLib.CriticalLRP.Orchestration.Witness

namespace PercLib.CriticalLRP.Orchestration.Witness

open PercLib.CriticalLRP.Orchestration

/-! ## 5. The endpoint derivative with `T`, `S`, `hcontinf` and `hex` eliminated

The landed wrappers `sourceModelWitness_hasDerivAt_cutMassReal_rhsScalar_of_endpoint_of_moments`
and `..._of_measurability` carry an existential vertex exhaustion `T`, an existential edge
exhaustion `S`, the per-vertex flux continuity `hcontinf` (or its sufficient condition `hB`), and
(for the measurability route) also `hex` and `hboundint`.  Sections 1–4 construct or prove all of
them, so both are restated here with only the geometry, the two endpoint moments and the off-corner
condition left. -/

/-- **The off-corner endpoint derivative of the explicit power-law model** — envelope route, with
no exhaustion, flux-continuity or excluded-mass-continuity hypothesis.  What remains is exactly:
`0 < a`, `a < r0 < b`, the window is off corner, and the second and third cutoff moments are finite
at `b`. -/
theorem sourceModelWitness_hasDerivAt_cutMassReal_rhsScalar_of_endpoint
    (d : ℕ) (hd : 1 ≤ d) (α : ℝ) (hα : 0 < α) {a b r0 : ℝ} (ha : 0 < a) (har0 : a < r0)
    (hr0b : r0 < b)
    (hoff : ∀ r ∈ Set.Ioo a b, r ∉ (sourceModelWitness d hd α hα).cornerRadii)
    (h2b : (sourceModelWitness d hd α hα).cutMoment 2 b ≠ ⊤)
    (h3b : (sourceModelWitness d hd α hα).cutMoment 3 b ≠ ⊤) :
    HasDerivAt (sourceModelWitness d hd α hα).cutMassReal
      ((sourceModelWitness d hd α hα).rhsScalar r0) r0 := by
  obtain ⟨T, hTmono, hT⟩ :=
    SourceModelData.exists_monotone_finset_exhaustion (sourceModelWitness d hd α hα)
  obtain ⟨S, hSmono, hS⟩ := exists_monotone_finset_exhaustion_sym2
    (ι := (sourceModelWitness d hd α hα).V) hTmono hT
  exact sourceModelWitness_hasDerivAt_cutMassReal_rhsScalar_of_endpoint_of_moments d hd α hα
    T hTmono hT S hSmono hS ha har0 hr0b hoff h2b h3b
    (sourceModelWitness_hcontinf_of_moment_two d hd α hα ha hoff h2b)

/-- **The same off-corner endpoint derivative — measurability route**, again with the exhaustion,
`hboundint`, `hcontinf` and `hex` all supplied here rather than assumed.  Since this route's
dominator is the total pivotal weight, this is the form in which the *interchange* between the
radius derivative and the vertex sum is consumed. -/
theorem sourceModelWitness_hasDerivAt_cutMassReal_rhsScalar_of_endpoint_measurability_discharged
    (d : ℕ) (hd : 1 ≤ d) (α : ℝ) (hα : 0 < α) {a b r0 : ℝ} (ha : 0 < a) (har0 : a < r0)
    (hr0b : r0 < b)
    (hoff : ∀ r ∈ Set.Ioo a b, r ∉ (sourceModelWitness d hd α hα).cornerRadii)
    (h2b : (sourceModelWitness d hd α hα).cutMoment 2 b ≠ ⊤)
    (h3b : (sourceModelWitness d hd α hα).cutMoment 3 b ≠ ⊤) :
    HasDerivAt (sourceModelWitness d hd α hα).cutMassReal
      ((sourceModelWitness d hd α hα).rhsScalar r0) r0 := by
  obtain ⟨T, hTmono, hT⟩ :=
    SourceModelData.exists_monotone_finset_exhaustion (sourceModelWitness d hd α hα)
  obtain ⟨S, hSmono, hS⟩ := exists_monotone_finset_exhaustion_sym2
    (ι := (sourceModelWitness d hd α hα).V) hTmono hT
  exact sourceModelWitness_hasDerivAt_cutMassReal_rhsScalar_of_endpoint_of_measurability
    d hd α hα T hTmono hT S hSmono hS ha har0 hr0b hoff h2b
    (sourceModelWitness_intervalIntegrable_pivotalWeight d hd α hα ha
      (SourceModelData.cutMoment_one_ne_top_of_two
        (M := sourceModelWitness d hd α hα) h2b))
    (sourceModelWitness_hcontinf_of_moment_two d hd α hα ha hoff h2b)
    (sourceModelWitness_continuousAt_exclScalar_of_moments d hd α hα ha hoff h2b h3b)

/-- **The off-corner endpoint derivative in the paper's own scale**:
`d/dr χ(r) = β_c r0 ^ (-(d) - α - 1) (exclMass r0)` at `r0`, with only the geometry, the two
endpoint moments and the off-corner condition as hypotheses. -/
theorem sourceModelWitness_hasDerivAt_cutMassReal_powerLaw_of_endpoint
    (d : ℕ) (hd : 1 ≤ d) (α : ℝ) (hα : 0 < α) {a b r0 : ℝ} (ha : 0 < a) (har0 : a < r0)
    (hr0b : r0 < b)
    (hoff : ∀ r ∈ Set.Ioo a b, r ∉ (sourceModelWitness d hd α hα).cornerRadii)
    (h2b : (sourceModelWitness d hd α hα).cutMoment 2 b ≠ ⊤)
    (h3b : (sourceModelWitness d hd α hα).cutMoment 3 b ≠ ⊤) :
    HasDerivAt (sourceModelWitness d hd α hα).cutMassReal
      (((sourceModelWitness d hd α hα).betaCrit : ℝ) * r0 ^ (-(d : ℝ) - α - 1) *
        (sourceModelWitness d hd α hα).exclScalar r0) r0 := by
  have h := sourceModelWitness_hasDerivAt_cutMassReal_rhsScalar_of_endpoint d hd α hα
    ha har0 hr0b hoff h2b h3b
  rwa [sourceModelWitness_rhsScalar_eq d hd α hα (lt_trans ha har0)] at h

/-! ## 6. The off-corner derivative bound on a window, and its constant majorant -/

/-- **A window majorant for the radial derivative of the cut mass** at the explicit power-law
model.  Off corner, `|χ'(u)| = |rhsScalar u| ≤ β_c a ^ (-(d) - α - 1) · |B_b| · (cutMoment 2 b)²`:
the coefficient is bounded by `SourceModelData.abs_rhsScalar_le_of_window` using the explicit
derivative `r ↦ -r ^ (-(d) - α - 1)`, and the excluded mass by the second moment at `b`.

The majorant is *constant in `u`*, so it is bounded on the window and no radius-local uniformity
(compare `OffCorner/UniformObstruction.lean`) is asserted or needed. -/
theorem sourceModelWitness_offCorner_deriv_bound (d : ℕ) (hd : 1 ≤ d) (α : ℝ) (hα : 0 < α)
    {a b : ℝ} (ha : 0 < a)
    (hoff : ∀ r ∈ Set.Ioo a b, r ∉ (sourceModelWitness d hd α hα).cornerRadii)
    (h2b : (sourceModelWitness d hd α hα).cutMoment 2 b ≠ ⊤)
    (h3b : (sourceModelWitness d hd α hα).cutMoment 3 b ≠ ⊤) :
    ∀ u ∈ Set.Ioo a b, u ∉ (sourceModelWitness d hd α hα).cornerRadii →
      DifferentiableAt ℝ (sourceModelWitness d hd α hα).cutMassReal u ∧
        |deriv (sourceModelWitness d hd α hα).cutMassReal u| ≤
          (sourceModelWitness d hd α hα).betaCrit *
            (a ^ (-(d : ℝ) - α - 1)) *
              (((sourceModelWitness d hd α hα).ball b).ncard *
                ((sourceModelWitness d hd α hα).cutMoment 2 b).toReal ^ 2) := by
  intro u hu huoff
  have hderiv := sourceModelWitness_hasDerivAt_cutMassReal_rhsScalar_of_endpoint d hd α hα
    ha hu.1 hu.2 hoff h2b h3b
  refine ⟨hderiv.differentiableAt, ?_⟩
  rw [hderiv.deriv]
  have hp : -(d : ℝ) - α - 1 ≤ 0 := by
    have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
    linarith
  refine SourceModelData.abs_rhsScalar_le_of_window
    (M := sourceModelWitness d hd α hα) (a := a) (b := b)
    (C := a ^ (-(d : ℝ) - α - 1)) ha.le ?_ (Real.rpow_nonneg ha.le _) h2b
    (Nat.cast_nonneg _) u ⟨hu.1.le, hu.2.le⟩
  intro r hr
  rw [abs_deriv_sourceModelWitness_K d hd α hα (lt_of_lt_of_le ha hr.1)]
  simpa using Real.rpow_le_rpow_of_nonpos ha hr.1 hp

/-! ## 7. Continuity on the whole window from one-sided information

The `IntervalAC` theorems need `ContinuousOn χ (Icc a b)`.  `continuousOn_cutMassReal` supplies it
only from a finite mean at a radius *strictly above* `b`.  That is stronger than necessary for the
absolute-continuity statement: within `Icc a b` the only approach to `b` is from the left, and the
left continuity of `χ` at `b` is available from finiteness at `b` itself
(`SourceModelData.tendsto_cutMassReal_nhdsLT`).  The next lemma therefore proves
`ContinuousOn χ (Icc a b)` from finiteness at `b`, and the absolute-continuity and
fundamental-theorem statements below are stated on the whole window, not merely on a compact
subwindow. -/

set_option maxHeartbeats 1000000 in
-- The large source-model expressions are elaborated only for this declaration.
/-- **Continuity of the cut mass on a closed window from finiteness at the right endpoint only.**
`SourceModelData.continuousAt_cutMassReal` gives two-sided continuity at every interior point (its
"strictly larger radius" is `b` itself), and at `b` the filter `𝓝[Icc a b] b` is
`𝓝[<] b ⊔ 𝓟 {b}`, on both parts of which `χ` tends to `χ b`. -/
theorem sourceModelWitness_continuousOn_cutMassReal (d : ℕ) (hd : 1 ≤ d) (α : ℝ) (hα : 0 < α)
    {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (hfinb : (sourceModelWitness d hd α hα).cutMassAt b 0 ≠ ⊤) :
    ContinuousOn (sourceModelWitness d hd α hα).cutMassReal (Set.Icc a b) := by
  intro x hx
  rcases eq_or_lt_of_le hx.2 with hxb | hxb
  · -- right endpoint: only the left approach within `Icc a b` is available, and the left
    -- continuity of `χ` at `b` follows from finiteness at `b` itself.
    rw [hxb]
    have h1 : Tendsto (sourceModelWitness d hd α hα).cutMassReal (𝓝[<] b)
        (𝓝 ((sourceModelWitness d hd α hα).cutMassReal b)) :=
      SourceModelData.tendsto_cutMassReal_nhdsLT (sourceModelWitness d hd α hα) b
        (lt_trans ha hab) hfinb
    rw [Metric.continuousWithinAt_iff]
    intro ε hε
    obtain ⟨δ, hδ, hspec⟩ := Metric.tendsto_nhdsWithin_nhds.mp h1 ε hε
    refine ⟨δ, hδ, fun y hy hdist => ?_⟩
    rcases eq_or_lt_of_le hy.2 with hyb | hyb
    · rw [← hyb]
      simpa using hε
    · exact hspec hyb hdist
  · exact ((sourceModelWitness d hd α hα).continuousAt_cutMassReal x
      (ha.trans_le hx.1) hxb hfinb).continuousWithinAt

set_option maxHeartbeats 1000000 in
-- The abstract-continuity wrapper expands the source-model expression.
/-- **Absolute continuity of the cut mass in its radius on the whole off-corner window**, from the
two endpoint moments at `b`. -/
theorem sourceModelWitness_cutMassReal_absolutelyContinuousOn_Icc (d : ℕ) (hd : 1 ≤ d) (α : ℝ)
    (hα : 0 < α) {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (hoff : ∀ r ∈ Set.Ioo a b, r ∉ (sourceModelWitness d hd α hα).cornerRadii)
    (h2b : (sourceModelWitness d hd α hα).cutMoment 2 b ≠ ⊤)
    (h3b : (sourceModelWitness d hd α hα).cutMoment 3 b ≠ ⊤) :
    AbsolutelyContinuousOnInterval (sourceModelWitness d hd α hα).cutMassReal a b := by
  have hfinb : (sourceModelWitness d hd α hα).cutMassAt b 0 ≠ ⊤ :=
    ne_top_of_le_ne_top h2b
      (PercLib.CriticalLRP.E1Sign.cutMassAt_le_cutMoment_two (sourceModelWitness d hd α hα) b)
  refine SourceModelData.cutMassReal_absolutelyContinuousOn
    (M := sourceModelWitness d hd α hα)
    (g := fun _ => (sourceModelWitness d hd α hα).betaCrit * (a ^ (-(d : ℝ) - α - 1)) *
      (((sourceModelWitness d hd α hα).ball b).ncard *
        ((sourceModelWitness d hd α hα).cutMoment 2 b).toReal ^ 2))
    hab.le (sourceModelWitness_continuousOn_cutMassReal d hd α hα ha hab hfinb)
    continuous_const.continuousOn
    ((sourceModelWitness d hd α hα).finite_cornerRadii_inter_Ioo a b) ?_
  intro u hu huoff
  exact sourceModelWitness_offCorner_deriv_bound d hd α hα ha hoff h2b h3b u hu huoff

set_option maxHeartbeats 1000000 in
-- The radial FTC wrapper expands the source-model expression.
/-- **Lemma I.4.1 in integrated form on the whole off-corner window**: the integral of the radial
derivative of the cut mass over `[a,b]` is its increment.  No differentiability is claimed at the
corner radii, and — unlike the compact-subwindow form —
no finite moment above `b` is needed. -/
theorem sourceModelWitness_cutMassReal_intervalIntegral_deriv_Icc (d : ℕ) (hd : 1 ≤ d) (α : ℝ)
    (hα : 0 < α) {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (hoff : ∀ r ∈ Set.Ioo a b, r ∉ (sourceModelWitness d hd α hα).cornerRadii)
    (h2b : (sourceModelWitness d hd α hα).cutMoment 2 b ≠ ⊤)
    (h3b : (sourceModelWitness d hd α hα).cutMoment 3 b ≠ ⊤) :
    ∫ t in a..b, deriv (sourceModelWitness d hd α hα).cutMassReal t =
      (sourceModelWitness d hd α hα).cutMassReal b -
        (sourceModelWitness d hd α hα).cutMassReal a := by
  have hfinb : (sourceModelWitness d hd α hα).cutMassAt b 0 ≠ ⊤ :=
    ne_top_of_le_ne_top h2b
      (PercLib.CriticalLRP.E1Sign.cutMassAt_le_cutMoment_two (sourceModelWitness d hd α hα) b)
  refine SourceModelData.cutMassReal_intervalIntegral_deriv
    (M := sourceModelWitness d hd α hα)
    (g := fun _ => (sourceModelWitness d hd α hα).betaCrit * (a ^ (-(d : ℝ) - α - 1)) *
      (((sourceModelWitness d hd α hα).ball b).ncard *
        ((sourceModelWitness d hd α hα).cutMoment 2 b).toReal ^ 2))
    hab.le (sourceModelWitness_continuousOn_cutMassReal d hd α hα ha hab hfinb)
    continuous_const.continuousOn
    ((sourceModelWitness d hd α hα).finite_cornerRadii_inter_Ioo a b) ?_
  intro u hu huoff
  exact sourceModelWitness_offCorner_deriv_bound d hd α hα ha hoff h2b h3b u hu huoff

/-! ## 7. Lemma I.4.1 in integrated form on the whole window

The `IntervalAC` theorems need `ContinuousOn χ (Icc a b)`, which `continuousOn_cutMassReal`
supplies only from a finite mean at a radius *strictly above* `b`.  For the absolute-continuity
statement that is stronger than necessary: within `Icc a b` the only approach to the right endpoint
`b` is from the left, and left continuity of `χ` at `b` is available from finiteness at `b` itself
(`SourceModelData.tendsto_cutMassReal_nhdsLT`).  So the statements below hold on the whole window
`[a,b]`.

The remaining analytic input is the *constant* window majorant of §6.  No derivative is claimed at
a corner radius; no uniformity of a radius-local quantity is used. -/

set_option maxHeartbeats 1000000 in
-- The incremental estimate wrapper expands the source-model expression.
/-- **Incremental bound for the cut mass on the whole off-corner window.** -/
theorem sourceModelWitness_cutMassReal_abs_sub_le_integral_Icc (d : ℕ) (hd : 1 ≤ d) (α : ℝ)
    (hα : 0 < α) {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (hoff : ∀ r ∈ Set.Ioo a b, r ∉ (sourceModelWitness d hd α hα).cornerRadii)
    (h2b : (sourceModelWitness d hd α hα).cutMoment 2 b ≠ ⊤)
    (h3b : (sourceModelWitness d hd α hα).cutMoment 3 b ≠ ⊤) :
    ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b, x ≤ y →
      |(sourceModelWitness d hd α hα).cutMassReal y -
          (sourceModelWitness d hd α hα).cutMassReal x| ≤
        ∫ _t in x..y, ((sourceModelWitness d hd α hα).betaCrit * (a ^ (-(d : ℝ) - α - 1)) *
          (((sourceModelWitness d hd α hα).ball b).ncard *
            ((sourceModelWitness d hd α hα).cutMoment 2 b).toReal ^ 2)) := by
  have hfinb : (sourceModelWitness d hd α hα).cutMassAt b 0 ≠ ⊤ :=
    ne_top_of_le_ne_top h2b
      (PercLib.CriticalLRP.E1Sign.cutMassAt_le_cutMoment_two (sourceModelWitness d hd α hα) b)
  refine SourceModelData.cutMassReal_abs_sub_le_integral
    (M := sourceModelWitness d hd α hα)
    (g := fun _ => (sourceModelWitness d hd α hα).betaCrit * (a ^ (-(d : ℝ) - α - 1)) *
      (((sourceModelWitness d hd α hα).ball b).ncard *
        ((sourceModelWitness d hd α hα).cutMoment 2 b).toReal ^ 2))
    (sourceModelWitness_continuousOn_cutMassReal d hd α hα ha hab hfinb)
    continuous_const.continuousOn
    ((sourceModelWitness d hd α hα).finite_cornerRadii_inter_Ioo a b) ?_
  intro u hu huoff
  exact sourceModelWitness_offCorner_deriv_bound d hd α hα ha hoff h2b h3b u hu huoff

set_option maxHeartbeats 1000000 in
-- The almost-everywhere differentiability wrapper expands the source-model expression.
/-- **A.e. differentiability of the cut mass in its radius** at the explicit power-law model, on the
whole off-corner window.  The conclusion is `DifferentiableAt` (not merely `DifferentiableWithinAt`
as the monotonicity route `SourceModelData.cutMassReal_ae_differentiableWithinAt` gives). -/
theorem sourceModelWitness_cutMassReal_ae_differentiableAt_Icc (d : ℕ) (hd : 1 ≤ d) (α : ℝ)
    (hα : 0 < α) {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (hoff : ∀ r ∈ Set.Ioo a b, r ∉ (sourceModelWitness d hd α hα).cornerRadii)
    (h2b : (sourceModelWitness d hd α hα).cutMoment 2 b ≠ ⊤)
    (h3b : (sourceModelWitness d hd α hα).cutMoment 3 b ≠ ⊤) :
    ∀ᵐ t, t ∈ Set.Icc a b → DifferentiableAt ℝ (sourceModelWitness d hd α hα).cutMassReal t := by
  have hfinb : (sourceModelWitness d hd α hα).cutMassAt b 0 ≠ ⊤ :=
    ne_top_of_le_ne_top h2b
      (PercLib.CriticalLRP.E1Sign.cutMassAt_le_cutMoment_two (sourceModelWitness d hd α hα) b)
  refine SourceModelData.cutMassReal_ae_differentiableAt
    (M := sourceModelWitness d hd α hα)
    (g := fun _ => (sourceModelWitness d hd α hα).betaCrit * (a ^ (-(d : ℝ) - α - 1)) *
      (((sourceModelWitness d hd α hα).ball b).ncard *
        ((sourceModelWitness d hd α hα).cutMoment 2 b).toReal ^ 2))
    hab.le (sourceModelWitness_continuousOn_cutMassReal d hd α hα ha hab hfinb)
    continuous_const.continuousOn
    ((sourceModelWitness d hd α hα).finite_cornerRadii_inter_Ioo a b) ?_
  intro u hu huoff
  exact sourceModelWitness_offCorner_deriv_bound d hd α hα ha hoff h2b h3b u hu huoff

set_option maxHeartbeats 1000000 in
-- The first-moment FTC wrapper expands the source-model expression.
/-- The radial fundamental-theorem identity with only a finite first cutoff moment at the
right endpoint. The second and third moments needed by the local regularity proof are supplied
by the native translation-invariant bound. No moment above `b` or moment construction is claimed. -/
theorem sourceModelWitness_cutMassReal_intervalIntegral_deriv_Icc_of_firstMoment
    (d : ℕ) (hd : 1 ≤ d) (α : ℝ) (hα : 0 < α) {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (hoff : ∀ r ∈ Set.Ioo a b, r ∉ (sourceModelWitness d hd α hα).cornerRadii)
    (h1b : (sourceModelWitness d hd α hα).cutMoment 1 b ≠ ⊤) :
    ∫ t in a..b, deriv (sourceModelWitness d hd α hα).cutMassReal t =
      (sourceModelWitness d hd α hα).cutMassReal b -
        (sourceModelWitness d hd α hα).cutMassReal a := by
  have hb : 0 < b := ha.trans hab
  exact sourceModelWitness_cutMassReal_intervalIntegral_deriv_Icc d hd α hα ha hab hoff
    (sourceModelWitness_cutMoment_two_ne_top d hd α hα hb h1b)
    (sourceModelWitness_cutMoment_three_ne_top d hd α hα hb h1b)

end PercLib.CriticalLRP.Orchestration.Witness

#print axioms PercLib.CriticalLRP.Orchestration.Witness.sourceModelWitness_cutMassReal_intervalIntegral_deriv_Icc_of_firstMoment

/-! ## 8. Axiom audit

Every declaration of this packet must rest only on Lean's three standard axioms (`propext`,
`Classical.choice`, `Quot.sound`): no `sorry`, no `native_decide`, no custom axiom.  The
`hashCommand` and long-line linters are switched off so that the audit output is library content
rather than a style violation. -/

set_option linter.hashCommand false
set_option linter.style.longLine false

namespace PercLib.CriticalLRP.Orchestration

#print axioms exists_monotone_finset_exhaustion_of_encodable
#print axioms SourceModelData.exists_monotone_finset_exhaustion
#print axioms exists_monotone_finset_exhaustion_sym2
#print axioms Witness.sourceModelWitness_intervalIntegrable_pivotalWeight
#print axioms Witness.sourceModelWitness_hcontinf_of_moment_two
#print axioms Witness.sourceModelWitness_continuousAt_exclScalar_of_moments
#print axioms Witness.sourceModelWitness_hasDerivAt_cutMassReal_rhsScalar_of_endpoint
#print axioms Witness.sourceModelWitness_hasDerivAt_cutMassReal_rhsScalar_of_endpoint_measurability_discharged
#print axioms Witness.sourceModelWitness_hasDerivAt_cutMassReal_powerLaw_of_endpoint
#print axioms Witness.sourceModelWitness_offCorner_deriv_bound
#print axioms Witness.sourceModelWitness_continuousOn_cutMassReal
#print axioms Witness.sourceModelWitness_cutMassReal_absolutelyContinuousOn_Icc
#print axioms Witness.sourceModelWitness_cutMassReal_abs_sub_le_integral_Icc
#print axioms Witness.sourceModelWitness_cutMassReal_intervalIntegral_deriv_Icc
#print axioms Witness.sourceModelWitness_cutMassReal_ae_differentiableAt_Icc

end PercLib.CriticalLRP.Orchestration
