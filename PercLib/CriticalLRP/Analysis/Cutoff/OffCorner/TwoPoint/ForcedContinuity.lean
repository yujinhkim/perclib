/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.
Continuity of the forced single-edge connection probabilities and of the pivotal flux.
-/
module

public import PercLib.CriticalLRP.Analysis.Cutoff.OffCorner.TwoPoint.ForcedEscape

/-!
# Continuity of the forced connection probabilities and of the fixed-edge pivotal flux

The pivotal flux of a fixed edge `e` for the cluster indicator of `y` is the difference of
the forced-open and forced-closed connection probabilities

  `pivotalFlux μ 1{y ∈ K_0} e = μ.real (rawOpenEvent e E) - μ.real (rawClosedEvent e E)`

(`integral_flipDiff_indicator`).  Both forced probabilities are continuous in the cutoff
radius at every positive `r₀` at which the first cutoff moment is finite at a larger radius:
the boxed forced connection depends only on the finitely many edges of the box, so the
finite-range variation bound applies, while the forced escape probability is controlled by
the three ordinary escapes of `escapeForce_subset` and tends to `0`.

Hence the fixed-edge pivotal flux is continuous in the cutoff radius.  This is the
"directly forced-edge analogue" of the two-point continuity statement; no off-corner
hypothesis is needed, and the only moment input is the first cutoff moment at a strictly
larger radius.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.hashCommand false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP.Orchestration

namespace SourceModelData

variable (M : SourceModelData)

/-- **The boxed forced connection event is measurable.** -/
theorem measurableSet_boxForce (e : Sym2 M.V) (η : Config M.V) (D : Finset (Sym2 M.V))
    (y : M.V) : MeasurableSet (M.boxForce e η D y) := by
  have hmap : Measurable fun ω : Config M.V =>
      M.restrictConf D (forceOn ({e} : Set (Sym2 M.V)) η ω) :=
    (M.measurable_restrictConf D).comp (measurable_forceOn ({e} : Set (Sym2 M.V)) η)
  exact (measurableSet_connects (0 : M.V) y).preimage hmap

/-- The boxed forced connection event is determined by the coordinates on `D`: the forced
edge `e` contributes a constant on `D`, and every other edge of `D` is read off `ω`. -/
theorem boxForce_congr {e : Sym2 M.V} {η : Config M.V} {D : Finset (Sym2 M.V)}
    {y : M.V} {ω ω' : Config M.V} (h : ∀ f ∈ D, ω f = ω' f) :
    (ω ∈ M.boxForce e η D y ↔ ω' ∈ M.boxForce e η D y) := by
  have hcfg : M.restrictConf D (forceOn ({e} : Set (Sym2 M.V)) η ω)
      = M.restrictConf D (forceOn ({e} : Set (Sym2 M.V)) η ω') := by
    funext f
    by_cases hf : f ∈ D
    · have hforce : (forceOn ({e} : Set (Sym2 M.V)) η ω f)
          = (forceOn ({e} : Set (Sym2 M.V)) η ω' f) := by
        by_cases hfe : f = e
        · have h1 : (f ∈ forceOn ({e} : Set (Sym2 M.V)) η ω) ↔ f ∈ η := by
            simp only [PercLib.CriticalLRP.forceOn, Set.mem_union, Set.mem_sdiff,
              Set.mem_inter_iff, Set.mem_singleton_iff, hfe, not_true,
              and_false, false_or, and_true]
          have h2 : (f ∈ forceOn ({e} : Set (Sym2 M.V)) η ω') ↔ f ∈ η := by
            simp only [PercLib.CriticalLRP.forceOn, Set.mem_union, Set.mem_sdiff,
              Set.mem_inter_iff, Set.mem_singleton_iff, hfe, not_true,
              and_false, false_or, and_true]
          exact propext (h1.trans h2.symm)
        · have h1 := mem_forceOn_of_notMem (S := ({e} : Set (Sym2 M.V))) (e := f)
            (by simpa using hfe) η ω
          have h2 := mem_forceOn_of_notMem (S := ({e} : Set (Sym2 M.V))) (e := f)
            (by simpa using hfe) η ω'
          exact propext (h1.trans ((Iff.of_eq (h f hf)).trans h2.symm))
      simp only [SourceModelData.restrictConf, hf, true_and, hforce]
    · simp only [SourceModelData.restrictConf, hf, false_and]
  simp only [SourceModelData.boxForce, Set.mem_ofPred_eq]
  rw [hcfg]

/-- The boxed forced connection event implies the forced connection event. -/
theorem boxForce_subset (e : Sym2 M.V) (η : Config M.V) (D : Finset (Sym2 M.V)) (y : M.V) :
    M.boxForce e η D y ⊆
      {ω : Config M.V | Connects (forceOn ({e} : Set (Sym2 M.V)) η ω) (0 : M.V) y} :=
  fun _ h => connects_mono (M.restrictConf_subset D _) h

/-- **Escape lemma for a forced edge.**  A forced connection that is not carried by the edges
inside the ball of radius `R` forces the cluster of the origin to leave that ball. -/
theorem forced_sdiff_boxForce_subset (e : Sym2 M.V) (η : Config M.V) (R : ℝ) (y : M.V) :
    {ω : Config M.V | Connects (forceOn ({e} : Set (Sym2 M.V)) η ω) (0 : M.V) y}
        \ M.boxForce e η (M.boxEdges R) y ⊆ M.escapeForce e η R := by
  intro ω hω
  obtain ⟨hconn, hbox⟩ := hω
  by_contra hno
  simp only [SourceModelData.escapeForce, Set.mem_ofPred_eq] at hno
  push Not at hno
  apply hbox
  have hsub : PercLib.CriticalLRP.cluster (forceOn ({e} : Set (Sym2 M.V)) η ω) (0 : M.V)
      ⊆ M.ball R := by
    intro z hz
    by_contra hz'
    exact hno z hz' (PercLib.CriticalLRP.mem_cluster_iff.mp hz)
  have hcl := M.cluster_subset_of_eq_on_box_gen (R := R) (v := (0 : M.V))
    (ω := forceOn ({e} : Set (Sym2 M.V)) η ω)
    (ω' := M.restrictConf (M.boxEdges R) (forceOn ({e} : Set (Sym2 M.V)) η ω))
    (fun f hfD hfF => ⟨hfD, hfF⟩) hsub
  simp only [SourceModelData.boxForce]
  exact hcl (PercLib.CriticalLRP.mem_cluster_iff.mpr hconn)

/-- **Comparison of a forced connection probability across two radii.** -/
theorem forcedEvent_abs_sub_le (e : Sym2 M.V) (η : Config M.V) (y : M.V) (r r0 R : ℝ) :
    |(M.cutLaw r).real ((fun ω : Config M.V => forceOn ({e} : Set (Sym2 M.V)) η ω) ⁻¹'
          {σ : Config M.V | Connects σ (0 : M.V) y})
        - (M.cutLaw r0).real ((fun ω : Config M.V => forceOn ({e} : Set (Sym2 M.V)) η ω) ⁻¹'
          {σ : Config M.V | Connects σ (0 : M.V) y})|
      ≤ (∑ f ∈ M.boxEdges R, |(M.cutProb r f : ℝ) - (M.cutProb r0 f : ℝ)|)
        + (M.cutLaw r).real (M.escapeForce e η R)
        + (M.cutLaw r0).real (M.escapeForce e η R) := by
  set D : Finset (Sym2 M.V) := M.boxEdges R with hD
  have hbox : MeasurableSet (M.boxForce e η D y) := M.measurableSet_boxForce e η D y
  have hsub : ((fun ω : Config M.V => forceOn ({e} : Set (Sym2 M.V)) η ω) ⁻¹'
        {σ : Config M.V | Connects σ (0 : M.V) y})
      ⊆ M.boxForce e η D y ∪ M.escapeForce e η R := by
    intro ω hω
    by_cases hb : ω ∈ M.boxForce e η D y
    · exact Or.inl hb
    · exact Or.inr (M.forced_sdiff_boxForce_subset e η R y ⟨hω, hb⟩)
  have hboxsub : M.boxForce e η D y ⊆
      ((fun ω : Config M.V => forceOn ({e} : Set (Sym2 M.V)) η ω) ⁻¹'
        {σ : Config M.V | Connects σ (0 : M.V) y}) :=
    fun _ h => M.boxForce_subset e η D y h
  set q : Sym2 M.V → unitInterval :=
    fun f => if f ∈ D then M.cutProb r f else M.cutProb r0 f with hq
  have hqD : ∀ f ∈ D, M.cutProb r f = q f := by
    intro f hf
    change M.cutProb r f = (if f ∈ D then M.cutProb r f else M.cutProb r0 f)
    rw [ite_eq_left hf]
  have hq_out : ∀ f, q f ≠ M.cutProb r0 f → f ∈ D := by
    intro f hf
    by_contra hmem
    apply hf
    change (if f ∈ D then M.cutProb r f else M.cutProb r0 f) = M.cutProb r0 f
    rw [ite_eq_right hmem]
  have hdet : ∀ ω ω' : Config M.V, (∀ f ∈ D, ω f = ω' f) →
      (ω ∈ M.boxForce e η D y ↔ ω' ∈ M.boxForce e η D y) :=
    fun _ _ h => M.boxForce_congr h
  have hcongr₁ : (edgeMeasure (M.cutProb r)) (M.boxForce e η D y)
      = (edgeMeasure q) (M.boxForce e η D y) :=
    edgeMeasure_congr_of_eq_on (p := M.cutProb r) (q := q) D hqD hbox hdet
  have hsum_eq : (∑ f ∈ D, |(q f : ℝ) - (M.cutProb r0 f : ℝ)|)
      = ∑ f ∈ D, |(M.cutProb r f : ℝ) - (M.cutProb r0 f : ℝ)| := by
    refine Finset.sum_congr rfl fun f hf => ?_
    rw [hqD f hf]
  have hTV : |(M.cutLaw r).real (M.boxForce e η D y)
      - (M.cutLaw r0).real (M.boxForce e η D y)|
      ≤ ∑ f ∈ D, |(M.cutProb r f : ℝ) - (M.cutProb r0 f : ℝ)| := by
    rw [measureReal_def, measureReal_def,
      show M.cutLaw r = edgeMeasure (M.cutProb r) from rfl,
      show M.cutLaw r0 = edgeMeasure (M.cutProb r0) from rfl]
    have hraw := edgeMeasure_abs_sub_le q (M.cutProb r0) D hq_out (M.boxForce e η D y) hbox
    rw [hsum_eq] at hraw
    rw [← hcongr₁] at hraw
    exact hraw
  have h1 : (M.cutLaw r).real ((fun ω : Config M.V => forceOn ({e} : Set (Sym2 M.V)) η ω) ⁻¹'
        {σ : Config M.V | Connects σ (0 : M.V) y})
      ≤ (M.cutLaw r).real (M.boxForce e η D y) + (M.cutLaw r).real (M.escapeForce e η R) := by
    calc (M.cutLaw r).real ((fun ω : Config M.V => forceOn ({e} : Set (Sym2 M.V)) η ω) ⁻¹'
          {σ : Config M.V | Connects σ (0 : M.V) y})
        ≤ (M.cutLaw r).real (M.boxForce e η D y ∪ M.escapeForce e η R) := measureReal_mono hsub
      _ ≤ _ + _ := measureReal_union_le _ _
  have h2 : (M.cutLaw r0).real ((fun ω : Config M.V => forceOn ({e} : Set (Sym2 M.V)) η ω) ⁻¹'
        {σ : Config M.V | Connects σ (0 : M.V) y})
      ≤ (M.cutLaw r0).real (M.boxForce e η D y) + (M.cutLaw r0).real (M.escapeForce e η R) := by
    calc (M.cutLaw r0).real ((fun ω : Config M.V => forceOn ({e} : Set (Sym2 M.V)) η ω) ⁻¹'
          {σ : Config M.V | Connects σ (0 : M.V) y})
        ≤ (M.cutLaw r0).real (M.boxForce e η D y ∪ M.escapeForce e η R) := measureReal_mono hsub
      _ ≤ _ + _ := measureReal_union_le _ _
  have hmono : (M.cutLaw r0).real (M.boxForce e η D y)
      ≤ (M.cutLaw r0).real ((fun ω : Config M.V => forceOn ({e} : Set (Sym2 M.V)) η ω) ⁻¹'
        {σ : Config M.V | Connects σ (0 : M.V) y}) :=
    measureReal_mono hboxsub
  have hmono_r : (M.cutLaw r).real (M.boxForce e η D y)
      ≤ (M.cutLaw r).real ((fun ω : Config M.V => forceOn ({e} : Set (Sym2 M.V)) η ω) ⁻¹'
        {σ : Config M.V | Connects σ (0 : M.V) y}) :=
    measureReal_mono hboxsub
  have hA' : (M.cutLaw r).real (M.boxForce e η D y)
      ≤ (M.cutLaw r0).real (M.boxForce e η D y)
        + ∑ f ∈ D, |(M.cutProb r f : ℝ) - (M.cutProb r0 f : ℝ)| := by
    have hle := (abs_le.mp hTV).2
    linarith
  have hB' : (M.cutLaw r0).real (M.boxForce e η D y)
      ≤ (M.cutLaw r).real (M.boxForce e η D y)
        + ∑ f ∈ D, |(M.cutProb r f : ℝ) - (M.cutProb r0 f : ℝ)| := by
    have hle := (abs_le.mp hTV).1
    linarith
  rw [hD] at hA' hB'
  rw [abs_le]
  constructor <;> linarith

end SourceModelData

end PercLib.CriticalLRP.Orchestration
