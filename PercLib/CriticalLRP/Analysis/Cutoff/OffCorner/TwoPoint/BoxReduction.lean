/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.
Reduction of the two-point connection event to a finite box plus an escape event.
-/
module

public import PercLib.CriticalLRP.Analysis.Cutoff.OffCorner.TwoPoint.MarkCoupling
public import PercLib.CriticalLRP.Analysis.Cutoff.OffCorner.TwoPoint.EscapeLimit
public import PercLib.CriticalLRP.Analysis.Cutoff.OffCorner.TwoPoint.KernelCont
public import PercLib.CriticalLRP.Analysis.Cutoff.OffCorner.PairMassRegularity.Main

/-!
# Localising the connection event to a finite box

For a finite edge set `D` carrying the edges inside the lattice ball of radius `R`, the event
`boxConn D y` — the origin is connected to `y` inside the sub-configuration on `D` — has two
properties that the two-point function needs:

* it is contained in the full connection event, and the difference lies inside the escape
  event `escapeConf R`: if the cluster of the origin stays inside the ball, then the boxed
  cluster is the whole cluster (`SourceModelData.cluster_subset_of_eq_on_box_gen`);
* it is determined by the coordinates on `D`, so its probability under two edge profiles
  that agree on `D` is the same (`edgeMeasure_congr_of_eq_on`), which reduces the
  comparison of the cutoff laws at two radii to the finite-range variation bound
  `edgeMeasure_abs_sub_le`.

Together with monotonicity of the escape probability in the cutoff radius this gives a
uniform control of the two-point function near a positive radius with finite cutoff mass.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.hashCommand false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP

section Generic

variable {V : Type*} [Countable V]

/-- **Probabilities of events determined by a finite block only depend on that block.** -/
theorem edgeMeasure_congr_of_eq_on (p q : Sym2 V → unitInterval) (D : Finset (Sym2 V))
    (hD : ∀ e ∈ D, p e = q e) {A : Set (Config V)} (hA : MeasurableSet A)
    (hdet : ∀ ω ω' : Config V, (∀ e ∈ D, ω e = ω' e) → (ω ∈ A ↔ ω' ∈ A)) :
    edgeMeasure p A = edgeMeasure q A := by
  have hpre : (atParameter p) ⁻¹' A = (atParameter q) ⁻¹' A := by
    ext u
    have hcfg : ∀ e ∈ D, atParameter p u e = atParameter q u e := by
      intro e he
      have hp : (p e : ℝ) = (q e : ℝ) := by rw [hD e he]
      change (u e < (p e : ℝ)) = (u e < (q e : ℝ))
      rw [hp]
    exact hdet _ _ hcfg
  have hkey : ∀ r : Sym2 V → unitInterval,
      edgeMeasure r A = (markMeasure V) ((atParameter r) ⁻¹' A) := by
    intro r
    rw [← markMeasure_map_atParameter r]
    exact Measure.map_apply (measurable_atParameter r) hA
  rw [hkey p, hkey q, hpre]

end Generic

namespace Orchestration

namespace SourceModelData

variable (M : SourceModelData)

/-- The invariant sub-configuration on `D` is contained in the full configuration. -/
theorem restrictConf_subset (D : Finset (Sym2 M.V)) (ω : Config M.V) :
    ∀ e, e ∈ M.restrictConf D ω → e ∈ ω :=
  fun _ he => he.2

/-- **The boxed connection event is measurable.** -/
theorem measurableSet_boxConn (D : Finset (Sym2 M.V)) (y : M.V) :
    MeasurableSet (M.boxConn D y) := by
  classical
  have h : M.boxConn D y = ⋃ (s : Finset (Sym2 M.V)),
      {ω : Config M.V | (∃ p : (⊤ : SimpleGraph M.V).Walk (0 : M.V) y,
        p.edges.toFinset = s) ∧ s ⊆ D ∧ ∀ e ∈ s, e ∈ ω} := by
    ext ω
    constructor
    · intro hconn
      simp only [SourceModelData.boxConn, SourceModelData.boxConnAt, Set.mem_ofPred_eq] at hconn
      rw [← pathConnects_iff] at hconn
      obtain ⟨p, hp⟩ := hconn
      refine Set.mem_iUnion.mpr ⟨p.edges.toFinset, ⟨p, rfl⟩, ?_, ?_⟩
      · intro e he
        exact (hp e (by simpa using he)).1
      · intro e he
        exact (hp e (by simpa using he)).2
    · intro hmem
      simp only [Set.mem_iUnion, Set.mem_ofPred_eq] at hmem
      rcases hmem with ⟨s, ⟨p, hp⟩, hsD, hω⟩
      simp only [SourceModelData.boxConn, SourceModelData.boxConnAt, Set.mem_ofPred_eq]
      rw [← pathConnects_iff]
      have hmem : ∀ e ∈ p.edges, e ∈ s := by
        intro e he
        rw [← hp]
        simpa using he
      exact ⟨p, fun e he => ⟨hsD (hmem e he), hω e (hmem e he)⟩⟩
  rw [h]
  refine MeasurableSet.iUnion fun s => ?_
  by_cases hsD : s ⊆ D
  · by_cases hex : ∃ p : (⊤ : SimpleGraph M.V).Walk (0 : M.V) y, p.edges.toFinset = s
    · have hset : {ω : Config M.V | (∃ p : (⊤ : SimpleGraph M.V).Walk (0 : M.V) y,
          p.edges.toFinset = s) ∧ s ⊆ D ∧ ∀ e ∈ s, e ∈ ω}
          = {ω : Config M.V | ∀ e ∈ s, e ∈ ω} := by
        ext ω
        simp [hex, hsD]
      rw [hset]
      exact measurableSet_allOpen s
    · have hset : {ω : Config M.V | (∃ p : (⊤ : SimpleGraph M.V).Walk (0 : M.V) y,
          p.edges.toFinset = s) ∧ s ⊆ D ∧ ∀ e ∈ s, e ∈ ω} = ∅ := by
        ext ω
        simp [hex]
      rw [hset]
      exact MeasurableSet.empty
  · have hset : {ω : Config M.V | (∃ p : (⊤ : SimpleGraph M.V).Walk (0 : M.V) y,
        p.edges.toFinset = s) ∧ s ⊆ D ∧ ∀ e ∈ s, e ∈ ω} = ∅ := by
      ext ω
      simp [hsD]
    rw [hset]
    exact MeasurableSet.empty

/-- The boxed connection event is determined by the coordinates on `D`. -/
theorem boxConn_congr (D : Finset (Sym2 M.V)) (y : M.V) {ω ω' : Config M.V}
    (h : ∀ e ∈ D, ω e = ω' e) : (ω ∈ M.boxConn D y ↔ ω' ∈ M.boxConn D y) := by
  have hcfg : M.restrictConf D ω = M.restrictConf D ω' := by
    funext e
    by_cases he : e ∈ D
    · have hh : ω e = ω' e := h e he
      simp only [SourceModelData.restrictConf, he, true_and]
      exact hh
    · simp only [SourceModelData.restrictConf, he, false_and]
  simp only [SourceModelData.boxConn, SourceModelData.boxConnAt, Set.mem_ofPred_eq, hcfg]

/-- The boxed connection event is contained in the full connection event. -/
theorem boxConn_subset_conn (D : Finset (Sym2 M.V)) (y : M.V) :
    M.boxConn D y ⊆ {ω : Config M.V | Connects ω (0 : M.V) y} :=
  fun _ h => connects_mono (M.restrictConf_subset D _) h

/-- **Escape lemma.**  A connection that is not carried by the edges inside the lattice ball
of radius `R` must leave that ball. -/
theorem conn_sdiff_boxConn_subset_escapeConf (R : ℝ) (y : M.V) :
    {ω : Config M.V | Connects ω (0 : M.V) y} \ M.boxConn (M.boxEdges R) y
      ⊆ M.escapeConf R := by
  intro ω hω
  obtain ⟨hconn, hbox⟩ := hω
  by_contra hno
  simp only [SourceModelData.escapeConf, SourceModelData.escapeAt, Set.mem_ofPred_eq] at hno
  push Not at hno
  apply hbox
  have hsub : PercLib.CriticalLRP.cluster ω (0 : M.V) ⊆ M.ball R := by
    intro z hz
    by_contra hz'
    exact hno z hz' (mem_cluster_iff.mp hz)
  have hcl := M.cluster_subset_of_eq_on_box_gen (R := R) (v := (0 : M.V))
    (ω := ω) (ω' := M.restrictConf (M.boxEdges R) ω)
    (fun e he he' => ⟨he, he'⟩) hsub
  exact hcl (mem_cluster_iff.mpr hconn)

/-- **The escape probability is monotone in the cutoff radius.** -/
theorem escapeConf_real_mono {r r₁ R : ℝ} (hr : 0 < r) (hr₁ : 0 < r₁) (h : r ≤ r₁) :
    (M.cutLaw r).real (M.escapeConf R) ≤ (M.cutLaw r₁).real (M.escapeConf R) :=
  ENNReal.toReal_mono (measure_ne_top _ _)
    (M.cutLaw_mono_of_le hr hr₁ h (M.measurableSet_escapeAt (0 : M.V) R) (M.isIncreasing_escapeAt (0 : M.V) R))

end SourceModelData

end Orchestration

end PercLib.CriticalLRP
