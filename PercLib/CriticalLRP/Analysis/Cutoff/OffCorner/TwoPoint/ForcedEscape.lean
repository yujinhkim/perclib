/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.
Forced-edge events: locality in a box, escape reduction, and continuity in the cutoff radius.
-/
module

public import PercLib.CriticalLRP.Analysis.Cutoff.OffCorner.TwoPoint.BoxReduction
public import PercLib.CriticalLRP.Analysis.Cutoff.OffCorner.RadiusMeasurability.Main

/-!
# Forced single-edge connection events

The pivotal flux of a fixed edge `e` for the cluster indicator of `y` is the difference of
two *forced* connection probabilities (`integral_flipDiff_indicator`): the probability that
the origin is connected to `y` when `e` is forced open, minus the same probability when `e`
is forced closed.  This file proves that both forced probabilities are continuous in the
cutoff radius, and hence that the fixed-edge pivotal flux is.

The argument is the same localisation as for the two-point function, applied to the
configuration with the single edge `e` flipped:

* the forced connection is carried by the edges of a ball unless the forced cluster of the
  origin leaves it, and the forced cluster is contained in the three ordinary clusters of
  the endpoints of `e` (`cluster_forceOn_singleton_subset`), so the forced escape
  probability tends to `0` and is monotone in the radius;
* the boxed forced connection is determined by the finitely many edges of the box, so the
  finite-range variation bound applies.

The only inputs are the first cutoff moment at a strictly larger radius and the continuity
of the single-edge cutoff profile.
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

/-- **Restriction to a finite edge window is measurable.** -/
theorem measurable_restrictConf (D : Finset (Sym2 M.V)) : Measurable (M.restrictConf D) := by
  classical
  refine measurable_pi_iff.mpr fun f => ?_
  by_cases hf : f ∈ D
  · have h : (fun ω : Config M.V => M.restrictConf D ω f) = fun ω : Config M.V => f ∈ ω := by
      funext ω
      simp only [SourceModelData.restrictConf]
      exact propext (and_iff_right hf)
    rw [h]
    exact measurable_to_prop (by simpa using measurableSet_mem f)
  · have h : (fun ω : Config M.V => M.restrictConf D ω f) = fun _ => False := by
      funext ω
      simp only [SourceModelData.restrictConf]
      exact propext ⟨fun hcon => absurd hcon.1 hf, fun hcon => hcon.elim⟩
    rw [h]
    exact measurable_const

/-- **The cluster with one forced edge is contained in three ordinary clusters.**  Forcing the
single edge `e = s(a,b)` to any state `η` contained in `{e}` can only connect points through
`e`, so any point of the forced cluster of `v` lies in the cluster of `v`, of `a` or of `b`.
This is `cluster_union_subset` for the singleton set of extra edges. -/
theorem cluster_forceOn_singleton_subset {e : Sym2 M.V} {η : Config M.V}
    (hη : ∀ f : Sym2 M.V, f ∈ η → f = e) (ω : Config M.V) {a b : M.V} (hab : e = s(a, b))
    (v : M.V) :
    PercLib.CriticalLRP.cluster (forceOn ({e} : Set (Sym2 M.V)) η ω) v
      ⊆ PercLib.CriticalLRP.cluster ω v ∪ PercLib.CriticalLRP.cluster ω a
        ∪ PercLib.CriticalLRP.cluster ω b := by
  have hsub : forceOn ({e} : Set (Sym2 M.V)) η ω ⊆ ω ∪ ({e} : Set (Sym2 M.V)) := by
    intro f hf
    rw [PercLib.CriticalLRP.forceOn] at hf
    rcases hf with hf | hf
    · exact Or.inl hf.1
    · exact Or.inr hf.2
  have hmain := PercLib.CriticalLRP.cluster_union_subset ω ({e} : Set (Sym2 M.V)) v
  refine (PercLib.CriticalLRP.cluster_mono hsub v).trans ?_
  rw [Set.union_assoc]
  refine hmain.trans ?_
  intro z hz
  rcases hz with hz | hz
  · exact Or.inl hz
  · simp only [Set.mem_iUnion, Set.mem_singleton_iff, exists_prop] at hz
    obtain ⟨e', he', v', hv', hzv⟩ := hz
    subst he'
    rw [hab] at hv'
    rcases Sym2.mem_iff.mp hv' with rfl | rfl
    · exact Or.inr (Or.inl hzv)
    · exact Or.inr (Or.inr hzv)

/-- **Forced escape is bounded by the three ordinary escapes.** -/
theorem escapeForce_subset {e : Sym2 M.V} {η : Config M.V}
    (hη : ∀ f : Sym2 M.V, f ∈ η → f = e) {a b : M.V} (hab : e = s(a, b)) (R : ℝ) :
    M.escapeForce e η R ⊆ M.escapeAt (0 : M.V) R ∪ M.escapeAt a R ∪ M.escapeAt b R := by
  rintro ω ⟨z, hz, hc⟩
  have hcl := M.cluster_forceOn_singleton_subset hη ω hab (0 : M.V)
  rcases hcl (PercLib.CriticalLRP.mem_cluster_iff.mpr hc) with h | h
  · rcases h with h | h
    · exact Or.inl (Or.inl ⟨z, hz, PercLib.CriticalLRP.mem_cluster_iff.mp h⟩)
    · exact Or.inl (Or.inr ⟨z, hz, PercLib.CriticalLRP.mem_cluster_iff.mp h⟩)
  · exact Or.inr ⟨z, hz, PercLib.CriticalLRP.mem_cluster_iff.mp h⟩

/-- The forced escape event is measurable. -/
theorem measurableSet_escapeForce (e : Sym2 M.V) (η : Config M.V) (R : ℝ) :
    MeasurableSet (M.escapeForce e η R) := by
  have h : M.escapeForce e η R = ⋃ z : {z : M.V // z ∉ M.ball R},
      {ω : Config M.V | Connects (forceOn ({e} : Set (Sym2 M.V)) η ω) (0 : M.V) (z : M.V)} := by
    ext ω
    simp only [SourceModelData.escapeForce, Set.mem_ofPred_eq, Set.mem_iUnion]
    exact ⟨fun ⟨z, hz, hc⟩ => ⟨⟨z, hz⟩, hc⟩, fun ⟨z, hc⟩ => ⟨z, z.2, hc⟩⟩
  rw [h]
  refine MeasurableSet.iUnion fun z => ?_
  exact (measurableSet_connects (0 : M.V) (z : M.V)).preimage
    (measurable_forceOn ({e} : Set (Sym2 M.V)) η)

/-- The forced escape event is increasing in the configuration. -/
theorem isIncreasing_escapeForce (e : Sym2 M.V) (η : Config M.V) (R : ℝ) :
    IsIncreasing (M.escapeForce e η R) := by
  rintro ω ω' h ⟨z, hz, hc⟩
  exact ⟨z, hz, connects_mono (monotone_forceOn ({e} : Set (Sym2 M.V)) η h) hc⟩

/-- **The forced escape probability is monotone in the cutoff radius.** -/
theorem escapeForce_real_mono {r r₁ R : ℝ} (hr : 0 < r) (hr₁ : 0 < r₁) (h : r ≤ r₁)
    (e : Sym2 M.V) (η : Config M.V) :
    (M.cutLaw r).real (M.escapeForce e η R) ≤ (M.cutLaw r₁).real (M.escapeForce e η R) :=
  ENNReal.toReal_mono (measure_ne_top _ _)
    (M.cutLaw_mono_of_le hr hr₁ h (M.measurableSet_escapeForce e η R)
      (M.isIncreasing_escapeForce e η R))

/-- **The forced escape probability tends to zero.** -/
theorem exists_escapeForce_lt {r : ℝ} (e : Sym2 M.V) (η : Config M.V) {a b : M.V}
    (hη : ∀ f : Sym2 M.V, f ∈ η → f = e) (hab : e = s(a, b))
    (hfin : M.cutMassAt r 0 ≠ ⊤) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → (M.cutLaw r).real (M.escapeForce e η (n : ℝ)) < ε := by
  have h0 : M.cutMassAt r (0 : M.V) ≠ ⊤ := hfin
  have ha : M.cutMassAt r a ≠ ⊤ := by rw [M.cutMassAt_eq_zero]; exact hfin
  have hb : M.cutMassAt r b ≠ ⊤ := by rw [M.cutMassAt_eq_zero]; exact hfin
  obtain ⟨N0, hN0⟩ := M.exists_escapeAt_lt (0 : M.V) h0 (ε := ε / 3) (by linarith)
  obtain ⟨Na, hNa⟩ := M.exists_escapeAt_lt a ha (ε := ε / 3) (by linarith)
  obtain ⟨Nb, hNb⟩ := M.exists_escapeAt_lt b hb (ε := ε / 3) (by linarith)
  refine ⟨max N0 (max Na Nb), fun n hn => ?_⟩
  have hn0 : N0 ≤ n := le_trans (le_max_left _ _) hn
  have hna : Na ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
  have hnb : Nb ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn
  have hsub := M.escapeForce_subset hη hab (n : ℝ)
  have h1 : (M.cutLaw r).real (M.escapeForce e η (n : ℝ))
      ≤ (M.cutLaw r).real (M.escapeAt (0 : M.V) (n : ℝ) ∪ M.escapeAt a (n : ℝ)
        ∪ M.escapeAt b (n : ℝ)) :=
    measureReal_mono hsub
  have h2 : (M.cutLaw r).real (M.escapeAt (0 : M.V) (n : ℝ) ∪ M.escapeAt a (n : ℝ)
        ∪ M.escapeAt b (n : ℝ))
      ≤ (M.cutLaw r).real (M.escapeAt (0 : M.V) (n : ℝ))
        + (M.cutLaw r).real (M.escapeAt a (n : ℝ))
        + (M.cutLaw r).real (M.escapeAt b (n : ℝ)) := by
    have h := measureReal_union_le (μ := M.cutLaw r)
      (M.escapeAt (0 : M.V) (n : ℝ) ∪ M.escapeAt a (n : ℝ)) (M.escapeAt b (n : ℝ))
    have h' := measureReal_union_le (μ := M.cutLaw r) (M.escapeAt (0 : M.V) (n : ℝ))
      (M.escapeAt a (n : ℝ))
    linarith
  linarith [hN0 n hn0, hNa n hna, hNb n hnb]

end SourceModelData

end PercLib.CriticalLRP.Orchestration
