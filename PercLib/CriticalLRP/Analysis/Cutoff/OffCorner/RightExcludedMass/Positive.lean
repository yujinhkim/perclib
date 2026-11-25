/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.
-/
module

public import PercLib.CriticalLRP.Analysis.Cutoff.OffCorner.RightExcludedMass.ShellPositive
public import PercLib.CriticalLRP.CountableProduct.RestorationCompl

/-!
# Positivity of the shell excluded mass

The shell at an attained radius contributes positive mass. The origin has positive
probability of being isolated: close the loop and the finite incident support, at positive
probability, and close every longer edge almost surely. On this event the excluded
contribution of any one shell vertex is at least one.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.hashCommand false
set_option linter.style.longLine false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP.Orchestration

variable {V : Type*} [MeasurableSpace V]

/-- Intersecting any set with an almost-everywhere true predicate preserves its outer measure. -/
theorem measure_inter_ae_eq_left {μ : Measure V} (A B : Set V) (hB : ∀ᵐ x ∂μ, x ∈ B) :
    μ (A ∩ B) = μ A := by
  apply le_antisymm (measure_mono (Set.inter_subset_left))
  have hzero : μ (A \ B) = 0 := measure_mono_null (Set.inter_subset_right) (mem_ae_iff.mp hB)
  calc
    μ A = μ ((A ∩ B) ∪ (A \ B)) := by rw [Set.inter_union_sdiff]
    _ ≤ μ (A ∩ B) + μ (A \ B) := measure_union_le _ _
    _ = μ (A ∩ B) := by rw [hzero, add_zero]

namespace SourceModelData

variable (M : SourceModelData)

/-- A variant of `ae_far_edge_closed` stated using the source distance rather than the
name of its negated vector. -/
theorem ae_edge_closed_of_dist_far {r : ℝ} (x : M.V) (hxr : r < M.S.dist 0 x) :
    ∀ᵐ ω ∂(M.cutLaw r), s(0, x) ∉ ω := by
  have hx := hxr
  rw [SourceNormData.dist, toVec_sub_eq_neg x 0, SourceNormData.ρ_neg M.S, sub_zero] at hx
  exact M.ae_far_edge_closed x hx

/-- Every edge longer than the cutoff is closed almost everywhere, simultaneously at all
vertices of the countable lattice. -/
theorem ae_all_far_edge_closed (r : ℝ) :
    ∀ᵐ ω ∂(M.cutLaw r), ∀ x : M.V, r < M.S.dist 0 x → s(0, x) ∉ ω := by
  rw [MeasureTheory.ae_all_iff]
  intro x
  by_cases hx : r < M.S.dist 0 x
  · filter_upwards [M.ae_edge_closed_of_dist_far x hx] with ω hω
    exact fun _ => hω
  · exact ae_of_all _ fun _ h => (hx h).elim

/-- The source norm of the origin vanishes. -/
theorem rho_toVec_zero : M.S.ρ (toVec (0 : M.V)) = 0 := by
  have htv : toVec (0 : M.V) = 0 := by
    funext i
    change ((0 : ℤ) : ℝ) = 0
    exact Int.cast_zero
  rw [htv, M.S.ρ_zero]

/-- At a nonempty shell, the excluded shell mass is strictly positive. -/
theorem exclMassShell_ne_zero_of_shell {r : ℝ} (hr : 0 < r) (hshell : (M.shellF r).Nonempty) :
    M.exclMassShell r ≠ 0 := by
  classical
  obtain ⟨x, hx⟩ := hshell
  have hxmem : x ∈ M.shellF r := hx
  have hx0 : x ≠ 0 := by
    intro hxeq
    subst x
    have hn : M.S.ρ (toVec 0) = r := M.mem_shellF.mp hx
    have hz : M.S.ρ (toVec (0 : M.V)) = 0 := M.rho_toVec_zero
    linarith
  let G : Finset (Sym2 M.V) := insert s(0, 0) (finite_incidentSupport M r 0).toFinset
  let A : Set (Config M.V) := {ω | ∀ e ∈ G, e ∉ ω}
  let B : Set (Config M.V) := {ω | ∀ u : M.V, r < M.S.dist 0 u → s(0, u) ∉ ω}
  have hGprob : 0 < (M.cutLaw r) A := M.cutLaw_all_closed_pos G
  have hAB : (M.cutLaw r) (A ∩ B) = (M.cutLaw r) A :=
    measure_inter_ae_eq_left A B (M.ae_all_far_edge_closed r)
  have hmeas : MeasurableSet (A ∩ B) := by
    have h1 : MeasurableSet A := by
      have hA : A = ⋂ e ∈ G, {ω : Config M.V | e ∉ ω} := by
        ext ω
        simp only [A, Set.mem_iInter, Set.mem_ofPred_eq]
      rw [hA]
      exact Finset.measurableSet_biInter G fun e _ => (measurableSet_mem e).compl
    have h2 : MeasurableSet B := by
      have heq : B = ⋂ u : {u : M.V // r < M.S.dist 0 u},
          {ω : Config M.V | s(0, (u : M.V)) ∉ ω} := by
        ext ω
        simp only [B, Set.mem_iInter, Set.mem_ofPred_eq]
        constructor
        · intro h u
          exact h u u.property
        · intro h u hu
          exact h ⟨u, hu⟩
      rw [heq]
      exact MeasurableSet.iInter fun u => (measurableSet_mem s(0, (u : M.V))).compl
    exact h1.inter h2
  have hpoint : ∀ ω : Config M.V, (A ∩ B).indicator (fun _ => (1 : ℝ≥0∞)) ω ≤ M.exclShellFun r ω := by
    intro ω
    by_cases hω : ω ∈ A ∩ B
    · rw [Set.indicator_of_mem hω]
      have hcl : cluster ω 0 = {0} := cluster_eq_singleton_of_isolated fun u => by
        by_cases hu0 : u = 0
        · subst u
          exact hω.1 _ (by simp [G])
        by_cases hu : M.S.dist 0 u ≤ r
        · have he : s(0, u) ∈ G := Finset.mem_insert_of_mem
            ((finite_incidentSupport M r 0).mem_toFinset.mpr
              ⟨Sym2.mem_mk_left 0 u, 0, u, Ne.symm hu0, rfl, hu⟩)
          exact hω.1 _ he
        · exact hω.2 u (not_le.mp hu)
      have hroot : clusterVol ω (0 : M.V) = 1 := by
        rw [clusterVol_eq_encard, hcl]
        simp
      rw [SourceModelData.exclShellFun, hroot, hcl, one_mul]
      calc
        (1 : ℝ≥0∞) ≤ (({0} : Set M.V)ᶜ).indicator
            (fun _ => (1 : ℝ≥0∞)) x * clusterVol ω x := by
              rw [Set.indicator_of_mem (by simpa using hx0), one_mul]
              exact SourceModelData.one_le_clusterVol (V := M.V) ω x
        _ ≤ ∑ y ∈ M.shellF r, (({0} : Set M.V)ᶜ).indicator
            (fun _ => (1 : ℝ≥0∞)) y * clusterVol ω y :=
          Finset.single_le_sum
            (f := fun y => (({0} : Set M.V)ᶜ).indicator
              (fun _ => (1 : ℝ≥0∞)) y * clusterVol ω y)
            (fun y _ => zero_le) hxmem
    · rw [Set.indicator_of_notMem hω]
      exact zero_le
  have hpos : 0 < M.exclMassShell r := by
    rw [SourceModelData.exclMassShell]
    calc
      0 < (M.cutLaw r) (A ∩ B) := by rw [hAB]; exact hGprob
      _ = ∫⁻ ω, (A ∩ B).indicator (fun _ => (1 : ℝ≥0∞)) ω ∂(M.cutLaw r) := by
          rw [lintegral_indicator_const hmeas 1, one_mul]
      _ ≤ ∫⁻ ω, M.exclShellFun r ω ∂(M.cutLaw r) := lintegral_mono hpoint
  exact ne_of_gt hpos

/-- The shell at radius zero is the origin singleton. -/
theorem shellF_zero : M.shellF 0 = {0} := by
  ext y
  rw [M.mem_shellF, Finset.mem_singleton]
  constructor
  · intro h
    by_contra hy
    have htv : toVec y ≠ 0 := by
      intro h0
      refine hy (funext fun i => ?_)
      have hi : ((y i : ℝ)) = 0 := by
        have hi := congrFun h0 i
        simpa [toVec] using hi
      exact_mod_cast hi
    have hpos := M.S.ρ_pos (toVec y) htv
    linarith
  · rintro rfl
    exact M.rho_toVec_zero

/-- At radius zero the shell excluded mass vanishes, even though its shell is nonempty. -/
theorem exclMassShell_zero : M.exclMassShell 0 = 0 := by
  have hshell : M.shellF 0 = {0} := M.shellF_zero
  have hzero : ∀ ω : Config M.V, M.exclShellFun 0 ω = 0 := by
    intro ω
    rw [SourceModelData.exclShellFun, hshell, Finset.sum_singleton]
    rw [Set.indicator_of_notMem (by simp [PercLib.Percolation.Bond.mem_cluster_self])]
    simp
  rw [SourceModelData.exclMassShell]
  simp only [hzero]
  simp

/-- An empty activation shell carries no excluded mass. -/
theorem exclMassShell_eq_zero_of_shellF_eq_empty {r : ℝ} (h : M.shellF r = ∅) :
    M.exclMassShell r = 0 := by
  have hzero : ∀ ω : Config M.V, M.exclShellFun r ω = 0 := by
    intro ω
    rw [SourceModelData.exclShellFun, h, Finset.sum_empty, mul_zero]
  rw [SourceModelData.exclMassShell]
  simp only [hzero]
  simp

/-- No vertex lies on a negative source-norm sphere. -/
theorem shellF_eq_empty_of_neg {r : ℝ} (hr : r < 0) : M.shellF r = ∅ := by
  refine Finset.eq_empty_iff_forall_notMem.mpr fun y hy => ?_
  have h1 : M.S.ρ (toVec y) = r := M.mem_shellF.mp hy
  rcases eq_or_ne y 0 with hy0 | hy0
  · subst hy0
    rw [M.rho_toVec_zero] at h1
    linarith
  · have hpos := M.S.ρ_pos (toVec y) (by
      intro h
      exact hy0 (funext fun i => by
        have hi : ((y i : ℝ)) = 0 := by
          have hi := congrFun h i
          simpa [toVec] using hi
        exact_mod_cast hi))
    linarith

/-- The shell mass is nonzero exactly at positive radii with nonempty shell. -/
theorem exclMassShell_ne_zero_iff {r : ℝ} :
    M.exclMassShell r ≠ 0 ↔ 0 < r ∧ (M.shellF r).Nonempty := by
  constructor
  · intro hne
    rcases lt_trichotomy r 0 with hr | hr | hr
    · exact absurd (M.exclMassShell_eq_zero_of_shellF_eq_empty (M.shellF_eq_empty_of_neg hr)) hne
    · subst hr
      exact absurd M.exclMassShell_zero hne
    · refine ⟨hr, ?_⟩
      by_contra hemp
      exact hne (M.exclMassShell_eq_zero_of_shellF_eq_empty
        (Finset.not_nonempty_iff_eq_empty.mp hemp))
  · rintro ⟨hr, hne⟩
    exact M.exclMassShell_ne_zero_of_shell hr hne

end SourceModelData

end Orchestration
end CriticalLRP
end PercLib

/-
# Axiom audit
-/

#print axioms PercLib.CriticalLRP.Orchestration.measure_inter_ae_eq_left
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.ae_edge_closed_of_dist_far
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.ae_all_far_edge_closed
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.exclMassShell_ne_zero_of_shell
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.rho_toVec_zero
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.shellF_zero
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.exclMassShell_zero
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.exclMassShell_ne_zero_iff
