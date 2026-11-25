/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.
New glue on the D-2 interface, using mathlib infinitePi_map_pi and
map_bernoulliMeasure at revision 56a005855ea17e0b0958f73ec801ae140b0a1679.
No upstream proof is copied. The probability space retains diagonal coordinates;
only observables insensitive to them have equal distributions.
-/
module

public import PercLib.Percolation.Bond.Susceptibility

@[expose] public section

open MeasureTheory ProbabilityTheory Set PercLib.Probability
open scoped ENNReal

namespace PercLib.Percolation.Bond

variable {V : Type*}

/-- Removing diagonal pairs does not change the open graph. -/
theorem openGraph_sdiff_diagSet (ω : Config V) :
    openGraph (ω \ Sym2.diagSet) = openGraph ω := by
  ext x y
  simp only [openGraph_adj_iff, Set.mem_sdiff, Sym2.mem_diagSet, Sym2.mk_isDiag_iff]
  tauto

/-- Deleting the diagonal is a measurable configuration map for any vertex type. -/
theorem measurable_sdiff_diagSet :
    Measurable (fun ω : Config V => ω \ Sym2.diagSet) := by
  apply Measurable.of_mem
  intro e
  exact ((measurableSet_mem e).inter (MeasurableSet.const _)).mem

open Classical in
/-- The law after deleting loops is the law with zero diagonal parameters. -/
theorem law_map_sdiff_diagSet (p : Sym2 V → unitInterval) :
    (law p).map (fun ω => ω \ Sym2.diagSet) =
      law (fun e => if e.IsDiag then 0 else p e) := by
  classical
  have hpi := Measure.infinitePi_map_pi
    (μ := fun e => bernoulliMeasure True False (p e))
    (f := fun e (b : Prop) => b ∧ ¬ e.IsDiag) (fun _ => by fun_prop)
  have hm : (fun e => (bernoulliMeasure True False (p e)).map
      (fun b => b ∧ ¬ e.IsDiag)) =
      (fun e => bernoulliMeasure True False (if e.IsDiag then 0 else p e)) := by
    funext e
    rw [map_bernoulliMeasure]
    by_cases hd : e.IsDiag <;> simp [hd]
  rw [hm] at hpi
  simp only [law, prodBernoulli_eq_map]
  rw [Measure.map_map measurable_sdiff_diagSet measurable_setOfPred,
    ← hpi, Measure.map_map measurable_setOfPred (by fun_prop)]
  congr 1

/-- Profiles agreeing off the diagonal give the same loop-erased configuration law. -/
theorem law_map_sdiff_diagSet_eq (p q : Sym2 V → unitInterval)
    (hpq : ∀ e, ¬ e.IsDiag → p e = q e) :
    (law p).map (fun ω => ω \ Sym2.diagSet) =
      (law q).map (fun ω => ω \ Sym2.diagSet) := by
  classical
  rw [law_map_sdiff_diagSet, law_map_sdiff_diagSet]
  congr 1
  funext e
  split_ifs with h
  · rfl
  · exact hpq e h

/-- Every measurable observable unchanged by deleting loops has the same law. -/
theorem law_map_eq_of_offDiagonal {α : Type*} [MeasurableSpace α]
    (p q : Sym2 V → unitInterval) (hpq : ∀ e, ¬ e.IsDiag → p e = q e)
    (f : Config V → α) (hf : Measurable f)
    (hdiag : ∀ ω, f (ω \ Sym2.diagSet) = f ω) :
    (law p).map f = (law q).map f := by
  have h := congrArg (Measure.map f) (law_map_sdiff_diagSet_eq p q hpq)
  simpa only [Measure.map_map hf measurable_sdiff_diagSet, Function.comp_def, hdiag] using h

/-- Measurable events determined by the non-diagonal coordinates have equal probability. -/
theorem law_event_eq_of_offDiagonal (p q : Sym2 V → unitInterval)
    (hpq : ∀ e, ¬ e.IsDiag → p e = q e) {A : Set (Config V)}
    (hA : MeasurableSet A)
    (hdep : ∀ ω ω', ω \ Sym2.diagSet = ω' \ Sym2.diagSet → (ω ∈ A ↔ ω' ∈ A)) :
    law p A = law q A := by
  have hpre : (fun ω : Config V => ω \ Sym2.diagSet) ⁻¹' A = A := by
    ext ω
    exact hdep _ _ (by ext e; simp)
  have h := congrArg (fun μ : Measure (Config V) => μ A) (law_map_sdiff_diagSet_eq p q hpq)
  simpa only [Measure.map_apply measurable_sdiff_diagSet hA, hpre] using h

variable [Countable V]

/-- Two-point probabilities depend only on off-diagonal parameters. -/
theorem tau_eq_of_offDiagonal (p q : Sym2 V → unitInterval)
    (hpq : ∀ e, ¬ e.IsDiag → p e = q e) (x y : V) : tau p x y = tau q x y := by
  apply law_event_eq_of_offDiagonal p q hpq (measurableSet_conn x y)
  intro ω ω' h
  have hg : openGraph ω = openGraph ω' := by
    rw [← openGraph_sdiff_diagSet ω, h, openGraph_sdiff_diagSet]
  simp only [mem_conn_iff, hg]

/-- The distribution of full ENat-valued cluster volume is diagonal-insensitive. -/
theorem cluster_volume_law_eq_of_offDiagonal (p q : Sym2 V → unitInterval)
    (hpq : ∀ e, ¬ e.IsDiag → p e = q e) (x : V) :
    (law p).map (fun ω => (cluster ω x).encard) =
      (law q).map (fun ω => (cluster ω x).encard) := by
  apply law_map_eq_of_offDiagonal p q hpq _ (measurable_encard_cluster x)
  intro ω
  simp only [cluster, openGraph_sdiff_diagSet]

/-- Susceptibility is diagonal-insensitive even when it is infinite. -/
theorem chi_eq_of_offDiagonal (p q : Sym2 V → unitInterval)
    (hpq : ∀ e, ¬ e.IsDiag → p e = q e) (x : V) : chi p x = chi q x := by
  simp_rw [chi_eq_tsum_tau, tau_eq_of_offDiagonal p q hpq]

-- Opposite diagonal endpoints do not affect susceptibility on the two-vertex graph.
open Classical in
example (p : Sym2 Bool → unitInterval) (x : Bool) :
    chi (fun e => if e.IsDiag then 0 else p e) x =
      chi (fun e => if e.IsDiag then 1 else p e) x :=
  chi_eq_of_offDiagonal _ _ (fun e he => by simp [he]) x

-- The same equality covers infinite susceptibility, not merely finite moments.
open Classical in
example : chi (fun e : Sym2 ℕ => if e.IsDiag then 0 else 1) 0 = ∞ := by
  rw [chi_eq_of_offDiagonal _ (fun _ => 1) (fun e he => by simp [he])]
  have hc : cluster (Set.univ : Config ℕ) 0 = Set.univ := by
    ext y
    simp [cluster, openGraph, SimpleGraph.fromEdgeSet_univ]
  simp [chi, law, prodBernoulli_const, hc]

end PercLib.Percolation.Bond
