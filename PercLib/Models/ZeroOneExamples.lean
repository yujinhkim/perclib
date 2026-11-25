/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.
Q-75: two examples around the zero-one law. New for this project; no upstream proof is
copied, and no new definition is introduced.
-/
module

public import PercLib.Percolation.Bond.Forest
public import PercLib.Percolation.Bond.Intensity.Defs
public import PercLib.Percolation.Bond.ZeroOne
public import PercLib.Probability.Cylinder

/-!
# Zero-one examples

* `law_root_cluster_infinite_eq` / `exists_root_percolation_eq` (1J3B): the event that some
  infinite cluster exists can have probability one while a given root percolates with any
  prescribed probability `p`. The model is the integer line `some '' ℤ`, with every line bond
  open almost surely, plus a root `none` joined to `some 0` with probability `p`.
* `rootCriticalIntensity_eq_top_of_finite` / `globalCriticalIntensity_eq_top_of_finite`
  (KB1L): on a finite vertex type every cluster is finite in every configuration, so both
  critical intensities are `⊤` for every kernel.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set PercLib.Probability PercLib.Percolation.Bond
open scoped ENNReal NNReal

namespace PercLib.Models.ZeroOneExamples

/-- When every line bond is open, all line vertices are connected to `some 0`. -/
theorem reachable_line {ω : Config (Option ℤ)}
    (hω : ∀ a : ℤ, s(some a, some (a + 1)) ∈ ω) (a : ℤ) :
    (openGraph ω).Reachable (some 0) (some a) := by
  have hadj (b : ℤ) : (openGraph ω).Adj (some b) (some (b + 1)) :=
    (openGraph_adj_iff ω _ _).mpr ⟨hω b, by simp⟩
  induction a using Int.induction_on with
  | zero => rfl
  | succ i ih => exact ih.trans (hadj i).reachable
  | pred i ih =>
    have h := (hadj (-(i : ℤ) - 1)).reachable
    rw [sub_add_cancel] at h
    exact ih.trans h.symm

/-- When every line bond is open, the cluster of `some 0` is infinite. -/
theorem cluster_some_zero_infinite {ω : Config (Option ℤ)}
    (hω : ∀ a : ℤ, s(some a, some (a + 1)) ∈ ω) : (cluster ω (some 0)).Infinite :=
  Set.infinite_of_injective_forall_mem (Option.some_injective ℤ) fun a => reachable_line hω a

/-- **1J3B**, concrete model. On `Option ℤ`, let every line bond `s(some a, some (a+1))` have
probability one, let the root bond `s(none, some 0)` have probability `p`, and let every
other bond at `none` have probability zero. Then an infinite cluster exists almost surely,
while the root `none` percolates with probability exactly `p`. -/
theorem law_root_cluster_infinite_eq (p : unitInterval) (q : Sym2 (Option ℤ) → unitInterval)
    (hline : ∀ a : ℤ, q s(some a, some (a + 1)) = 1) (hroot : q s(none, some 0) = p)
    (hother : ∀ a : ℤ, a ≠ 0 → q s(none, some a) = 0) :
    law q {ω | ∃ v, (cluster ω v).Infinite} = 1 ∧
      law q {ω | (cluster ω none).Infinite} = (unitInterval.toNNReal p : ℝ≥0∞) := by
  have hL : ∀ᵐ ω ∂law q, ∀ a : ℤ, s(some a, some (a + 1)) ∈ ω := by
    rw [ae_all_iff]
    intro a
    apply (mem_ae_iff_prob_eq_one (measurableSet_mem _)).mpr
    simp [law, prodBernoulli_setOf_mem, hline a]
  refine ⟨?_, ?_⟩
  · apply (mem_ae_iff_prob_eq_one measurableSet_exists_cluster_infinite).mp
    filter_upwards [hL] with ω hω
    exact ⟨some 0, cluster_some_zero_infinite hω⟩
  · have heq : {ω : Config (Option ℤ) | (cluster ω none).Infinite} =ᵐ[law q]
        {ω | s(none, some 0) ∈ ω} := by
      rw [Filter.eventuallyEqSet_iff]
      filter_upwards [hL, ae_config_subset_positive q] with ω hω hpos
      constructor
      · intro hinf
        by_contra hclosed
        apply hinf
        have hno : ∀ x, ¬ (openGraph ω).Adj none x := by
          intro x hx
          obtain ⟨hx, hne⟩ := (openGraph_adj_iff ω none x).mp hx
          have hq := hpos hx
          cases x with
          | none => exact hne rfl
          | some a =>
            by_cases ha : a = 0
            · subst ha; exact hclosed hx
            · simp [hother a ha] at hq
        apply (Set.finite_singleton (none : Option ℤ)).subset
        intro y hy
        obtain ⟨w⟩ := (mem_cluster_iff ω none y).mp hy
        cases w with
        | nil => rfl
        | cons hadj _ => exact absurd hadj (hno _)
      · intro hopen
        have hr : (openGraph ω).Reachable none (some 0) :=
          ((openGraph_adj_iff ω _ _).mpr ⟨hopen, by simp⟩).reachable
        refine (cluster_some_zero_infinite hω).mono ?_
        intro y hy
        exact hr.trans hy
    rw [measure_congr heq]
    simp [law, prodBernoulli_setOf_mem, hroot]

/-- **1J3B.** For every `p ∈ [0,1]` (in particular every `p ∈ (0,1)`) there are a countable
vertex type, a profile and a root such that an infinite cluster exists almost surely while
the root percolates with probability exactly `p`. -/
theorem exists_root_percolation_eq (p : unitInterval) :
    ∃ (V : Type) (_ : Countable V) (q : Sym2 V → unitInterval) (o : V),
      law q {ω | ∃ v, (cluster ω v).Infinite} = 1 ∧
        law q {ω | (cluster ω o).Infinite} = (unitInterval.toNNReal p : ℝ≥0∞) := by
  classical
  let q : Sym2 (Option ℤ) → unitInterval := fun e =>
    if ∃ a : ℤ, e = s(some a, some (a + 1)) then 1 else if e = s(none, some 0) then p else 0
  have hline (a : ℤ) : q s(some a, some (a + 1)) = 1 := ite_eq_left ⟨a, rfl⟩
  have hnotline (a : ℤ) : ¬ ∃ b : ℤ, s(none, some a) = s(some b, some (b + 1)) := by
    rintro ⟨b, hb⟩
    simp at hb
  have hroot : q s(none, some 0) = p := by
    simp only [q, ite_eq_right (hnotline 0), ite_true]
  have hother (a : ℤ) (ha : a ≠ 0) : q s(none, some a) = 0 := by
    simp only [q, ite_eq_right (hnotline a)]
    rw [ite_eq_right]
    simpa using ha
  exact ⟨Option ℤ, inferInstance, q, none, law_root_cluster_infinite_eq p q hline hroot hother⟩

/-! ### Finite vertex types -/

/-- On a finite vertex type every cluster is finite, in every configuration. -/
theorem cluster_finite {V : Type*} [Finite V] (ω : Config V) (v : V) : (cluster ω v).Finite :=
  Set.toFinite _

/-- On a finite vertex type no configuration has an infinite cluster. -/
theorem setOf_exists_cluster_infinite_eq_empty {V : Type*} [Finite V] :
    {ω : Config V | ∃ v, (cluster ω v).Infinite} = ∅ :=
  Set.eq_empty_of_forall_notMem fun ω ⟨v, hv⟩ => hv (cluster_finite ω v)

/-- **KB1L**, global threshold: on a finite vertex type the global critical intensity of
every kernel is `⊤`. -/
theorem globalCriticalIntensity_eq_top_of_finite {V : Type*} [Finite V] (J : Sym2 V → ℝ≥0) :
    globalCriticalIntensity J = ⊤ := by
  apply top_le_iff.mp
  apply le_sInf
  rintro b ⟨β, rfl, hpos⟩
  rw [setOf_exists_cluster_infinite_eq_empty, measure_empty] at hpos
  exact (lt_irrefl _ hpos).elim

/-- **KB1L**, root threshold: on a finite vertex type the root critical intensity of every
kernel at every root is `⊤`. -/
theorem rootCriticalIntensity_eq_top_of_finite {V : Type*} [Finite V] (J : Sym2 V → ℝ≥0)
    (x : V) : rootCriticalIntensity J x = ⊤ := by
  apply top_le_iff.mp
  apply le_sInf
  rintro b ⟨β, rfl, hpos⟩
  have h : {ω : Config V | (cluster ω x).Infinite} = ∅ :=
    Set.eq_empty_of_forall_notMem fun ω hω => hω (cluster_finite ω x)
  rw [h, measure_empty] at hpos
  exact (lt_irrefl _ hpos).elim

/-! ### Non-vacuity witnesses (D-5) -/

/-- KB1L on `Fin 3` with the complete unit kernel. -/
example : globalCriticalIntensity (fun _ : Sym2 (Fin 3) => (1 : ℝ≥0)) = ⊤ ∧
    ∀ x : Fin 3, rootCriticalIntensity (fun _ : Sym2 (Fin 3) => (1 : ℝ≥0)) x = ⊤ :=
  ⟨globalCriticalIntensity_eq_top_of_finite _, rootCriticalIntensity_eq_top_of_finite _⟩

/-- 1J3B at `p = 1/2`: the root percolates with probability `1/2` while an infinite cluster
exists almost surely. -/
example : ∃ (V : Type) (_ : Countable V) (q : Sym2 V → unitInterval) (o : V),
    law q {ω | ∃ v, (cluster ω v).Infinite} = 1 ∧
      law q {ω | (cluster ω o).Infinite} = (unitInterval.toNNReal ⟨1 / 2, by norm_num, by norm_num⟩ : ℝ≥0∞) :=
  exists_root_percolation_eq _

end PercLib.Models.ZeroOneExamples
