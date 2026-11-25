/-
Deterministic set-coordinate consequences of PercLib's finite-profile Russo API.
The force/flip/difference method originates in NearCritical/Russo.lean at
Tom Hutchcroft's near-critical-diffusivity revision
c820fea91a7482c1755de0ec94ecb9f59ccfcacc, reused under permission R-3.
We reuse the existing pivotal and force definitions, and their proved identities;
no probability or differentiation theorem is reproved here.
-/
module

public import PercLib.Probability.Russo
public import PercLib.Percolation.Bond.Basic

/-! # Pivotal-event algebra on canonical configurations

Pivotality is state independent: the coordinate is tested both open and closed.
The algebra holds on arbitrary index types. Measurability requires only that the
event be measurable, and is automatic for finite indices. Loops are never pivotal
for bond connectivity, even though they remain coordinates of the probability law.
-/

@[expose] public section

open MeasureTheory Set
open scoped Classical

namespace PercLib.Probability.FiniteProfile

variable {E : Type*}

/-- The canonical set is recovered from its Boolean membership encoding. -/
theorem toSet_decide_mem (ω : Set E) : toSet (fun i => decide (i ∈ ω)) = ω := by
  ext i
  simp [toSet]

/-- Existing Boolean pivotality, expressed by insertion and deletion of a set coordinate. -/
theorem pivotal_decide_iff (A : Set (Set E)) (e : E) (ω : Set E) :
    pivotal A e (fun i => decide (i ∈ ω)) ↔ insert e ω ∈ A ∧ ω \ {e} ∉ A := by
  simp only [pivotal, toSet_force_true, toSet_force_false, toSet_decide_mem]

/-- The forced-open test can equivalently be performed after deleting the coordinate. -/
theorem pivotal_decide_iff_insert_sdiff (A : Set (Set E)) (e : E) (ω : Set E) :
    pivotal A e (fun i => decide (i ∈ ω)) ↔
      insert e (ω \ {e}) ∈ A ∧ ω \ {e} ∉ A := by
  rw [Set.insert_sdiff_singleton, pivotal_decide_iff]

/-- Changing only the tested coordinate leaves pivotality unchanged. -/
theorem pivotal_decide_of_sdiff_eq (A : Set (Set E)) (e : E) {ω ω' : Set E}
    (h : ω \ {e} = ω' \ {e}) :
    pivotal A e (fun i => decide (i ∈ ω)) ↔ pivotal A e (fun i => decide (i ∈ ω')) := by
  simp only [pivotal_decide_iff_insert_sdiff, h]

theorem pivotal_decide_insert (A : Set (Set E)) (e : E) (ω : Set E) :
    pivotal A e (fun i => decide (i ∈ insert e ω)) ↔
      pivotal A e (fun i => decide (i ∈ ω)) := by
  simpa using pivotal_decide_of_sdiff_eq A e (ω := insert e ω) (ω' := ω) (by ext i; by_cases hi : i = e <;> simp [hi])

theorem pivotal_decide_sdiff (A : Set (Set E)) (e : E) (ω : Set E) :
    pivotal A e (fun i => decide (i ∈ ω \ {e})) ↔
      pivotal A e (fun i => decide (i ∈ ω)) := by
  simpa using pivotal_decide_of_sdiff_eq A e (ω := ω \ {e}) (ω' := ω) (by ext i; simp)

/-- Pivotality is measurable whenever the original event is measurable. -/
theorem measurableSet_pivotal_decide {A : Set (Set E)} (hA : MeasurableSet A) (e : E) :
    MeasurableSet {ω : Set E | pivotal A e (fun i => decide (i ∈ ω))} := by
  simp only [pivotal_decide_iff]
  exact (hA.preimage (show Measurable (fun ω : Set E => insert e ω) from by
      apply Measurable.of_mem
      intro i
      change Measurable (fun ω : Set E => i = e ∨ i ∈ ω)
      fun_prop)).inter
    (hA.preimage (by fun_prop : Measurable (fun ω : Set E => ω \ {e}))).compl

/-- In particular no measurability hypothesis is needed on a finite index space. -/
theorem measurableSet_pivotal_decide_finite [Finite E] (A : Set (Set E)) (e : E) :
    MeasurableSet {ω : Set E | pivotal A e (fun i => decide (i ∈ ω))} :=
  measurableSet_pivotal_decide (MeasurableSet.of_discrete) e

/-- For increasing events, the forced indicator increment is exactly the pivotal indicator. -/
theorem indicator_insert_sub_sdiff {A : Set (Set E)} (hA : IsUpperSet A) (e : E)
    (ω : Set E) :
    A.indicator (fun _ => (1 : ℝ)) (insert e ω) -
      A.indicator (fun _ => (1 : ℝ)) (ω \ {e}) =
    {η : Set E | pivotal A e (fun i => decide (i ∈ η))}.indicator (fun _ => (1 : ℝ)) ω := by
  simpa only [difference, eventValue, toSet_force_true, toSet_force_false,
    toSet_decide_mem, Set.indicator, Set.mem_ofPred_eq] using
    difference_eventValue hA e (fun i => decide (i ∈ ω))

/-- Split an increasing event into its pivotal-open part and its part already true
with the coordinate closed. -/
theorem event_eq_pivotal_open_union {A : Set (Set E)} (hA : IsUpperSet A) (e : E) :
    A = {ω : Set E | pivotal A e (fun i => decide (i ∈ ω)) ∧ e ∈ ω} ∪
      {ω | ω \ {e} ∈ A} := by
  ext ω
  simp only [Set.mem_union, Set.mem_ofPred_eq, pivotal_decide_iff]
  constructor
  · intro hω
    by_cases hc : ω \ {e} ∈ A
    · exact Or.inr hc
    · apply Or.inl
      refine ⟨⟨hA (Set.subset_insert e ω) hω, hc⟩, ?_⟩
      by_contra he
      exact hc (by simpa [Set.sdiff_singleton_eq_self he] using hω)
  · rintro (⟨⟨ho, _⟩, he⟩ | hc)
    · simpa [Set.insert_eq_of_mem he] using ho
    · exact hA Set.sdiff_subset hc

/-- The two parts in the pivotal decomposition are disjoint. -/
theorem disjoint_pivotal_open_closed (A : Set (Set E)) (e : E) :
    Disjoint {ω : Set E | pivotal A e (fun i => decide (i ∈ ω)) ∧ e ∈ ω}
      {ω | ω \ {e} ∈ A} := by
  apply Set.disjoint_left.mpr
  intro ω hω hc
  exact (pivotal_decide_iff A e ω).mp hω.1 |>.2 hc

end PercLib.Probability.FiniteProfile

namespace PercLib.Percolation.Bond

open PercLib.Probability.FiniteProfile

/-- Diagonal coordinates never affect connectivity and hence are never pivotal.
This deterministic statement does not require a finite or countable vertex type. -/
theorem not_pivotal_conn_diag {V : Type*} (x y v : V) (ω : Config V) :
    ¬ pivotal (conn x y) s(v, v) (fun e => decide (e ∈ ω)) := by
  rw [pivotal_decide_iff]
  have hg : openGraph (insert s(v, v) ω) = openGraph (ω \ {s(v, v)}) := by
    ext a b
    simp only [openGraph_adj_iff, Set.mem_insert_iff, Set.mem_sdiff,
      Set.mem_singleton_iff]
    have h : a ≠ b → s(a, b) ≠ s(v, v) := by
      intro hab he
      rcases Sym2.eq_iff.mp he with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;> exact hab (ha.trans hb.symm)
    tauto
  change ¬ ((openGraph (insert s(v, v) ω)).Reachable x y ∧
    ¬ (openGraph (ω \ {s(v, v)})).Reachable x y)
  rw [hg]
  exact fun h => h.2 h.1

/-- The one genuine bond of a two-vertex graph is pivotal in every configuration. -/
example (ω : Config Bool) :
    pivotal (conn false true) s(false, true) (fun e => decide (e ∈ ω)) := by
  rw [pivotal_decide_iff]
  constructor
  · exact (show (openGraph (insert s(false, true) ω)).Adj false true from
      (openGraph_adj_iff _ _ _).mpr ⟨Set.mem_insert _ _, Bool.false_ne_true⟩).reachable
  · intro h
    have hg : openGraph (ω \ {s(false, true)}) = ⊥ := by
      ext a b
      cases a <;> cases b <;> simp [openGraph_adj_iff, Sym2.eq_swap]
    change (openGraph (ω \ {s(false, true)})).Reachable false true at h
    rw [hg, SimpleGraph.reachable_bot] at h
    exact Bool.false_ne_true h

example (ω : Config Bool) :
    ¬ pivotal (conn false true) s(false, false) (fun e => decide (e ∈ ω)) :=
  not_pivotal_conn_diag false true false ω

end PercLib.Percolation.Bond

namespace PercLib.Probability.FiniteProfile

-- The indicator difference is nonzero for a real one-coordinate event.
example (ω : Set Unit) :
    {η : Set Unit | () ∈ η}.indicator (fun _ => (1 : ℝ)) (insert () ω) -
      {η : Set Unit | () ∈ η}.indicator (fun _ => (1 : ℝ)) (ω \ {()}) = 1 := by
  simp

example (ω : Set Bool) : ¬ pivotal (Set.univ : Set (Set Bool)) false
    (fun e => decide (e ∈ ω)) := by
  simp [pivotal_decide_iff]

end PercLib.Probability.FiniteProfile
