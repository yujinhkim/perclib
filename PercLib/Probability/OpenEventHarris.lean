/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

New proofs for issue 69 (REUSE OpenEventHarris), written on 2026-11-14. They cover the
role of `percolation_harris_of_finite_witnesses`, `escapeEvent_eq_iUnion_truncation` and
`percolation_escape_harris` in NearCritical/OpenEventHarris.lean of
tomhutchcroft/near-critical-diffusivity at revision
c820fea91a7482c1755de0ec94ecb9f59ccfcacc. That source was not consulted and no code was
copied: every statement here is derived from the canonical Harris inequality
`PercLib.Probability.prodBernoulli_harris` on the D-2 interface.
-/
module

public import PercLib.Percolation.Bond.Basic
public import PercLib.Probability.Harris

/-!
# Harris for events with finite open witnesses, connections and escape events

The Harris inequality `PercLib.Probability.prodBernoulli_harris` holds for all increasing
measurable events. This file adds no definition. It proves:

* Harris for finitely many increasing events, `prodBernoulli_prod_le_biInter`.
* Finite-witness association: an increasing event in which every configuration contains
  a finite open witness of the event is a countable union of cylinder events, hence
  measurable when the index type is countable, so Harris needs no measurability
  hypothesis for it (`prodBernoulli_harris_of_finite_witness`).
* On the D-2 bond interface: every open connection has a finite open witness
  (`exists_finset_of_mem_conn`), and the same holds for escaping a set of vertices,
  written `⋃ y ∈ Fᶜ, conn x y`. Connection, escape and infinite-cluster events are
  increasing, so they satisfy Harris (`law_harris_conn`, `law_harris_escape`,
  `law_harris_cluster_infinite`), and `tau q x y * tau q y z ≤ tau q x z`.

Escape from a finite set is not the infinite-cluster event: the second is the
intersection of the first over all finite sets (`cluster_infinite_eq_iInter`), and a
witness at the end of this file separates them.
-/

@[expose] public section

open MeasureTheory Set

namespace PercLib.Probability

variable {ι : Type*}

/-- Harris for finitely many increasing measurable events. -/
@[tag "22S9"] theorem prodBernoulli_prod_le_biInter (q : ι → unitInterval) {α : Type*} (s : Finset α)
    (A : α → Set (Set ι)) (hA : ∀ a ∈ s, IsUpperSet (A a))
    (hAm : ∀ a ∈ s, MeasurableSet (A a)) :
    ∏ a ∈ s, prodBernoulli q (A a) ≤ prodBernoulli q (⋂ a ∈ s, A a) := by
  classical
  revert hA hAm
  refine Finset.induction_on s ?_ ?_
  · intro _ _
    simp
  · intro a s ha ih hA hAm
    have hs : ∀ b ∈ s, IsUpperSet (A b) := fun b hb => hA b (Finset.mem_insert_of_mem hb)
    have hsm : ∀ b ∈ s, MeasurableSet (A b) := fun b hb =>
      hAm b (Finset.mem_insert_of_mem hb)
    rw [Finset.prod_insert ha, Finset.set_biInter_insert]
    calc prodBernoulli q (A a) * ∏ b ∈ s, prodBernoulli q (A b)
        ≤ prodBernoulli q (A a) * prodBernoulli q (⋂ b ∈ s, A b) := by
          gcongr
          exact ih hs hsm
      _ ≤ prodBernoulli q (A a ∩ ⋂ b ∈ s, A b) :=
          prodBernoulli_harris q (hA a (Finset.mem_insert_self a s)) (isUpperSet_iInter₂ hs)
            (hAm a (Finset.mem_insert_self a s)) (Finset.measurableSet_biInter s hsm)

/-- The configurations that contain a given set of indices form an increasing event. -/
theorem isUpperSet_setOf_subset (S : Set ι) : IsUpperSet {ω : Set ι | S ⊆ ω} :=
  fun _ _ hab ha => Set.Subset.trans ha hab

/-- The configurations that contain a given finite set of indices form a measurable
event. -/
theorem measurableSet_setOf_finset_subset (F : Finset ι) :
    MeasurableSet {ω : Set ι | (F : Set ι) ⊆ ω} := by
  have hset : {ω : Set ι | (F : Set ι) ⊆ ω} = ⋂ i ∈ F, {ω : Set ι | i ∈ ω} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    exact ⟨fun h i hi => h (Finset.mem_coe.2 hi), fun h i hi => h i (Finset.mem_coe.1 hi)⟩
  rw [hset]
  exact Finset.measurableSet_biInter F fun i _ => measurableSet_mem i

/-- The event that some finite set in a family `W` is entirely open is increasing. -/
theorem isUpperSet_iUnion_witness (W : Set (Finset ι)) :
    IsUpperSet (⋃ F ∈ W, {ω : Set ι | (F : Set ι) ⊆ ω}) :=
  isUpperSet_iUnion₂ fun F _ => isUpperSet_setOf_subset (F : Set ι)

/-- The event that some finite set in a family `W` is entirely open is measurable when
there are countably many indices. -/
theorem measurableSet_iUnion_witness [Countable ι] (W : Set (Finset ι)) :
    MeasurableSet (⋃ F ∈ W, {ω : Set ι | (F : Set ι) ⊆ ω}) :=
  MeasurableSet.biUnion (Set.to_countable W) fun F _ => measurableSet_setOf_finset_subset F

/-- An increasing event in which every configuration contains a finite witness is the
union of the cylinder events of its finite members. -/
theorem eq_iUnion_finite_witness {A : Set (Set ι)} (hA : IsUpperSet A)
    (hfin : ∀ ω ∈ A, ∃ F : Finset ι, (F : Set ι) ⊆ ω ∧ (F : Set ι) ∈ A) :
    A = ⋃ F ∈ {F : Finset ι | (F : Set ι) ∈ A}, {ω : Set ι | (F : Set ι) ⊆ ω} := by
  ext ω
  rw [Set.mem_iUnion₂]
  constructor
  · intro hω
    obtain ⟨F, hF, hFA⟩ := hfin ω hω
    exact ⟨F, hFA, hF⟩
  · rintro ⟨F, hFA, hF⟩
    exact hA hF hFA

/-- An increasing event with finite witnesses is measurable when there are countably many
indices. -/
@[tag "5CN6"] theorem measurableSet_of_finite_witness [Countable ι] {A : Set (Set ι)} (hA : IsUpperSet A)
    (hfin : ∀ ω ∈ A, ∃ F : Finset ι, (F : Set ι) ⊆ ω ∧ (F : Set ι) ∈ A) :
    MeasurableSet A := by
  rw [eq_iUnion_finite_witness hA hfin]
  exact measurableSet_iUnion_witness _

/-- **Finite-witness association.** Harris for increasing events with finite witnesses,
with no measurability hypothesis. -/
theorem prodBernoulli_harris_of_finite_witness [Countable ι] (q : ι → unitInterval)
    {A B : Set (Set ι)} (hA : IsUpperSet A) (hB : IsUpperSet B)
    (hAfin : ∀ ω ∈ A, ∃ F : Finset ι, (F : Set ι) ⊆ ω ∧ (F : Set ι) ∈ A)
    (hBfin : ∀ ω ∈ B, ∃ F : Finset ι, (F : Set ι) ⊆ ω ∧ (F : Set ι) ∈ B) :
    prodBernoulli q A * prodBernoulli q B ≤ prodBernoulli q (A ∩ B) :=
  prodBernoulli_harris q hA hB (measurableSet_of_finite_witness hA hAfin)
    (measurableSet_of_finite_witness hB hBfin)

end PercLib.Probability

namespace PercLib.Percolation.Bond

open PercLib.Probability

variable {V : Type*}

/-- Clusters grow with the configuration. -/
theorem cluster_mono {ω ω' : Config V} (h : ω ⊆ ω') (x : V) :
    cluster ω x ⊆ cluster ω' x :=
  fun _ hy => conn_mono h hy

/-- Connection is an increasing event. -/
theorem isUpperSet_conn (x y : V) : IsUpperSet (conn x y : Set (Config V)) :=
  fun _ _ h hxy => conn_mono h hxy

/-- **Finite open path witness.** An open connection uses only finitely many open
edges. -/
theorem exists_finset_of_mem_conn {ω : Config V} {x y : V} (h : ω ∈ conn x y) :
    ∃ F : Finset (Sym2 V), (F : Config V) ⊆ ω ∧ (F : Config V) ∈ conn x y := by
  classical
  obtain ⟨p⟩ : (openGraph ω).Reachable x y := h
  induction p with
  | nil =>
    refine ⟨∅, ?_, ?_⟩
    · rw [Finset.coe_empty]
      exact Set.empty_subset ω
    · rw [conn_self]
      exact Set.mem_univ _
  | @cons a b c hadj p ih =>
    obtain ⟨F, hFω, hF⟩ := ih
    have had := (openGraph_adj_iff ω a b).1 hadj
    refine ⟨insert s(a, b) F, ?_, ?_⟩
    · rw [Finset.coe_insert]
      exact Set.insert_subset had.1 hFω
    · rw [Finset.coe_insert]
      exact conn_trans (mem_conn_of_mem had.2 (Set.mem_insert _ _))
        (conn_mono (Set.subset_insert _ _) hF)

/-- A connection event is the union of the cylinder events of its finite open
witnesses. -/
theorem conn_eq_iUnion_finset (x y : V) :
    (conn x y : Set (Config V)) =
      ⋃ F ∈ {F : Finset (Sym2 V) | (F : Config V) ∈ conn x y},
        {ω : Config V | (F : Config V) ⊆ ω} :=
  eq_iUnion_finite_witness (isUpperSet_conn x y) fun _ h => exists_finset_of_mem_conn h

/-- Escaping a set of vertices is an increasing event. -/
theorem isUpperSet_escape (x : V) (F : Set V) :
    IsUpperSet (⋃ y ∈ Fᶜ, conn x y : Set (Config V)) :=
  isUpperSet_iUnion₂ fun y _ => isUpperSet_conn x y

/-- Escaping a set of vertices is measurable when there are countably many vertices. -/
theorem measurableSet_escape [Countable V] (x : V) (F : Set V) :
    MeasurableSet (⋃ y ∈ Fᶜ, conn x y : Set (Config V)) :=
  MeasurableSet.biUnion (Set.to_countable _) fun y _ => measurableSet_conn x y

/-- **Finite open path witness for escape.** Escaping a set of vertices uses only
finitely many open edges. -/
theorem exists_finset_of_mem_escape {ω : Config V} {x : V} {F : Set V}
    (h : ω ∈ (⋃ y ∈ Fᶜ, conn x y : Set (Config V))) :
    ∃ G : Finset (Sym2 V), (G : Config V) ⊆ ω ∧
      (G : Config V) ∈ (⋃ y ∈ Fᶜ, conn x y : Set (Config V)) := by
  obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.1 h
  obtain ⟨G, hG, hGc⟩ := exists_finset_of_mem_conn hxy
  exact ⟨G, hG, Set.mem_iUnion₂.2 ⟨y, hy, hGc⟩⟩

/-- An escape event is the union of the cylinder events of its finite open witnesses. -/
theorem escape_eq_iUnion_finset (x : V) (F : Set V) :
    (⋃ y ∈ Fᶜ, conn x y : Set (Config V)) =
      ⋃ G ∈ {G : Finset (Sym2 V) |
          (G : Config V) ∈ (⋃ y ∈ Fᶜ, conn x y : Set (Config V))},
        {ω : Config V | (G : Config V) ⊆ ω} :=
  eq_iUnion_finite_witness (isUpperSet_escape x F) fun _ h => exists_finset_of_mem_escape h

/-- The event that a cluster is infinite is increasing. -/
theorem isUpperSet_cluster_infinite (x : V) :
    IsUpperSet {ω : Config V | (cluster ω x).Infinite} :=
  fun _ _ h hx => Set.Infinite.mono (cluster_mono h x) hx

/-- Harris for two connection events. -/
theorem law_harris_conn [Countable V] (q : Sym2 V → unitInterval) (x y u v : V) :
    law q (conn x y) * law q (conn u v) ≤ law q (conn x y ∩ conn u v) :=
  prodBernoulli_harris q (isUpperSet_conn x y) (isUpperSet_conn u v)
    (measurableSet_conn x y) (measurableSet_conn u v)

/-- The two-point function is supermultiplicative along a middle vertex. -/
theorem tau_mul_tau_le [Countable V] (q : Sym2 V → unitInterval) (x y z : V) :
    tau q x y * tau q y z ≤ tau q x z := by
  show law q (conn x y) * law q (conn y z) ≤ law q (conn x z)
  exact (law_harris_conn q x y y z).trans (measure_mono fun _ h => conn_trans h.1 h.2)

/-- Harris for two escape events. -/
theorem law_harris_escape [Countable V] (q : Sym2 V → unitInterval) (x x' : V)
    (F F' : Set V) :
    law q (⋃ y ∈ Fᶜ, conn x y) * law q (⋃ y ∈ F'ᶜ, conn x' y) ≤
      law q ((⋃ y ∈ Fᶜ, conn x y) ∩ ⋃ y ∈ F'ᶜ, conn x' y) :=
  prodBernoulli_harris q (isUpperSet_escape x F) (isUpperSet_escape x' F')
    (measurableSet_escape x F) (measurableSet_escape x' F')

/-- Harris for two infinite-cluster events. -/
theorem law_harris_cluster_infinite [Countable V] (q : Sym2 V → unitInterval) (x y : V) :
    law q {ω : Config V | (cluster ω x).Infinite} *
        law q {ω : Config V | (cluster ω y).Infinite} ≤
      law q ({ω : Config V | (cluster ω x).Infinite} ∩
        {ω : Config V | (cluster ω y).Infinite}) :=
  prodBernoulli_harris q (isUpperSet_cluster_infinite x) (isUpperSet_cluster_infinite y)
    (measurableSet_cluster_infinite x) (measurableSet_cluster_infinite y)

/-- Harris for a connection event and an infinite-cluster event. -/
theorem law_harris_conn_cluster_infinite [Countable V] (q : Sym2 V → unitInterval)
    (x y z : V) :
    law q (conn x y) * law q {ω : Config V | (cluster ω z).Infinite} ≤
      law q (conn x y ∩ {ω : Config V | (cluster ω z).Infinite}) :=
  prodBernoulli_harris q (isUpperSet_conn x y) (isUpperSet_cluster_infinite z)
    (measurableSet_conn x y) (measurableSet_cluster_infinite z)

end PercLib.Percolation.Bond

/-! ### Non-vacuity -/
section Witnesses

open PercLib.Percolation.Bond

/-- The finite-witness hypothesis is met by a connection event that is neither empty nor
everything. -/
example : ∀ ω ∈ (conn false true : Set (Config Bool)),
    ∃ F : Finset (Sym2 Bool), (F : Config Bool) ⊆ ω ∧
      (F : Config Bool) ∈ conn false true :=
  fun _ h => exists_finset_of_mem_conn h

example : (Set.univ : Config Bool) ∈ conn false true ∧
    (∅ : Config Bool) ∉ conn false true :=
  ⟨mem_conn_of_mem (by decide) (Set.mem_univ _), by rw [empty_mem_conn_iff]; decide⟩

/-- With every pair open, `false` escapes the finite set `{false}`, but its cluster is
finite: escaping a finite set is not the infinite-cluster event. -/
example : (Set.univ : Config Bool) ∈ (⋃ y ∈ ({false} : Set Bool)ᶜ, conn false y) ∧
    (Set.univ : Config Bool) ∉ {ω : Config Bool | (cluster ω false).Infinite} := by
  refine ⟨Set.mem_iUnion₂.2
    ⟨true, by simp, mem_conn_of_mem (by decide) (Set.mem_univ _)⟩, ?_⟩
  intro h
  exact (h : (cluster (Set.univ : Config Bool) false).Infinite) (Set.toFinite _)

/-- With no pair open, nothing escapes. -/
example : (∅ : Config Bool) ∉ (⋃ y ∈ ({false} : Set Bool)ᶜ, conn false y) := by
  intro h
  obtain ⟨y, hy, hc⟩ := Set.mem_iUnion₂.1 h
  rw [empty_mem_conn_iff] at hc
  subst hc
  exact hy (Set.mem_singleton _)

end Witnesses
