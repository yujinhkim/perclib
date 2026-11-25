/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.
New proof of the factorisation of the law of the set of vertices of a finite domain
that are not joined to its exterior (wiki finite-size-sharpness, tag HATE, item 1).
No upstream proof is copied, no definition is added and no Input is introduced.
-/
module

public import PercLib.Percolation.Bond.DomainIndependence
public import PercLib.Percolation.Bond.RootIndependence
public import PercLib.Probability.DeterminedIndependence

/-! # The unexplored region of a finite domain

For a finite `Λ ⊆ V` let `S(ω) = {u ∈ Λ | K_u(ω) ⊆ Λ}` be the set of vertices of `Λ`
whose cluster stays in `Λ`. On `{S = T}` every pair joining `T` to its complement is
closed, the vertices of `Λ \ T` reach the exterior without entering `T`, and so the
event `{S = T}` does not depend on the pairs inside `T`. Consequently, for `o, u ∈ T`,
`P(S = T, o ↔_T u) = P(S = T) τ_T(o,u)`, with no conditioning on null events.
-/

@[expose] public section
noncomputable section
open MeasureTheory Set PercLib.Probability
open scoped ENNReal

namespace PercLib.Percolation.Bond
variable {V : Type*}

/-- If no open pair leaves `T`, clusters started in `T` stay in `T`. -/
theorem cluster_subset_of_boundary_closed {ω : Config V} {T : Set V}
    (hcl : ∀ t ∈ T, ∀ w ∉ T, s(t, w) ∉ ω) {t : V} (ht : t ∈ T) : cluster ω t ⊆ T := by
  have key : ∀ a b : V, (openGraph ω).Walk a b → a ∈ T → b ∈ T := by
    intro a b p
    induction p with
    | nil => exact id
    | @cons a c d hac p ih =>
      intro ha
      apply ih
      by_contra hc
      exact hcl a ha c hc ((openGraph_adj_iff ω a c).mp hac).1
  intro y ⟨p⟩
  exact key t y p ht

/-- If no open pair leaves `T`, a connection of `ω` from outside `T` avoids `T`, so it is a
connection of every configuration agreeing with `ω` on pairs not inside `T`. -/
theorem conn_of_boundary_closed_of_agree {ω ω' : Config V} {T : Set V}
    (hcl : ∀ t ∈ T, ∀ w ∉ T, s(t, w) ∉ ω)
    (hag : ∀ e : Sym2 V, ¬ (∀ v ∈ e, v ∈ T) → (e ∈ ω ↔ e ∈ ω')) {a b : V} (ha : a ∉ T)
    (hab : ω ∈ conn a b) : ω' ∈ conn a b := by
  have key : ∀ a b : V, (openGraph ω).Walk a b → a ∉ T → (openGraph ω').Reachable a b := by
    intro a b p
    induction p with
    | nil => exact fun _ => .refl _
    | @cons a c d hac p ih =>
      intro ha
      have hac' := (openGraph_adj_iff ω a c).mp hac
      have hc : c ∉ T := by
        intro hc
        exact hcl c hc a ha (by rw [Sym2.eq_swap]; exact hac'.1)
      have hnot : ¬ ∀ v ∈ s(a, c), v ∈ T := fun h => ha (h a (Sym2.mem_mk_left a c))
      have hadj : (openGraph ω').Adj a c :=
        (openGraph_adj_iff ω' a c).mpr ⟨(hag _ hnot).mp hac'.1, hac'.2⟩
      exact hadj.reachable.trans (ih hc)
  obtain ⟨p⟩ := hab
  exact key a b p ha

/-- On `{S = T}` every pair leaving `T` is closed. -/
theorem boundary_closed_of_unexplored_eq {ω : Config V} {Λ : Set V} {T : Set V}
    (hS : {v | v ∈ Λ ∧ cluster ω v ⊆ Λ} = T) : ∀ t ∈ T, ∀ w ∉ T, s(t, w) ∉ ω := by
  intro t ht w hw hopen
  have htS : t ∈ Λ ∧ cluster ω t ⊆ Λ := by rw [← hS] at ht; exact ht
  have htw : t ≠ w := fun h => hw (h ▸ ht)
  have hconn : ω ∈ conn t w :=
    ((openGraph_adj_iff ω t w).mpr ⟨hopen, htw⟩).reachable
  have hwΛ : w ∈ Λ := htS.2 hconn
  have hwS : ¬ (w ∈ Λ ∧ cluster ω w ⊆ Λ) := by
    intro h
    rw [← hS] at hw
    exact hw h
  apply hwS
  refine ⟨hwΛ, ?_⟩
  rw [← cluster_eq_of_mem_conn hconn]
  exact htS.2

/-- `{S = T}` is not affected by the pairs inside `T`. -/
theorem unexplored_eq_of_agree {ω ω' : Config V} {Λ T : Set V}
    (hag : ∀ e : Sym2 V, ¬ (∀ v ∈ e, v ∈ T) → (e ∈ ω ↔ e ∈ ω'))
    (hS : {v | v ∈ Λ ∧ cluster ω v ⊆ Λ} = T) : {v | v ∈ Λ ∧ cluster ω' v ⊆ Λ} = T := by
  have hcl := boundary_closed_of_unexplored_eq hS
  have hcl' : ∀ t ∈ T, ∀ w ∉ T, s(t, w) ∉ ω' := by
    intro t ht w hw h
    have hnot : ¬ ∀ v ∈ s(t, w), v ∈ T := fun h' => hw (h' w (Sym2.mem_mk_right t w))
    exact hcl t ht w hw ((hag _ hnot).mpr h)
  have hTΛ : T ⊆ Λ := by
    intro t ht
    rw [← hS] at ht
    exact ht.1
  ext v
  constructor
  · rintro ⟨hvΛ, hv⟩
    by_contra hvT
    have hvS : ¬ (v ∈ Λ ∧ cluster ω v ⊆ Λ) := by
      intro h
      rw [← hS] at hvT
      exact hvT h
    have hnot : ¬ cluster ω v ⊆ Λ := fun h => hvS ⟨hvΛ, h⟩
    obtain ⟨y, hy, hyΛ⟩ := not_subset.mp hnot
    exact hyΛ (hv (conn_of_boundary_closed_of_agree hcl hag hvT hy))
  · intro hvT
    exact ⟨hTΛ hvT, (cluster_subset_of_boundary_closed hcl' hvT).trans hTΛ⟩

/-- The event `{S = T}` is measurable. -/
theorem measurableSet_unexplored_eq [Countable V] (Λ T : Set V) :
    MeasurableSet {ω : Config V | {v | v ∈ Λ ∧ cluster ω v ⊆ Λ} = T} := by
  have hsub : ∀ v, MeasurableSet {ω : Config V | cluster ω v ⊆ Λ} := by
    intro v
    have : {ω : Config V | cluster ω v ⊆ Λ} = ⋂ y, ⋂ (_ : y ∉ Λ), (conn v y)ᶜ := by
      ext ω
      simp only [mem_ofPred_eq, mem_iInter, mem_compl_iff]
      exact ⟨fun h y hy hc => hy (h hc), fun h y hc => by_contra fun hy => h y hy hc⟩
    rw [this]
    exact .iInter fun y => .iInter fun _ => (measurableSet_conn v y).compl
  have : {ω : Config V | {v | v ∈ Λ ∧ cluster ω v ⊆ Λ} = T} =
      ⋂ v, {ω : Config V | (v ∈ Λ ∧ cluster ω v ⊆ Λ) ↔ v ∈ T} := by
    ext ω
    simp only [mem_ofPred_eq, mem_iInter, Set.ext_iff]
  rw [this]
  refine .iInter fun v => ?_
  by_cases hvΛ : v ∈ Λ <;> by_cases hvT : v ∈ T
  · convert hsub v using 1
    ext ω
    simp [hvΛ, hvT]
  · convert (hsub v).compl using 1
    ext ω
    simp [hvΛ, hvT]
  · convert (MeasurableSet.empty : MeasurableSet (∅ : Set (Config V))) using 1
    ext ω
    simp [hvΛ, hvT]
  · convert (MeasurableSet.univ : MeasurableSet (univ : Set (Config V))) using 1
    ext ω
    simp [hvΛ, hvT]

/-- **Item 1 of HATE: factorisation.** For a finite domain `Λ`, a finite `T` and
`o, u ∈ T`, `P(S = T, o ↔_T u) = P(S = T) τ_T(o,u)`, where `S` is the set of vertices of
`Λ` whose cluster stays in `Λ`. No conditioning on null events is involved. -/
theorem law_unexplored_eq_inter_localConn [Countable V] (q : Sym2 V → unitInterval)
    (Λ T : Finset V) {o u : V} (ho : o ∈ T) (hu : u ∈ T) :
    law q {ω | {v | v ∈ (Λ : Set V) ∧ cluster ω v ⊆ Λ} = (T : Set V) ∧
        ((openGraph ω).induce (T : Set V)).Reachable ⟨o, ho⟩ ⟨u, hu⟩} =
      law q {ω | {v | v ∈ (Λ : Set V) ∧ cluster ω v ⊆ Λ} = (T : Set V)} *
        law q {ω | ((openGraph ω).induce (T : Set V)).Reachable ⟨o, ho⟩ ⟨u, hu⟩} := by
  have hdisj : Disjoint {e : Sym2 V | ¬ ∀ v ∈ e, v ∈ (T : Set V)}
      {e : Sym2 V | ∀ v ∈ e, v ∈ (T : Set V)} :=
    Set.disjoint_left.mpr fun _ h h' => h h'
  have hA : ∀ ω ω' : Config V, ω ∩ {e | ¬ ∀ v ∈ e, v ∈ (T : Set V)} =
      ω' ∩ {e | ¬ ∀ v ∈ e, v ∈ (T : Set V)} →
      (ω ∈ {ω : Config V | {v | v ∈ (Λ : Set V) ∧ cluster ω v ⊆ Λ} = (T : Set V)} ↔
        ω' ∈ {ω : Config V | {v | v ∈ (Λ : Set V) ∧ cluster ω v ⊆ Λ} = (T : Set V)}) := by
    intro ω ω' heq
    have hag : ∀ e : Sym2 V, ¬ (∀ v ∈ e, v ∈ (T : Set V)) → (e ∈ ω ↔ e ∈ ω') := by
      intro e he
      have := Set.ext_iff.mp heq e
      simp only [mem_inter_iff, mem_ofPred_eq] at this
      exact ⟨fun h => (this.mp ⟨h, he⟩).1, fun h => (this.mpr ⟨h, he⟩).1⟩
    exact ⟨unexplored_eq_of_agree hag,
      unexplored_eq_of_agree fun e he => (hag e he).symm⟩
  have h := prodBernoulli_inter_of_determined q hdisj (measurableSet_unexplored_eq _ _)
    (measurableSet_localConn (T : Set V) ⟨o, ho⟩ ⟨u, hu⟩) hA
    (localConn_determined (T : Set V) ⟨o, ho⟩ ⟨u, hu⟩)
  exact h

-- Non-vacuity: a two-vertex domain on `Bool` with `T = Λ`, at an arbitrary profile.
example (q : Sym2 Bool → unitInterval) :
    law q {ω | {v | v ∈ ((Finset.univ : Finset Bool) : Set Bool) ∧
        cluster ω v ⊆ (Finset.univ : Finset Bool)} = ((Finset.univ : Finset Bool) : Set Bool) ∧
        ((openGraph ω).induce ((Finset.univ : Finset Bool) : Set Bool)).Reachable
          ⟨false, by simp⟩ ⟨true, by simp⟩} =
      law q {ω | {v | v ∈ ((Finset.univ : Finset Bool) : Set Bool) ∧
        cluster ω v ⊆ (Finset.univ : Finset Bool)} = ((Finset.univ : Finset Bool) : Set Bool)} *
        law q {ω | ((openGraph ω).induce ((Finset.univ : Finset Bool) : Set Bool)).Reachable
          ⟨false, by simp⟩ ⟨true, by simp⟩} :=
  law_unexplored_eq_inter_localConn q Finset.univ Finset.univ (by simp) (by simp)

end PercLib.Percolation.Bond
