/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

New for this project (issue 156, Q-22, item 3 and the second half of item 4). No upstream
proof is copied.
-/
module

public import PercLib.Percolation.Bond.ProfileRegularity
public import PercLib.Probability.Cylinder

/-!
# Upper semicontinuity of `θ` on a locally finite support

Let `G` be a locally finite graph and `P_G` the profiles vanishing on every non-diagonal pair
outside `G`. For `q ∈ P_G`, almost surely every open non-diagonal pair is an edge of `G`, and
then escaping a finite set `F` from `x` depends only on the finitely many `G`-edges with an
endpoint in `F`. Its probability is therefore continuous on `P_G`, and `θ` is the infimum of
these probabilities over a finite exhaustion, hence upper semicontinuous on `P_G`. Along a
monotone continuous family inside `P_G`, `θ` is right-continuous.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology PercLib.Probability
open scoped ENNReal

namespace PercLib.Percolation.Bond

variable {V : Type*}

/-! ### Escaping through boundary edges -/

/-- A walk in the open graph from inside `F` to outside `F` can be shortened to one that uses
only open pairs with an endpoint in `F`. -/
theorem exists_reachable_inter_of_walk {F : Set V} {B : Set (Sym2 V)} {ω : Config V}
    (hB : ∀ e ∈ ω, ¬ e.IsDiag → (∃ a ∈ e, a ∈ F) → e ∈ B) {u v : V}
    (w : (openGraph ω).Walk u v) (hu : u ∈ F) (hv : v ∉ F) :
    ∃ z ∉ F, (openGraph (ω ∩ B)).Reachable u z := by
  induction w with
  | nil => exact absurd hu hv
  | @cons a b c hab w ih =>
    have hab' := (openGraph_adj_iff ω a b).1 hab
    have hB' : s(a, b) ∈ ω ∩ B :=
      ⟨hab'.1, hB _ hab'.1 (Sym2.mk_isDiag_iff.not.2 hab'.2) ⟨a, Sym2.mem_mk_left a b, hu⟩⟩
    have hadj : (openGraph (ω ∩ B)).Adj a b := (openGraph_adj_iff _ a b).2 ⟨hB', hab'.2⟩
    by_cases hb : b ∈ F
    · obtain ⟨z, hz, hbz⟩ := ih hb hv
      exact ⟨z, hz, hadj.reachable.trans hbz⟩
    · exact ⟨b, hb, hadj.reachable⟩

/-- On configurations whose open non-diagonal pairs carry an endpoint in `F` only through `B`,
escaping `F` is decided by the pairs in `B`. -/
theorem mem_escape_iff_inter {F : Set V} {B : Set (Sym2 V)} {ω : Config V}
    (hB : ∀ e ∈ ω, ¬ e.IsDiag → (∃ a ∈ e, a ∈ F) → e ∈ B) (x : V) :
    ω ∈ (⋃ y ∈ Fᶜ, conn x y : Set (Config V)) ↔
      ω ∩ B ∈ (⋃ y ∈ Fᶜ, conn x y : Set (Config V)) := by
  simp only [mem_iUnion, mem_compl_iff, exists_prop]
  constructor
  · rintro ⟨y, hy, hxy⟩
    by_cases hx : x ∈ F
    · obtain ⟨w⟩ := hxy
      exact exists_reachable_inter_of_walk hB w hx hy
    · exact ⟨x, hx, SimpleGraph.Reachable.refl x⟩
  · rintro ⟨y, hy, hxy⟩
    exact ⟨y, hy, conn_mono inter_subset_left hxy⟩

/-- The `G`-edges with an endpoint in a finite set form a finite set. -/
theorem finite_edges_meeting (G : SimpleGraph V) [G.LocallyFinite] (F : Finset V) :
    {e : Sym2 V | e ∈ G.edgeSet ∧ ∃ a ∈ e, a ∈ (F : Set V)}.Finite := by
  refine (F.finite_toSet.biUnion fun a _ =>
    (G.neighborSet a).toFinite.image fun b => s(a, b)).subset ?_
  rintro e ⟨he, a, hae, ha⟩
  obtain ⟨b, rfl⟩ := Sym2.mem_iff_exists.1 hae
  exact mem_biUnion ha ⟨b, (G.mem_edgeSet).1 he, rfl⟩

/-- Under a profile supported on `G` off the diagonal, almost surely every open non-diagonal
pair is an edge of `G`. -/
theorem ae_open_offDiag_mem_edgeSet [Countable V] (G : SimpleGraph V)
    {q : Sym2 V → unitInterval} (hq : ∀ e, e ∉ G.edgeSet → ¬ e.IsDiag → q e = 0) :
    ∀ᵐ ω ∂law q, ∀ e ∈ ω, ¬ e.IsDiag → e ∈ G.edgeSet := by
  classical
  have he (e : Sym2 V) : ∀ᵐ ω ∂law q, e ∈ ω → ¬ e.IsDiag → e ∈ G.edgeSet := by
    by_cases h : e ∈ G.edgeSet ∨ e.IsDiag
    · exact Eventually.of_forall fun _ _ hd => h.resolve_right hd
    · rw [not_or] at h
      have hz : law q {ω | e ∈ ω} = 0 := by
        simpa [law, hq e h.1 h.2] using prodBernoulli_setOf_mem q e
      rw [ae_iff]
      refine measure_mono_null (fun ω hω => ?_) hz
      simp only [mem_ofPred_eq, not_forall] at hω
      obtain ⟨hω, -, -⟩ := hω
      exact hω
  filter_upwards [ae_all_iff.2 he] with ω hω e he' hd
  exact hω e he' hd

/-! ### Upper semicontinuity of `θ` -/

/-- **Upper semicontinuity of `θ`** on the profiles supported by a locally finite graph. -/
theorem upperSemicontinuousOn_law_cluster_infinite [Countable V] (G : SimpleGraph V)
    [G.LocallyFinite] (x : V) :
    UpperSemicontinuousOn (fun q : Sym2 V → unitInterval => law q {ω | (cluster ω x).Infinite})
      {q | ∀ e, e ∉ G.edgeSet → ¬ e.IsDiag → q e = 0} := by
  classical
  obtain ⟨S, hS, hcover⟩ := exists_finset_exhaustion (V := V)
  set B : ℕ → Finset (Sym2 V) := fun n => (finite_edges_meeting G (S n)).toFinset with hBdef
  have hB : ∀ n, ∀ ω : Config V, (∀ e ∈ ω, ¬ e.IsDiag → e ∈ G.edgeSet) →
      ∀ e ∈ ω, ¬ e.IsDiag → (∃ a ∈ e, a ∈ (S n : Set V)) → e ∈ (B n : Set (Sym2 V)) := by
    intro n ω hω e he hd ha
    simp only [hBdef, Set.Finite.coe_toFinset]
    exact ⟨hω e he hd, ha⟩
  set E : ℕ → Set (Config V) := fun n => ⋃ y ∈ (S n : Set V)ᶜ, conn x y with hE
  set D : ℕ → Set (Config V) := fun n => {ω | ω ∩ (B n : Set (Sym2 V)) ∈ E n} with hD
  -- `θ` is the infimum of the escape probabilities.
  have hinter : {ω : Config V | (cluster ω x).Infinite} = ⋂ n, E n := by
    ext ω
    simp only [mem_ofPred_eq, mem_iInter, hE, mem_iUnion, mem_compl_iff, Finset.mem_coe,
      exists_prop]
    constructor
    · intro hinf n
      obtain ⟨y, hy, hyS⟩ := hinf.exists_notMem_finset (S n)
      exact ⟨y, hyS, hy⟩
    · intro h hfin
      obtain ⟨n, hn⟩ := hS.directed_le.exists_mem_subset_of_finset_subset_biUnion
        (s := hfin.toFinset) (f := fun n => (S n : Set V)) fun v _ =>
          mem_iUnion.2 (hcover v)
      obtain ⟨y, hy, hxy⟩ := h n
      exact hy (hn (hfin.mem_toFinset.2 hxy))
  have hanti : Antitone E := by
    intro m n hmn ω hω
    simp only [hE, mem_iUnion, mem_compl_iff, Finset.mem_coe, exists_prop] at hω ⊢
    obtain ⟨y, hy, hxy⟩ := hω
    exact ⟨y, fun h => hy (hS hmn h), hxy⟩
  have htheta : ∀ q : Sym2 V → unitInterval,
      law q {ω | (cluster ω x).Infinite} = ⨅ n, law q (E n) := by
    intro q
    rw [hinter]
    exact hanti.measure_iInter (fun n => (measurableSet_escape x _).nullMeasurableSet)
      ⟨0, measure_ne_top _ _⟩
  -- On `P_G`, each escape probability equals a continuous one.
  have hcont : ∀ n, Continuous fun q : Sym2 V → unitInterval => law q (D n) := by
    intro n
    refine continuous_prodBernoulli_of_determined (B n) fun ω ω' h => ?_
    simp only [hD, mem_ofPred_eq, h]
  have hEq : ∀ q ∈ {q : Sym2 V → unitInterval | ∀ e, e ∉ G.edgeSet → ¬ e.IsDiag → q e = 0},
      ∀ n, law q (E n) = law q (D n) := by
    intro q hq n
    refine measure_congr ?_
    filter_upwards [ae_open_offDiag_mem_edgeSet G hq] with ω hω
    exact propext (mem_escape_iff_inter (hB n ω hω) x)
  have husc : UpperSemicontinuousOn (fun q : Sym2 V → unitInterval => ⨅ n, law q (D n))
      {q | ∀ e, e ∉ G.edgeSet → ¬ e.IsDiag → q e = 0} :=
    upperSemicontinuousOn_iInf fun n => (hcont n).upperSemicontinuous.upperSemicontinuousOn _
  intro q hq
  refine UpperSemicontinuousWithinAt.congr_of_eventuallyEq (husc q hq) hq ?_
  filter_upwards [self_mem_nhdsWithin] with q' hq'
  rw [htheta]
  exact iInf_congr fun n => (hEq q' hq' n).symm

/-! ### One-parameter families -/

/-- **Right-continuity of `θ`** along a monotone family inside `P_G` that is continuous in
each coordinate. -/
theorem continuousWithinAt_law_cluster_infinite_Ici [Countable V] (G : SimpleGraph V)
    [G.LocallyFinite] {α : Type*} [TopologicalSpace α] [Preorder α]
    {q : α → Sym2 V → unitInterval} (hmono : Monotone q) (hcont : ∀ e, Continuous (q · e))
    (hG : ∀ s e, e ∉ G.edgeSet → ¬ e.IsDiag → q s e = 0) (x : V) (t : α) :
    ContinuousWithinAt (fun s => law (q s) {ω | (cluster ω x).Infinite}) (Ici t) t := by
  have husc := upperSemicontinuousOn_law_cluster_infinite G x (q t) (hG t)
  have hq : Tendsto q (𝓝 t) (𝓝[{q | ∀ e, e ∉ G.edgeSet → ¬ e.IsDiag → q e = 0}] (q t)) :=
    tendsto_nhdsWithin_iff.2 ⟨(continuous_pi hcont).tendsto t,
      Eventually.of_forall fun s => hG s⟩
  refine tendsto_order.2 ⟨fun a ha => ?_, fun b hb => ?_⟩
  · exact eventually_nhdsWithin_of_forall fun s hs =>
      ha.trans_le (law_cluster_infinite_mono (hmono hs) x)
  · exact nhdsWithin_le_nhds (hq.eventually (husc b hb))

/-! ### Non-vacuity -/

/-- The complete graph on `Fin 3` is locally finite and supports every profile. -/
example (x : Fin 3) :
    UpperSemicontinuousOn
      (fun q : Sym2 (Fin 3) → unitInterval => law q {ω | (cluster ω x).Infinite})
      {q | ∀ e, e ∉ (⊤ : SimpleGraph (Fin 3)).edgeSet → ¬ e.IsDiag → q e = 0} :=
  upperSemicontinuousOn_law_cluster_infinite ⊤ x

end PercLib.Percolation.Bond

end
