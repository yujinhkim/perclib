/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.
New proofs of the restricted-domain first-exit inequality and of the uniform boundary
contraction bound on the susceptibility (wiki boundary-laws, tags USAC and YLZV).
No upstream proof is copied, no definition is added and no Input is introduced.
-/
module

public import PercLib.Percolation.Bond.FirstExit
public import PercLib.Percolation.Bond.FiniteVolume
public import PercLib.Percolation.Bond.VolumeTails
public import PercLib.Percolation.Bond.ProfileRegularity
public import PercLib.Probability.DeterminedIndependence
public import PercLib.Probability.FirstMoment

/-! # First exit from a domain and boundary contraction

For `S ⊆ V` write `τ_S(x,u)` for the probability that `x` and `u` are joined inside `S`,
spelled `law q {ω | ∃ hx : x ∈ S, ∃ hu : u ∈ S, ((openGraph ω).induce S).Reachable ⟨x,hx⟩ ⟨u,hu⟩}`.

* `law_reach_le_firstExit` (USAC): for `u ∈ S`, `B ⊆ A \ S`,
  `P(u ↔_A B) ≤ ∑_{x ∈ S} ∑'_{y ∈ A \ S} τ_S(u,x) q(x,y) P(y ↔_A B)`.
* `chi_le_of_boundary_contraction` (YLZV): if each `x` has a finite `S_x ∋ x` with
  `∑_{u ∈ S_x} τ_{S_x}(x,u) ≤ B` and `Φ_q(x,S_x) ≤ a < 1`, then `χ(x) ≤ B (1 - a)⁻¹`,
  and with `B < ∞` almost surely every cluster is finite.

The proof of the first exit inequality decomposes according to the cluster `K` of `u`
inside `S`, takes the last open pair leaving `K`, and uses that `{K_S(u) = K}`, the exit
pair and connections in `A \ K` are determined by disjoint sets of pairs. The domain `S`
is first finite and then exhausted by finite sets. The susceptibility bound is proved in
finite volume, where the supremum over roots is finite, and then passes to the limit.
-/

@[expose] public section
noncomputable section
open MeasureTheory Set PercLib.Probability
open scoped ENNReal NNReal Classical

namespace PercLib.Percolation.Bond
variable {V : Type*}

/-! ## Walks in induced graphs -/

/-- Along a walk inside `A` ending outside `K`, either the walk avoids `K` altogether or
there is a last edge `z y` with `z ∈ K`, after which the walk stays in `A \ K`. -/
theorem induce_walk_last_exit (G : SimpleGraph V) (A K : Set V) {a b : A}
    (p : (G.induce A).Walk a b) (hb : (b : V) ∉ K) :
    (∃ ha : (a : V) ∈ A \ K, ∃ hb' : (b : V) ∈ A \ K,
        (G.induce (A \ K)).Reachable ⟨a, ha⟩ ⟨b, hb'⟩) ∨
      ∃ z ∈ K, ∃ y, ∃ hy : y ∈ A \ K, G.Adj z y ∧ ∃ hb' : (b : V) ∈ A \ K,
        (G.induce (A \ K)).Reachable ⟨y, hy⟩ ⟨b, hb'⟩ := by
  induction p with
  | nil => exact Or.inl ⟨⟨Subtype.prop _, hb⟩, ⟨Subtype.prop _, hb⟩, .refl _⟩
  | @cons a c d hac p ih =>
    rcases ih hb with ⟨hc, hd, hr⟩ | ⟨z, hz, y, hy, hzy, hd, hr⟩
    · by_cases haK : (a : V) ∈ K
      · exact Or.inr ⟨a, haK, c, hc, hac, hd, hr⟩
      · refine Or.inl ⟨⟨a.2, haK⟩, hd, ?_⟩
        have hadj : (G.induce (A \ K)).Adj ⟨a, ⟨a.2, haK⟩⟩ ⟨c, hc⟩ := hac
        exact hadj.reachable.trans hr
    · exact Or.inr ⟨z, hz, y, hy, hzy, hd, hr⟩

/-- Internal connections are preserved by enlarging the domain. -/
theorem exists_localConn_mono {ω : Config V} {D D' : Set V} (h : D ⊆ D') {a b : V}
    (hab : ∃ ha : a ∈ D, ∃ hb : b ∈ D, ((openGraph ω).induce D).Reachable ⟨a, ha⟩ ⟨b, hb⟩) :
    ∃ ha : a ∈ D', ∃ hb : b ∈ D', ((openGraph ω).induce D').Reachable ⟨a, ha⟩ ⟨b, hb⟩ := by
  obtain ⟨ha, hb, r⟩ := hab
  exact ⟨h ha, h hb, localConn_mono_domain ω h ⟨a, ha⟩ ⟨b, hb⟩ r⟩

/-- The event `{K_S(u) = K}` depends only on pairs meeting `K` with both ends in `S`. -/
theorem induce_cluster_eq_of_agree (S K : Set V) (u : V) {ω ω' : Config V}
    (hagree : ∀ a ∈ K, ∀ b ∈ S, (s(a, b) ∈ ω ↔ s(a, b) ∈ ω'))
    (h : ∀ v, (∃ hu : u ∈ S, ∃ hv : v ∈ S,
      ((openGraph ω).induce S).Reachable ⟨u, hu⟩ ⟨v, hv⟩) ↔ v ∈ K) :
    ∀ v, (∃ hu : u ∈ S, ∃ hv : v ∈ S,
      ((openGraph ω').induce S).Reachable ⟨u, hu⟩ ⟨v, hv⟩) ↔ v ∈ K := by
  -- Walks of `ω'` inside `S` starting in `K` stay in `K`.
  have hstay : ∀ (a b : S) (p : ((openGraph ω').induce S).Walk a b), (a : V) ∈ K →
      (b : V) ∈ K := by
    intro a b p
    induction p with
    | nil => exact id
    | @cons a c d hac p ih =>
      intro ha
      apply ih
      have hac' := (openGraph_adj_iff ω' a c).mp hac
      have hω : (openGraph ω).Adj a c :=
        (openGraph_adj_iff ω a c).mpr ⟨(hagree a ha c c.2).mpr hac'.1, hac'.2⟩
      obtain ⟨hu, ha', r⟩ := (h a).mpr ha
      have hadj : ((openGraph ω).induce S).Adj ⟨a, ha'⟩ c := hω
      exact (h c).mp ⟨hu, c.2, r.trans hadj.reachable⟩
  -- Walks of `ω` inside `S` from a vertex of `K` are walks of `ω'`.
  have htransfer : ∀ (a b : S) (p : ((openGraph ω).induce S).Walk a b),
      (∃ hu : u ∈ S, ((openGraph ω).induce S).Reachable ⟨u, hu⟩ a) →
      ((openGraph ω').induce S).Reachable a b := by
    intro a b p
    induction p with
    | nil => exact fun _ => .refl _
    | @cons a c d hac p ih =>
      rintro ⟨hu, r⟩
      have haK : (a : V) ∈ K := (h a).mp ⟨hu, a.2, r⟩
      have hac' := (openGraph_adj_iff ω a c).mp hac
      have hω' : ((openGraph ω').induce S).Adj a c :=
        (openGraph_adj_iff ω' a c).mpr ⟨(hagree a haK c c.2).mp hac'.1, hac'.2⟩
      have hadj : ((openGraph ω).induce S).Adj a c := hac
      exact hω'.reachable.trans (ih ⟨hu, r.trans hadj.reachable⟩)
  intro v
  constructor
  · rintro ⟨hu, hv, ⟨p⟩⟩
    have huK : u ∈ K := (h u).mp ⟨hu, hu, .refl _⟩
    exact hstay _ _ p huK
  · intro hv
    obtain ⟨hu, hv', r⟩ := (h v).mpr hv
    obtain ⟨p⟩ := r
    exact ⟨hu, hv', htransfer _ _ p ⟨hu, .refl _⟩⟩

/-! ## Measurability -/

/-- Connection inside a domain to some vertex of a target set is measurable. -/
theorem measurableSet_exists_induce_conn [Countable V] (D T : Set V) (y : V) :
    MeasurableSet {ω : Config V | ∃ b ∈ T, ∃ hy : y ∈ D, ∃ hb : b ∈ D,
      ((openGraph ω).induce D).Reachable ⟨y, hy⟩ ⟨b, hb⟩} := by
  have : {ω : Config V | ∃ b ∈ T, ∃ hy : y ∈ D, ∃ hb : b ∈ D,
      ((openGraph ω).induce D).Reachable ⟨y, hy⟩ ⟨b, hb⟩} =
      ⋃ b ∈ T, {ω : Config V | ∃ hy : y ∈ D, ∃ hb : b ∈ D,
        ((openGraph ω).induce D).Reachable ⟨y, hy⟩ ⟨b, hb⟩} := by
    ext ω
    simp
  rw [this]
  exact MeasurableSet.biUnion T.to_countable fun b _ => measurableSet_induce_conn D y b

/-- The event that the internal cluster of `u` in `S` equals `K` is measurable. -/
theorem measurableSet_induce_cluster_eq [Countable V] (S K : Set V) (u : V) :
    MeasurableSet {ω : Config V | ∀ v, (∃ hu : u ∈ S, ∃ hv : v ∈ S,
      ((openGraph ω).induce S).Reachable ⟨u, hu⟩ ⟨v, hv⟩) ↔ v ∈ K} := by
  rw [ofPred_forall]
  refine MeasurableSet.iInter fun v => ?_
  by_cases hv : v ∈ K
  · convert measurableSet_induce_conn S u v using 1
    ext ω
    simp [hv]
  · convert (measurableSet_induce_conn S u v).compl using 1
    ext ω
    simp [hv]

/-! ## The first-exit inequality for a finite domain -/

/-- **First exit from a finite domain.** Connections inside `A` from `u ∈ S` to targets
not joined to `u` inside `S` pass through a pair `x y` with `x ∈ S`, `y ∉ S`. -/
theorem law_reach_not_localConn_le_firstExit [Countable V] (q : Sym2 V → unitInterval)
    (S : Finset V) (A T : Set V) {u : V} (hu : u ∈ S) :
    law q {ω | ∃ b ∈ T, (∃ hu : u ∈ A, ∃ hb : b ∈ A,
        ((openGraph ω).induce A).Reachable ⟨u, hu⟩ ⟨b, hb⟩) ∧
        ¬ ∃ hu : u ∈ (S : Set V), ∃ hb : b ∈ (S : Set V),
          ((openGraph ω).induce (S : Set V)).Reachable ⟨u, hu⟩ ⟨b, hb⟩} ≤
      ∑ x ∈ S, ∑' y, if y ∈ S then 0 else
        law q {ω | ∃ hu : u ∈ (S : Set V), ∃ hx : x ∈ (S : Set V),
          ((openGraph ω).induce (S : Set V)).Reachable ⟨u, hu⟩ ⟨x, hx⟩} *
        (unitInterval.toNNReal (q s(x, y)) : ℝ≥0∞) *
        law q {ω | ∃ b ∈ T, ∃ hy : y ∈ A, ∃ hb : b ∈ A,
          ((openGraph ω).induce A).Reachable ⟨y, hy⟩ ⟨b, hb⟩} := by
  -- The internal cluster events, the exit events and the joint events.
  set E : Finset V → Set (Config V) := fun K => {ω | ∀ v, (∃ hu : u ∈ (S : Set V),
    ∃ hv : v ∈ (S : Set V), ((openGraph ω).induce (S : Set V)).Reachable ⟨u, hu⟩ ⟨v, hv⟩) ↔
      v ∈ K} with hE
  set F : Finset V → V → Set (Config V) := fun K y => {ω | ∃ b ∈ T,
    ∃ hy : y ∈ A \ (K : Set V), ∃ hb : b ∈ A \ (K : Set V),
      ((openGraph ω).induce (A \ (K : Set V))).Reachable ⟨y, hy⟩ ⟨b, hb⟩} with hF
  set H : Finset V → V → V → Set (Config V) := fun K x y =>
    {ω | x ∈ K ∧ y ∉ S ∧ ω ∈ E K ∧ s(x, y) ∈ ω ∧ ω ∈ F K y} with hH
  set τ : V → ℝ≥0∞ := fun x => law q {ω | ∃ hu : u ∈ (S : Set V), ∃ hx : x ∈ (S : Set V),
    ((openGraph ω).induce (S : Set V)).Reachable ⟨u, hu⟩ ⟨x, hx⟩} with hτ
  set P : V → ℝ≥0∞ := fun y => law q {ω | ∃ b ∈ T, ∃ hy : y ∈ A, ∃ hb : b ∈ A,
    ((openGraph ω).induce A).Reachable ⟨y, hy⟩ ⟨b, hb⟩} with hP
  -- Covering by the joint events.
  have hcover : {ω | ∃ b ∈ T, (∃ hu : u ∈ A, ∃ hb : b ∈ A,
        ((openGraph ω).induce A).Reachable ⟨u, hu⟩ ⟨b, hb⟩) ∧
        ¬ ∃ hu : u ∈ (S : Set V), ∃ hb : b ∈ (S : Set V),
          ((openGraph ω).induce (S : Set V)).Reachable ⟨u, hu⟩ ⟨b, hb⟩} ⊆
      ⋃ x ∈ S, ⋃ y, ⋃ K ∈ S.powerset, H K x y := by
    rintro ω ⟨b, hbT, ⟨huA, hbA, ⟨p⟩⟩, hnot⟩
    set K : Finset V := S.filter fun v => ∃ hu : u ∈ (S : Set V), ∃ hv : v ∈ (S : Set V),
      ((openGraph ω).induce (S : Set V)).Reachable ⟨u, hu⟩ ⟨v, hv⟩ with hK
    have hmemK : ∀ v, v ∈ K ↔ ∃ hu : u ∈ (S : Set V), ∃ hv : v ∈ (S : Set V),
        ((openGraph ω).induce (S : Set V)).Reachable ⟨u, hu⟩ ⟨v, hv⟩ := by
      intro v
      rw [hK, Finset.mem_filter]
      exact ⟨fun h => h.2, fun h => ⟨h.2.1, h⟩⟩
    have huK : u ∈ K := (hmemK u).mpr ⟨hu, hu, .refl _⟩
    have hbK : b ∉ (K : Set V) := fun h => hnot ((hmemK b).mp h)
    rcases induce_walk_last_exit (openGraph ω) A K p hbK with ⟨hu', _, _⟩ | ⟨z, hz, y, hy, hzy,
      hb', r⟩
    · exact absurd huK hu'.2
    · have hzS : z ∈ S := (Finset.mem_filter.mp hz).1
      have hyS : y ∉ S := by
        intro hyS
        obtain ⟨hu0, hz0, r0⟩ := (hmemK z).mp hz
        have hadj : ((openGraph ω).induce (S : Set V)).Adj ⟨z, hz0⟩ ⟨y, hyS⟩ := hzy
        exact hy.2 ((hmemK y).mpr ⟨hu0, hyS, r0.trans hadj.reachable⟩)
      refine mem_iUnion₂.mpr ⟨z, hzS, mem_iUnion.mpr ⟨y, mem_iUnion₂.mpr
        ⟨K, Finset.mem_powerset.mpr (Finset.filter_subset _ _), ?_⟩⟩⟩
      exact ⟨hz, hyS, fun v => (hmemK v).symm, ((openGraph_adj_iff ω z y).mp hzy).1,
        b, hbT, hy, hb', r⟩
  -- Each joint event factorises.
  have hjoint : ∀ x ∈ S, ∀ y, ∀ K ∈ S.powerset, law q (H K x y) ≤
      (if y ∈ S then 0 else
        (if x ∈ K then law q (E K) else 0) * (unitInterval.toNNReal (q s(x, y)) : ℝ≥0∞) *
          P y) := by
    intro x _ y K hK
    have hKS : (K : Set V) ⊆ S := Finset.coe_subset.mpr (Finset.mem_powerset.mp hK)
    by_cases hyS : y ∈ S
    · have : H K x y = ∅ := by
        ext ω
        simp [hH, hyS]
      simp [this, hyS]
    by_cases hxK : x ∈ K
    swap
    · have : H K x y = ∅ := by
        ext ω
        simp [hH, hxK]
      simp [this]
    simp only [hyS, hxK, ↓reduceIte]
    have hHeq : H K x y = E K ∩ ({ω | s(x, y) ∈ ω} ∩ F K y) := by
      ext ω
      simp only [hH, mem_ofPred_eq, mem_inter_iff]
      tauto
    have hyK : y ∉ (K : Set V) := fun h => hyS (hKS h)
    -- Measurability.
    have hEm : MeasurableSet (E K) := measurableSet_induce_cluster_eq _ _ u
    have hFm : MeasurableSet (F K y) := by
      have h := measurableSet_exists_induce_conn (A \ (K : Set V)) T y
      convert h using 1
    have hxym : MeasurableSet {ω : Config V | s(x, y) ∈ ω} := measurableSet_mem _
    -- Determinedness.
    have hEdet : ∀ ω ω' : Config V,
        ω ∩ {e | (∃ v ∈ e, v ∈ K) ∧ ∀ v ∈ e, v ∈ (S : Set V)} =
          ω' ∩ {e | (∃ v ∈ e, v ∈ K) ∧ ∀ v ∈ e, v ∈ (S : Set V)} →
        (ω ∈ E K ↔ ω' ∈ E K) := by
      have key : ∀ ω ω' : Config V,
          ω ∩ {e | (∃ v ∈ e, v ∈ K) ∧ ∀ v ∈ e, v ∈ (S : Set V)} =
            ω' ∩ {e | (∃ v ∈ e, v ∈ K) ∧ ∀ v ∈ e, v ∈ (S : Set V)} →
          ω ∈ E K → ω' ∈ E K := by
        intro ω ω' heq hω
        refine induce_cluster_eq_of_agree (S : Set V) (K : Set V) u ?_ hω
        intro a ha b hb
        have hmem : s(a, b) ∈ {e : Sym2 V | (∃ v ∈ e, v ∈ K) ∧ ∀ v ∈ e, v ∈ (S : Set V)} := by
          refine ⟨⟨a, Sym2.mem_mk_left a b, ha⟩, fun v hv => ?_⟩
          rcases Sym2.mem_iff.mp hv with rfl | rfl
          · exact hKS ha
          · exact hb
        have := congrArg (fun t : Set (Sym2 V) => s(a, b) ∈ t) heq
        simp only [mem_inter_iff, eq_iff_iff] at this
        exact ⟨fun h => (this.mp ⟨h, hmem⟩).1, fun h => (this.mpr ⟨h, hmem⟩).1⟩
      exact fun ω ω' heq => ⟨key ω ω' heq, key ω' ω heq.symm⟩
    have hFdet : ∀ ω ω' : Config V,
        ω ∩ {e | ∀ v ∈ e, v ∈ A \ (K : Set V)} = ω' ∩ {e | ∀ v ∈ e, v ∈ A \ (K : Set V)} →
        (ω ∈ F K y ↔ ω' ∈ F K y) := by
      intro ω ω' heq
      have hag : ∀ a ∈ A \ (K : Set V), ∀ b ∈ A \ (K : Set V), (s(a, b) ∈ ω ↔ s(a, b) ∈ ω') := by
        intro a ha b hb
        have hmem : s(a, b) ∈ {e : Sym2 V | ∀ v ∈ e, v ∈ A \ (K : Set V)} := by
          intro v hv
          rcases Sym2.mem_iff.mp hv with rfl | rfl
          · exact ha
          · exact hb
        have := congrArg (fun t : Set (Sym2 V) => s(a, b) ∈ t) heq
        simp only [mem_inter_iff, eq_iff_iff] at this
        exact ⟨fun h => (this.mp ⟨h, hmem⟩).1, fun h => (this.mpr ⟨h, hmem⟩).1⟩
      simp only [hF, mem_ofPred_eq]
      exact exists_congr fun b => and_congr_right fun _ => exists_congr fun hy =>
        exists_congr fun hb => localConn_iff_of_agree _ ⟨y, hy⟩ ⟨b, hb⟩ hag
    have hxydet : ∀ ω ω' : Config V, ω ∩ {s(x, y)} = ω' ∩ {s(x, y)} →
        (ω ∈ {ω : Config V | s(x, y) ∈ ω} ↔ ω' ∈ {ω : Config V | s(x, y) ∈ ω}) := by
      intro ω ω' heq
      have := congrArg (fun t : Set (Sym2 V) => s(x, y) ∈ t) heq
      simpa using this
    -- Disjointness of the determining pair sets.
    have hdisj1 : Disjoint {e : Sym2 V | (∃ v ∈ e, v ∈ K) ∧ ∀ v ∈ e, v ∈ (S : Set V)}
        ({s(x, y)} ∪ {e | ∀ v ∈ e, v ∈ A \ (K : Set V)}) := by
      rw [Set.disjoint_left]
      rintro e ⟨⟨v, hve, hvK⟩, hS⟩ (he | he)
      · rw [mem_singleton_iff] at he
        subst he
        exact hyS (hS y (Sym2.mem_mk_right x y))
      · exact (he v hve).2 hvK
    have hdisj2 : Disjoint ({s(x, y)} : Set (Sym2 V)) {e | ∀ v ∈ e, v ∈ A \ (K : Set V)} := by
      rw [Set.disjoint_singleton_left]
      intro h
      exact (h x (Sym2.mem_mk_left x y)).2 hxK
    have hInner : law q ({ω | s(x, y) ∈ ω} ∩ F K y) =
        (unitInterval.toNNReal (q s(x, y)) : ℝ≥0∞) * law q (F K y) := by
      rw [show law q ({ω | s(x, y) ∈ ω} ∩ F K y) =
          law q {ω : Config V | s(x, y) ∈ ω} * law q (F K y) from
        prodBernoulli_inter_of_determined q hdisj2 hxym hFm hxydet hFdet]
      simp only [law, prodBernoulli_setOf_mem]
    have hOuter : law q (E K ∩ ({ω | s(x, y) ∈ ω} ∩ F K y)) =
        law q (E K) * law q ({ω | s(x, y) ∈ ω} ∩ F K y) := by
      refine prodBernoulli_inter_of_determined q hdisj1 hEm (hxym.inter hFm) hEdet ?_
      intro ω ω' heq
      have hres : ∀ {Q' : Set (Sym2 V)},
          Q' ⊆ {s(x, y)} ∪ {e | ∀ v ∈ e, v ∈ A \ (K : Set V)} → ω ∩ Q' = ω' ∩ Q' := by
        intro Q' hQ
        ext e
        have he := Set.ext_iff.mp heq e
        simp only [mem_inter_iff] at he ⊢
        constructor
        · rintro ⟨h1, h2⟩
          exact ⟨(he.mp ⟨h1, hQ h2⟩).1, h2⟩
        · rintro ⟨h1, h2⟩
          exact ⟨(he.mpr ⟨h1, hQ h2⟩).1, h2⟩
      have h1 : ω ∩ {s(x, y)} = ω' ∩ {s(x, y)} := hres subset_union_left
      have h2 : ω ∩ {e | ∀ v ∈ e, v ∈ A \ (K : Set V)} =
          ω' ∩ {e | ∀ v ∈ e, v ∈ A \ (K : Set V)} := hres subset_union_right
      simp only [mem_inter_iff]
      exact and_congr (hxydet ω ω' h1) (hFdet ω ω' h2)
    have hFle : law q (F K y) ≤ P y := by
      refine measure_mono fun ω ⟨b, hbT, hy, hb, r⟩ => ⟨b, hbT, ?_⟩
      exact exists_localConn_mono sdiff_subset ⟨hy, hb, r⟩
    rw [hHeq, hOuter, hInner, ← mul_assoc]
    exact mul_le_mul' le_rfl hFle
  -- Summing the internal cluster events containing `x` gives `τ x`.
  have hsumE : ∀ x ∈ S, ∑ K ∈ S.powerset, (if x ∈ K then law q (E K) else 0) ≤ τ x := by
    intro x _
    have hdisjE : PairwiseDisjoint (↑(S.powerset.filter (x ∈ ·)) : Set (Finset V)) E := by
      intro K _ K' _ hne
      rw [Function.onFun, Set.disjoint_left]
      intro ω h h'
      apply hne
      ext v
      exact (h v).symm.trans (h' v)
    rw [← Finset.sum_filter, ← measure_biUnion_finset hdisjE
      (fun K _ => measurableSet_induce_cluster_eq _ _ u)]
    refine measure_mono ?_
    intro ω hω
    obtain ⟨K, hK, hω⟩ := mem_iUnion₂.mp hω
    exact (hω x).mpr (Finset.mem_filter.mp hK).2
  -- Assemble.
  calc law q _ ≤ law q (⋃ x ∈ S, ⋃ y, ⋃ K ∈ S.powerset, H K x y) := measure_mono hcover
    _ ≤ ∑ x ∈ S, law q (⋃ y, ⋃ K ∈ S.powerset, H K x y) := measure_biUnion_finset_le _ _
    _ ≤ ∑ x ∈ S, ∑' y, law q (⋃ K ∈ S.powerset, H K x y) :=
        Finset.sum_le_sum fun _ _ => measure_iUnion_le _
    _ ≤ ∑ x ∈ S, ∑' y, ∑ K ∈ S.powerset, law q (H K x y) :=
        Finset.sum_le_sum fun _ _ => ENNReal.tsum_le_tsum fun _ =>
          measure_biUnion_finset_le _ _
    _ ≤ ∑ x ∈ S, ∑' y, if y ∈ S then 0 else τ x *
          (unitInterval.toNNReal (q s(x, y)) : ℝ≥0∞) * P y := by
        refine Finset.sum_le_sum fun x hx => ENNReal.tsum_le_tsum fun y => ?_
        refine (Finset.sum_le_sum fun K hK => hjoint x hx y K hK).trans ?_
        by_cases hyS : y ∈ S
        · simp [hyS]
        · simp only [hyS, ↓reduceIte]
          rw [← Finset.sum_mul, ← Finset.sum_mul]
          exact mul_le_mul' (mul_le_mul' (hsumE x hx) le_rfl) le_rfl

/-! ## The restricted-domain first-exit inequality (USAC) -/

/-- **Restricted-domain first exit (USAC).** For `u ∈ S` and `B ⊆ A \ S`, with no
finiteness assumed,
`P(u ↔_A B) ≤ ∑_{x ∈ S} ∑'_{y ∈ A \ S} τ_S(u,x) q(x,y) P(y ↔_A B)`.
Terms with `x ∉ S` or `y ∉ A` vanish because the events require membership. -/
theorem law_reach_le_firstExit [Countable V] (q : Sym2 V → unitInterval) {S A B : Set V}
    {u : V} (hu : u ∈ S) (hB : B ⊆ A \ S) :
    law q {ω | ∃ b ∈ B, ∃ hu : u ∈ A, ∃ hb : b ∈ A,
        ((openGraph ω).induce A).Reachable ⟨u, hu⟩ ⟨b, hb⟩} ≤
      ∑' x, ∑' y, if y ∈ S then 0 else
        law q {ω | ∃ hu : u ∈ S, ∃ hx : x ∈ S,
          ((openGraph ω).induce S).Reachable ⟨u, hu⟩ ⟨x, hx⟩} *
        (unitInterval.toNNReal (q s(x, y)) : ℝ≥0∞) *
        law q {ω | ∃ b ∈ B, ∃ hy : y ∈ A, ∃ hb : b ∈ A,
          ((openGraph ω).induce A).Reachable ⟨y, hy⟩ ⟨b, hb⟩} := by
  set R : Finset V → Set (Config V) := fun F => {ω | ∃ b ∈ B,
    ∃ hu : u ∈ A ∩ (F : Set V), ∃ hb : b ∈ A ∩ (F : Set V),
      ((openGraph ω).induce (A ∩ (F : Set V))).Reachable ⟨u, hu⟩ ⟨b, hb⟩} with hR
  -- Every connection inside `A` is a connection inside `A ∩ F` for a finite `F`.
  have hcover : {ω | ∃ b ∈ B, ∃ hu : u ∈ A, ∃ hb : b ∈ A,
      ((openGraph ω).induce A).Reachable ⟨u, hu⟩ ⟨b, hb⟩} ⊆ ⋃ F, R F := by
    rintro ω ⟨b, hbB, huA, hbA, ⟨p⟩⟩
    let p' := p.map (SimpleGraph.Embedding.induce A).toHom
    let F : Finset V := p'.support.toFinset
    have hsupp : {v | v ∈ p'.support} ⊆ A ∩ (F : Set V) := by
      intro v hv
      change v ∈ p'.support at hv
      refine ⟨?_, Finset.mem_coe.mpr (List.mem_toFinset.mpr hv)⟩
      rw [SimpleGraph.Walk.support_map] at hv
      obtain ⟨w, _, hw⟩ := List.mem_map.mp hv
      subst hw
      exact w.2
    have hconn := p'.connected_induce_support
    have hr := hconn.preconnected ⟨u, p'.start_mem_support⟩ ⟨b, p'.end_mem_support⟩
    exact mem_iUnion.mpr ⟨F, b, hbB, hsupp p'.start_mem_support, hsupp p'.end_mem_support,
      hr.map ((openGraph ω).induceHomOfLE hsupp).toHom⟩
  have hdir : Directed (· ⊆ ·) R := by
    intro F G
    refine ⟨F ∪ G, ?_, ?_⟩ <;>
    · rintro ω ⟨b, hbB, h⟩
      refine ⟨b, hbB, exists_localConn_mono ?_ h⟩
      exact inter_subset_inter_right _ (by simp [Finset.coe_union])
  refine (measure_mono hcover).trans ?_
  rw [hdir.measure_iUnion]
  refine iSup_le fun F => ?_
  by_cases huF : u ∈ F
  swap
  · have : R F = ∅ := Set.eq_empty_iff_forall_notMem.mpr fun ω ⟨_, _, hu', _⟩ => huF hu'.2
    rw [this, measure_empty]
    exact zero_le
  set S' : Finset V := F.filter (· ∈ S) with hS'
  have huS' : u ∈ S' := Finset.mem_filter.mpr ⟨huF, hu⟩
  have hS'S : (S' : Set V) ⊆ S := fun v hv => (Finset.mem_filter.mp hv).2
  have hRsub : R F ⊆ {ω | ∃ b ∈ B, (∃ hu : u ∈ A ∩ (F : Set V), ∃ hb : b ∈ A ∩ (F : Set V),
        ((openGraph ω).induce (A ∩ (F : Set V))).Reachable ⟨u, hu⟩ ⟨b, hb⟩) ∧
        ¬ ∃ hu : u ∈ (S' : Set V), ∃ hb : b ∈ (S' : Set V),
          ((openGraph ω).induce (S' : Set V)).Reachable ⟨u, hu⟩ ⟨b, hb⟩} := by
    rintro ω ⟨b, hbB, h⟩
    exact ⟨b, hbB, h, fun ⟨_, hb, _⟩ => (hB hbB).2 (hS'S hb)⟩
  refine (measure_mono hRsub).trans ((law_reach_not_localConn_le_firstExit q S'
    (A ∩ (F : Set V)) B huS').trans ?_)
  refine (Finset.sum_le_sum fun x _ => ENNReal.tsum_le_tsum fun y => ?_).trans
    (ENNReal.sum_le_tsum S')
  by_cases hyS : y ∈ S
  · by_cases hyF : y ∈ F
    · have : y ∈ S' := Finset.mem_filter.mpr ⟨hyF, hyS⟩
      simp [this]
    · have hP0 : law q {ω | ∃ b ∈ B, ∃ hy : y ∈ A ∩ (F : Set V), ∃ hb : b ∈ A ∩ (F : Set V),
          ((openGraph ω).induce (A ∩ (F : Set V))).Reachable ⟨y, hy⟩ ⟨b, hb⟩} = 0 := by
        have : {ω : Config V | ∃ b ∈ B, ∃ hy : y ∈ A ∩ (F : Set V),
            ∃ hb : b ∈ A ∩ (F : Set V),
            ((openGraph ω).induce (A ∩ (F : Set V))).Reachable ⟨y, hy⟩ ⟨b, hb⟩} = ∅ :=
          Set.eq_empty_iff_forall_notMem.mpr fun ω ⟨_, _, hy', _⟩ => hyF hy'.2
        rw [this, measure_empty]
      rw [hP0, mul_zero, ite_self]
      exact zero_le
  · have hyS' : y ∉ S' := fun h => hyS (hS'S h)
    simp only [hyS, hyS', ↓reduceIte]
    exact mul_le_mul' (mul_le_mul' (measure_mono fun ω h => exists_localConn_mono hS'S h) le_rfl)
      (measure_mono fun ω ⟨b, hbB, h⟩ => ⟨b, hbB, exists_localConn_mono inter_subset_left h⟩)

/-! ## Finite-volume susceptibility -/

/-- The expected size of an internal cluster is the sum of internal connection
probabilities. -/
theorem lintegral_encard_induce [Countable V] (q : Sym2 V → unitInterval) (D : Set V) (x : V) :
    ∫⁻ ω, (({y | ∃ hx : x ∈ D, ∃ hy : y ∈ D,
      ((openGraph ω).induce D).Reachable ⟨x, hx⟩ ⟨y, hy⟩} : Set V).encard : ℝ≥0∞) ∂law q =
      ∑' v, law q {ω | ∃ hx : x ∈ D, ∃ hv : v ∈ D,
        ((openGraph ω).induce D).Reachable ⟨x, hx⟩ ⟨v, hv⟩} := by
  have hpt : ∀ ω : Config V, ((({y | ∃ hx : x ∈ D, ∃ hy : y ∈ D,
      ((openGraph ω).induce D).Reachable ⟨x, hx⟩ ⟨y, hy⟩} : Set V).encard : ℝ≥0∞)) =
      ∑' v, ({ω : Config V | ∃ hx : x ∈ D, ∃ hv : v ∈ D,
        ((openGraph ω).induce D).Reachable ⟨x, hx⟩ ⟨v, hv⟩}).indicator 1 ω := by
    intro ω
    rw [encard_eq_tsum_indicator]
    refine tsum_congr fun v => ?_
    simp only [indicator, mem_ofPred_eq, Pi.one_apply]
  simp_rw [hpt]
  rw [lintegral_tsum fun v => (measurable_one.indicator
    (measurableSet_induce_conn D x v)).aemeasurable]
  exact tsum_congr fun v => lintegral_indicator_one (measurableSet_induce_conn D x v)

/-- Off the domain the internal connection probabilities vanish. -/
theorem law_induce_conn_eq_zero_of_notMem {q : Sym2 V → unitInterval} {D : Set V} {x v : V}
    (h : x ∉ D ∨ v ∉ D) :
    law q {ω | ∃ hx : x ∈ D, ∃ hv : v ∈ D,
      ((openGraph ω).induce D).Reachable ⟨x, hx⟩ ⟨v, hv⟩} = 0 := by
  have : {ω : Config V | ∃ hx : x ∈ D, ∃ hv : v ∈ D,
      ((openGraph ω).induce D).Reachable ⟨x, hx⟩ ⟨v, hv⟩} = ∅ := by
    refine Set.eq_empty_iff_forall_notMem.mpr fun ω ⟨hx, hv, _⟩ => ?_
    rcases h with h | h
    · exact h hx
    · exact h hv
  rw [this, measure_empty]

/-- In a finite domain the expected internal cluster size is at most its cardinality. -/
theorem tsum_law_induce_conn_le_card {q : Sym2 V → unitInterval} (Λ : Finset V) (x : V) :
    ∑' v, law q {ω | ∃ hx : x ∈ (Λ : Set V), ∃ hv : v ∈ (Λ : Set V),
      ((openGraph ω).induce (Λ : Set V)).Reachable ⟨x, hx⟩ ⟨v, hv⟩} ≤ Λ.card := by
  rw [tsum_eq_sum (s := Λ) fun v hv => law_induce_conn_eq_zero_of_notMem (Or.inr hv)]
  calc _ ≤ ∑ _v ∈ Λ, (1 : ℝ≥0∞) := Finset.sum_le_sum fun _ _ => prob_le_one
    _ = Λ.card := by simp

/-- **Boundary contraction in finite volume.** -/
theorem tsum_law_induce_conn_le_of_boundary_contraction [Countable V]
    (q : Sym2 V → unitInterval) (Sx : V → Finset V) (hSx : ∀ x, x ∈ Sx x) {B a : ℝ≥0∞}
    (ha : a < 1)
    (hB : ∀ x, ∑ u ∈ Sx x, law q {ω | ∃ hx : x ∈ (Sx x : Set V), ∃ hu : u ∈ (Sx x : Set V),
      ((openGraph ω).induce (Sx x : Set V)).Reachable ⟨x, hx⟩ ⟨u, hu⟩} ≤ B)
    (hΦ : ∀ x, ∑ u ∈ Sx x, ∑' v, (if v ∈ Sx x then 0 else
      law q {ω | ∃ hx : x ∈ (Sx x : Set V), ∃ hu : u ∈ (Sx x : Set V),
        ((openGraph ω).induce (Sx x : Set V)).Reachable ⟨x, hx⟩ ⟨u, hu⟩} *
      (unitInterval.toNNReal (q s(u, v)) : ℝ≥0∞)) ≤ a)
    (Λ : Finset V) (x : V) :
    ∑' v, law q {ω | ∃ hx : x ∈ (Λ : Set V), ∃ hv : v ∈ (Λ : Set V),
      ((openGraph ω).induce (Λ : Set V)).Reachable ⟨x, hx⟩ ⟨v, hv⟩} ≤ B / (1 - a) := by
  set W : V → ℝ≥0∞ := fun y => ∑' v, law q {ω | ∃ hy : y ∈ (Λ : Set V),
    ∃ hv : v ∈ (Λ : Set V), ((openGraph ω).induce (Λ : Set V)).Reachable ⟨y, hy⟩ ⟨v, hv⟩}
    with hW
  set M : ℝ≥0∞ := ⨆ y, W y with hM
  have hWM : ∀ y, W y ≤ M := fun y => le_iSup W y
  have hMtop : M ≠ ∞ :=
    ne_top_of_le_ne_top (ENNReal.natCast_ne_top Λ.card)
      (iSup_le fun y => tsum_law_induce_conn_le_card Λ y)
  have hW0 : ∀ y, y ∉ Λ → W y = 0 := fun y hy =>
    ENNReal.tsum_eq_zero.mpr fun v => law_induce_conn_eq_zero_of_notMem (Or.inl hy)
  -- The recursive bound `W y ≤ B + a M`.
  have hstep : ∀ y, W y ≤ B + a * M := by
    intro y
    by_cases hyΛ : y ∈ Λ
    swap
    · rw [hW0 y hyΛ]
      exact zero_le
    set S' : Finset V := (Sx y).filter (· ∈ Λ) with hS'
    have hyS' : y ∈ S' := Finset.mem_filter.mpr ⟨hSx y, hyΛ⟩
    have hS'Sx : (S' : Set V) ⊆ Sx y := fun v hv => (Finset.mem_filter.mp hv).1
    have hS'Λ : (S' : Set V) ⊆ Λ := fun v hv => (Finset.mem_filter.mp hv).2
    -- Split each connection according to whether it is internal to `S'`.
    have hsplit : ∀ v, law q {ω | ∃ hy : y ∈ (Λ : Set V), ∃ hv : v ∈ (Λ : Set V),
        ((openGraph ω).induce (Λ : Set V)).Reachable ⟨y, hy⟩ ⟨v, hv⟩} ≤
        law q {ω | ∃ hy : y ∈ (S' : Set V), ∃ hv : v ∈ (S' : Set V),
          ((openGraph ω).induce (S' : Set V)).Reachable ⟨y, hy⟩ ⟨v, hv⟩} +
        ∑ z ∈ S', ∑' w, if w ∈ S' then 0 else
          law q {ω | ∃ hy : y ∈ (S' : Set V), ∃ hz : z ∈ (S' : Set V),
            ((openGraph ω).induce (S' : Set V)).Reachable ⟨y, hy⟩ ⟨z, hz⟩} *
          (unitInterval.toNNReal (q s(z, w)) : ℝ≥0∞) *
          law q {ω | ∃ hw : w ∈ (Λ : Set V), ∃ hv : v ∈ (Λ : Set V),
            ((openGraph ω).induce (Λ : Set V)).Reachable ⟨w, hw⟩ ⟨v, hv⟩} := by
      intro v
      have hfe := law_reach_not_localConn_le_firstExit q S' (Λ : Set V) {v} hyS'
      simp only [mem_singleton_iff, exists_eq_left] at hfe
      refine (measure_mono ?_).trans ((measure_union_le _ _).trans (add_le_add le_rfl hfe))
      intro ω hω
      by_cases hin : ∃ hy : y ∈ (S' : Set V), ∃ hv : v ∈ (S' : Set V),
          ((openGraph ω).induce (S' : Set V)).Reachable ⟨y, hy⟩ ⟨v, hv⟩
      · exact Or.inl hin
      · exact Or.inr ⟨hω, hin⟩
    -- The internal part.
    have hint : ∑' v, law q {ω | ∃ hy : y ∈ (S' : Set V), ∃ hv : v ∈ (S' : Set V),
        ((openGraph ω).induce (S' : Set V)).Reachable ⟨y, hy⟩ ⟨v, hv⟩} ≤ B := by
      rw [tsum_eq_sum (s := Sx y) fun v hv =>
        law_induce_conn_eq_zero_of_notMem (Or.inr fun h => hv (hS'Sx h))]
      refine le_trans (Finset.sum_le_sum fun v _ => measure_mono fun ω h =>
        exists_localConn_mono hS'Sx h) (hB y)
    -- The boundary part.
    have hbd : ∑' v, ∑ z ∈ S', ∑' w, (if w ∈ S' then 0 else
          law q {ω | ∃ hy : y ∈ (S' : Set V), ∃ hz : z ∈ (S' : Set V),
            ((openGraph ω).induce (S' : Set V)).Reachable ⟨y, hy⟩ ⟨z, hz⟩} *
          (unitInterval.toNNReal (q s(z, w)) : ℝ≥0∞) *
          law q {ω | ∃ hw : w ∈ (Λ : Set V), ∃ hv : v ∈ (Λ : Set V),
            ((openGraph ω).induce (Λ : Set V)).Reachable ⟨w, hw⟩ ⟨v, hv⟩}) ≤ a * M := by
      rw [Summable.tsum_finsetSum fun _ _ => ENNReal.summable]
      rw [Finset.sum_congr rfl fun z _ => ENNReal.tsum_comm]
      have hinner : ∀ z ∈ S', ∀ w, ∑' v, (if w ∈ S' then 0 else
          law q {ω | ∃ hy : y ∈ (S' : Set V), ∃ hz : z ∈ (S' : Set V),
            ((openGraph ω).induce (S' : Set V)).Reachable ⟨y, hy⟩ ⟨z, hz⟩} *
          (unitInterval.toNNReal (q s(z, w)) : ℝ≥0∞) *
          law q {ω | ∃ hw : w ∈ (Λ : Set V), ∃ hv : v ∈ (Λ : Set V),
            ((openGraph ω).induce (Λ : Set V)).Reachable ⟨w, hw⟩ ⟨v, hv⟩}) ≤
          (if w ∈ Sx y then 0 else
            law q {ω | ∃ hy : y ∈ (Sx y : Set V), ∃ hz : z ∈ (Sx y : Set V),
              ((openGraph ω).induce (Sx y : Set V)).Reachable ⟨y, hy⟩ ⟨z, hz⟩} *
            (unitInterval.toNNReal (q s(z, w)) : ℝ≥0∞)) * M := by
        intro z _ w
        by_cases hwS' : w ∈ S'
        · simp [hwS']
        simp only [hwS', ↓reduceIte]
        rw [ENNReal.tsum_mul_left]
        by_cases hwΛ : w ∈ Λ
        · have hwSx : w ∉ Sx y := fun h => hwS' (Finset.mem_filter.mpr ⟨h, hwΛ⟩)
          simp only [hwSx, ↓reduceIte]
          exact mul_le_mul' (mul_le_mul' (measure_mono fun ω h => exists_localConn_mono hS'Sx h)
            le_rfl) (hWM w)
        · rw [show (∑' v, law q {ω | ∃ hw : w ∈ (Λ : Set V), ∃ hv : v ∈ (Λ : Set V),
              ((openGraph ω).induce (Λ : Set V)).Reachable ⟨w, hw⟩ ⟨v, hv⟩}) = 0 from
            hW0 w hwΛ, mul_zero]
          exact zero_le
      calc _ ≤ ∑ z ∈ S', ∑' w, (if w ∈ Sx y then 0 else
            law q {ω | ∃ hy : y ∈ (Sx y : Set V), ∃ hz : z ∈ (Sx y : Set V),
              ((openGraph ω).induce (Sx y : Set V)).Reachable ⟨y, hy⟩ ⟨z, hz⟩} *
            (unitInterval.toNNReal (q s(z, w)) : ℝ≥0∞)) * M :=
            Finset.sum_le_sum fun z hz => ENNReal.tsum_le_tsum fun w => hinner z hz w
        _ ≤ ∑ z ∈ Sx y, ∑' w, (if w ∈ Sx y then 0 else
            law q {ω | ∃ hy : y ∈ (Sx y : Set V), ∃ hz : z ∈ (Sx y : Set V),
              ((openGraph ω).induce (Sx y : Set V)).Reachable ⟨y, hy⟩ ⟨z, hz⟩} *
            (unitInterval.toNNReal (q s(z, w)) : ℝ≥0∞)) * M :=
            Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
        _ = (∑ z ∈ Sx y, ∑' w, (if w ∈ Sx y then 0 else
            law q {ω | ∃ hy : y ∈ (Sx y : Set V), ∃ hz : z ∈ (Sx y : Set V),
              ((openGraph ω).induce (Sx y : Set V)).Reachable ⟨y, hy⟩ ⟨z, hz⟩} *
            (unitInterval.toNNReal (q s(z, w)) : ℝ≥0∞))) * M := by
            rw [Finset.sum_mul]
            simp_rw [ENNReal.tsum_mul_right]
        _ ≤ a * M := mul_le_mul' (hΦ y) le_rfl
    calc W y ≤ ∑' v, (law q {ω | ∃ hy : y ∈ (S' : Set V), ∃ hv : v ∈ (S' : Set V),
          ((openGraph ω).induce (S' : Set V)).Reachable ⟨y, hy⟩ ⟨v, hv⟩} +
        ∑ z ∈ S', ∑' w, if w ∈ S' then 0 else
          law q {ω | ∃ hy : y ∈ (S' : Set V), ∃ hz : z ∈ (S' : Set V),
            ((openGraph ω).induce (S' : Set V)).Reachable ⟨y, hy⟩ ⟨z, hz⟩} *
          (unitInterval.toNNReal (q s(z, w)) : ℝ≥0∞) *
          law q {ω | ∃ hw : w ∈ (Λ : Set V), ∃ hv : v ∈ (Λ : Set V),
            ((openGraph ω).induce (Λ : Set V)).Reachable ⟨w, hw⟩ ⟨v, hv⟩}) :=
          ENNReal.tsum_le_tsum hsplit
      _ ≤ B + a * M := by
          rw [ENNReal.tsum_add]
          exact add_le_add hint hbd
  -- Solve `M ≤ B + a M`.
  have hMle : M ≤ B + a * M := iSup_le hstep
  have h1a : (1 - a) ≠ 0 := (tsub_pos_of_lt ha).ne'
  have hfin : M * (1 - a) ≤ B := by
    rw [mul_comm, ENNReal.sub_mul fun _ _ => hMtop, one_mul]
    exact tsub_le_iff_left.mpr (by rw [add_comm]; exact hMle)
  have hMB : M ≤ B / (1 - a) :=
    (ENNReal.le_div_iff_mul_le (Or.inl h1a) (Or.inl (ENNReal.sub_ne_top ENNReal.one_ne_top))).mpr hfin
  exact (hWM x).trans hMB

/-! ## Uniform boundary contraction (YLZV) -/

/-- **Uniform boundary contraction (YLZV).** If every `x` has a finite `S_x ∋ x` with
`∑_{u ∈ S_x} τ_{S_x}(x,u) ≤ B` and `Φ_q(x,S_x) ≤ a < 1`, then `χ(x) ≤ B (1 - a)⁻¹`. -/
theorem chi_le_of_boundary_contraction [Countable V] (q : Sym2 V → unitInterval)
    (Sx : V → Finset V) (hSx : ∀ x, x ∈ Sx x) {B a : ℝ≥0∞} (ha : a < 1)
    (hB : ∀ x, ∑ u ∈ Sx x, law q {ω | ∃ hx : x ∈ (Sx x : Set V), ∃ hu : u ∈ (Sx x : Set V),
      ((openGraph ω).induce (Sx x : Set V)).Reachable ⟨x, hx⟩ ⟨u, hu⟩} ≤ B)
    (hΦ : ∀ x, ∑ u ∈ Sx x, ∑' v, (if v ∈ Sx x then 0 else
      law q {ω | ∃ hx : x ∈ (Sx x : Set V), ∃ hu : u ∈ (Sx x : Set V),
        ((openGraph ω).induce (Sx x : Set V)).Reachable ⟨x, hx⟩ ⟨u, hu⟩} *
      (unitInterval.toNNReal (q s(u, v)) : ℝ≥0∞)) ≤ a)
    (x : V) : chi q x ≤ B * (1 - a)⁻¹ := by
  obtain ⟨Λ, hΛ, hcov⟩ := exists_finset_exhaustion (V := V)
  have hmono : Monotone fun n => (Λ n : Set V) := fun m n h => Finset.coe_subset.mpr (hΛ h)
  rw [chi_eq_iSup_lintegral_induce q hmono hcov x, ← div_eq_mul_inv]
  refine iSup_le fun n => ?_
  rw [lintegral_encard_induce]
  exact tsum_law_induce_conn_le_of_boundary_contraction q Sx hSx ha hB hΦ (Λ n) x

/-- **Uniform boundary contraction, almost-sure finiteness.** Under the hypotheses of
`chi_le_of_boundary_contraction` with `B < ∞`, almost surely every cluster is finite. -/
theorem ae_cluster_finite_of_boundary_contraction [Countable V] (q : Sym2 V → unitInterval)
    (Sx : V → Finset V) (hSx : ∀ x, x ∈ Sx x) {B a : ℝ≥0∞} (hBtop : B < ∞) (ha : a < 1)
    (hB : ∀ x, ∑ u ∈ Sx x, law q {ω | ∃ hx : x ∈ (Sx x : Set V), ∃ hu : u ∈ (Sx x : Set V),
      ((openGraph ω).induce (Sx x : Set V)).Reachable ⟨x, hx⟩ ⟨u, hu⟩} ≤ B)
    (hΦ : ∀ x, ∑ u ∈ Sx x, ∑' v, (if v ∈ Sx x then 0 else
      law q {ω | ∃ hx : x ∈ (Sx x : Set V), ∃ hu : u ∈ (Sx x : Set V),
        ((openGraph ω).induce (Sx x : Set V)).Reachable ⟨x, hx⟩ ⟨u, hu⟩} *
      (unitInterval.toNNReal (q s(u, v)) : ℝ≥0∞)) ≤ a) :
    ∀ᵐ ω ∂law q, ∀ x, (cluster ω x).Finite := by
  rw [ae_all_iff]
  intro x
  have hchi : chi q x ≠ ∞ := by
    refine ne_top_of_le_ne_top ?_ (chi_le_of_boundary_contraction q Sx hSx ha hB hΦ x)
    exact ENNReal.mul_ne_top hBtop.ne (ENNReal.inv_ne_top.mpr (tsub_pos_of_lt ha).ne')
  have h0 := law_cluster_infinite_eq_zero_of_chi_ne_top q x hchi
  rw [ae_iff]
  simpa only [Set.not_infinite.symm, not_not] using h0

/-- **Uniform boundary contraction with bounded domains.** If `|S_x| ≤ N` for all `x`,
the bound holds with `B = N`. -/
theorem chi_le_of_boundary_contraction_card [Countable V] (q : Sym2 V → unitInterval)
    (Sx : V → Finset V) (hSx : ∀ x, x ∈ Sx x) {N : ℕ} (hN : ∀ x, (Sx x).card ≤ N)
    {a : ℝ≥0∞} (ha : a < 1)
    (hΦ : ∀ x, ∑ u ∈ Sx x, ∑' v, (if v ∈ Sx x then 0 else
      law q {ω | ∃ hx : x ∈ (Sx x : Set V), ∃ hu : u ∈ (Sx x : Set V),
        ((openGraph ω).induce (Sx x : Set V)).Reachable ⟨x, hx⟩ ⟨u, hu⟩} *
      (unitInterval.toNNReal (q s(u, v)) : ℝ≥0∞)) ≤ a)
    (x : V) : chi q x ≤ N * (1 - a)⁻¹ := by
  refine chi_le_of_boundary_contraction q Sx hSx ha (fun y => ?_) hΦ x
  calc _ ≤ ∑ _u ∈ Sx y, (1 : ℝ≥0∞) := Finset.sum_le_sum fun _ _ => prob_le_one
    _ = (Sx y).card := by simp
    _ ≤ N := by exact_mod_cast hN y

/-- Singleton domains: an off-diagonal row-sum bound `a < 1` gives `χ ≤ (1 - a)⁻¹`. -/
theorem chi_le_of_rowSum_le [Countable V] (q : Sym2 V → unitInterval) {a : ℝ≥0∞}
    (ha : a < 1)
    (hrow : ∀ x, (∑' v, if v = x then 0 else (unitInterval.toNNReal (q s(x, v)) : ℝ≥0∞)) ≤ a)
    (x : V) : chi q x ≤ (1 - a)⁻¹ := by
  have h := chi_le_of_boundary_contraction_card q (fun x => {x}) (fun x => by simp)
    (N := 1) (fun x => by simp) ha (fun y => ?_) x
  · simpa using h
  rw [Finset.sum_singleton]
  refine le_trans (ENNReal.tsum_le_tsum fun v => ?_) (hrow y)
  by_cases hv : v = y
  · simp [hv]
  · have hv' : v ∉ ({y} : Finset V) := by simpa using hv
    simp only [hv', hv, ↓reduceIte]
    exact mul_le_of_le_one_left zero_le prob_le_one

-- Non-vacuity: an explicit profile on `Bool` with off-diagonal value `1/2`, where the
-- singleton domains give `B = 1` and `a = 1/2`.
example (x : Bool) :
    chi (fun _ : Sym2 Bool => (⟨1/2, by norm_num, by norm_num⟩ : unitInterval)) x ≤
      (1 - 2⁻¹)⁻¹ := by
  have hq : unitInterval.toNNReal (⟨1/2, by norm_num, by norm_num⟩ : unitInterval) = 2⁻¹ :=
    NNReal.eq (by norm_num [unitInterval.toNNReal]; rfl)
  refine chi_le_of_rowSum_le _ (ENNReal.inv_lt_one.mpr ENNReal.one_lt_two) (fun y => ?_) x
  rw [tsum_fintype, hq, ENNReal.coe_inv two_ne_zero, ENNReal.coe_ofNat]
  cases y <;> simp

-- Non-vacuity at `a = 0`: the zero profile.
example [Countable V] (x : V) : chi (fun _ : Sym2 V => 0) x ≤ 1 := by
  have h0 : unitInterval.toNNReal 0 = 0 := NNReal.eq (by simp [unitInterval.toNNReal]; rfl)
  have h := chi_le_of_rowSum_le (V := V) (fun _ => 0) (a := 0) (by norm_num)
    (fun y => by simp [h0]) x
  simpa using h

end PercLib.Percolation.Bond
