/-
The shallow/deep three-group certificate regrouping for the `p = 4`, `k = 2` fourth-moment
tree-graph bound.  Ultramath `smwpq441z` member m3 (Direction C).

A `CombSlots` realization with arms `p0..p4` and spine pieces `s1 : u → v`, `s2 : v → w` is
regrouped around the *single* common centre `v`:

* `walkEdges (p0 ++ s1) ∪ walkEdges (p1 ++ s1)` certifies `conn b0 v ∩ conn b1 v`;
* `walkEdges p2` certifies `conn b2 v`;
* `walkEdges (p3 ++ s2.reverse) ∪ walkEdges (p4 ++ s2.reverse)` certifies
  `conn b3 v ∩ conn b4 v`.

The spine pieces `s1`, `s2` are each shared only inside their own group, and the three
groups consume `3 + 1 + 3 = 7` original walks, so the groups are pairwise edge-disjoint.
Both branch vertices `u` and `w` then vanish from the probability expression, so their
unions cost nothing.  Threefold BK leaves `J(b0,b1,v) * tau(b2,v) * J(b3,b4,v)`.
-/
module

public import PercLib.CriticalLRP.Correlation.FourthMoment.MixedK2.Slot

open Set MeasureTheory
open scoped ENNReal BigOperators
open PercLib.Percolation.Bond
open PercLib.Probability

@[expose] public section

namespace PercLib.CriticalLRP.TreeExpansion.FivePoint

variable {V : Type*}

/-! ### Reversing a walk does not change its edge set -/

theorem walkEdges_reverse [Countable V] {ω : Config V} {a b : V}
    (p : (openGraph ω).Walk a b) : walkEdges p.reverse = walkEdges p := by
  ext e
  simp [walkEdges, SimpleGraph.Walk.edges_reverse]


/-! ### List disjointness bookkeeping -/

theorem listDisjoint_append_left {α : Type*} {a b c : List α}
    (ha : a.Disjoint c) (hb : b.Disjoint c) : (a ++ b).Disjoint c := by
  rw [List.disjoint_left] at *
  intro x hx hy
  rw [List.mem_append] at hx
  exact hx.elim (fun h => ha h hy) (fun h => hb h hy)

theorem listDisjoint_append_right {α : Type*} {a b c : List α}
    (ha : a.Disjoint b) (hb : a.Disjoint c) : a.Disjoint (b ++ c) := by
  rw [List.disjoint_left] at *
  intro x hx hy
  rw [List.mem_append] at hy
  exact hy.elim (fun h => ha hx h) (fun h => hb hx h)

theorem listDisjoint_reverse_right {α : Type*} {a b : List α} (h : a.Disjoint b) :
    a.Disjoint b.reverse := by
  rw [List.disjoint_left] at *
  intro x hx hy
  exact h hx (List.mem_reverse.mp hy)

/-! ### Threefold BK with three pairwise disjoint finite certificates -/

/-- A `ThreeCertEvent` is a nested disjoint occurrence of three increasing events. -/
theorem threeCertEvent_subset [Countable V] {A₀ A₁ A₂ : Set (Config V)}
    (h₀ : IsUpperSet A₀) (h₁ : IsUpperSet A₁) (h₂ : IsUpperSet A₂) :
    ThreeCertEvent A₀ A₁ A₂ ⊆ disjointOccurrence (disjointOccurrence A₀ A₁) A₂ := by
  rintro ω ⟨W₀, W₁, W₂, hf0, hf1, hf2, hs0, hs1, hs2, hm0, hm1, hm2, hd01, hd02, hd12⟩
  exact (mem_disjointOccurrence_three_iff h₀ h₁ h₂ ω).mpr
    ⟨W₀, W₁, W₂, hf0, hf1, hf2, hd01, hd02, hd12, hs0, hs1, hs2, hm0, hm1, hm2⟩

/-- **Threefold BK at the native countable law.** -/
theorem threeCert_le [Countable V] (π : Sym2 V → unitInterval) {A₀ A₁ A₂ : Set (Config V)}
    (h₀ : IsUpperSet A₀) (h₁ : IsUpperSet A₁) (h₂ : IsUpperSet A₂) :
    law π (ThreeCertEvent A₀ A₁ A₂) ≤ law π A₀ * (law π A₁ * law π A₂) := by
  refine (measure_mono (threeCertEvent_subset h₀ h₁ h₂)).trans ?_
  have hbk := countable_profile_bk_foldl (p := π) [A₁, A₂] ?_ (A := A₀) h₀
  · simpa [law, List.foldl] using hbk
  · intro B hB
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hB
    rcases hB with rfl | rfl
    exacts [h₁, h₂]

/-! ### The three-group regrouping of `CombSlots` -/

/-- Two appends are edge-disjoint when each factor is. -/
theorem disjoint_append_append [Countable V] {ω : Config V} {a b c d e f : V}
    (p : (openGraph ω).Walk a b) (q : (openGraph ω).Walk b c)
    (r : (openGraph ω).Walk d e) (s : (openGraph ω).Walk e f)
    (h1 : p.edges.Disjoint r.edges) (h2 : p.edges.Disjoint s.edges)
    (h3 : q.edges.Disjoint r.edges) (h4 : q.edges.Disjoint s.edges) :
    Disjoint (walkEdges (p.append q)) (walkEdges (r.append s)) := by
  rw [walkEdges_append, walkEdges_append]
  exact disjoint_union_left.mpr
    ⟨disjoint_union_right.mpr ⟨disjoint_walkEdges p r h1, disjoint_walkEdges p s h2⟩,
     disjoint_union_right.mpr ⟨disjoint_walkEdges q r h3, disjoint_walkEdges q s h4⟩⟩

/-- **The three-group certificate bound.**  The common centre is the middle vertex `v`; the
two branch vertices `u`, `w` occur in no event. -/
theorem combSlots_subset_threeCert [Countable V] (b0 b1 b2 b3 b4 u v w : V) :
    {ω | CombSlots (openGraph ω) b0 b1 b2 b3 b4 u v w} ⊆
      ThreeCertEvent (V := V) (conn b0 v ∩ conn b1 v) (conn b2 v)
        (conn b3 v ∩ conn b4 v) := by
  rintro ω ⟨p0, p1, p2, p3, p4, s1, s2, hnd⟩
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, d01, d02, d03, d04, d05, d06, d12, d13, d14, d15,
    d16, d23, d24, d25, d26, d34, d35, d36, d45, d46, d56⟩ := nodup_append7_facts hnd
  have e2 : (s2.reverse).edges = s2.edges.reverse := SimpleGraph.Walk.edges_reverse s2
  -- single walks against the reversed spine
  have hp0s2 : p0.edges.Disjoint (s2.reverse).edges := by
    rw [e2]; exact listDisjoint_reverse_right d06
  have hp1s2 : p1.edges.Disjoint (s2.reverse).edges := by
    rw [e2]; exact listDisjoint_reverse_right d16
  have hp2s2 : p2.edges.Disjoint (s2.reverse).edges := by
    rw [e2]; exact listDisjoint_reverse_right d26
  have hs1s2 : s1.edges.Disjoint (s2.reverse).edges := by
    rw [e2]; exact listDisjoint_reverse_right d56
  have h03 : (p0.edges ++ s1.edges).Disjoint p3.edges :=
    listDisjoint_append_left d03 d35.symm
  have h04 : (p0.edges ++ s1.edges).Disjoint p4.edges :=
    listDisjoint_append_left d04 d45.symm
  have h13 : (p1.edges ++ s1.edges).Disjoint p3.edges :=
    listDisjoint_append_left d13 d35.symm
  have h14 : (p1.edges ++ s1.edges).Disjoint p4.edges :=
    listDisjoint_append_left d14 d45.symm
  refine ⟨walkEdges (p0.append s1) ∪ walkEdges (p1.append s1), walkEdges p2,
    walkEdges (p3.append s2.reverse) ∪ walkEdges (p4.append s2.reverse), ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (walkEdges_finite (p0.append s1)).union (walkEdges_finite (p1.append s1))
  · exact walkEdges_finite p2
  · exact (walkEdges_finite (p3.append s2.reverse)).union
      (walkEdges_finite (p4.append s2.reverse))
  · exact union_subset (walkEdges_subset (p0.append s1)) (walkEdges_subset (p1.append s1))
  · exact walkEdges_subset p2
  · exact union_subset (walkEdges_subset (p3.append s2.reverse))
      (walkEdges_subset (p4.append s2.reverse))
  · exact ⟨conn_mono subset_union_left (mem_conn_walkEdges (p0.append s1)),
      conn_mono subset_union_right (mem_conn_walkEdges (p1.append s1))⟩
  · exact mem_conn_walkEdges p2
  · exact ⟨conn_mono subset_union_left (mem_conn_walkEdges (p3.append s2.reverse)),
      conn_mono subset_union_right (mem_conn_walkEdges (p4.append s2.reverse))⟩
  · exact disjoint_union_left.mpr
      ⟨disjoint_walkEdges_append_left p0 s1 p2 d02 d25.symm,
       disjoint_walkEdges_append_left p1 s1 p2 d12 d25.symm⟩
  · exact disjoint_union_left.mpr
      ⟨disjoint_union_right.mpr
          ⟨disjoint_append_append p0 s1 p3 s2.reverse d03 hp0s2 d35.symm hs1s2,
           disjoint_append_append p0 s1 p4 s2.reverse d04 hp0s2 d45.symm hs1s2⟩,
       disjoint_union_right.mpr
          ⟨disjoint_append_append p1 s1 p3 s2.reverse d13 hp1s2 d35.symm hs1s2,
           disjoint_append_append p1 s1 p4 s2.reverse d14 hp1s2 d45.symm hs1s2⟩⟩
  · refine disjoint_union_right.mpr ⟨?_, ?_⟩
    · rw [walkEdges_append]
      exact disjoint_union_right.mpr ⟨disjoint_walkEdges p2 p3 d23,
        disjoint_walkEdges p2 s2.reverse hp2s2⟩
    · rw [walkEdges_append]
      exact disjoint_union_right.mpr ⟨disjoint_walkEdges p2 p4 d24,
        disjoint_walkEdges p2 s2.reverse hp2s2⟩

end PercLib.CriticalLRP.TreeExpansion.FivePoint
