/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Proof of the `p = 4`, `k = 1` case of Hutchcroft Lemma I.4.16. The two
five-group BK regroupings retain one joint two-arm event; their sums recover
exactly the native second cluster moment times the fourth power of the first.
Supplied by Ultramath `smwpmcy6r` member m1 and reviewed before integration.
-/
module

public import PercLib.CriticalLRP.Correlation.FourthMoment.Mixed.Defs

open Set MeasureTheory
open scoped ENNReal BigOperators
open PercLib.Percolation.Bond
open PercLib.Probability

@[expose] public section

namespace PercLib.CriticalLRP.TreeExpansion.FivePoint

variable {V : Type*}

/-- **Fivefold BK for one joint event and four singleton events.**  The joint event
`A₀` is not split: its certificate is a single finite open set. -/
theorem fiveGroup_le [Countable V] (π : Sym2 V → unitInterval)
    {A₀ A₁ A₂ A₃ A₄ : Set (Config V)} (h₀ : IsUpperSet A₀) (h₁ : IsUpperSet A₁)
    (h₂ : IsUpperSet A₂) (h₃ : IsUpperSet A₃) (h₄ : IsUpperSet A₄) :
    law π (FiveGroupEvent A₀ A₁ A₂ A₃ A₄) ≤
      law π A₀ * (law π A₁ * (law π A₂ * (law π A₃ * law π A₄))) :=
  prodBernoulli_five_wit_le π h₀ h₁ h₂ h₃ h₄

/-- A walk whose two halves are edge-disjoint from `r` has edge set disjoint from `r`. -/
theorem disjoint_walkEdges_append_left [Countable V] {ω : Config V} {a b c d e : V}
    (p : (openGraph ω).Walk a b) (q : (openGraph ω).Walk b c) (r : (openGraph ω).Walk d e)
    (hp : p.edges.Disjoint r.edges) (hq : q.edges.Disjoint r.edges) :
    Disjoint (walkEdges (p.append q)) (walkEdges r) := by
  rw [walkEdges_append]
  exact disjoint_union_left.mpr ⟨disjoint_walkEdges p r hp, disjoint_walkEdges q r hq⟩

/-- **Root at `u`: certificates.**  The joint pair at `v` is certified by the two
concatenations through `u`; the branch vertex `u` occurs in no event. -/
theorem combSlots_subset_rootU [Countable V] (b0 b1 b2 b3 b4 u v w : V) :
    {ω | CombSlots (openGraph ω) b0 b1 b2 b3 b4 u v w} ⊆
      FiveGroupEvent (V := V) (conn b0 v ∩ conn b1 v) (conn b2 v) (conn v w)
        (conn b3 w) (conn b4 w) := by
  rintro ω ⟨p0, p1, p2, p3, p4, s1, s2, hnd⟩
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, d01, d02, d03, d04, d05, d06, d12, d13, d14, d15,
    d16, d23, d24, d25, d26, d34, d35, d36, d45, d46, d56⟩ := nodup_append7_facts hnd
  have hfs1 : s1.edges.Disjoint p2.edges := d25.symm
  have hfs2 : s1.edges.Disjoint p3.edges := d35.symm
  have hfs3 : s1.edges.Disjoint p4.edges := d45.symm
  have dW0W1 : Disjoint (walkEdges (p0.append s1) ∪ walkEdges (p1.append s1))
      (walkEdges p2) :=
    disjoint_union_left.mpr
      ⟨disjoint_walkEdges_append_left p0 s1 p2 d02 hfs1,
        disjoint_walkEdges_append_left p1 s1 p2 d12 hfs1⟩
  have dW0W2 : Disjoint (walkEdges (p0.append s1) ∪ walkEdges (p1.append s1))
      (walkEdges s2) :=
    disjoint_union_left.mpr
      ⟨disjoint_walkEdges_append_left p0 s1 s2 d06 d56,
        disjoint_walkEdges_append_left p1 s1 s2 d16 d56⟩
  have dW0W3 : Disjoint (walkEdges (p0.append s1) ∪ walkEdges (p1.append s1))
      (walkEdges p3) :=
    disjoint_union_left.mpr
      ⟨disjoint_walkEdges_append_left p0 s1 p3 d03 hfs2,
        disjoint_walkEdges_append_left p1 s1 p3 d13 hfs2⟩
  have dW0W4 : Disjoint (walkEdges (p0.append s1) ∪ walkEdges (p1.append s1))
      (walkEdges p4) :=
    disjoint_union_left.mpr
      ⟨disjoint_walkEdges_append_left p0 s1 p4 d04 hfs3,
        disjoint_walkEdges_append_left p1 s1 p4 d14 hfs3⟩
  exact ⟨walkEdges (p0.append s1) ∪ walkEdges (p1.append s1), walkEdges p2, walkEdges s2,
    walkEdges p3, walkEdges p4,
    (walkEdges_finite (p0.append s1)).union (walkEdges_finite (p1.append s1)),
    walkEdges_finite p2, walkEdges_finite s2, walkEdges_finite p3, walkEdges_finite p4,
    union_subset (walkEdges_subset (p0.append s1)) (walkEdges_subset (p1.append s1)),
    walkEdges_subset p2, walkEdges_subset s2, walkEdges_subset p3, walkEdges_subset p4,
    ⟨conn_mono subset_union_left (mem_conn_walkEdges (p0.append s1)),
      conn_mono subset_union_right (mem_conn_walkEdges (p1.append s1))⟩,
    mem_conn_walkEdges p2, mem_conn_walkEdges s2, mem_conn_walkEdges p3,
    mem_conn_walkEdges p4,
    dW0W1, dW0W2, dW0W3, dW0W4,
    disjoint_walkEdges p2 s2 d26, disjoint_walkEdges p2 p3 d23,
    disjoint_walkEdges p2 p4 d24, disjoint_walkEdges s2 p3 d36.symm,
    disjoint_walkEdges s2 p4 d46.symm, disjoint_walkEdges p3 p4 d34⟩

/-- **Root at `v`: certificates.**  The joint pair at `w` is certified by the two arms
`root → v → w` (`p₂ ++ s₂`) and `u → v → w` (`s₁ ++ s₂`), which share the spine `s₂`;
the middle vertex `v` occurs in no event and is union-bounded.  The four singleton groups
are the shallow arms `b₀ — u`, `b₁ — u` and the two deep arms `b₃ — w`, `b₄ — w`. -/
theorem combSlots_subset_rootV [Countable V] (b0 b1 b2 b3 b4 u v w : V) :
    {ω | CombSlots (openGraph ω) b0 b1 b2 b3 b4 u v w} ⊆
      FiveGroupEvent (V := V) (conn b2 w ∩ conn u w) (conn b0 u) (conn b1 u)
        (conn b3 w) (conn b4 w) := by
  rintro ω ⟨p0, p1, p2, p3, p4, s1, s2, hnd⟩
  obtain ⟨n0, n1, n2, n3, n4, n5, n6, d01, d02, d03, d04, d05, d06, d12, d13, d14, d15,
    d16, d23, d24, d25, d26, d34, d35, d36, d45, d46, d56⟩ := nodup_append7_facts hnd
  have h1' : p2.edges.Disjoint p0.edges := d02.symm
  have h2' : s2.edges.Disjoint p0.edges := d06.symm
  have h3' : p2.edges.Disjoint p1.edges := d12.symm
  have h4' : s2.edges.Disjoint p1.edges := d16.symm
  have h5' : s2.edges.Disjoint p3.edges := d36.symm
  have h6' : s2.edges.Disjoint p4.edges := d46.symm
  have dW0W1 : Disjoint (walkEdges (p2.append s2) ∪ walkEdges (s1.append s2))
      (walkEdges p0) :=
    disjoint_union_left.mpr
      ⟨disjoint_walkEdges_append_left p2 s2 p0 h1' h2',
        disjoint_walkEdges_append_left s1 s2 p0 d05.symm h2'⟩
  have dW0W2 : Disjoint (walkEdges (p2.append s2) ∪ walkEdges (s1.append s2))
      (walkEdges p1) :=
    disjoint_union_left.mpr
      ⟨disjoint_walkEdges_append_left p2 s2 p1 h3' h4',
        disjoint_walkEdges_append_left s1 s2 p1 d15.symm h4'⟩
  have dW0W3 : Disjoint (walkEdges (p2.append s2) ∪ walkEdges (s1.append s2))
      (walkEdges p3) :=
    disjoint_union_left.mpr
      ⟨disjoint_walkEdges_append_left p2 s2 p3 d23 h5',
        disjoint_walkEdges_append_left s1 s2 p3 d35.symm h5'⟩
  have dW0W4 : Disjoint (walkEdges (p2.append s2) ∪ walkEdges (s1.append s2))
      (walkEdges p4) :=
    disjoint_union_left.mpr
      ⟨disjoint_walkEdges_append_left p2 s2 p4 d24 h6',
        disjoint_walkEdges_append_left s1 s2 p4 d45.symm h6'⟩
  exact ⟨walkEdges (p2.append s2) ∪ walkEdges (s1.append s2), walkEdges p0, walkEdges p1,
    walkEdges p3, walkEdges p4,
    (walkEdges_finite (p2.append s2)).union (walkEdges_finite (s1.append s2)),
    walkEdges_finite p0, walkEdges_finite p1, walkEdges_finite p3, walkEdges_finite p4,
    union_subset (walkEdges_subset (p2.append s2)) (walkEdges_subset (s1.append s2)),
    walkEdges_subset p0, walkEdges_subset p1, walkEdges_subset p3, walkEdges_subset p4,
    ⟨conn_mono subset_union_left (mem_conn_walkEdges (p2.append s2)),
      conn_mono subset_union_right (mem_conn_walkEdges (s1.append s2))⟩,
    mem_conn_walkEdges p0, mem_conn_walkEdges p1, mem_conn_walkEdges p3,
    mem_conn_walkEdges p4,
    dW0W1, dW0W2, dW0W3, dW0W4,
    disjoint_walkEdges p0 p1 d01, disjoint_walkEdges p0 p3 d03,
    disjoint_walkEdges p0 p4 d04, disjoint_walkEdges p1 p3 d13,
    disjoint_walkEdges p1 p4 d14, disjoint_walkEdges p3 p4 d34⟩

/-- **Root at `u`: the slot-event bound.**  The branch vertex `u` is union-bounded, so the
right-hand side is `u`-free; `v` stays summed. -/
theorem combSlots_event_rootU [Countable V] (π : Sym2 V → unitInterval)
    (b0 b1 b2 b3 b4 u v w : V) :
    law π {ω | CombSlots (openGraph ω) b0 b1 b2 b3 b4 u v w} ≤
      law π (conn b0 v ∩ conn b1 v) *
        (tau π b2 v * (tau π v w * (tau π b3 w * tau π b4 w))) := by
  refine (measure_mono (combSlots_subset_rootU b0 b1 b2 b3 b4 u v w)).trans ?_
  have hbk := fiveGroup_le (V := V) π (A₁ := conn b2 v) (A₂ := conn v w) (A₃ := conn b3 w)
    (A₄ := conn b4 w) (isUpperSet_inter_conn b0 b1 v)
    (isIncreasing_connects b2 v) (isIncreasing_connects v w)
    (isIncreasing_connects b3 w) (isIncreasing_connects b4 w)
  simpa [tau] using hbk

/-- **Root at `v`: the slot-event bound.**  The middle vertex `v` is union-bounded, so the
right-hand side is `v`-free; `u` and `w` stay summed. -/
theorem combSlots_event_rootV [Countable V] (π : Sym2 V → unitInterval)
    (b0 b1 b2 b3 b4 u v w : V) :
    law π {ω | CombSlots (openGraph ω) b0 b1 b2 b3 b4 u v w} ≤
      law π (conn b2 w ∩ conn u w) *
        (tau π b0 u * (tau π b1 u * (tau π b3 w * tau π b4 w))) := by
  refine (measure_mono (combSlots_subset_rootV b0 b1 b2 b3 b4 u v w)).trans ?_
  have hbk := fiveGroup_le (V := V) π (A₁ := conn b0 u) (A₂ := conn b1 u) (A₃ := conn b3 w)
    (A₄ := conn b4 w) (isUpperSet_inter_conn b2 u w)
    (isIncreasing_connects b0 u) (isIncreasing_connects b1 u)
    (isIncreasing_connects b3 w) (isIncreasing_connects b4 w)
  simpa [tau] using hbk

/-! ## Lifting the two root cases to the fifteen labelled slot patterns -/

/-- Root-at-`u` slot bound, in slot form: the root sits in slot `0`. -/
theorem slotEvent_le_rootU [Countable V] (π : Sym2 V → unitInterval) (k : Fin 15)
    (hk : pat k 0 = 0) (u v w : V) (T : Fin 5 → V) :
    law π {ω | CombShape (openGraph ω) k u v w T} ≤
      law π (conn (T 0) v ∩ conn (T (pat k 1)) v) *
        (tau π (T (pat k 2)) v * (tau π v w * (tau π (T (pat k 3)) w *
          tau π (T (pat k 4)) w))) := by
  have h := combSlots_event_rootU (V := V) π (T (pat k 0)) (T (pat k 1)) (T (pat k 2))
    (T (pat k 3)) (T (pat k 4)) u v w
  simpa only [CombShape, hk] using h

/-- Root-at-`v` slot bound, in slot form: the root sits in slot `2`. -/
theorem slotEvent_le_rootV [Countable V] (π : Sym2 V → unitInterval) (k : Fin 15)
    (hk : pat k 2 = 0) (u v w : V) (T : Fin 5 → V) :
    law π {ω | CombShape (openGraph ω) k u v w T} ≤
      law π (conn (T 0) w ∩ conn u w) *
        (tau π (T (pat k 0)) u * (tau π (T (pat k 1)) u * (tau π (T (pat k 3)) w *
          tau π (T (pat k 4)) w))) := by
  have h := combSlots_event_rootV (V := V) π (T (pat k 0)) (T (pat k 1)) (T (pat k 2))
    (T (pat k 3)) (T (pat k 4)) u v w
  simpa only [CombShape, hk] using h

/-- **Per-shape bound, all fifteen patterns.**  The union over both branch vertices `u, v`
is bounded; `root_slot_cases` decides which of the two regroupings applies. -/
theorem slotEvent_le [Countable V] (π : Sym2 V → unitInterval) (k : Fin 15) (w : V)
    (T : Fin 5 → V) :
    law π (⋃ u : V, ⋃ v : V, {ω | CombShape (openGraph ω) k u v w T}) ≤
      slotDiagram π k w T := by
  simp only [slotDiagram]
  split
  · next h =>
      rw [Set.iUnion_comm]
      refine (measure_iUnion_le (μ := law π) (s := fun v : V =>
        ⋃ u : V, {ω | CombShape (openGraph ω) k u v w T})).trans ?_
      refine ENNReal.tsum_le_tsum fun v => ?_
      refine (measure_mono ?_).trans
        (fiveGroup_le (V := V) π (A₁ := conn (T (pat k 2)) v) (A₂ := conn v w)
          (A₃ := conn (T (pat k 3)) w) (A₄ := conn (T (pat k 4)) w)
          (isUpperSet_inter_conn (T 0) (T (pat k 1)) v)
          (isIncreasing_connects (T (pat k 2)) v) (isIncreasing_connects v w)
          (isIncreasing_connects (T (pat k 3)) w) (isIncreasing_connects (T (pat k 4)) w))
      intro ω hω
      obtain ⟨u, hu⟩ := Set.mem_iUnion.mp hω
      exact combSlots_subset_rootU (T 0) (T (pat k 1)) (T (pat k 2)) (T (pat k 3))
        (T (pat k 4)) u v w (by simpa only [CombShape, h] using hu)
  · next h =>
      have h' : pat k 2 = 0 := (root_slot_cases k).resolve_left h
      refine (measure_iUnion_le (μ := law π) (s := fun u : V =>
        ⋃ v : V, {ω | CombShape (openGraph ω) k u v w T})).trans ?_
      refine ENNReal.tsum_le_tsum fun u => ?_
      refine (measure_mono ?_).trans
        (fiveGroup_le (V := V) π (A₁ := conn (T (pat k 0)) u) (A₂ := conn (T (pat k 1)) u)
          (A₃ := conn (T (pat k 3)) w) (A₄ := conn (T (pat k 4)) w)
          (isUpperSet_inter_conn (T 0) u w)
          (isIncreasing_connects (T (pat k 0)) u) (isIncreasing_connects (T (pat k 1)) u)
          (isIncreasing_connects (T (pat k 3)) w) (isIncreasing_connects (T (pat k 4)) w))
      intro ω hω
      obtain ⟨v, hv⟩ := Set.mem_iUnion.mp hω
      exact combSlots_subset_rootV (T (pat k 0)) (T (pat k 1)) (T 0) (T (pat k 3))
        (T (pat k 4)) u v w (by simpa only [CombShape, h'] using hv)

/-- **Coverage.**  Whenever `o, x₁, …, x₄` lie in one open cluster, one of the fifteen labelled
slot patterns is realised with some branch vertices. -/
theorem fourPoint_subset_slotEvents [Countable V] (o x1 x2 x3 x4 : V) :
    (conn o x1 ∩ conn o x2 ∩ conn o x3 ∩ conn o x4) ⊆
      ⋃ k : Fin 15, ⋃ w, ⋃ u, ⋃ v,
        {ω | CombShape (openGraph ω) k u v w ![o, x1, x2, x3, x4]} := by
  rintro ω ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
  obtain ⟨k, u, v, w, hk⟩ := exists_combShape_connects ω o x1 x2 x3 x4 h1 h2 h3 h4
  exact Set.mem_iUnion.mpr ⟨k, Set.mem_iUnion.mpr ⟨w, Set.mem_iUnion.mpr ⟨u,
    Set.mem_iUnion.mpr ⟨v, hk⟩⟩⟩⟩

/-- **The pointwise event reduction.**  The four-point connection event is bounded by the sum
over the fifteen slot patterns and the remaining branch vertices of the slot diagrams. -/
theorem fourPoint_le_slotSum [Countable V] (π : Sym2 V → unitInterval) (o x1 x2 x3 x4 : V) :
    law π (conn o x1 ∩ conn o x2 ∩ conn o x3 ∩ conn o x4) ≤
      ∑' k : Fin 15, ∑' w, slotDiagram π k w ![o, x1, x2, x3, x4] := by
  refine (measure_mono (fourPoint_subset_slotEvents o x1 x2 x3 x4)).trans ?_
  refine (measure_iUnion_le (μ := law π) (s := fun k : Fin 15 =>
    ⋃ w, ⋃ u, ⋃ v, {ω | CombShape (openGraph ω) k u v w ![o, x1, x2, x3, x4]})).trans ?_
  refine ENNReal.tsum_le_tsum fun k => ?_
  refine (measure_iUnion_le (μ := law π) (s := fun w : V =>
    ⋃ u, ⋃ v, {ω | CombShape (openGraph ω) k u v w ![o, x1, x2, x3, x4]})).trans ?_
  exact ENNReal.tsum_le_tsum fun w => slotEvent_le π k w _

#print axioms PercLib.CriticalLRP.TreeExpansion.FivePoint.fiveGroup_le
#print axioms PercLib.CriticalLRP.TreeExpansion.FivePoint.combSlots_event_rootU
#print axioms PercLib.CriticalLRP.TreeExpansion.FivePoint.combSlots_event_rootV
#print axioms PercLib.CriticalLRP.TreeExpansion.FivePoint.slotEvent_le
#print axioms PercLib.CriticalLRP.TreeExpansion.FivePoint.fourPoint_le_slotSum

/-! ## Exact summation of the slot diagrams -/

set_option linter.unusedSectionVars false

section Summation

variable [Countable V] [AddCommGroup V]

/-- Four nested sums over `V` as one sum over `Fin 4 → V`. -/
theorem tsum_fin4 (G : (Fin 4 → V) → ℝ≥0∞) :
    (∑' X : Fin 4 → V, G X) = ∑' x0, ∑' x1, ∑' x2, ∑' x3, G ![x0, x1, x2, x3] := by
  rw [← Equiv.tsum_eq fin4Prod.symm G]
  simp only [ENNReal.tsum_prod']
  rfl

/-- A four-fold sum is invariant under permuting the four index positions. -/
theorem tsum_fin4_perm (σ : Equiv.Perm (Fin 4)) (G : (Fin 4 → V) → ℝ≥0∞) :
    (∑' X : Fin 4 → V, G (fun i => X (σ i))) = ∑' X : Fin 4 → V, G X :=
  Equiv.tsum_eq (Equiv.arrowCongr σ.symm (Equiv.refl V)) G

/-- The nested form of `tsum_fin4_perm`. -/
theorem tsum_four_perm (σ : Equiv.Perm (Fin 4)) (H : V → V → V → V → ℝ≥0∞) :
    (∑' x0, ∑' x1, ∑' x2, ∑' x3,
        H (![x0, x1, x2, x3] (σ 0)) (![x0, x1, x2, x3] (σ 1))
          (![x0, x1, x2, x3] (σ 2)) (![x0, x1, x2, x3] (σ 3)))
      = ∑' x0, ∑' x1, ∑' x2, ∑' x3, H x0 x1 x2 x3 := by
  rw [← tsum_fin4 (G := fun X => H (X (σ 0)) (X (σ 1)) (X (σ 2)) (X (σ 3)))]
  rw [tsum_fin4_perm σ (G := fun X => H (X 0) (X 1) (X 2) (X 3))]
  rw [tsum_fin4 (G := fun X => H (X 0) (X 1) (X 2) (X 3))]
  rfl

/-- Pull a constant out of a twofold sum. -/
theorem tsum_two_const_mul (a : ℝ≥0∞) (R : V → V → ℝ≥0∞) :
    (∑' x2, ∑' x3, a * R x2 x3) = a * ∑' x2, ∑' x3, R x2 x3 := by
  rw [show (∑' x2, ∑' x3, a * R x2 x3) = ∑' x2, a * (∑' x3, R x2 x3) from
    tsum_congr fun x2 => ENNReal.tsum_mul_left]
  exact ENNReal.tsum_mul_left

/-- Pull a constant out of a twofold sum (product form). -/
theorem tsum_two_mul_const (F : V → V → ℝ≥0∞) (Y : ℝ≥0∞) :
    (∑' x0, ∑' x1, F x0 x1 * Y) = (∑' x0, ∑' x1, F x0 x1) * Y := by
  rw [show (∑' x0, ∑' x1, F x0 x1 * Y) = ∑' x0, (∑' x1, F x0 x1) * Y from
    tsum_congr fun x0 => ENNReal.tsum_mul_right]
  exact ENNReal.tsum_mul_right

/-- A product of four one-variable sums, with a constant factor. -/
theorem tsum_four_mul_const (f g h k : V → ℝ≥0∞) (C : ℝ≥0∞) :
    (∑' x0, ∑' x1, ∑' x2, ∑' x3, f x0 * (g x1 * (h x2 * (k x3 * C))))
      = (∑' x, f x) * ((∑' x, g x) * ((∑' x, h x) * ((∑' x, k x) * C))) := by
  have hk : (∑' x3, k x3 * C) = (∑' x, k x) * C := ENNReal.tsum_mul_right
  have hY : (∑' x2, ∑' x3, h x2 * (k x3 * C))
      = (∑' x, h x) * ((∑' x, k x) * C) := by
    rw [show (∑' x2, ∑' x3, h x2 * (k x3 * C))
        = ∑' x2, h x2 * (∑' x3, k x3 * C) from
      tsum_congr fun x2 => ENNReal.tsum_mul_left]
    rw [ENNReal.tsum_mul_right, hk]
  have hAB : (∑' x0, ∑' x1, ∑' x2, ∑' x3, f x0 * (g x1 * (h x2 * (k x3 * C))))
      = ∑' x0, ∑' x1, (f x0 * g x1) * (∑' x2, ∑' x3, h x2 * (k x3 * C)) := by
    refine tsum_congr fun x0 => tsum_congr fun x1 => ?_
    rw [show (∑' x2, ∑' x3, f x0 * (g x1 * (h x2 * (k x3 * C))))
        = ∑' x2, ∑' x3, (f x0 * g x1) * (h x2 * (k x3 * C)) from
      tsum_congr fun x2 => tsum_congr fun x3 => by ring]
    exact tsum_two_const_mul (f x0 * g x1) (fun x2 x3 => h x2 * (k x3 * C))
  rw [hAB, hY]
  rw [tsum_two_mul_const (F := fun x0 x1 => f x0 * g x1)
    (Y := (∑' x, h x) * ((∑' x, k x) * C))]
  rw [PercLib.CriticalLRP.TreeExpansion.tsum_two_mul (f := f) (g := g)]
  ring

/-- Move the last index of a six-fold sum to the front. -/
theorem tsum_move_last_six (F : V → V → V → V → V → V → ℝ≥0∞) :
    (∑' a, ∑' b, ∑' c, ∑' d, ∑' x, ∑' y, F a b c d x y)
      = ∑' y, ∑' a, ∑' b, ∑' c, ∑' d, ∑' x, F a b c d x y := by
  calc (∑' a, ∑' b, ∑' c, ∑' d, ∑' x, ∑' y, F a b c d x y)
      = ∑' a, ∑' b, ∑' c, ∑' d, ∑' y, ∑' x, F a b c d x y :=
        tsum_congr fun a => tsum_congr fun b => tsum_congr fun c => tsum_congr fun d =>
          ENNReal.tsum_comm
    _ = ∑' a, ∑' b, ∑' c, ∑' y, ∑' d, ∑' x, F a b c d x y :=
        tsum_congr fun a => tsum_congr fun b => tsum_congr fun c => ENNReal.tsum_comm
    _ = ∑' a, ∑' b, ∑' y, ∑' c, ∑' d, ∑' x, F a b c d x y :=
        tsum_congr fun a => tsum_congr fun b => ENNReal.tsum_comm
    _ = ∑' a, ∑' y, ∑' b, ∑' c, ∑' d, ∑' x, F a b c d x y :=
        tsum_congr fun a => ENNReal.tsum_comm
    _ = ∑' y, ∑' a, ∑' b, ∑' c, ∑' d, ∑' x, F a b c d x y := ENNReal.tsum_comm

/-- Move the last index of a five-fold sum to the front. -/
theorem tsum_move_last_five (F : V → V → V → V → V → ℝ≥0∞) :
    (∑' a, ∑' b, ∑' c, ∑' d, ∑' x, F a b c d x)
      = ∑' x, ∑' a, ∑' b, ∑' c, ∑' d, F a b c d x := by
  calc (∑' a, ∑' b, ∑' c, ∑' d, ∑' x, F a b c d x)
      = ∑' a, ∑' b, ∑' c, ∑' x, ∑' d, F a b c d x :=
        tsum_congr fun a => tsum_congr fun b => tsum_congr fun c => ENNReal.tsum_comm
    _ = ∑' a, ∑' b, ∑' x, ∑' c, ∑' d, F a b c d x :=
        tsum_congr fun a => tsum_congr fun b => ENNReal.tsum_comm
    _ = ∑' a, ∑' x, ∑' b, ∑' c, ∑' d, F a b c d x := tsum_congr fun a => ENNReal.tsum_comm
    _ = ∑' x, ∑' a, ∑' b, ∑' c, ∑' d, F a b c d x := ENNReal.tsum_comm

/-- Bring the two branch-vertex sums of a four-leaf diagram to the front. -/
theorem tsum_six_swap (F : V → V → V → V → V → V → ℝ≥0∞) :
    (∑' a, ∑' b, ∑' c, ∑' d, ∑' x, ∑' y, F a b c d x y)
      = ∑' x, ∑' y, ∑' a, ∑' b, ∑' c, ∑' d, F a b c d x y := by
  rw [tsum_move_last_six]
  rw [tsum_congr fun y => tsum_move_last_five (F := fun a b c d x => F a b c d x y)]
  rw [ENNReal.tsum_comm]

end Summation

end PercLib.CriticalLRP.TreeExpansion.FivePoint

/-! ## The two canonical slot diagrams and their exact sums -/

namespace PercLib.CriticalLRP.TreeExpansion.FivePoint

variable {V : Type*}

set_option linter.unusedSectionVars false

section Canonical

variable [Countable V] [AddCommGroup V]

/-- Pull a constant out of a fourfold sum. -/
theorem tsum_four_const_mul (C : ℝ≥0∞) (R : V → V → V → V → ℝ≥0∞) :
    (∑' a, ∑' b, ∑' c, ∑' d, C * R a b c d)
      = C * ∑' a, ∑' b, ∑' c, ∑' d, R a b c d := by
  rw [show (∑' a, ∑' b, ∑' c, ∑' d, C * R a b c d)
      = ∑' a, ∑' b, ∑' c, C * (∑' d, R a b c d) from
    tsum_congr fun a => tsum_congr fun b => tsum_congr fun c => ENNReal.tsum_mul_left]
  rw [show (∑' a, ∑' b, ∑' c, C * (∑' d, R a b c d))
      = ∑' a, ∑' b, C * (∑' c, ∑' d, R a b c d) from
    tsum_congr fun a => tsum_congr fun b => ENNReal.tsum_mul_left]
  rw [show (∑' a, ∑' b, C * (∑' c, ∑' d, R a b c d))
      = ∑' a, C * (∑' b, ∑' c, ∑' d, R a b c d) from
    tsum_congr fun a => ENNReal.tsum_mul_left]
  exact ENNReal.tsum_mul_left

/-- A product of four one-variable sums. -/
theorem tsum_four_mul (f g h k : V → ℝ≥0∞) :
    (∑' x0, ∑' x1, ∑' x2, ∑' x3, f x0 * (g x1 * (h x2 * k x3)))
      = (∑' x, f x) * ((∑' x, g x) * ((∑' x, h x) * (∑' x, k x))) := by
  simpa using tsum_four_mul_const f g h k 1

/-- **The balanced (root-at-`v`) diagram sums to `E|K_o|² χ⁴`.** -/
theorem canonV_tsum (π : Sym2 V → unitInterval) (o : V)
    (hinv : ∀ a b : V, tau π a b = tau π o (b - a)) :
    (∑' a, ∑' b, ∑' c, ∑' d, canonV π o a b c d)
      = (∑' x, ∑' w, law π (conn o w ∩ conn x w)) * (∑' x, tau π o x) ^ 4 := by
  have hsymm : ∀ a b : V, tau π a b = tau π b a := fun a b => tau_comm π a b
  have hcol : ∀ b : V, (∑' a, tau π a b) = ∑' x, tau π o x :=
    fun b => PercLib.CriticalLRP.TreeExpansion.tsum_col_eq (tau π) o hsymm hinv b
  have step : ∀ x w : V, (∑' a, ∑' b, ∑' c, ∑' d,
      law π (conn o w ∩ conn x w) * (tau π a x * (tau π b x * (tau π c w * tau π d w))))
      = law π (conn o w ∩ conn x w) *
        ((∑' x, tau π o x) * ((∑' x, tau π o x) * ((∑' x, tau π o x) * (∑' x, tau π o x)))) := by
    intro x w
    rw [tsum_four_const_mul]
    rw [tsum_four_mul (f := fun a => tau π a x) (g := fun b => tau π b x)
      (h := fun c => tau π c w) (k := fun d => tau π d w)]
    simp only [hcol]
  simp only [canonV]
  rw [show (∑' a, ∑' b, ∑' c, ∑' d, ∑' w, ∑' x,
        law π (conn o w ∩ conn x w) * (tau π a x * (tau π b x * (tau π c w * tau π d w))))
      = ∑' a, ∑' b, ∑' c, ∑' d, ∑' x, ∑' w,
        law π (conn o w ∩ conn x w) * (tau π a x * (tau π b x * (tau π c w * tau π d w))) from
    tsum_congr fun a => tsum_congr fun b => tsum_congr fun c => tsum_congr fun d =>
      ENNReal.tsum_comm]
  rw [tsum_six_swap]
  simp only [step]
  rw [tsum_two_mul_const (F := fun x w => law π (conn o w ∩ conn x w))
    (Y := (∑' x, tau π o x) * ((∑' x, tau π o x) * ((∑' x, tau π o x) * (∑' x, tau π o x))))]
  ring

/-- **The root-at-`u` diagram sums to `E|K_o|² χ⁴`.** -/
theorem canonU_tsum (π : Sym2 V → unitInterval) (o : V)
    (hinv : ∀ a b : V, tau π a b = tau π o (b - a)) :
    (∑' a, ∑' b, ∑' c, ∑' d, canonU π o a b c d)
      = (∑' x, ∑' w, law π (conn o w ∩ conn x w)) * (∑' x, tau π o x) ^ 4 := by
  have hsymm : ∀ a b : V, tau π a b = tau π b a := fun a b => tau_comm π a b
  have hrow : ∀ a : V, (∑' b, tau π a b) = ∑' x, tau π o x :=
    fun a => PercLib.CriticalLRP.TreeExpansion.tsum_row_eq (tau π) o hinv a
  have hcol : ∀ b : V, (∑' a, tau π a b) = ∑' x, tau π o x :=
    fun b => PercLib.CriticalLRP.TreeExpansion.tsum_col_eq (tau π) o hsymm hinv b
  have step : ∀ x w : V, (∑' a, ∑' b, ∑' c, ∑' d,
      law π (conn o x ∩ conn a x) * (tau π b x * (tau π x w * (tau π c w * tau π d w))))
      = (∑' a, law π (conn o x ∩ conn a x)) *
        ((∑' x, tau π o x) * ((∑' x, tau π o x) * ((∑' x, tau π o x) * tau π x w))) := by
    intro x w
    rw [show (∑' a, ∑' b, ∑' c, ∑' d,
        law π (conn o x ∩ conn a x) * (tau π b x * (tau π x w * (tau π c w * tau π d w))))
        = ∑' a, ∑' b, ∑' c, ∑' d,
          law π (conn o x ∩ conn a x) * (tau π b x * (tau π c w * (tau π d w * tau π x w))) from
      tsum_congr fun a => tsum_congr fun b => tsum_congr fun c => tsum_congr fun d => by ring]
    rw [tsum_four_mul_const (f := fun a => law π (conn o x ∩ conn a x))
      (g := fun b => tau π b x) (h := fun c => tau π c w) (k := fun d => tau π d w)
      (C := tau π x w)]
    simp only [hcol]
  simp only [canonU]
  rw [show (∑' a, ∑' b, ∑' c, ∑' d, ∑' w, ∑' x,
        law π (conn o x ∩ conn a x) * (tau π b x * (tau π x w * (tau π c w * tau π d w))))
      = ∑' a, ∑' b, ∑' c, ∑' d, ∑' x, ∑' w,
        law π (conn o x ∩ conn a x) * (tau π b x * (tau π x w * (tau π c w * tau π d w))) from
    tsum_congr fun a => tsum_congr fun b => tsum_congr fun c => tsum_congr fun d =>
      ENNReal.tsum_comm]
  rw [tsum_six_swap]
  simp only [step]
  have hinner : ∀ x : V, (∑' w, (∑' a, law π (conn o x ∩ conn a x)) *
        ((∑' x, tau π o x) * ((∑' x, tau π o x) * ((∑' x, tau π o x) * tau π x w))))
      = (∑' a, law π (conn o x ∩ conn a x)) *
        ((∑' x, tau π o x) * ((∑' x, tau π o x) * ((∑' x, tau π o x) * (∑' x, tau π o x)))) := by
    intro x
    rw [show (∑' w, (∑' a, law π (conn o x ∩ conn a x)) *
          ((∑' x, tau π o x) * ((∑' x, tau π o x) * ((∑' x, tau π o x) * tau π x w))))
        = ∑' w, ((∑' a, law π (conn o x ∩ conn a x)) *
          ((∑' x, tau π o x) * ((∑' x, tau π o x) * (∑' x, tau π o x)))) * tau π x w from
      tsum_congr fun w => by ring]
    rw [ENNReal.tsum_mul_left, hrow x]
    ring
  simp only [hinner]
  rw [ENNReal.tsum_mul_right]
  rw [ENNReal.tsum_comm (f := fun a x => law π (conn o x ∩ conn a x))]
  ring

end Canonical

end PercLib.CriticalLRP.TreeExpansion.FivePoint

/-! ## Assembling the fifteen slot diagrams and the mixed fourth-moment bound -/

namespace PercLib.CriticalLRP.TreeExpansion.FivePoint

variable {V : Type*}

set_option linter.unusedSectionVars false

section Assembly

variable [Countable V] [AddCommGroup V]

/-- Swap a finite `Fin 15` sum past four `V`-sums. -/
theorem tsum_fin_four_swap (F : V → V → V → V → Fin 15 → ℝ≥0∞) :
    (∑' a, ∑' b, ∑' c, ∑' d, ∑' k : Fin 15, F a b c d k)
      = ∑' k : Fin 15, ∑' a, ∑' b, ∑' c, ∑' d, F a b c d k := by
  calc (∑' a, ∑' b, ∑' c, ∑' d, ∑' k : Fin 15, F a b c d k)
      = ∑' a, ∑' b, ∑' c, ∑' k : Fin 15, ∑' d, F a b c d k :=
        tsum_congr fun a => tsum_congr fun b => tsum_congr fun c => ENNReal.tsum_comm
    _ = ∑' a, ∑' b, ∑' k : Fin 15, ∑' c, ∑' d, F a b c d k :=
        tsum_congr fun a => tsum_congr fun b => ENNReal.tsum_comm
    _ = ∑' a, ∑' k : Fin 15, ∑' b, ∑' c, ∑' d, F a b c d k :=
        tsum_congr fun a => ENNReal.tsum_comm
    _ = ∑' k : Fin 15, ∑' a, ∑' b, ∑' c, ∑' d, F a b c d k := ENNReal.tsum_comm

/-- A constant sum over `Fin 15`. -/
theorem tsum_fin15_const (c : ℝ≥0∞) : (∑' _ : Fin 15, c) = 15 * c := by
  rw [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  simp [nsmul_eq_mul]

/-- **The sum of one slot diagram over the four labelled leaves and the branch vertices.**
The four leaf slots of any of the fifteen patterns are a permutation of `1,2,3,4`, so the
four leaf sums produce `χ⁴` and the joint pair produces the native second moment. -/
theorem tsum_slotDiagram (π : Sym2 V → unitInterval)
    (hinv : ∀ a b : V, tau π a b = tau π 0 (b - a)) (k : Fin 15) :
    (∑' x1, ∑' x2, ∑' x3, ∑' x4, ∑' w, slotDiagram π k w ![0, x1, x2, x3, x4])
      = (∑' x, ∑' w, law π (conn 0 w ∩ conn x w)) * (∑' x, tau π 0 x) ^ 4 := by
  fin_cases k
  · calc (∑' x1, ∑' x2, ∑' x3, ∑' x4, ∑' w, slotDiagram π 0 w ![0, x1, x2, x3, x4])
          = ∑' x1, ∑' x2, ∑' x3, ∑' x4, canonV π 0 x1 x2 x3 x4 := by
            simp [slotDiagram, canonV, pat]
        _ = (∑' x, ∑' w, law π (conn 0 w ∩ conn x w)) * (∑' x, tau π 0 x) ^ 4 :=
            canonV_tsum π 0 hinv
  · calc (∑' x1, ∑' x2, ∑' x3, ∑' x4, ∑' w, slotDiagram π 1 w ![0, x1, x2, x3, x4])
          = ∑' x1, ∑' x2, ∑' x3, ∑' x4,
            canonV π 0 (![x1, x2, x3, x4] (![0, 2, 1, 3] 0))
              (![x1, x2, x3, x4] (![0, 2, 1, 3] 1))
              (![x1, x2, x3, x4] (![0, 2, 1, 3] 2))
              (![x1, x2, x3, x4] (![0, 2, 1, 3] 3)) := by
            simp [slotDiagram, canonV, pat]
        _ = ∑' x1, ∑' x2, ∑' x3, ∑' x4, canonV π 0 x1 x2 x3 x4 :=
            tsum_four_perm (Equiv.ofBijective ![0, 2, 1, 3] (by decide)) (H := canonV π 0)
        _ = (∑' x, ∑' w, law π (conn 0 w ∩ conn x w)) * (∑' x, tau π 0 x) ^ 4 :=
            canonV_tsum π 0 hinv
  · calc (∑' x1, ∑' x2, ∑' x3, ∑' x4, ∑' w, slotDiagram π 2 w ![0, x1, x2, x3, x4])
          = ∑' x1, ∑' x2, ∑' x3, ∑' x4,
            canonV π 0 (![x1, x2, x3, x4] (![0, 3, 1, 2] 0))
              (![x1, x2, x3, x4] (![0, 3, 1, 2] 1))
              (![x1, x2, x3, x4] (![0, 3, 1, 2] 2))
              (![x1, x2, x3, x4] (![0, 3, 1, 2] 3)) := by
            simp [slotDiagram, canonV, pat]
        _ = ∑' x1, ∑' x2, ∑' x3, ∑' x4, canonV π 0 x1 x2 x3 x4 :=
            tsum_four_perm (Equiv.ofBijective ![0, 3, 1, 2] (by decide)) (H := canonV π 0)
        _ = (∑' x, ∑' w, law π (conn 0 w ∩ conn x w)) * (∑' x, tau π 0 x) ^ 4 :=
            canonV_tsum π 0 hinv
  · calc (∑' x1, ∑' x2, ∑' x3, ∑' x4, ∑' w, slotDiagram π 3 w ![0, x1, x2, x3, x4])
          = ∑' x1, ∑' x2, ∑' x3, ∑' x4,
            canonU π 0 (![x1, x2, x3, x4] (![1, 0, 2, 3] 0))
              (![x1, x2, x3, x4] (![1, 0, 2, 3] 1))
              (![x1, x2, x3, x4] (![1, 0, 2, 3] 2))
              (![x1, x2, x3, x4] (![1, 0, 2, 3] 3)) := by
            simp [slotDiagram, canonU, pat]
        _ = ∑' x1, ∑' x2, ∑' x3, ∑' x4, canonU π 0 x1 x2 x3 x4 :=
            tsum_four_perm (Equiv.ofBijective ![1, 0, 2, 3] (by decide)) (H := canonU π 0)
        _ = (∑' x, ∑' w, law π (conn 0 w ∩ conn x w)) * (∑' x, tau π 0 x) ^ 4 :=
            canonU_tsum π 0 hinv
  · calc (∑' x1, ∑' x2, ∑' x3, ∑' x4, ∑' w, slotDiagram π 4 w ![0, x1, x2, x3, x4])
          = ∑' x1, ∑' x2, ∑' x3, ∑' x4,
            canonU π 0 (![x1, x2, x3, x4] (![2, 0, 1, 3] 0))
              (![x1, x2, x3, x4] (![2, 0, 1, 3] 1))
              (![x1, x2, x3, x4] (![2, 0, 1, 3] 2))
              (![x1, x2, x3, x4] (![2, 0, 1, 3] 3)) := by
            simp [slotDiagram, canonU, pat]
        _ = ∑' x1, ∑' x2, ∑' x3, ∑' x4, canonU π 0 x1 x2 x3 x4 :=
            tsum_four_perm (Equiv.ofBijective ![2, 0, 1, 3] (by decide)) (H := canonU π 0)
        _ = (∑' x, ∑' w, law π (conn 0 w ∩ conn x w)) * (∑' x, tau π 0 x) ^ 4 :=
            canonU_tsum π 0 hinv
  · calc (∑' x1, ∑' x2, ∑' x3, ∑' x4, ∑' w, slotDiagram π 5 w ![0, x1, x2, x3, x4])
          = ∑' x1, ∑' x2, ∑' x3, ∑' x4,
            canonU π 0 (![x1, x2, x3, x4] (![3, 0, 1, 2] 0))
              (![x1, x2, x3, x4] (![3, 0, 1, 2] 1))
              (![x1, x2, x3, x4] (![3, 0, 1, 2] 2))
              (![x1, x2, x3, x4] (![3, 0, 1, 2] 3)) := by
            simp [slotDiagram, canonU, pat]
        _ = ∑' x1, ∑' x2, ∑' x3, ∑' x4, canonU π 0 x1 x2 x3 x4 :=
            tsum_four_perm (Equiv.ofBijective ![3, 0, 1, 2] (by decide)) (H := canonU π 0)
        _ = (∑' x, ∑' w, law π (conn 0 w ∩ conn x w)) * (∑' x, tau π 0 x) ^ 4 :=
            canonU_tsum π 0 hinv
  · calc (∑' x1, ∑' x2, ∑' x3, ∑' x4, ∑' w, slotDiagram π 6 w ![0, x1, x2, x3, x4])
          = ∑' x1, ∑' x2, ∑' x3, ∑' x4, canonU π 0 x1 x2 x3 x4 := by
            simp [slotDiagram, canonU, pat]
        _ = (∑' x, ∑' w, law π (conn 0 w ∩ conn x w)) * (∑' x, tau π 0 x) ^ 4 :=
            canonU_tsum π 0 hinv
  · calc (∑' x1, ∑' x2, ∑' x3, ∑' x4, ∑' w, slotDiagram π 7 w ![0, x1, x2, x3, x4])
          = ∑' x1, ∑' x2, ∑' x3, ∑' x4,
            canonU π 0 (![x1, x2, x3, x4] (![2, 1, 0, 3] 0))
              (![x1, x2, x3, x4] (![2, 1, 0, 3] 1))
              (![x1, x2, x3, x4] (![2, 1, 0, 3] 2))
              (![x1, x2, x3, x4] (![2, 1, 0, 3] 3)) := by
            simp [slotDiagram, canonU, pat]
        _ = ∑' x1, ∑' x2, ∑' x3, ∑' x4, canonU π 0 x1 x2 x3 x4 :=
            tsum_four_perm (Equiv.ofBijective ![2, 1, 0, 3] (by decide)) (H := canonU π 0)
        _ = (∑' x, ∑' w, law π (conn 0 w ∩ conn x w)) * (∑' x, tau π 0 x) ^ 4 :=
            canonU_tsum π 0 hinv
  · calc (∑' x1, ∑' x2, ∑' x3, ∑' x4, ∑' w, slotDiagram π 8 w ![0, x1, x2, x3, x4])
          = ∑' x1, ∑' x2, ∑' x3, ∑' x4,
            canonU π 0 (![x1, x2, x3, x4] (![3, 1, 0, 2] 0))
              (![x1, x2, x3, x4] (![3, 1, 0, 2] 1))
              (![x1, x2, x3, x4] (![3, 1, 0, 2] 2))
              (![x1, x2, x3, x4] (![3, 1, 0, 2] 3)) := by
            simp [slotDiagram, canonU, pat]
        _ = ∑' x1, ∑' x2, ∑' x3, ∑' x4, canonU π 0 x1 x2 x3 x4 :=
            tsum_four_perm (Equiv.ofBijective ![3, 1, 0, 2] (by decide)) (H := canonU π 0)
        _ = (∑' x, ∑' w, law π (conn 0 w ∩ conn x w)) * (∑' x, tau π 0 x) ^ 4 :=
            canonU_tsum π 0 hinv
  · calc (∑' x1, ∑' x2, ∑' x3, ∑' x4, ∑' w, slotDiagram π 9 w ![0, x1, x2, x3, x4])
          = ∑' x1, ∑' x2, ∑' x3, ∑' x4,
            canonU π 0 (![x1, x2, x3, x4] (![0, 2, 1, 3] 0))
              (![x1, x2, x3, x4] (![0, 2, 1, 3] 1))
              (![x1, x2, x3, x4] (![0, 2, 1, 3] 2))
              (![x1, x2, x3, x4] (![0, 2, 1, 3] 3)) := by
            simp [slotDiagram, canonU, pat]
        _ = ∑' x1, ∑' x2, ∑' x3, ∑' x4, canonU π 0 x1 x2 x3 x4 :=
            tsum_four_perm (Equiv.ofBijective ![0, 2, 1, 3] (by decide)) (H := canonU π 0)
        _ = (∑' x, ∑' w, law π (conn 0 w ∩ conn x w)) * (∑' x, tau π 0 x) ^ 4 :=
            canonU_tsum π 0 hinv
  · calc (∑' x1, ∑' x2, ∑' x3, ∑' x4, ∑' w, slotDiagram π 10 w ![0, x1, x2, x3, x4])
          = ∑' x1, ∑' x2, ∑' x3, ∑' x4,
            canonU π 0 (![x1, x2, x3, x4] (![1, 2, 0, 3] 0))
              (![x1, x2, x3, x4] (![1, 2, 0, 3] 1))
              (![x1, x2, x3, x4] (![1, 2, 0, 3] 2))
              (![x1, x2, x3, x4] (![1, 2, 0, 3] 3)) := by
            simp [slotDiagram, canonU, pat]
        _ = ∑' x1, ∑' x2, ∑' x3, ∑' x4, canonU π 0 x1 x2 x3 x4 :=
            tsum_four_perm (Equiv.ofBijective ![1, 2, 0, 3] (by decide)) (H := canonU π 0)
        _ = (∑' x, ∑' w, law π (conn 0 w ∩ conn x w)) * (∑' x, tau π 0 x) ^ 4 :=
            canonU_tsum π 0 hinv
  · calc (∑' x1, ∑' x2, ∑' x3, ∑' x4, ∑' w, slotDiagram π 11 w ![0, x1, x2, x3, x4])
          = ∑' x1, ∑' x2, ∑' x3, ∑' x4,
            canonU π 0 (![x1, x2, x3, x4] (![3, 2, 0, 1] 0))
              (![x1, x2, x3, x4] (![3, 2, 0, 1] 1))
              (![x1, x2, x3, x4] (![3, 2, 0, 1] 2))
              (![x1, x2, x3, x4] (![3, 2, 0, 1] 3)) := by
            simp [slotDiagram, canonU, pat]
        _ = ∑' x1, ∑' x2, ∑' x3, ∑' x4, canonU π 0 x1 x2 x3 x4 :=
            tsum_four_perm (Equiv.ofBijective ![3, 2, 0, 1] (by decide)) (H := canonU π 0)
        _ = (∑' x, ∑' w, law π (conn 0 w ∩ conn x w)) * (∑' x, tau π 0 x) ^ 4 :=
            canonU_tsum π 0 hinv
  · calc (∑' x1, ∑' x2, ∑' x3, ∑' x4, ∑' w, slotDiagram π 12 w ![0, x1, x2, x3, x4])
          = ∑' x1, ∑' x2, ∑' x3, ∑' x4,
            canonU π 0 (![x1, x2, x3, x4] (![0, 3, 1, 2] 0))
              (![x1, x2, x3, x4] (![0, 3, 1, 2] 1))
              (![x1, x2, x3, x4] (![0, 3, 1, 2] 2))
              (![x1, x2, x3, x4] (![0, 3, 1, 2] 3)) := by
            simp [slotDiagram, canonU, pat]
        _ = ∑' x1, ∑' x2, ∑' x3, ∑' x4, canonU π 0 x1 x2 x3 x4 :=
            tsum_four_perm (Equiv.ofBijective ![0, 3, 1, 2] (by decide)) (H := canonU π 0)
        _ = (∑' x, ∑' w, law π (conn 0 w ∩ conn x w)) * (∑' x, tau π 0 x) ^ 4 :=
            canonU_tsum π 0 hinv
  · calc (∑' x1, ∑' x2, ∑' x3, ∑' x4, ∑' w, slotDiagram π 13 w ![0, x1, x2, x3, x4])
          = ∑' x1, ∑' x2, ∑' x3, ∑' x4,
            canonU π 0 (![x1, x2, x3, x4] (![1, 3, 0, 2] 0))
              (![x1, x2, x3, x4] (![1, 3, 0, 2] 1))
              (![x1, x2, x3, x4] (![1, 3, 0, 2] 2))
              (![x1, x2, x3, x4] (![1, 3, 0, 2] 3)) := by
            simp [slotDiagram, canonU, pat]
        _ = ∑' x1, ∑' x2, ∑' x3, ∑' x4, canonU π 0 x1 x2 x3 x4 :=
            tsum_four_perm (Equiv.ofBijective ![1, 3, 0, 2] (by decide)) (H := canonU π 0)
        _ = (∑' x, ∑' w, law π (conn 0 w ∩ conn x w)) * (∑' x, tau π 0 x) ^ 4 :=
            canonU_tsum π 0 hinv
  · calc (∑' x1, ∑' x2, ∑' x3, ∑' x4, ∑' w, slotDiagram π 14 w ![0, x1, x2, x3, x4])
          = ∑' x1, ∑' x2, ∑' x3, ∑' x4,
            canonU π 0 (![x1, x2, x3, x4] (![2, 3, 0, 1] 0))
              (![x1, x2, x3, x4] (![2, 3, 0, 1] 1))
              (![x1, x2, x3, x4] (![2, 3, 0, 1] 2))
              (![x1, x2, x3, x4] (![2, 3, 0, 1] 3)) := by
            simp [slotDiagram, canonU, pat]
        _ = ∑' x1, ∑' x2, ∑' x3, ∑' x4, canonU π 0 x1 x2 x3 x4 :=
            tsum_four_perm (Equiv.ofBijective ![2, 3, 0, 1] (by decide)) (H := canonU π 0)
        _ = (∑' x, ∑' w, law π (conn 0 w ∩ conn x w)) * (∑' x, tau π 0 x) ^ 4 :=
            canonU_tsum π 0 hinv

end Assembly

end PercLib.CriticalLRP.TreeExpansion.FivePoint

/-! ## The mixed fourth-moment tree-graph bound -/

namespace PercLib.CriticalLRP.TreeExpansion.FivePoint

variable {V : Type*}

set_option linter.unusedSectionVars false

/-- **Lemma I.4.16 at `p = 4`, mixed form.**  For percolation on a countable weighted graph
with a translation-invariant two-point function, the fourth cluster moment is bounded by
`15 (E|K|²) (E|K|)⁴`, with no moment-finiteness hypothesis. -/
theorem fourth_moment_mixed_le [Countable V] [AddCommGroup V] (π : Sym2 V → unitInterval)
    (hinv : ∀ a b : V, tau π a b = tau π 0 (b - a)) :
    ∫⁻ ω, (PercLib.CriticalLRP.Percolation.cardFun (PercLib.CriticalLRP.cluster ω 0)) ^ 4
        ∂(law π) ≤
      15 * (∫⁻ ω, (PercLib.CriticalLRP.Percolation.cardFun
          (PercLib.CriticalLRP.cluster ω 0)) ^ 2 ∂(law π)) *
        (∫⁻ ω, PercLib.CriticalLRP.Percolation.cardFun
          (PercLib.CriticalLRP.cluster ω 0) ∂(law π)) ^ 4 := by
  have hmean : (∫⁻ ω, PercLib.CriticalLRP.Percolation.cardFun
      (PercLib.CriticalLRP.cluster ω 0) ∂(law π)) = ∑' x, tau π 0 x := by
    rw [show (∫⁻ ω, PercLib.CriticalLRP.Percolation.cardFun
        (PercLib.CriticalLRP.cluster ω 0) ∂(law π))
        = ∫⁻ ω, ((PercLib.CriticalLRP.cluster ω 0).encard : ℝ≥0∞) ∂(law π) from
      lintegral_congr fun ω => PercLib.CriticalLRP.Percolation.cardFun_eq_encard _]
    exact chi_eq_tsum_tau π 0
  rw [lintegral_cardFun_four_eq π 0, hmean, ← joinSum_eq_cardFun_sq π 0]
  calc ∑' y, ∑' z, ∑' w, ∑' q, law π (conn 0 y ∩ conn 0 z ∩ conn 0 w ∩ conn 0 q)
      ≤ ∑' y, ∑' z, ∑' w, ∑' q, ∑' k : Fin 15, ∑' c,
          slotDiagram π k c ![0, y, z, w, q] :=
        ENNReal.tsum_le_tsum fun y => ENNReal.tsum_le_tsum fun z =>
          ENNReal.tsum_le_tsum fun w => ENNReal.tsum_le_tsum fun q =>
            fourPoint_le_slotSum π 0 y z w q
    _ = ∑' k : Fin 15, ∑' y, ∑' z, ∑' w, ∑' q, ∑' c,
          slotDiagram π k c ![0, y, z, w, q] :=
        tsum_fin_four_swap (F := fun y z w q k => ∑' c, slotDiagram π k c ![0, y, z, w, q])
    _ = ∑' k : Fin 15,
          ((∑' x, ∑' w, law π (conn 0 w ∩ conn x w)) * (∑' x, tau π 0 x) ^ 4) :=
        tsum_congr fun k => tsum_slotDiagram π hinv k
    _ = 15 * ((∑' x, ∑' w, law π (conn 0 w ∩ conn x w)) * (∑' x, tau π 0 x) ^ 4) :=
        tsum_fin15_const _
    _ = 15 * (∑' x, ∑' w, law π (conn 0 w ∩ conn x w)) * (∑' x, tau π 0 x) ^ 4 := by ring

/-! ## Axiom audit -/


#print axioms PercLib.CriticalLRP.TreeExpansion.FivePoint.canonU_tsum
#print axioms PercLib.CriticalLRP.TreeExpansion.FivePoint.canonV_tsum
#print axioms PercLib.CriticalLRP.TreeExpansion.FivePoint.tsum_slotDiagram
#print axioms PercLib.CriticalLRP.TreeExpansion.FivePoint.fourth_moment_mixed_le

end PercLib.CriticalLRP.TreeExpansion.FivePoint
