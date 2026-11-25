/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Five-vertex deterministic tree-arm decomposition supplied by Ultramath
`smwpj8umm` member m1, including first-hit attachment and the fifteen-pattern
normalization. Earlier three-arm components came from `smwj645my` under the
project's Apache-2.0 attribution.
-/
module

public import PercLib.CriticalLRP.Correlation.FourthMoment.Arms

/-
Swarm `smwpj8umm`, member `m1` (direction d1), continuation.

# Fifth-leaf attachment and the universal five-vertex cover

`attachAny`: the fifth terminal is attached to the four-terminal `H`-structure `Slots4` along the
first hit of a walk into the union of the five arm supports; the arm it lands on is split, giving
one of the five slot forms of the seven-arm comb, with the concatenated edge list still `Nodup`.

`exists_combShape`: **every** five vertices in a common component of an arbitrary graph realise one
of the fifteen labelled five-leaf combs `CombShape G k u v w T`, `k : Fin 15`.
-/

open Set MeasureTheory
open scoped ENNReal
open PercLib.Percolation.Bond

@[expose] public section

namespace PercLib.CriticalLRP.TreeExpansion.FivePoint

variable {V : Type*}

/-! ## List bookkeeping: splitting a `Nodup` concatenation into disjoint blocks -/

theorem disjoint_append_left_iff {α : Type*} {l₁ l₂ l₃ : List α} :
    (l₁ ++ l₂).Disjoint l₃ ↔ l₁.Disjoint l₃ ∧ l₂.Disjoint l₃ := by
  rw [List.disjoint_left, List.disjoint_left, List.disjoint_left]
  constructor
  · intro h
    exact ⟨fun a ha ha3 => h (List.mem_append_left _ ha) ha3,
      fun a ha ha3 => h (List.mem_append_right _ ha) ha3⟩
  · rintro ⟨h1, h2⟩ a ha ha3
    rcases List.mem_append.mp ha with h | h
    · exact h1 h ha3
    · exact h2 h ha3

/-- The five blocks of a `Nodup` five-fold concatenation: each is `Nodup` and the ten pairwise
disjointnesses hold. -/
theorem nodup_append5_facts {α : Type*} {a b c d e : List α}
    (h : (a ++ b ++ c ++ d ++ e).Nodup) :
    a.Nodup ∧ b.Nodup ∧ c.Nodup ∧ d.Nodup ∧ e.Nodup ∧
    a.Disjoint b ∧ a.Disjoint c ∧ a.Disjoint d ∧ a.Disjoint e ∧
    b.Disjoint c ∧ b.Disjoint d ∧ b.Disjoint e ∧ c.Disjoint d ∧ c.Disjoint e ∧
    d.Disjoint e := by
  have h4 : (a ++ b ++ c ++ d).Nodup := h.of_append_left
  have h3 : (a ++ b ++ c).Nodup := h4.of_append_left
  have h2 : (a ++ b).Nodup := h3.of_append_left
  obtain ⟨ha, hb, hab⟩ := List.nodup_append'.mp h2
  obtain ⟨_, hc, h2c⟩ := List.nodup_append'.mp h3
  obtain ⟨_, hd, h3d⟩ := List.nodup_append'.mp h4
  obtain ⟨_, he, h4e⟩ := List.nodup_append'.mp h
  obtain ⟨hac, hbc⟩ := disjoint_append_left_iff.mp h2c
  obtain ⟨habd, hcd⟩ := disjoint_append_left_iff.mp h3d
  obtain ⟨had, hbd⟩ := disjoint_append_left_iff.mp habd
  obtain ⟨habce, hde⟩ := disjoint_append_left_iff.mp h4e
  obtain ⟨habe, hce⟩ := disjoint_append_left_iff.mp habce
  obtain ⟨hae, hbe⟩ := disjoint_append_left_iff.mp habe
  exact ⟨ha, hb, hc, hd, he, hab, hac, had, hae, hbc, hbd, hbe, hcd, hce, hde⟩

/-- The seven blocks of a `Nodup` seven-fold concatenation: each is `Nodup` and the twenty-one
pairwise disjointnesses hold. -/
theorem nodup_append7_facts {α : Type*} {a b c d e f g : List α}
    (h : (a ++ b ++ c ++ d ++ e ++ f ++ g).Nodup) :
    a.Nodup ∧ b.Nodup ∧ c.Nodup ∧ d.Nodup ∧ e.Nodup ∧ f.Nodup ∧ g.Nodup ∧
    a.Disjoint b ∧ a.Disjoint c ∧ a.Disjoint d ∧ a.Disjoint e ∧ a.Disjoint f ∧
      a.Disjoint g ∧
    b.Disjoint c ∧ b.Disjoint d ∧ b.Disjoint e ∧ b.Disjoint f ∧ b.Disjoint g ∧
    c.Disjoint d ∧ c.Disjoint e ∧ c.Disjoint f ∧ c.Disjoint g ∧
    d.Disjoint e ∧ d.Disjoint f ∧ d.Disjoint g ∧ e.Disjoint f ∧ e.Disjoint g ∧
    f.Disjoint g := by
  have h6 : (a ++ b ++ c ++ d ++ e ++ f).Nodup := h.of_append_left
  have h5 : (a ++ b ++ c ++ d ++ e).Nodup := h6.of_append_left
  have h4 : (a ++ b ++ c ++ d).Nodup := h5.of_append_left
  have h3 : (a ++ b ++ c).Nodup := h4.of_append_left
  have h2 : (a ++ b).Nodup := h3.of_append_left
  obtain ⟨ha, hb, hab⟩ := List.nodup_append'.mp h2
  obtain ⟨_, hc, h2c⟩ := List.nodup_append'.mp h3
  obtain ⟨_, hd, h3d⟩ := List.nodup_append'.mp h4
  obtain ⟨_, he, h4e⟩ := List.nodup_append'.mp h5
  obtain ⟨_, hf, h5f⟩ := List.nodup_append'.mp h6
  obtain ⟨_, hg, h6g⟩ := List.nodup_append'.mp h
  obtain ⟨hac, hbc⟩ := disjoint_append_left_iff.mp h2c
  obtain ⟨habd, hcd⟩ := disjoint_append_left_iff.mp h3d
  obtain ⟨had, hbd⟩ := disjoint_append_left_iff.mp habd
  obtain ⟨habce0, hde⟩ := disjoint_append_left_iff.mp h4e
  obtain ⟨habe, hce⟩ := disjoint_append_left_iff.mp habce0
  obtain ⟨hae, hbe⟩ := disjoint_append_left_iff.mp habe
  obtain ⟨habcdf, hef⟩ := disjoint_append_left_iff.mp h5f
  obtain ⟨habcdf', hdf⟩ := disjoint_append_left_iff.mp habcdf
  obtain ⟨habc, hcf⟩ := disjoint_append_left_iff.mp habcdf'
  obtain ⟨haf, hbf⟩ := disjoint_append_left_iff.mp habc
  obtain ⟨habcdeg, hfg⟩ := disjoint_append_left_iff.mp h6g
  obtain ⟨habcdeg', heg⟩ := disjoint_append_left_iff.mp habcdeg
  obtain ⟨habcdeg'', hdg⟩ := disjoint_append_left_iff.mp habcdeg'
  obtain ⟨habcd, hcg⟩ := disjoint_append_left_iff.mp habcdeg''
  obtain ⟨hag, hbg⟩ := disjoint_append_left_iff.mp habcd
  exact ⟨ha, hb, hc, hd, he, hf, hg, hab, hac, had, hae, haf, hag, hbc, hbd, hbe, hbf,
    hbg, hcd, hce, hcf, hcg, hde, hdf, hdg, hef, heg, hfg⟩

/-- Rebuild a `Nodup` seven-fold concatenation from its blocks. -/
theorem nodup_seven {α : Type*} {l0 l1 l2 l3 l4 l5 l6 : List α}
    (h0 : l0.Nodup) (h1 : l1.Nodup) (h2 : l2.Nodup) (h3 : l3.Nodup) (h4 : l4.Nodup)
    (h5 : l5.Nodup) (h6 : l6.Nodup)
    (d01 : l0.Disjoint l1) (d02 : l0.Disjoint l2) (d03 : l0.Disjoint l3)
    (d04 : l0.Disjoint l4) (d05 : l0.Disjoint l5) (d06 : l0.Disjoint l6)
    (d12 : l1.Disjoint l2) (d13 : l1.Disjoint l3) (d14 : l1.Disjoint l4)
    (d15 : l1.Disjoint l5) (d16 : l1.Disjoint l6)
    (d23 : l2.Disjoint l3) (d24 : l2.Disjoint l4) (d25 : l2.Disjoint l5)
    (d26 : l2.Disjoint l6)
    (d34 : l3.Disjoint l4) (d35 : l3.Disjoint l5) (d36 : l3.Disjoint l6)
    (d45 : l4.Disjoint l5) (d46 : l4.Disjoint l6) (d56 : l5.Disjoint l6) :
    (l0 ++ l1 ++ l2 ++ l3 ++ l4 ++ l5 ++ l6).Nodup := by
  have e01 : (l0 ++ l1).Nodup := List.Nodup.append h0 h1 d01
  have a02 : (l0 ++ l1).Disjoint l2 := disjoint_append_left_of d02 d12
  have e02 : (l0 ++ l1 ++ l2).Nodup := List.Nodup.append e01 h2 a02
  have a03 : (l0 ++ l1 ++ l2).Disjoint l3 :=
    disjoint_append_left_of (disjoint_append_left_of d03 d13) d23
  have e03 : (l0 ++ l1 ++ l2 ++ l3).Nodup := List.Nodup.append e02 h3 a03
  have a04 : (l0 ++ l1 ++ l2 ++ l3).Disjoint l4 :=
    disjoint_append_left_of (disjoint_append_left_of (disjoint_append_left_of d04 d14) d24) d34
  have e04 : (l0 ++ l1 ++ l2 ++ l3 ++ l4).Nodup := List.Nodup.append e03 h4 a04
  have a05 : (l0 ++ l1 ++ l2 ++ l3 ++ l4).Disjoint l5 :=
    disjoint_append_left_of
      (disjoint_append_left_of (disjoint_append_left_of (disjoint_append_left_of d05 d15) d25)
        d35) d45
  have e05 : (l0 ++ l1 ++ l2 ++ l3 ++ l4 ++ l5).Nodup := List.Nodup.append e04 h5 a05
  have a06 : (l0 ++ l1 ++ l2 ++ l3 ++ l4 ++ l5).Disjoint l6 :=
    disjoint_append_left_of
      (disjoint_append_left_of
        (disjoint_append_left_of (disjoint_append_left_of (disjoint_append_left_of d06 d16) d26)
          d36) d46) d56
  exact List.Nodup.append e05 h6 a06

/-! ## `CombSlots` is invariant under the slot symmetries and under reversing the spine -/

theorem combSlots_swap01 {G : SimpleGraph V} {x y z p q u v w : V}
    (h : CombSlots G x y z p q u v w) : CombSlots G y x z p q u v w := by
  obtain ⟨p0, p1, p2, p3, p4, s1, s2, hnd⟩ := h
  obtain ⟨h0, h1, h2, h3, h4, hs1, hs2, d01, d02, d03, d04, d05, d06, d12, d13, d14, d15,
    d16, d23, d24, d25, d26, d34, d35, d36, d45, d46, d56⟩ := nodup_append7_facts hnd
  exact ⟨p1, p0, p2, p3, p4, s1, s2,
    nodup_seven h1 h0 h2 h3 h4 hs1 hs2 d01.symm d12 d13 d14 d15 d16 d02 d03 d04 d05 d06
      d23 d24 d25 d26 d34 d35 d36 d45 d46 d56⟩

theorem combSlots_swap34 {G : SimpleGraph V} {x y z p q u v w : V}
    (h : CombSlots G x y z p q u v w) : CombSlots G x y z q p u v w := by
  obtain ⟨p0, p1, p2, p3, p4, s1, s2, hnd⟩ := h
  obtain ⟨h0, h1, h2, h3, h4, hs1, hs2, d01, d02, d03, d04, d05, d06, d12, d13, d14, d15,
    d16, d23, d24, d25, d26, d34, d35, d36, d45, d46, d56⟩ := nodup_append7_facts hnd
  exact ⟨p0, p1, p2, p4, p3, s1, s2,
    nodup_seven h0 h1 h2 h4 h3 hs1 hs2 d01 d02 d04 d03 d05 d06 d12 d14 d13 d15 d16 d24 d23 d25
      d26 d34.symm d45 d46 d35 d36 d56⟩

/-- Reversing the spine `u — v — w` gives the same labelled comb with the roles of the two end
branch vertices exchanged. -/
theorem combSlots_reverse {G : SimpleGraph V} {x y z p q u v w : V}
    (h : CombSlots G x y z p q u v w) : CombSlots G p q z x y w v u := by
  obtain ⟨p0, p1, p2, p3, p4, s1, s2, hnd⟩ := h
  obtain ⟨h0, h1, h2, h3, h4, hs1, hs2, d01, d02, d03, d04, d05, d06, d12, d13, d14, d15,
    d16, d23, d24, d25, d26, d34, d35, d36, d45, d46, d56⟩ := nodup_append7_facts hnd
  refine ⟨p3, p4, p2, p0, p1, s2.reverse, s1.reverse, ?_⟩
  rw [SimpleGraph.Walk.edges_reverse, SimpleGraph.Walk.edges_reverse]
  exact nodup_seven h3 h4 h2 h0 h1 (List.nodup_reverse.mpr hs2) (List.nodup_reverse.mpr hs1)
    d34 d23.symm d03.symm d13.symm (List.disjoint_reverse_right.mpr d36)
    (List.disjoint_reverse_right.mpr d35) d24.symm d04.symm d14.symm
    (List.disjoint_reverse_right.mpr d46) (List.disjoint_reverse_right.mpr d45) d02.symm d12.symm
    (List.disjoint_reverse_right.mpr d26) (List.disjoint_reverse_right.mpr d25) d01
    (List.disjoint_reverse_right.mpr d06) (List.disjoint_reverse_right.mpr d05)
    (List.disjoint_reverse_right.mpr d16) (List.disjoint_reverse_right.mpr d15)
    (List.disjoint_reverse_left.mpr (List.disjoint_reverse_right.mpr d56.symm))

/-! ## Attaching a fifth terminal to the four-terminal structure -/

theorem attachAny {G : SimpleGraph V} {b0 b1 b2 b3 t u v : V}
    (h : Slots4 G b0 b1 b2 b3 u v) (M : G.Walk t b0) :
    (∃ c, CombSlots G b0 t b1 b2 b3 c u v) ∨
      (∃ c, CombSlots G b1 t b0 b2 b3 c u v) ∨
      (∃ c, CombSlots G b0 b1 b3 b2 t u v c) ∨
      (∃ c, CombSlots G b0 b1 b2 b3 t u v c) ∨
      (∃ c, CombSlots G b0 b1 t b2 b3 u c v) := by
  classical
  obtain ⟨p0, p1, p2, p3, s, hnd⟩ := h
  obtain ⟨n0, n1, n2, n3, ns, d01, d02, d03, d04, d12, d13, d14, d23, d24, d34⟩ :=
    nodup_append5_facts hnd
  obtain ⟨c, hcS, P', hP'⟩ :=
    exists_first_hit {x | x ∈ p0.support ∨ x ∈ p1.support ∨ x ∈ p2.support ∨
      x ∈ p3.support ∨ x ∈ s.support} (M.append p0)
      (by
        simp only [Set.mem_ofPred_eq]
        exact Or.inl (SimpleGraph.Walk.end_mem_support p0))
  have hNb : P'.bypass.edges.Nodup :=
    SimpleGraph.Walk.edges_nodup_of_support_nodup (SimpleGraph.Walk.bypass_isPath P').support_nodup
  have hNf : ∀ x, x ∈ P'.bypass.support →
      (x ∈ p0.support ∨ x ∈ p1.support ∨ x ∈ p2.support ∨ x ∈ p3.support ∨
        x ∈ s.support) → x = c :=
    fun x hx hxs => hP' x (SimpleGraph.Walk.support_bypass_subset_support P' hx) hxs
  have ndisj : ∀ {a b : V} (w : G.Walk a b),
      (∀ x, x ∈ w.support → (x ∈ p0.support ∨ x ∈ p1.support ∨ x ∈ p2.support ∨
        x ∈ p3.support ∨ x ∈ s.support)) → P'.bypass.edges.Disjoint w.edges :=
    fun w hw => edges_disjoint_of_support_unique P'.bypass w hNf hw
  have sp0 : ∀ x, x ∈ p0.support →
      (x ∈ p0.support ∨ x ∈ p1.support ∨ x ∈ p2.support ∨ x ∈ p3.support ∨ x ∈ s.support) :=
    fun x hx => Or.inl hx
  have sp1 : ∀ x, x ∈ p1.support →
      (x ∈ p0.support ∨ x ∈ p1.support ∨ x ∈ p2.support ∨ x ∈ p3.support ∨ x ∈ s.support) :=
    fun x hx => Or.inr (Or.inl hx)
  have sp2 : ∀ x, x ∈ p2.support →
      (x ∈ p0.support ∨ x ∈ p1.support ∨ x ∈ p2.support ∨ x ∈ p3.support ∨ x ∈ s.support) :=
    fun x hx => Or.inr (Or.inr (Or.inl hx))
  have sp3 : ∀ x, x ∈ p3.support →
      (x ∈ p0.support ∨ x ∈ p1.support ∨ x ∈ p2.support ∨ x ∈ p3.support ∨ x ∈ s.support) :=
    fun x hx => Or.inr (Or.inr (Or.inr (Or.inl hx)))
  have sps : ∀ x, x ∈ s.support →
      (x ∈ p0.support ∨ x ∈ p1.support ∨ x ∈ p2.support ∨ x ∈ p3.support ∨ x ∈ s.support) :=
    fun x hx => Or.inr (Or.inr (Or.inr (Or.inr hx)))
  rcases hcS with hc | hc | hc | hc | hc
  · -- the fifth terminal lands on the first arm `b0 → u`
    have hTill : (p0.takeUntil c hc).edges ⊆ p0.edges :=
      SimpleGraph.Walk.edges_takeUntil_subset_edges p0 hc
    have hDrop : (p0.dropUntil c hc).edges ⊆ p0.edges :=
      SimpleGraph.Walk.edges_dropUntil_subset_edges p0 hc
    have hsplit : ((p0.takeUntil c hc).edges ++ (p0.dropUntil c hc).edges).Nodup := by
      rw [← SimpleGraph.Walk.edges_append, SimpleGraph.Walk.take_spec]
      exact n0
    refine Or.inl ⟨c, p0.takeUntil c hc, P'.bypass, p1, p2, p3, p0.dropUntil c hc, s, ?_⟩
    exact nodup_seven (List.Nodup.of_append_left hsplit) hNb n1 n2 n3
      (List.Nodup.of_append_right hsplit) ns
      (ndisj _ (fun x hx => sp0 x (SimpleGraph.Walk.support_takeUntil_subset_support p0 hc hx))).symm
      (disjoint_of_subset_left hTill d01) (disjoint_of_subset_left hTill d02)
      (disjoint_of_subset_left hTill d03)
      (List.disjoint_of_nodup_append hsplit)
      (disjoint_of_subset_left hTill d04)
      (ndisj _ sp1) (ndisj _ sp2) (ndisj _ sp3)
      (ndisj _ (fun x hx => sp0 x (SimpleGraph.Walk.support_dropUntil_subset_support p0 hc hx)))
      (ndisj _ sps)
      d12 d13 (disjoint_of_subset_right hDrop d01.symm) d14
      d23 (disjoint_of_subset_right hDrop d02.symm) d24
      (disjoint_of_subset_right hDrop d03.symm) d34
      (disjoint_of_subset_left hDrop d04)
  · -- the fifth terminal lands on the second arm `b1 → u`
    have hTill : (p1.takeUntil c hc).edges ⊆ p1.edges :=
      SimpleGraph.Walk.edges_takeUntil_subset_edges p1 hc
    have hDrop : (p1.dropUntil c hc).edges ⊆ p1.edges :=
      SimpleGraph.Walk.edges_dropUntil_subset_edges p1 hc
    have hsplit : ((p1.takeUntil c hc).edges ++ (p1.dropUntil c hc).edges).Nodup := by
      rw [← SimpleGraph.Walk.edges_append, SimpleGraph.Walk.take_spec]
      exact n1
    refine Or.inr (Or.inl ⟨c, p1.takeUntil c hc, P'.bypass, p0, p2, p3, p1.dropUntil c hc, s, ?_⟩)
    exact nodup_seven (List.Nodup.of_append_left hsplit) hNb n0 n2 n3
      (List.Nodup.of_append_right hsplit) ns
      (ndisj _ (fun x hx => sp1 x (SimpleGraph.Walk.support_takeUntil_subset_support p1 hc hx))).symm
      (disjoint_of_subset_left hTill d01.symm) (disjoint_of_subset_left hTill d12)
      (disjoint_of_subset_left hTill d13)
      (List.disjoint_of_nodup_append hsplit)
      (disjoint_of_subset_left hTill d14)
      (ndisj _ sp0) (ndisj _ sp2) (ndisj _ sp3)
      (ndisj _ (fun x hx => sp1 x (SimpleGraph.Walk.support_dropUntil_subset_support p1 hc hx)))
      (ndisj _ sps)
      d02 d03 (disjoint_of_subset_right hDrop d01) d04
      d23 (disjoint_of_subset_right hDrop d12.symm) d24
      (disjoint_of_subset_right hDrop d13.symm) d34
      (disjoint_of_subset_left hDrop d14)
  · -- the fifth terminal lands on the arm `b2 → v`: the spine is read from the `v` end
    have hTill : (p2.takeUntil c hc).edges ⊆ p2.edges :=
      SimpleGraph.Walk.edges_takeUntil_subset_edges p2 hc
    have hDrop : (p2.dropUntil c hc).edges ⊆ p2.edges :=
      SimpleGraph.Walk.edges_dropUntil_subset_edges p2 hc
    have hsplit : ((p2.takeUntil c hc).edges ++ (p2.dropUntil c hc).edges).Nodup := by
      rw [← SimpleGraph.Walk.edges_append, SimpleGraph.Walk.take_spec]
      exact n2
    refine Or.inr (Or.inr (Or.inl ⟨c, p0, p1, p3, p2.takeUntil c hc, P'.bypass, s, (p2.dropUntil c hc).reverse, ?_⟩))
    rw [SimpleGraph.Walk.edges_reverse]
    exact nodup_seven n0 n1 n3 (List.Nodup.of_append_left hsplit) hNb ns
      (List.nodup_reverse.mpr (List.Nodup.of_append_right hsplit))
      d01 d03 (disjoint_of_subset_right hTill d02) (ndisj _ sp0).symm d04
      (List.disjoint_reverse_right.mpr (disjoint_of_subset_right hDrop d02))
      d13 (disjoint_of_subset_right hTill d12) (ndisj _ sp1).symm d14
      (List.disjoint_reverse_right.mpr (disjoint_of_subset_right hDrop d12))
      (disjoint_of_subset_right hTill d23.symm) (ndisj _ sp3).symm d34
      (List.disjoint_reverse_right.mpr (disjoint_of_subset_right hDrop d23.symm))
      (ndisj _ (fun x hx => sp2 x (SimpleGraph.Walk.support_takeUntil_subset_support p2 hc hx))).symm
      (disjoint_of_subset_left hTill d24)
      (List.disjoint_reverse_right.mpr (List.disjoint_of_nodup_append hsplit))
      (ndisj _ sps)
      (List.disjoint_reverse_right.mpr
        (ndisj _ (fun x hx => sp2 x (SimpleGraph.Walk.support_dropUntil_subset_support p2 hc hx))))
      (List.disjoint_reverse_right.mpr (disjoint_of_subset_left hDrop d24).symm)
  · -- the fifth terminal lands on the arm `b3 → v`
    have hTill : (p3.takeUntil c hc).edges ⊆ p3.edges :=
      SimpleGraph.Walk.edges_takeUntil_subset_edges p3 hc
    have hDrop : (p3.dropUntil c hc).edges ⊆ p3.edges :=
      SimpleGraph.Walk.edges_dropUntil_subset_edges p3 hc
    have hsplit : ((p3.takeUntil c hc).edges ++ (p3.dropUntil c hc).edges).Nodup := by
      rw [← SimpleGraph.Walk.edges_append, SimpleGraph.Walk.take_spec]
      exact n3
    refine Or.inr (Or.inr (Or.inr (Or.inl ⟨c, p0, p1, p2, p3.takeUntil c hc, P'.bypass, s, (p3.dropUntil c hc).reverse, ?_⟩)))
    rw [SimpleGraph.Walk.edges_reverse]
    exact nodup_seven n0 n1 n2 (List.Nodup.of_append_left hsplit) hNb ns
      (List.nodup_reverse.mpr (List.Nodup.of_append_right hsplit))
      d01 d02 (disjoint_of_subset_right hTill d03) (ndisj _ sp0).symm d04
      (List.disjoint_reverse_right.mpr (disjoint_of_subset_right hDrop d03))
      d12 (disjoint_of_subset_right hTill d13) (ndisj _ sp1).symm d14
      (List.disjoint_reverse_right.mpr (disjoint_of_subset_right hDrop d13))
      (disjoint_of_subset_right hTill d23) (ndisj _ sp2).symm d24
      (List.disjoint_reverse_right.mpr (disjoint_of_subset_right hDrop d23))
      (ndisj _ (fun x hx => sp3 x (SimpleGraph.Walk.support_takeUntil_subset_support p3 hc hx))).symm
      (disjoint_of_subset_left hTill d34)
      (List.disjoint_reverse_right.mpr (List.disjoint_of_nodup_append hsplit))
      (ndisj _ sps)
      (List.disjoint_reverse_right.mpr
        (ndisj _ (fun x hx => sp3 x (SimpleGraph.Walk.support_dropUntil_subset_support p3 hc hx))))
      (List.disjoint_reverse_right.mpr (disjoint_of_subset_left hDrop d34).symm)
  · -- the fifth terminal lands on the spine
    have hTill : (s.takeUntil c hc).edges ⊆ s.edges :=
      SimpleGraph.Walk.edges_takeUntil_subset_edges s hc
    have hDrop : (s.dropUntil c hc).edges ⊆ s.edges :=
      SimpleGraph.Walk.edges_dropUntil_subset_edges s hc
    have hsplit : ((s.takeUntil c hc).edges ++ (s.dropUntil c hc).edges).Nodup := by
      rw [← SimpleGraph.Walk.edges_append, SimpleGraph.Walk.take_spec]
      exact ns
    refine Or.inr (Or.inr (Or.inr (Or.inr ⟨c, p0, p1, P'.bypass, p2, p3, s.takeUntil c hc, s.dropUntil c hc, ?_⟩)))
    exact nodup_seven n0 n1 hNb n2 n3
      (List.Nodup.of_append_left hsplit) (List.Nodup.of_append_right hsplit)
      d01 (ndisj _ sp0).symm d02 d03
      (disjoint_of_subset_right hTill d04) (disjoint_of_subset_right hDrop d04)
      (ndisj _ sp1).symm d12 d13
      (disjoint_of_subset_right hTill d14) (disjoint_of_subset_right hDrop d14)
      (ndisj _ sp2) (ndisj _ sp3)
      (ndisj _ (fun x hx => sps x (SimpleGraph.Walk.support_takeUntil_subset_support s hc hx)))
      (ndisj _ (fun x hx => sps x (SimpleGraph.Walk.support_dropUntil_subset_support s hc hx)))
      d23 (disjoint_of_subset_right hTill d24) (disjoint_of_subset_right hDrop d24)
      (disjoint_of_subset_right hTill d34) (disjoint_of_subset_right hDrop d34)
      (List.disjoint_of_nodup_append hsplit)

/-- `CombShape` from a slot pattern equal to `pat k` up to the order of the terminal variables. -/
theorem combShape_of_pat {G : SimpleGraph V} {T : Fin 5 → V} {u v w : V} {k : Fin 15}
    {bIdx : Fin 5 → Fin 5} (hk : ∀ i, pat k i = bIdx i)
    (h : CombSlots G (T (bIdx 0)) (T (bIdx 1)) (T (bIdx 2)) (T (bIdx 3)) (T (bIdx 4)) u v w) :
    CombShape G k u v w T := by
  simp only [CombShape]
  rw [show pat k = bIdx from funext hk]
  exact h

/-! ## The universal five-vertex cover: one of the fifteen labelled combs is realised -/

theorem exists_combShape {G : SimpleGraph V} (T : Fin 5 → V)
    (h : ∀ i, G.Reachable (T 0) (T i)) : ∃ k : Fin 15, ∃ u v w, CombShape G k u v w T := by
  classical
  obtain ⟨M⟩ : Nonempty (G.Walk (T 0) (T 1)) := h 1
  have h4 : ∀ i : Fin 4, G.Reachable ((fun j : Fin 4 => T j.succ) 0) ((fun j : Fin 4 => T j.succ) i) :=
    fun i => (h 1).symm.trans (h i.succ)
  rcases exists_slots4 (fun j : Fin 4 => T j.succ) h4 with ⟨u, v, hsl⟩ | ⟨u, v, hsl⟩ |
    ⟨u, v, hsl⟩
  · rcases attachAny hsl M with ⟨c, hc⟩ | ⟨c, hc⟩ | ⟨c, hc⟩ | ⟨c, hc⟩ | ⟨c, hc⟩
    · exact ⟨6, c, u, v, combShape_of_pat (k := 6) (bIdx := ![0, 1, 2, 3, 4])
        (by decide) (combSlots_swap01 hc)⟩
    · exact ⟨3, c, u, v, combShape_of_pat (k := 3) (bIdx := ![0, 2, 1, 3, 4])
        (by decide) (combSlots_swap01 hc)⟩
    · exact ⟨14, c, v, u, combShape_of_pat (k := 14) (bIdx := ![0, 3, 4, 1, 2])
        (by decide) (combSlots_reverse (combSlots_swap34 hc))⟩
    · exact ⟨11, c, v, u, combShape_of_pat (k := 11) (bIdx := ![0, 4, 3, 1, 2])
        (by decide) (combSlots_reverse (combSlots_swap34 hc))⟩
    · exact ⟨0, u, c, v, combShape_of_pat (k := 0) (bIdx := ![1, 2, 0, 3, 4])
        (by decide) hc⟩
  · rcases attachAny hsl M with ⟨c, hc⟩ | ⟨c, hc⟩ | ⟨c, hc⟩ | ⟨c, hc⟩ | ⟨c, hc⟩
    · exact ⟨9, c, u, v, combShape_of_pat (k := 9) (bIdx := ![0, 1, 3, 2, 4])
        (by decide) (combSlots_swap01 hc)⟩
    · exact ⟨4, c, u, v, combShape_of_pat (k := 4) (bIdx := ![0, 3, 1, 2, 4])
        (by decide) (combSlots_swap01 hc)⟩
    · exact ⟨13, c, v, u, combShape_of_pat (k := 13) (bIdx := ![0, 2, 4, 1, 3])
        (by decide) (combSlots_reverse (combSlots_swap34 hc))⟩
    · exact ⟨8, c, v, u, combShape_of_pat (k := 8) (bIdx := ![0, 4, 2, 1, 3])
        (by decide) (combSlots_reverse (combSlots_swap34 hc))⟩
    · exact ⟨1, u, c, v, combShape_of_pat (k := 1) (bIdx := ![1, 3, 0, 2, 4])
        (by decide) hc⟩
  · rcases attachAny hsl M with ⟨c, hc⟩ | ⟨c, hc⟩ | ⟨c, hc⟩ | ⟨c, hc⟩ | ⟨c, hc⟩
    · exact ⟨12, c, u, v, combShape_of_pat (k := 12) (bIdx := ![0, 1, 4, 2, 3])
        (by decide) (combSlots_swap01 hc)⟩
    · exact ⟨5, c, u, v, combShape_of_pat (k := 5) (bIdx := ![0, 4, 1, 2, 3])
        (by decide) (combSlots_swap01 hc)⟩
    · exact ⟨10, c, v, u, combShape_of_pat (k := 10) (bIdx := ![0, 2, 3, 1, 4])
        (by decide) (combSlots_reverse (combSlots_swap34 hc))⟩
    · exact ⟨7, c, v, u, combShape_of_pat (k := 7) (bIdx := ![0, 3, 2, 1, 4])
        (by decide) (combSlots_reverse (combSlots_swap34 hc))⟩
    · exact ⟨2, u, c, v, combShape_of_pat (k := 2) (bIdx := ![1, 4, 0, 2, 3])
        (by decide) hc⟩

/-- The native five-point form: if `o, x₁, x₂, x₃, x₄` lie in one open cluster, one of the fifteen
labelled five-leaf combs is realised in the open graph.  This is the deterministic input of the
`k = 4` tree-graph inequality. -/
theorem exists_combShape_connects [Countable V] (ω : Config V) (o x1 x2 x3 x4 : V)
    (h1 : PercLib.CriticalLRP.Connects ω o x1) (h2 : PercLib.CriticalLRP.Connects ω o x2)
    (h3 : PercLib.CriticalLRP.Connects ω o x3) (h4 : PercLib.CriticalLRP.Connects ω o x4) :
    ∃ k : Fin 15, ∃ u v w, CombShape (openGraph ω) k u v w ![o, x1, x2, x3, x4] := by
  refine exists_combShape ![o, x1, x2, x3, x4] ?_
  intro i
  fin_cases i
  · exact SimpleGraph.Reachable.rfl
  · exact h1
  · exact h2
  · exact h3
  · exact h4

/-- **The fifteen labelled combs split as `12 + 3`.**  In twelve of the fifteen slot patterns the
origin (terminal `0`, by convention the root) is a leaf at the *first* branch vertex `u` — these are
the twelve combs of the source's count — and in three it is the leaf at the *middle* branch vertex
`v` — the balanced shapes. -/
theorem card_root_at_first :
    (Finset.univ.filter (fun k : Fin 15 => pat k 0 = 0)).card = 12 := by
  decide

theorem card_root_at_middle :
    (Finset.univ.filter (fun k : Fin 15 => pat k 2 = 0)).card = 3 := by
  decide

/-- The fifteen slot patterns partition the fifteen patterns: every `k` has the root in slot `0`
(twelve of them) or in slot `2` (three of them). -/
theorem root_slot_cases : ∀ k : Fin 15, pat k 0 = 0 ∨ pat k 2 = 0 := by
  decide

/-- Each of the fifteen slot patterns is a permutation of the five terminals. -/
theorem pat_bijective : ∀ k : Fin 15, Function.Bijective (pat k) := by
  decide

end PercLib.CriticalLRP.TreeExpansion.FivePoint
