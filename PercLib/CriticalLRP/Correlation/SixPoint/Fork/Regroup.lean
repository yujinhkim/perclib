/-
Swarm `smwprafq1`, member `m2` (direction B: event/BK side of `p = 5`, `k = 1`).

# The sevenfold BK kit and the fork regrouping

Two independent pieces:

* `sevenCert_le`: seven increasing events certified by seven pairwise disjoint finite open
  sets have probability at most the product of the seven probabilities (sevenfold BK at the
  native countable law).
* `forkSlots_subset_sevenCert`: the nine-arm six-terminal fork slot realization yields a
  seven-group certificate in which group `0` is the **joint pair** `conn b0 a ∩ conn b1 a`
  (kept joint — never split into `tau * tau`) and groups `1 … 6` are the six two-point
  groups.  The three other branch vertices `u`, `v`, `w` are eliminated by monotone
  weakening inside the union bound, so no sum over them is ever taken.
-/
module

public import PercLib.CriticalLRP.Correlation.SixPoint.Fork.Defs

set_option autoImplicit false

open Set MeasureTheory
open scoped ENNReal BigOperators
open PercLib.Percolation.Bond
open PercLib.Probability

@[expose] public section

namespace PercLib.CriticalLRP.TreeExpansion.FivePoint

variable {V : Type*}

/-! ### Sevenfold BK in grouped form -/

/-- **Sevenfold BK, grouped form.**  Seven increasing events with seven pairwise disjoint
finite certificates have probability at most the product of their probabilities. -/
theorem sevenCert_le [Countable V] (π : Sym2 V → unitInterval)
    {A₀ A₁ A₂ A₃ A₄ A₅ A₆ : Set (Config V)}
    (h₀ : IsUpperSet A₀) (h₁ : IsUpperSet A₁) (h₂ : IsUpperSet A₂) (h₃ : IsUpperSet A₃)
    (h₄ : IsUpperSet A₄) (h₅ : IsUpperSet A₅) (h₆ : IsUpperSet A₆) :
    law π (SevenCertEvent A₀ A₁ A₂ A₃ A₄ A₅ A₆) ≤
      law π A₀ * (law π A₁ * (law π A₂ * (law π A₃ * (law π A₄ * (law π A₅ * law π A₆))))) := by
  have h := prodBernoulli_seven_wit_le (p := π) h₀ h₁ h₂ h₃ h₄ h₅ h₆
  simpa only [law, SevenCertEvent] using h

/-! ### Peeling a `Nodup` flattening into pairwise disjoint blocks -/

theorem nodup_cons_blocks {α : Type*} {l : List α} {ls : List (List α)}
    (h : (l :: ls).flatten.Nodup) :
    l.Nodup ∧ ls.flatten.Nodup ∧ ∀ m ∈ ls, l.Disjoint m := by
  rw [List.flatten_cons] at h
  obtain ⟨hl, hls, hd⟩ := List.nodup_append'.mp h
  refine ⟨hl, hls, fun m hm => ?_⟩
  rw [List.disjoint_left] at hd ⊢
  intro e he hem
  exact hd he (List.mem_flatten.mpr ⟨m, hm, hem⟩)

/-- **The regrouping of the nine fork arms into seven certified groups.**

`u` is eliminated because the fork's certificate `p0 ++ t0` and `p1 ++ t0` already connects
`b0` and `b1` to the pair centre `a`; `v` and `w` do not occur in the conclusion at all. -/
theorem forkSlots_subset_sevenCert [Countable V] {ω : Config V} {b0 b1 b2 b3 b4 y u a v w : V}
    (h : ForkSlots ω b0 b1 b2 b3 b4 y u a v w) :
    ω ∈ SevenCertEvent (V := V) (conn b0 a ∩ conn b1 a) (conn a v) (conn b2 v) (conn v w)
      (conn b3 w) (conn b4 w) (conn y a) := by
  obtain ⟨p0, p1, t0, t1, p2, s2, p3, p4, p5, hnd⟩ := h
  have hnd' : ([p0.edges, p1.edges, t0.edges, t1.edges, p2.edges, s2.edges, p3.edges,
      p4.edges, p5.edges] : List (List (Sym2 V))).flatten.Nodup := by
    simpa using hnd
  obtain ⟨-, hR1, d0⟩ := nodup_cons_blocks (l := p0.edges)
    (ls := [p1.edges, t0.edges, t1.edges, p2.edges, s2.edges, p3.edges, p4.edges, p5.edges]) hnd'
  obtain ⟨-, hR2, d1⟩ := nodup_cons_blocks (l := p1.edges)
    (ls := [t0.edges, t1.edges, p2.edges, s2.edges, p3.edges, p4.edges, p5.edges]) hR1
  obtain ⟨-, hR3, d2⟩ := nodup_cons_blocks (l := t0.edges)
    (ls := [t1.edges, p2.edges, s2.edges, p3.edges, p4.edges, p5.edges]) hR2
  obtain ⟨-, hR4, d3⟩ := nodup_cons_blocks (l := t1.edges)
    (ls := [p2.edges, s2.edges, p3.edges, p4.edges, p5.edges]) hR3
  obtain ⟨-, hR5, d4⟩ := nodup_cons_blocks (l := p2.edges)
    (ls := [s2.edges, p3.edges, p4.edges, p5.edges]) hR4
  obtain ⟨-, hR6, d5⟩ := nodup_cons_blocks (l := s2.edges)
    (ls := [p3.edges, p4.edges, p5.edges]) hR5
  obtain ⟨-, hR7, d6⟩ := nodup_cons_blocks (l := p3.edges)
    (ls := [p4.edges, p5.edges]) hR6
  obtain ⟨-, -, d7⟩ := nodup_cons_blocks (l := p4.edges) (ls := [p5.edges]) hR7
  -- the fork certificate, against each of the six single arms
  have e01 : Disjoint (walkEdges (p0.append t0) ∪ walkEdges (p1.append t0))
      (walkEdges t1) :=
    disjoint_union_left.mpr
      ⟨disjoint_walkEdges_append_left p0 t0 t1 (d0 _ (by simp)) (d2 _ (by simp)),
       disjoint_walkEdges_append_left p1 t0 t1 (d1 _ (by simp)) (d2 _ (by simp))⟩
  have e02 : Disjoint (walkEdges (p0.append t0) ∪ walkEdges (p1.append t0))
      (walkEdges p2) :=
    disjoint_union_left.mpr
      ⟨disjoint_walkEdges_append_left p0 t0 p2 (d0 _ (by simp)) (d2 _ (by simp)),
       disjoint_walkEdges_append_left p1 t0 p2 (d1 _ (by simp)) (d2 _ (by simp))⟩
  have e03 : Disjoint (walkEdges (p0.append t0) ∪ walkEdges (p1.append t0))
      (walkEdges s2) :=
    disjoint_union_left.mpr
      ⟨disjoint_walkEdges_append_left p0 t0 s2 (d0 _ (by simp)) (d2 _ (by simp)),
       disjoint_walkEdges_append_left p1 t0 s2 (d1 _ (by simp)) (d2 _ (by simp))⟩
  have e04 : Disjoint (walkEdges (p0.append t0) ∪ walkEdges (p1.append t0))
      (walkEdges p3) :=
    disjoint_union_left.mpr
      ⟨disjoint_walkEdges_append_left p0 t0 p3 (d0 _ (by simp)) (d2 _ (by simp)),
       disjoint_walkEdges_append_left p1 t0 p3 (d1 _ (by simp)) (d2 _ (by simp))⟩
  have e05 : Disjoint (walkEdges (p0.append t0) ∪ walkEdges (p1.append t0))
      (walkEdges p4) :=
    disjoint_union_left.mpr
      ⟨disjoint_walkEdges_append_left p0 t0 p4 (d0 _ (by simp)) (d2 _ (by simp)),
       disjoint_walkEdges_append_left p1 t0 p4 (d1 _ (by simp)) (d2 _ (by simp))⟩
  have e06 : Disjoint (walkEdges (p0.append t0) ∪ walkEdges (p1.append t0))
      (walkEdges p5) :=
    disjoint_union_left.mpr
      ⟨disjoint_walkEdges_append_left p0 t0 p5 (d0 _ (by simp)) (d2 _ (by simp)),
       disjoint_walkEdges_append_left p1 t0 p5 (d1 _ (by simp)) (d2 _ (by simp))⟩
  -- the six single arms among themselves
  have e12 : Disjoint (walkEdges t1) (walkEdges p2) :=
    disjoint_walkEdges t1 p2 (d3 _ (by simp))
  have e13 : Disjoint (walkEdges t1) (walkEdges s2) :=
    disjoint_walkEdges t1 s2 (d3 _ (by simp))
  have e14 : Disjoint (walkEdges t1) (walkEdges p3) :=
    disjoint_walkEdges t1 p3 (d3 _ (by simp))
  have e15 : Disjoint (walkEdges t1) (walkEdges p4) :=
    disjoint_walkEdges t1 p4 (d3 _ (by simp))
  have e16 : Disjoint (walkEdges t1) (walkEdges p5) :=
    disjoint_walkEdges t1 p5 (d3 _ (by simp))
  have e23 : Disjoint (walkEdges p2) (walkEdges s2) :=
    disjoint_walkEdges p2 s2 (d4 _ (by simp))
  have e24 : Disjoint (walkEdges p2) (walkEdges p3) :=
    disjoint_walkEdges p2 p3 (d4 _ (by simp))
  have e25 : Disjoint (walkEdges p2) (walkEdges p4) :=
    disjoint_walkEdges p2 p4 (d4 _ (by simp))
  have e26 : Disjoint (walkEdges p2) (walkEdges p5) :=
    disjoint_walkEdges p2 p5 (d4 _ (by simp))
  have e34 : Disjoint (walkEdges s2) (walkEdges p3) :=
    disjoint_walkEdges s2 p3 (d5 _ (by simp))
  have e35 : Disjoint (walkEdges s2) (walkEdges p4) :=
    disjoint_walkEdges s2 p4 (d5 _ (by simp))
  have e36 : Disjoint (walkEdges s2) (walkEdges p5) :=
    disjoint_walkEdges s2 p5 (d5 _ (by simp))
  have e45 : Disjoint (walkEdges p3) (walkEdges p4) :=
    disjoint_walkEdges p3 p4 (d6 _ (by simp))
  have e46 : Disjoint (walkEdges p3) (walkEdges p5) :=
    disjoint_walkEdges p3 p5 (d6 _ (by simp))
  have e56 : Disjoint (walkEdges p4) (walkEdges p5) :=
    disjoint_walkEdges p4 p5 (d7 _ (by simp))
  refine ⟨walkEdges (p0.append t0) ∪ walkEdges (p1.append t0), walkEdges t1, walkEdges p2,
    walkEdges s2, walkEdges p3, walkEdges p4, walkEdges p5,
    (walkEdges_finite (p0.append t0)).union (walkEdges_finite (p1.append t0)),
    walkEdges_finite t1, walkEdges_finite p2, walkEdges_finite s2, walkEdges_finite p3,
    walkEdges_finite p4, walkEdges_finite p5,
    union_subset (walkEdges_subset (p0.append t0)) (walkEdges_subset (p1.append t0)),
    walkEdges_subset t1, walkEdges_subset p2, walkEdges_subset s2, walkEdges_subset p3,
    walkEdges_subset p4, walkEdges_subset p5,
    ⟨conn_mono subset_union_left (mem_conn_walkEdges (p0.append t0)),
      conn_mono subset_union_right (mem_conn_walkEdges (p1.append t0))⟩,
    mem_conn_walkEdges t1, mem_conn_walkEdges p2, mem_conn_walkEdges s2,
    mem_conn_walkEdges p3, mem_conn_walkEdges p4, mem_conn_walkEdges p5,
    e01, e02, e03, e04, e05, e06, e12, e13, e14, e15, e16, e23, e24, e25, e26, e34, e35,
    e36, e45, e46, e56⟩

/-- With the pair centre `a` and the two lower hubs `v`, `w` fixed, the remaining branch
vertex `u` is eliminated by the union bound: the fork realization is contained in the
seven-group certificate event. -/
theorem forkSlots_union_subset_sevenCert [Countable V] (b0 b1 b2 b3 b4 y a v w : V) :
    (⋃ u : V, {ω | ForkSlots ω b0 b1 b2 b3 b4 y u a v w}) ⊆
      SevenCertEvent (V := V) (conn b0 a ∩ conn b1 a) (conn a v) (conn b2 v) (conn v w)
        (conn b3 w) (conn b4 w) (conn y a) := by
  intro ω h
  obtain ⟨u, hu⟩ := Set.mem_iUnion.mp h
  exact forkSlots_subset_sevenCert hu

/-- **The per-centre fork event bound.**  One joint pair (at the fixed centre `a`) plus six
two-point groups; `u` disappears inside the pair certificate, and `v`, `w` remain as free hub
variables whose sums are taken outside. -/
theorem forkSlots_event_le [Countable V] (π : Sym2 V → unitInterval) (b0 b1 b2 b3 b4 y a v w : V) :
    law π (⋃ u : V, {ω | ForkSlots ω b0 b1 b2 b3 b4 y u a v w}) ≤
      law π (conn b0 a ∩ conn b1 a) *
        (law π (conn a v) * (law π (conn b2 v) * (law π (conn v w) *
          (law π (conn b3 w) * (law π (conn b4 w) * law π (conn y a)))))) :=
  (measure_mono (forkSlots_union_subset_sevenCert b0 b1 b2 b3 b4 y a v w)).trans
    (sevenCert_le (V := V) π (isUpperSet_inter_conn b0 b1 a)
      (isIncreasing_connects a v) (isIncreasing_connects b2 v) (isIncreasing_connects v w)
      (isIncreasing_connects b3 w) (isIncreasing_connects b4 w) (isIncreasing_connects y a))

/-- **The fork shape event is bounded by the fork slot diagram.**  The three branch vertices
`a`, `v`, `w` are summed as hub variables; no sum over `u` is ever taken. -/
theorem forkEvent_le_diagram [Countable V] (π : Sym2 V → unitInterval)
    (b0 b1 b2 b3 b4 y : V) :
    law π (ForkEvent b0 b1 b2 b3 b4 y) ≤ forkDiagram π b0 b1 b2 b3 b4 y := by
  have hset : ForkEvent b0 b1 b2 b3 b4 y =
      ⋃ a, ⋃ v, ⋃ w, ⋃ u : V, {ω | ForkSlots ω b0 b1 b2 b3 b4 y u a v w} := by
    ext ω
    simp only [ForkEvent, Set.mem_iUnion]
    exact ⟨fun ⟨u, a, v, w, h⟩ => ⟨a, v, w, u, h⟩, fun ⟨a, v, w, u, h⟩ => ⟨u, a, v, w, h⟩⟩
  rw [hset]
  refine (measure_iUnion_le (μ := law π) (s := fun a : V => ⋃ v, ⋃ w, ⋃ u : V,
    {ω | ForkSlots ω b0 b1 b2 b3 b4 y u a v w})).trans ?_
  refine ENNReal.tsum_le_tsum fun a => ?_
  refine (measure_iUnion_le (μ := law π) (s := fun v : V => ⋃ w, ⋃ u : V,
    {ω | ForkSlots ω b0 b1 b2 b3 b4 y u a v w})).trans ?_
  refine ENNReal.tsum_le_tsum fun v => ?_
  refine (measure_iUnion_le (μ := law π) (s := fun w : V => ⋃ u : V,
    {ω | ForkSlots ω b0 b1 b2 b3 b4 y u a v w})).trans ?_
  refine ENNReal.tsum_le_tsum fun w => ?_
  have h := forkSlots_event_le (V := V) π b0 b1 b2 b3 b4 y a v w
  simpa only [forkDiagram, jointP, tau] using h

end PercLib.CriticalLRP.TreeExpansion.FivePoint
