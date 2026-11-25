/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Six-terminal deterministic cover for the `p = 5`, `k = 1` mixed moment.
Supplied by Ultramath `smwprafq1` member `m1` (direction d1).

**Main result.**  If six vertices `T 0, …, T 5` lie in a common component of the open graph,
then for some five-terminal pattern `k : Fin 15`, some arm `j : Fin 7` of the seven-arm comb on
`T 0, …, T 4`, and some landing point `c` on arm `j`, the six-terminal arm system `SixShape` holds.
Hence the `15 * 7 = 105` indices cover every connected six-terminal configuration, matching the
coefficient `(2 * 5 - 3)!! = 105` of Lemma I.4.16 at `p = 5`.
-/
module

public import PercLib.CriticalLRP.Correlation.FourthMoment.MixedK2.Final
public import PercLib.CriticalLRP.Correlation.SixPoint.Attachment.Defs

open Set MeasureTheory
open scoped ENNReal
open PercLib.Percolation.Bond
open PercLib.CriticalLRP.TreeExpansion.FivePoint

@[expose] public section

namespace PercLib.CriticalLRP.TreeExpansion.SixPoint

variable {V : Type*}

/-! ## Appending the eighth arm to a `Nodup` seven-fold concatenation -/

theorem nodup_append8_of {α : Type*} {a b c d e f g q : List α}
    (h : (a ++ b ++ c ++ d ++ e ++ f ++ g).Nodup) (hq : q.Nodup)
    (ha : q.Disjoint a) (hb : q.Disjoint b) (hc : q.Disjoint c) (hd : q.Disjoint d)
    (he : q.Disjoint e) (hf : q.Disjoint f) (hg : q.Disjoint g) :
    (a ++ b ++ c ++ d ++ e ++ f ++ g ++ q).Nodup := by
  have h1 : q.Disjoint (a ++ b) := disjoint_append_right_of ha hb
  have h2 : q.Disjoint (a ++ b ++ c) := disjoint_append_right_of h1 hc
  have h3 : q.Disjoint (a ++ b ++ c ++ d) := disjoint_append_right_of h2 hd
  have h4 : q.Disjoint (a ++ b ++ c ++ d ++ e) := disjoint_append_right_of h3 he
  have h5 : q.Disjoint (a ++ b ++ c ++ d ++ e ++ f) := disjoint_append_right_of h4 hf
  have h6 : q.Disjoint (a ++ b ++ c ++ d ++ e ++ f ++ g) := disjoint_append_right_of h5 hg
  exact List.Nodup.append h hq h6.symm

/-- Repackaging: seven edge-disjoint comb arms plus an eighth arm edge-disjoint from all of
them and landing on arm `j` give the six-terminal arm system. -/
theorem combSystem_of_arms {G : SimpleGraph V} {b0 b1 b2 b3 b4 t u v w c : V} {j : Fin 7}
    (p0 : G.Walk b0 u) (p1 : G.Walk b1 u) (p2 : G.Walk b2 v) (p3 : G.Walk b3 w)
    (p4 : G.Walk b4 w) (s1 : G.Walk u v) (s2 : G.Walk v w) (Q : G.Walk t c)
    (hnd : (p0.edges ++ p1.edges ++ p2.edges ++ p3.edges ++ p4.edges ++ s1.edges ++
      s2.edges).Nodup)
    (hQ : Q.edges.Nodup)
    (hQ0 : Q.edges.Disjoint p0.edges) (hQ1 : Q.edges.Disjoint p1.edges)
    (hQ2 : Q.edges.Disjoint p2.edges) (hQ3 : Q.edges.Disjoint p3.edges)
    (hQ4 : Q.edges.Disjoint p4.edges) (hQ5 : Q.edges.Disjoint s1.edges)
    (hQ6 : Q.edges.Disjoint s2.edges)
    (hc : c ∈ (combFam p0 p1 p2 p3 p4 s1 s2 j).support) :
    CombSystem G b0 b1 b2 b3 b4 t u v w c j :=
  ⟨p0, p1, p2, p3, p4, s1, s2, Q,
    nodup_append8_of hnd hQ hQ0 hQ1 hQ2 hQ3 hQ4 hQ5 hQ6, hc⟩

/-! ## The universal six-terminal cover -/

/-- **Deterministic six-terminal cover.**  Whenever the six vertices `T 0, …, T 5` of an
arbitrary graph `G` lie in one component, one of the `15 * 7 = 105` six-terminal arm systems
is realised: a five-terminal comb pattern `k`, an arm `j` of it, and a landing point `c` on that
arm joined to `T 5`. -/
theorem exists_sixShape [Countable V] (G : SimpleGraph V) (T : Fin 6 → V)
    (h : ∀ i, G.Reachable (T 0) (T i)) :
    ∃ (k : Fin 15) (j : Fin 7) (c u v w : V), SixShape G k j c u v w T := by
  classical
  obtain ⟨k, u, v, w, hk⟩ :=
    exists_combShape (fun i : Fin 5 => T (lift5 i)) (fun i => h (lift5 i))
  obtain ⟨p0, p1, p2, p3, p4, s1, s2, hnd⟩ := hk
  obtain ⟨M₀⟩ := h 5
  -- the arm family of the five-terminal comb, in slot form
  let F : (i : Fin 7) → G.Walk (armSrc (T (lift5 (pat k 0))) (T (lift5 (pat k 1)))
      (T (lift5 (pat k 2))) (T (lift5 (pat k 3))) (T (lift5 (pat k 4))) u v i)
      (armTgt u v w i) := combFam p0 p1 p2 p3 p4 s1 s2
  let S : Set V := ⋃ i : Fin 7, {x : V | x ∈ (F i).support}
  -- the arm whose source is the root `T 0`, and the walk from the sixth terminal into `S`
  have hmain : ∀ (i0 : Fin 7), armSrc (T (lift5 (pat k 0))) (T (lift5 (pat k 1)))
      (T (lift5 (pat k 2))) (T (lift5 (pat k 3))) (T (lift5 (pat k 4))) u v i0 = T 0 →
      ∃ (j : Fin 7) (c : V), CombSystem G (T (lift5 (pat k 0))) (T (lift5 (pat k 1)))
        (T (lift5 (pat k 2))) (T (lift5 (pat k 3))) (T (lift5 (pat k 4))) (T 5) u v w c j := by
    intro i0 hi0
    let W0 : G.Walk (T 5) (armTgt u v w i0) := (hi0.symm ▸ M₀.reverse).append (F i0)
    have hend : armTgt u v w i0 ∈ S :=
      Set.mem_iUnion.mpr ⟨i0, SimpleGraph.Walk.end_mem_support _⟩
    obtain ⟨c, hcS, P', hP'⟩ :=
      PercLib.CriticalLRP.TreeExpansion.FivePoint.exists_first_hit (S := S) (p := W0) hend
    -- replace the first-hit walk by a trail with the same first-contact property
    let Q : G.Walk (T 5) c := P'.bypass
    have huniq : ∀ v, v ∈ Q.support → v ∈ S → v = c :=
      fun v hv hvS => hP' v (SimpleGraph.Walk.support_bypass_subset_support P' hv) hvS
    have hQn : Q.edges.Nodup :=
      SimpleGraph.Walk.edges_nodup_of_support_nodup (SimpleGraph.Walk.bypass_isPath P').support_nodup
    have hdisj : ∀ i : Fin 7, Q.edges.Disjoint (F i).edges :=
      fun i => edges_disjoint_of_support_unique Q (F i) huniq
        (fun v hv => Set.mem_iUnion.mpr ⟨i, hv⟩)
    obtain ⟨j, hcj⟩ := Set.mem_iUnion.mp hcS
    exact ⟨j, c, combSystem_of_arms p0 p1 p2 p3 p4 s1 s2 Q hnd hQn
      (hdisj 0) (hdisj 1) (hdisj 2) (hdisj 3) (hdisj 4) (hdisj 5) (hdisj 6) hcj⟩
  rcases root_slot_cases k with h0 | h2
  · have hi0 : armSrc (T (lift5 (pat k 0))) (T (lift5 (pat k 1))) (T (lift5 (pat k 2)))
        (T (lift5 (pat k 3))) (T (lift5 (pat k 4))) u v 0 = T 0 := by
      show T (lift5 (pat k 0)) = T 0
      rw [h0]
      rfl
    obtain ⟨j, c, hcs⟩ := hmain 0 hi0
    exact ⟨k, j, c, u, v, w, hcs⟩
  · have hi2 : armSrc (T (lift5 (pat k 0))) (T (lift5 (pat k 1))) (T (lift5 (pat k 2)))
        (T (lift5 (pat k 3))) (T (lift5 (pat k 4))) u v 2 = T 0 := by
      show T (lift5 (pat k 2)) = T 0
      rw [h2]
      rfl
    obtain ⟨j, c, hcs⟩ := hmain 2 hi2
    exact ⟨k, j, c, u, v, w, hcs⟩

/-- The native form: if `o` is connected to each of `x₁, …, x₅`, one of the `15 * 7` arm systems
is realised on the terminal family `![o, x₁, x₂, x₃, x₄, x₅]`. -/
theorem exists_sixShape_connects [Countable V] (ω : PercLib.CriticalLRP.Config V)
    (o x1 x2 x3 x4 x5 : V)
    (h1 : PercLib.CriticalLRP.Connects ω o x1) (h2 : PercLib.CriticalLRP.Connects ω o x2)
    (h3 : PercLib.CriticalLRP.Connects ω o x3) (h4 : PercLib.CriticalLRP.Connects ω o x4)
    (h5 : PercLib.CriticalLRP.Connects ω o x5) :
    ∃ (k : Fin 15) (j : Fin 7) (c u v w : V),
      SixShape (PercLib.CriticalLRP.openGraph ω) k j c u v w ![o, x1, x2, x3, x4, x5] := by
  refine exists_sixShape (PercLib.CriticalLRP.openGraph ω) ![o, x1, x2, x3, x4, x5] ?_
  intro i
  fin_cases i
  · exact SimpleGraph.Reachable.rfl
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5

end PercLib.CriticalLRP.TreeExpansion.SixPoint

namespace PercLib.CriticalLRP.TreeExpansion.SixPoint

variable {V : Type*}

/-! ## The event-level cover and the `105`-fold union bound -/

/-- The six-terminal connection event is covered by the `15 * 7` arm-system events. -/
theorem sixPoint_subset_sixShapeEvents [Countable V] (T : Fin 6 → V) :
    (⋂ i : Fin 6, {ω : PercLib.CriticalLRP.Config V |
        PercLib.CriticalLRP.Connects ω (T 0) (T i)}) ⊆
      ⋃ k : Fin 15, ⋃ j : Fin 7, ⋃ c : V, ⋃ u : V, ⋃ v : V, ⋃ w : V,
        {ω | SixShape (PercLib.CriticalLRP.openGraph ω) k j c u v w T} := by
  intro ω hω
  have h : ∀ i, (PercLib.CriticalLRP.openGraph ω).Reachable (T 0) (T i) :=
    fun i => Set.mem_iInter.mp hω i
  obtain ⟨k, j, c, u, v, w, hs⟩ := exists_sixShape (PercLib.CriticalLRP.openGraph ω) T h
  exact Set.mem_iUnion.mpr ⟨k, Set.mem_iUnion.mpr ⟨j, Set.mem_iUnion.mpr ⟨c,
    Set.mem_iUnion.mpr ⟨u, Set.mem_iUnion.mpr ⟨v, Set.mem_iUnion.mpr ⟨w, hs⟩⟩⟩⟩⟩⟩

open PercLib.CriticalLRP.TreeExpansion.FivePoint in
/-- **The `105`-fold union bound.**  The six-point connection event is bounded by the sum of the
`15 * 7` per-shape laws; no moment finiteness is used. -/
theorem sixPoint_le_sixShapeSum [Countable V] (π : Sym2 V → unitInterval) (T : Fin 6 → V) :
    law π (⋂ i : Fin 6, {ω : PercLib.CriticalLRP.Config V |
        PercLib.CriticalLRP.Connects ω (T 0) (T i)}) ≤
      ∑' k : Fin 15, ∑' j : Fin 7, ∑' c : V, ∑' u : V, ∑' v : V, ∑' w : V,
        law π {ω | SixShape (PercLib.CriticalLRP.openGraph ω) k j c u v w T} := by
  refine (measure_mono (sixPoint_subset_sixShapeEvents T)).trans ?_
  refine (measure_iUnion_le (μ := law π) (s := fun k : Fin 15 => ⋃ j : Fin 7, ⋃ c : V,
    ⋃ u : V, ⋃ v : V, ⋃ w : V,
      {ω | SixShape (PercLib.CriticalLRP.openGraph ω) k j c u v w T})).trans ?_
  refine ENNReal.tsum_le_tsum fun k => ?_
  refine (measure_iUnion_le (μ := law π) (s := fun j : Fin 7 => ⋃ c : V, ⋃ u : V, ⋃ v : V,
    ⋃ w : V, {ω | SixShape (PercLib.CriticalLRP.openGraph ω) k j c u v w T})).trans ?_
  refine ENNReal.tsum_le_tsum fun j => ?_
  refine (measure_iUnion_le (μ := law π) (s := fun c : V => ⋃ u : V, ⋃ v : V, ⋃ w : V,
    {ω | SixShape (PercLib.CriticalLRP.openGraph ω) k j c u v w T})).trans ?_
  refine ENNReal.tsum_le_tsum fun c => ?_
  refine (measure_iUnion_le (μ := law π) (s := fun u : V => ⋃ v : V, ⋃ w : V,
    {ω | SixShape (PercLib.CriticalLRP.openGraph ω) k j c u v w T})).trans ?_
  refine ENNReal.tsum_le_tsum fun u => ?_
  refine (measure_iUnion_le (μ := law π) (s := fun v : V => ⋃ w : V,
    {ω | SixShape (PercLib.CriticalLRP.openGraph ω) k j c u v w T})).trans ?_
  exact ENNReal.tsum_le_tsum fun v => measure_iUnion_le _

end PercLib.CriticalLRP.TreeExpansion.SixPoint
