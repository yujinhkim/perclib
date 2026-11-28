/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Ultramath `smwzuf8hm`, member `m2`, direction `d4`.

Seven-terminal deterministic tree-arm decomposition for the `p = 6`, `k = 2` mixed moment
(Hutchcroft, *Critical long-range percolation I*, arXiv:2508.18807v1, Lemma I.4.16).
-/
module

public import PercLib.CriticalLRP.Correlation.SixPoint.Attachment.Assembly
public import PercLib.CriticalLRP.Analysis.SecondMomentCase2.Source.Defs

/-!
# The seven-terminal, nine-arm event-realization stage for `p = 6`

`Attachment/Cover.lean` in production covers every connected six-terminal configuration by
`15 * 7 = 105` six-terminal arm systems, which is the deterministic input of the `p = 5`,
`k = 1` mixed moment.  This file supplies the next stage: every connected *seven*-terminal
configuration (one root and six free leaves, so `p = 6`) is covered by
`15 * 7 * 8 = 840` seven-terminal arm systems, each consisting of

* seven pairwise edge-disjoint comb arms `b₀—u, b₁—u, b₂—v, b₃—w, b₄—w, u—v`,
  `v—w`,
* an eighth arm `t—c` landing anywhere (`c` on the comb), and
* a ninth arm `t'—c'` landing anywhere on the support of the first eight arms,

whose nine edge lists are pairwise disjoint.  The index count `840 ≤ 945 = (2 * 6 - 3)!!`
fits the source coefficient of Lemma I.4.16 at `p = 6`, `k = 2`.

No two terminals are assumed distinct, so a tuple in which several leaves collapse onto the
same vertex, or onto the root, is covered by the same statement: this is the degenerate-tuple
handling that the two-hub slot cover `HubK2.SixCover` lacked (it fails at `(0,3,3,3,3,3)`,
see `HubK2SixCounterexample.sixCover_false256`).  The ninth arm is a genuine new terminal on a
genuine tree, not a hub collapse.

The per-shape diagram evaluation to `(E|K|²)² (E|K|)^5` is *not* carried out here; only the
cover, its event-level consequence, and the arm bookkeeping are.  This gap is not pure
bookkeeping: the naive regrouping of these nine arms yields two joint pairs and six two-point
factors, i.e. ten summed variables and a bound by `(E|K|²)² (E|K|)^6`.  The `k = 2` pattern of
Lemma I.4.16 needs the source's bipartite-class regrouping of the binary tree instead.
-/

open Set MeasureTheory
open scoped ENNReal
open PercLib.Percolation.Bond

@[expose] public section

namespace PercLib.CriticalLRP.TreeExpansion.SevenPoint

variable {V : Type*}

/-! ## List bookkeeping for edge-disjointness -/

/-- Disjointness of a list from a concatenation, from disjointness from both parts. -/
theorem disjoint_append_right_of_disjoint {α : Type*} {l m n : List α}
    (hm : l.Disjoint m) (hn : l.Disjoint n) : l.Disjoint (m ++ n) := by
  rw [List.disjoint_left] at hm hn ⊢
  intro a ha han
  rw [List.mem_append] at han
  exact han.elim (fun h => hm ha h) (fun h => hn ha h)

/-! ## The nine-arm seven-terminal system -/

/-- `Fin 6` embedded in `Fin 7`: the seven terminals are the six terminals of the
`p = 5` package together with the new one. -/
def lift6 (i : Fin 6) : Fin 7 := ⟨(i : ℕ), Nat.lt_trans i.2 (by decide)⟩

@[simp] theorem lift6_val (i : Fin 6) : (lift6 i : ℕ) = (i : ℕ) := rfl

/-- Sources of the eight walks of a six-terminal arm system: the five comb slots, the two
interior comb vertices, and the sixth-terminal attachment. -/
def eightSrc (b0 b1 b2 b3 b4 t u v : V) : Fin 8 → V := ![b0, b1, b2, b3, b4, u, v, t]

/-- Targets of the eight walks of a six-terminal arm system. -/
def eightTgt (u v w c : V) : Fin 8 → V := ![u, u, v, w, w, v, w, c]

/-- The eight walks of a six-terminal arm system as a `Fin 8`-indexed family. -/
def eightFam {G : SimpleGraph V} {b0 b1 b2 b3 b4 t u v w c : V}
    (p0 : G.Walk b0 u) (p1 : G.Walk b1 u) (p2 : G.Walk b2 v) (p3 : G.Walk b3 w)
    (p4 : G.Walk b4 w) (s1 : G.Walk u v) (s2 : G.Walk v w) (Q : G.Walk t c) :
    (i : Fin 8) → G.Walk (eightSrc b0 b1 b2 b3 b4 t u v i) (eightTgt u v w c i) :=
  fun i => match i with
  | ⟨0, _⟩ => p0
  | ⟨1, _⟩ => p1
  | ⟨2, _⟩ => p2
  | ⟨3, _⟩ => p3
  | ⟨4, _⟩ => p4
  | ⟨5, _⟩ => s1
  | ⟨6, _⟩ => s2
  | ⟨7, _⟩ => Q

@[simp] theorem eightFam_zero {G : SimpleGraph V} {b0 b1 b2 b3 b4 t u v w c : V}
    (p0 : G.Walk b0 u) (p1 : G.Walk b1 u) (p2 : G.Walk b2 v) (p3 : G.Walk b3 w)
    (p4 : G.Walk b4 w) (s1 : G.Walk u v) (s2 : G.Walk v w) (Q : G.Walk t c) :
    (eightFam p0 p1 p2 p3 p4 s1 s2 Q 0).edges = p0.edges := rfl

@[simp] theorem eightFam_seven {G : SimpleGraph V} {b0 b1 b2 b3 b4 t u v w c : V}
    (p0 : G.Walk b0 u) (p1 : G.Walk b1 u) (p2 : G.Walk b2 v) (p3 : G.Walk b3 w)
    (p4 : G.Walk b4 w) (s1 : G.Walk u v) (s2 : G.Walk v w) (Q : G.Walk t c) :
    (eightFam p0 p1 p2 p3 p4 s1 s2 Q 7).edges = Q.edges := rfl

/-- **Seven-terminal arm system.**  Seven pairwise edge-disjoint comb arms
`b₀—u, b₁—u, b₂—v, b₃—w, b₄—w, u—v, v—w`, an eighth arm `t—c` landing on arm `j`,
and a ninth arm `t'—c'` landing on the `i`-th of the first eight walks, all nine edge
lists forming one `Nodup` concatenation.  The terminals are indexed by the fifteen
five-terminal patterns of the source, so that the leaves may be summed in any order.

No distinctness of `T 0, …, T 6` is assumed. -/
def SevenShape (G : SimpleGraph V) (k : Fin 15) (j : Fin 7) (i : Fin 8)
    (c c' u v w : V) (T : Fin 7 → V) : Prop :=
  ∃ (p0 : G.Walk (T (lift6 (PercLib.CriticalLRP.TreeExpansion.SixPoint.lift5
        (PercLib.CriticalLRP.TreeExpansion.FivePoint.pat k 0)))) u)
    (p1 : G.Walk (T (lift6 (PercLib.CriticalLRP.TreeExpansion.SixPoint.lift5
      (PercLib.CriticalLRP.TreeExpansion.FivePoint.pat k 1)))) u)
    (p2 : G.Walk (T (lift6 (PercLib.CriticalLRP.TreeExpansion.SixPoint.lift5
      (PercLib.CriticalLRP.TreeExpansion.FivePoint.pat k 2)))) v)
    (p3 : G.Walk (T (lift6 (PercLib.CriticalLRP.TreeExpansion.SixPoint.lift5
      (PercLib.CriticalLRP.TreeExpansion.FivePoint.pat k 3)))) w)
    (p4 : G.Walk (T (lift6 (PercLib.CriticalLRP.TreeExpansion.SixPoint.lift5
      (PercLib.CriticalLRP.TreeExpansion.FivePoint.pat k 4)))) w)
    (s1 : G.Walk u v) (s2 : G.Walk v w) (Q : G.Walk (T (lift6 5)) c) (Q' : G.Walk (T 6) c'),
    (p0.edges ++ p1.edges ++ p2.edges ++ p3.edges ++ p4.edges ++ s1.edges ++ s2.edges ++
        Q.edges ++ Q'.edges).Nodup ∧
      c ∈ (PercLib.CriticalLRP.TreeExpansion.SixPoint.combFam p0 p1 p2 p3 p4 s1 s2 j).support ∧
      c' ∈ (eightFam p0 p1 p2 p3 p4 s1 s2 Q i).support

end PercLib.CriticalLRP.TreeExpansion.SevenPoint

namespace PercLib.CriticalLRP.TreeExpansion.SevenPoint

variable {V : Type*}

/-! ## The cover: every connected seven-terminal configuration realises one of `840` shapes -/

/-- **Deterministic seven-terminal cover.**  If the seven terminals `T 0, …, T 6` of an
arbitrary graph `G` lie in one component, then one of the `15 * 7 * 8 = 840 ≤ 945` seven-terminal
arm systems is realised: a five-terminal comb pattern `k`, an arm `j` of the comb carrying the
sixth terminal, one of the eight walks of the resulting arm system carrying the seventh terminal,
and the two landing points.  No two terminals are assumed distinct, so degenerate tuples are
covered exactly as they are. -/
theorem exists_sevenShape [Countable V] (G : SimpleGraph V) (T : Fin 7 → V)
    (h : ∀ i : Fin 7, G.Reachable (T 0) (T i)) :
    ∃ (k : Fin 15) (j : Fin 7) (i : Fin 8) (c c' u v w : V),
      SevenShape G k j i c c' u v w T := by
  classical
  obtain ⟨k, j, c, u, v, w, hcs⟩ :=
    PercLib.CriticalLRP.TreeExpansion.SixPoint.exists_sixShape G (fun i : Fin 6 => T (lift6 i))
      (fun i => h (lift6 i))
  obtain ⟨p0, p1, p2, p3, p4, s1, s2, Q, hnd, hcj⟩ := hcs
  let F := eightFam p0 p1 p2 p3 p4 s1 s2 Q
  let S : Set V := ⋃ i : Fin 8, {x : V | x ∈ (F i).support}
  have hb0 : T (lift6 (PercLib.CriticalLRP.TreeExpansion.SixPoint.lift5
      (PercLib.CriticalLRP.TreeExpansion.FivePoint.pat k 0))) ∈ S := by
    refine Set.mem_iUnion.mpr ⟨0, ?_⟩
    exact SimpleGraph.Walk.start_mem_support p0
  have hreach : G.Reachable (T (lift6 (PercLib.CriticalLRP.TreeExpansion.SixPoint.lift5
      (PercLib.CriticalLRP.TreeExpansion.FivePoint.pat k 0)))) (T 6) :=
    ((h (lift6 (PercLib.CriticalLRP.TreeExpansion.SixPoint.lift5
      (PercLib.CriticalLRP.TreeExpansion.FivePoint.pat k 0)))).symm).trans (h 6)
  obtain ⟨W6⟩ := hreach
  obtain ⟨c', hc'S, P', hP'⟩ :=
    PercLib.CriticalLRP.TreeExpansion.FivePoint.exists_first_hit (S := S) (p := W6.reverse) hb0
  let Q' : G.Walk (T 6) c' := P'.bypass
  have huniq : ∀ v, v ∈ Q'.support → v ∈ S → v = c' :=
    fun v hv hvS => hP' v (SimpleGraph.Walk.support_bypass_subset_support P' hv) hvS
  have hQ'n : Q'.edges.Nodup :=
    SimpleGraph.Walk.edges_nodup_of_support_nodup (SimpleGraph.Walk.bypass_isPath P').support_nodup
  have hdisj : ∀ i : Fin 8, Q'.edges.Disjoint (F i).edges :=
    fun i => PercLib.CriticalLRP.TreeExpansion.FivePoint.edges_disjoint_of_support_unique Q' (F i)
      huniq (fun v hv => Set.mem_iUnion.mpr ⟨i, hv⟩)
  have h0 : Q'.edges.Disjoint p0.edges := hdisj 0
  have h1 : Q'.edges.Disjoint p1.edges := hdisj 1
  have h2 : Q'.edges.Disjoint p2.edges := hdisj 2
  have h3 : Q'.edges.Disjoint p3.edges := hdisj 3
  have h4 : Q'.edges.Disjoint p4.edges := hdisj 4
  have h5 : Q'.edges.Disjoint s1.edges := hdisj 5
  have h6 : Q'.edges.Disjoint s2.edges := hdisj 6
  have h7 : Q'.edges.Disjoint Q.edges := hdisj 7
  have hqall : Q'.edges.Disjoint
      (p0.edges ++ p1.edges ++ p2.edges ++ p3.edges ++ p4.edges ++ s1.edges ++ s2.edges ++
        Q.edges) :=
    disjoint_append_right_of_disjoint (disjoint_append_right_of_disjoint
      (disjoint_append_right_of_disjoint (disjoint_append_right_of_disjoint
      (disjoint_append_right_of_disjoint (disjoint_append_right_of_disjoint
      (disjoint_append_right_of_disjoint h0 h1) h2) h3) h4) h5) h6) h7
  have h9 : (p0.edges ++ p1.edges ++ p2.edges ++ p3.edges ++ p4.edges ++ s1.edges ++ s2.edges ++
      Q.edges ++ Q'.edges).Nodup :=
    List.Nodup.append hnd hQ'n hqall.symm
  obtain ⟨i, hc'i⟩ := Set.mem_iUnion.mp hc'S
  exact ⟨k, j, i, c, c', u, v, w, p0, p1, p2, p3, p4, s1, s2, Q, Q', h9, hcj, hc'i⟩

/-- Collapsed-tuple regression: the cover applies even when all seven terminals are the same
vertex, the configuration at which the two-hub slot cover fails. -/
theorem exists_sevenShape_collapsed [Countable V] (G : SimpleGraph V) (a : V) :
    ∃ (k : Fin 15) (j : Fin 7) (i : Fin 8) (c c' u v w : V),
      SevenShape G k j i c c' u v w (fun _ => a) :=
  exists_sevenShape G (fun _ => a) (fun _ => SimpleGraph.Reachable.refl a)

/-! ## The shape index and the event-level consequence -/

/-- The `15 * 7 * 8 = 840` shape indices of the seven-terminal cover. -/
structure SevenIdx (V : Type*) where
  /-- The five-terminal comb pattern. -/
  k : Fin 15
  /-- The comb arm carrying the sixth terminal. -/
  j : Fin 7
  /-- The walk of the six-terminal system carrying the seventh terminal. -/
  i : Fin 8
  /-- The landing point of the sixth terminal. -/
  c : V
  /-- The landing point of the seventh terminal. -/
  c' : V
  /-- First comb vertex. -/
  u : V
  /-- Second comb vertex. -/
  v : V
  /-- Third comb vertex. -/
  w : V

instance sevenIdxCountable [Countable V] : Countable (SevenIdx V) :=
  Function.Injective.countable
    (f := fun s : SevenIdx V => (s.k, s.j, s.i, s.c, s.c', s.u, s.v, s.w))
    (by intro a b hab; cases a; cases b; simp_all)

/-- The event that the shape with index `s` is realised on the terminals `T`. -/
def sevenShapeSet (T : Fin 7 → V) (s : SevenIdx V) : Set (Config V) :=
  {ω : Config V | SevenShape (openGraph ω) s.k s.j s.i s.c s.c' s.u s.v s.w T}

/-- The sixfold joint connection event of the root `o` with six free leaves. -/
def sevenConnSet (o x1 x2 x3 x4 x5 x6 : V) : Set (Config V) :=
  conn o x1 ∩ conn o x2 ∩ conn o x3 ∩ conn o x4 ∩ conn o x5 ∩ conn o x6

/-- At the level of configurations the `840` shapes cover the sixfold joint connection event,
with no distinctness hypothesis on the leaves. -/
theorem sevenConnSet_subset_sevenShape [Countable V] (o x1 x2 x3 x4 x5 x6 : V) :
    sevenConnSet o x1 x2 x3 x4 x5 x6 ⊆
      ⋃ s : SevenIdx V, sevenShapeSet ![o, x1, x2, x3, x4, x5, x6] s := by
  intro ω hω
  simp only [sevenConnSet, Set.mem_inter_iff, conn, Set.mem_ofPred_eq] at hω
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := hω
  have h : ∀ i : Fin 7, (openGraph ω).Reachable (![o, x1, x2, x3, x4, x5, x6] 0)
      (![o, x1, x2, x3, x4, x5, x6] i) := by
    intro i
    fin_cases i
    · exact SimpleGraph.Reachable.refl _
    · simpa using h1
    · simpa using h2
    · simpa using h3
    · simpa using h4
    · simpa using h5
    · simpa using h6
  obtain ⟨k, j, i, c, c', u, v, w, hshape⟩ := exists_sevenShape (openGraph ω) _ h
  exact Set.mem_iUnion.mpr ⟨⟨k, j, i, c, c', u, v, w⟩, hshape⟩

/-- The union bound at the actual product law: the sixfold joint connection probability is at
most the sum of the `840` shape masses.  This is the interface consumed by the per-shape BK
factorisation. -/
theorem law_sevenConnSet_le [Countable V] (π : Sym2 V → unitInterval)
    (o x1 x2 x3 x4 x5 x6 : V) :
    law π (sevenConnSet o x1 x2 x3 x4 x5 x6) ≤
      ∑' s : SevenIdx V, law π (sevenShapeSet ![o, x1, x2, x3, x4, x5, x6] s) :=
  (measure_mono (sevenConnSet_subset_sevenShape o x1 x2 x3 x4 x5 x6)).trans
    (measure_iUnion_le (fun s : SevenIdx V => sevenShapeSet ![o, x1, x2, x3, x4, x5, x6] s))

/-! ## The index count against the source coefficient `945 = (2 * 6 - 3)!!` -/

theorem card_shape_index : Fintype.card (Fin 15 × Fin 7 × Fin 8) = 840 := by
  norm_num [Fintype.card_prod]

theorem doubleFactorial_nine : Nat.doubleFactorial 9 = 945 := by decide

/-- The cover uses at most the `(2 * 6 - 3)!! = 945` slots of Lemma I.4.16 at `p = 6`. -/
theorem card_shape_index_le_doubleFactorial :
    Fintype.card (Fin 15 × Fin 7 × Fin 8) ≤ Nat.doubleFactorial 9 := by
  rw [card_shape_index, doubleFactorial_nine]
  norm_num

/-! ## Axiom audit -/

set_option linter.hashCommand false

#print axioms PercLib.CriticalLRP.TreeExpansion.SevenPoint.disjoint_append_right_of_disjoint
#print axioms PercLib.CriticalLRP.TreeExpansion.SevenPoint.exists_sevenShape
#print axioms PercLib.CriticalLRP.TreeExpansion.SevenPoint.exists_sevenShape_collapsed
#print axioms PercLib.CriticalLRP.TreeExpansion.SevenPoint.sevenConnSet_subset_sevenShape
#print axioms PercLib.CriticalLRP.TreeExpansion.SevenPoint.law_sevenConnSet_le
#print axioms PercLib.CriticalLRP.TreeExpansion.SevenPoint.card_shape_index
#print axioms PercLib.CriticalLRP.TreeExpansion.SevenPoint.doubleFactorial_nine
#print axioms PercLib.CriticalLRP.TreeExpansion.SevenPoint.card_shape_index_le_doubleFactorial
#print axioms PercLib.CriticalLRP.TreeExpansion.SevenPoint.sevenIdxCountable

end PercLib.CriticalLRP.TreeExpansion.SevenPoint
