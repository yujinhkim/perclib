/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Five-vertex deterministic tree-arm decomposition supplied by Ultramath
`smwpj8umm` member m1, including first-hit attachment and the fifteen-pattern
normalization. Earlier three-arm components came from `smwj645my` under the
project's Apache-2.0 attribution.
-/
module

public import PercLib.CriticalLRP.Correlation.FourthMoment.Defs
public import PercLib.CriticalLRP.TreeGraph.Connectivity
public import Mathlib.Combinatorics.SimpleGraph.Paths

/-
Swarm `smwpj8umm`, member `m1` (direction d1).

# The five-vertex (four-plus-one-point) binary arm decomposition

Deterministic core of the `p = 4` tree-graph bound (Lemma I.4.16 of Hutchcroft,
arXiv:2508.18807v1, the `k = 0` instance): five vertices in a common component of an arbitrary
graph span a *binary* tree with five labelled leaves — three branch vertices joined in a spine
`u — v — w` with leaf distribution `2, 1, 2`, i.e. `2 * 5 - 3 = 7` pairwise edge-disjoint arms.

Two steps, mirroring the compiled third-moment argument (`Correlation/ThirdMoment`, and the
discharge of its deterministic hypothesis in swarm `smwj645my`):
* four terminals give the `H`-shaped five-arm structure `Slots4` (`exists_slots4`);
* a fifth terminal is attached into that structure along the first hit of a walk into the union of
  its five arm supports, splitting the arm it lands on (`attachAny`).

The walk bookkeeping (`exists_first_hit`, `edges_disjoint_of_support_unique`,
`exists_three_arms_paths`) is taken from swarm `smwj645my` member `m2`'s `proof.lean`
(same project family, Apache-2.0), where it discharges the four-leaf hypothesis of
`four_point_of_arm_decomposition`; it is reproduced here with the trail/bookkeeping additions that
the fifth leaf needs.
-/

open Set MeasureTheory
open scoped ENNReal
open PercLib.Percolation.Bond

@[expose] public section

namespace PercLib.CriticalLRP.TreeExpansion.FivePoint

variable {V : Type*}

/-! ## Elementary walk bookkeeping -/

theorem mem_support_of_edge {G : SimpleGraph V} {a b v : V} {p : G.Walk a b} {e : Sym2 V}
    (he : e ∈ p.edges) (hv : v ∈ e) : v ∈ p.support := by
  rw [SimpleGraph.Walk.mem_support_iff_exists_mem_edges]
  exact Or.inr ⟨e, he, hv⟩

theorem disjoint_of_subset_left {α : Type*} {l1 l1' l2 : List α} (h : l1 ⊆ l1')
    (hd : l1'.Disjoint l2) : l1.Disjoint l2 := by
  rw [List.disjoint_left] at hd ⊢
  intro a ha ha'
  exact hd (h ha) ha'

theorem disjoint_of_subset_right {α : Type*} {l1 l2 l2' : List α} (h : l2 ⊆ l2')
    (hd : l1.Disjoint l2') : l1.Disjoint l2 := by
  rw [List.disjoint_left] at hd ⊢
  intro a ha ha'
  exact hd ha (h ha')

theorem disjoint_of_subset {α : Type*} {l1 l1' l2 l2' : List α} (h1 : l1 ⊆ l1')
    (h2 : l2 ⊆ l2') (hd : l1'.Disjoint l2') : l1.Disjoint l2 :=
  disjoint_of_subset_left h1 (disjoint_of_subset_right h2 hd)

/-- Disjointness of edge lists, transported across a reversed walk (left argument). -/
theorem disjoint_reverse_left {G : SimpleGraph V} {a b c d : V} {p : G.Walk a b} {q : G.Walk c d}
    (h : p.edges.Disjoint q.edges) : p.reverse.edges.Disjoint q.edges := by
  rw [SimpleGraph.Walk.edges_reverse]
  exact List.disjoint_reverse_left.mpr h

/-- Disjointness of edge lists, transported across a reversed walk (right argument). -/
theorem disjoint_reverse_right {G : SimpleGraph V} {a b c d : V} {p : G.Walk a b} {q : G.Walk c d}
    (h : p.edges.Disjoint q.edges) : p.edges.Disjoint q.reverse.edges := by
  rw [SimpleGraph.Walk.edges_reverse]
  exact List.disjoint_reverse_right.mpr h

theorem nodup_reverse_edges {G : SimpleGraph V} {a b : V} {p : G.Walk a b}
    (h : p.edges.Nodup) : p.reverse.edges.Nodup := by
  rw [SimpleGraph.Walk.edges_reverse]
  exact List.nodup_reverse.mpr h

/-! ## Concatenations of edge lists: under a single `Nodup` hypothesis -/

theorem disjoint_append_left_of {α : Type*} {l₁ l₂ l₃ : List α}
    (h₁ : l₁.Disjoint l₃) (h₂ : l₂.Disjoint l₃) : (l₁ ++ l₂).Disjoint l₃ := by
  rw [List.disjoint_left] at h₁ h₂ ⊢
  intro a ha ha3
  rcases List.mem_append.mp ha with h | h
  · exact h₁ h ha3
  · exact h₂ h ha3

theorem disjoint_append_right_of {α : Type*} {l₁ l₂ l₃ : List α}
    (h₁ : l₁.Disjoint l₂) (h₂ : l₁.Disjoint l₃) : l₁.Disjoint (l₂ ++ l₃) :=
  (disjoint_append_left_of h₁.symm h₂.symm).symm

/-- `(a ++ b ++ c ++ d ++ e).Nodup` from the five `Nodup` hypotheses and the ten pairwise
disjointness hypotheses. -/
theorem nodup_five {α : Type*} {a b c d e : List α} (ha : a.Nodup) (hb : b.Nodup)
    (hc : c.Nodup) (hd : d.Nodup) (he : e.Nodup)
    (hab : a.Disjoint b) (hac : a.Disjoint c) (had : a.Disjoint d) (hae : a.Disjoint e)
    (hbc : b.Disjoint c) (hbd : b.Disjoint d) (hbe : b.Disjoint e)
    (hcd : c.Disjoint d) (hce : c.Disjoint e) (hde : d.Disjoint e) :
    (a ++ b ++ c ++ d ++ e).Nodup := by
  have habc : (a ++ b).Disjoint c := disjoint_append_left_of hac hbc
  have habd : (a ++ b).Disjoint d := disjoint_append_left_of had hbd
  have habe : (a ++ b).Disjoint e := disjoint_append_left_of hae hbe
  have habcd : (a ++ b ++ c).Disjoint d := disjoint_append_left_of habd hcd
  have habce : (a ++ b ++ c).Disjoint e := disjoint_append_left_of habe hce
  have habcde : (a ++ b ++ c ++ d).Disjoint e := disjoint_append_left_of habce hde
  exact List.Nodup.append (List.Nodup.append (List.Nodup.append (List.Nodup.append ha hb hab)
    hc habc) hd habcd) he habcde

/-- `(a ++ b ++ c).Nodup` from three `Nodup` hypotheses and pairwise disjointness. -/
theorem nodup_three {α : Type*} {a b c : List α} (ha : a.Nodup) (hb : b.Nodup) (hc : c.Nodup)
    (hab : a.Disjoint b) (hac : a.Disjoint c) (hbc : b.Disjoint c) :
    (a ++ b ++ c).Nodup := by
  have habc : (a ++ b).Disjoint c := disjoint_append_left_of hac hbc
  exact List.Nodup.append (List.Nodup.append ha hb hab) hc habc

/-- `(a ++ b ++ c ++ d).Nodup` from four `Nodup` hypotheses and pairwise disjointness. -/
theorem nodup_four {α : Type*} {a b c d : List α} (ha : a.Nodup) (hb : b.Nodup) (hc : c.Nodup)
    (hd : d.Nodup) (hab : a.Disjoint b) (hac : a.Disjoint c) (had : a.Disjoint d)
    (hbc : b.Disjoint c) (hbd : b.Disjoint d) (hcd : c.Disjoint d) :
    (a ++ b ++ c ++ d).Nodup := by
  have habc : (a ++ b).Disjoint c := disjoint_append_left_of hac hbc
  have habd : (a ++ b).Disjoint d := disjoint_append_left_of had hbd
  have habcd : (a ++ b ++ c).Disjoint d := disjoint_append_left_of habd hcd
  exact List.Nodup.append (List.Nodup.append (List.Nodup.append ha hb hab) hc habc) hd habcd

/-- **First hit.**  Along a walk `p` from `a` to `b`, if the endpoint `b` lies in a set `S`, then
there is a prefix `p'` of `p` ending at a vertex `c ∈ S` whose support meets `S` only in `c`. -/
theorem exists_first_hit {G : SimpleGraph V} (S : Set V) {a b : V} (p : G.Walk a b) (hb : b ∈ S) :
    ∃ c ∈ S, ∃ p' : G.Walk a c, ∀ v, v ∈ p'.support → v ∈ S → v = c := by
  revert hb
  induction p with
  | nil => intro hb; exact ⟨_, hb, .nil, fun v hv _ => by simpa using hv⟩
  | @cons a a' b hadj p' ih =>
    intro hb
    by_cases ha : a ∈ S
    · exact ⟨a, ha, .nil, fun v hv _ => by simpa using hv⟩
    · obtain ⟨c, hcS, p'', hp''⟩ := ih hb
      refine ⟨c, hcS, .cons hadj p'', fun v hv hvS => ?_⟩
      rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hv
      rcases hv with rfl | hv
      · exact absurd hvS ha
      · exact hp'' v hv hvS

/-- If the only vertex of `S` in the support of `p` is the endpoint of `p`, then `p` has no edge
in common with a walk whose support lies in `S`. -/
theorem edges_disjoint_of_support_unique {G : SimpleGraph V} {S : Set V} {a b c d : V}
    (p : G.Walk a b) (q : G.Walk c d)
    (hp : ∀ v, v ∈ p.support → v ∈ S → v = b)
    (hq : ∀ v, v ∈ q.support → v ∈ S) :
    p.edges.Disjoint q.edges := by
  rw [List.disjoint_left]
  intro e hep heq
  induction e using Sym2.ind with
  | h x y =>
    have hne : x ≠ y := (SimpleGraph.Walk.adj_of_mem_edges p hep).ne
    have hxq : x ∈ q.support := mem_support_of_edge heq (Sym2.mem_mk_left x y)
    have hyq : y ∈ q.support := mem_support_of_edge heq (Sym2.mem_mk_right x y)
    have hxp : x ∈ p.support := mem_support_of_edge hep (Sym2.mem_mk_left x y)
    have hyp : y ∈ p.support := mem_support_of_edge hep (Sym2.mem_mk_right x y)
    exact hne ((hp x hxp (hq x hxq)).trans (hp y hyp (hq y hyq)).symm)

/-- **Three-arm (branch point) decomposition, trail form.**  If `x`, `y`, `z` lie in a common
component of an arbitrary graph `G`, there is a centre `m` and three trails from `x`, `y`, `z` to
`m` with pairwise disjoint edge lists.  (Swarm `smwj645my` member `m2`.) -/
theorem exists_three_arms_paths {G : SimpleGraph V} {x y z : V}
    (hxy : G.Reachable x y) (hxz : G.Reachable x z) :
    ∃ (m : V) (p : G.Walk x m) (q : G.Walk y m) (r : G.Walk z m),
      p.edges.Nodup ∧ q.edges.Nodup ∧ r.edges.Nodup ∧
      p.edges.Disjoint q.edges ∧ p.edges.Disjoint r.edges ∧ q.edges.Disjoint r.edges := by
  classical
  have hraw : ∃ (m : V) (p : G.Walk x m) (q : G.Walk y m) (r : G.Walk z m),
      p.edges.Disjoint q.edges ∧ p.edges.Disjoint r.edges ∧ q.edges.Disjoint r.edges := by
    obtain ⟨pxy⟩ := hxy
    obtain ⟨pxz⟩ := hxz
    have hex : ∃ n : ℕ, ∃ (m : V) (p : G.Walk x m) (q : G.Walk y m) (r : G.Walk z m),
        p.length + q.length + r.length = n :=
      ⟨pxy.length + pxz.length, x, SimpleGraph.Walk.nil, pxy.reverse, pxz.reverse, by simp⟩
    obtain ⟨m, p, q, r, hlen⟩ := Nat.find_spec hex
    have hmin : ∀ (m' : V) (p' : G.Walk x m') (q' : G.Walk y m') (r' : G.Walk z m'),
        Nat.find hex ≤ p'.length + q'.length + r'.length :=
      fun m' p' q' r' => Nat.find_min' hex ⟨m', p', q', r', rfl⟩
    have hpq : ∀ {u : V}, u ∈ p.support → u ∈ q.support → u = m := by
      intro u huP huQ
      by_contra hne
      have hlt := PercLib.CriticalLRP.TreeGraph.shorten_total p q r huP huQ hne
      have hge := hmin u (p.takeUntil u huP) (q.takeUntil u huQ)
        (r.append (p.dropUntil u huP).reverse)
      omega
    have hpr : ∀ {u : V}, u ∈ p.support → u ∈ r.support → u = m := by
      intro u huP huR
      by_contra hne
      have hlt := PercLib.CriticalLRP.TreeGraph.shorten_total p r q huP huR hne
      have hge := hmin u (p.takeUntil u huP) (q.append (p.dropUntil u huP).reverse)
        (r.takeUntil u huR)
      omega
    have hqr : ∀ {u : V}, u ∈ q.support → u ∈ r.support → u = m := by
      intro u huQ huR
      by_contra hne
      have hlt := PercLib.CriticalLRP.TreeGraph.shorten_total q r p huQ huR hne
      have hge := hmin u (p.append (q.dropUntil u huQ).reverse) (q.takeUntil u huQ)
        (r.takeUntil u huR)
      omega
    refine ⟨m, p, q, r, ?_, ?_, ?_⟩
    · rw [List.disjoint_left]
      intro e hep heq
      induction e using Sym2.ind with
      | h a b =>
        have hne : a ≠ b := (SimpleGraph.Walk.adj_of_mem_edges p hep).ne
        have hap : a ∈ p.support := mem_support_of_edge hep (Sym2.mem_mk_left a b)
        have haq : a ∈ q.support := mem_support_of_edge heq (Sym2.mem_mk_left a b)
        have hbp : b ∈ p.support := mem_support_of_edge hep (Sym2.mem_mk_right a b)
        have hbq : b ∈ q.support := mem_support_of_edge heq (Sym2.mem_mk_right a b)
        exact hne ((hpq hap haq).trans (hpq hbp hbq).symm)
    · rw [List.disjoint_left]
      intro e hep her
      induction e using Sym2.ind with
      | h a b =>
        have hne : a ≠ b := (SimpleGraph.Walk.adj_of_mem_edges p hep).ne
        have hap : a ∈ p.support := mem_support_of_edge hep (Sym2.mem_mk_left a b)
        have har : a ∈ r.support := mem_support_of_edge her (Sym2.mem_mk_left a b)
        have hbp : b ∈ p.support := mem_support_of_edge hep (Sym2.mem_mk_right a b)
        have hbr : b ∈ r.support := mem_support_of_edge her (Sym2.mem_mk_right a b)
        exact hne ((hpr hap har).trans (hpr hbp hbr).symm)
    · rw [List.disjoint_left]
      intro e heq her
      induction e using Sym2.ind with
      | h a b =>
        have hne : a ≠ b := (SimpleGraph.Walk.adj_of_mem_edges q heq).ne
        have haq : a ∈ q.support := mem_support_of_edge heq (Sym2.mem_mk_left a b)
        have har : a ∈ r.support := mem_support_of_edge her (Sym2.mem_mk_left a b)
        have hbq : b ∈ q.support := mem_support_of_edge heq (Sym2.mem_mk_right a b)
        have hbr : b ∈ r.support := mem_support_of_edge her (Sym2.mem_mk_right a b)
        exact hne ((hqr haq har).trans (hqr hbq hbr).symm)
  obtain ⟨m, p, q, r, hpq, hpr, hqr⟩ := hraw
  have hnp : p.bypass.edges.Nodup :=
    SimpleGraph.Walk.edges_nodup_of_support_nodup (SimpleGraph.Walk.bypass_isPath p).support_nodup
  have hnq : q.bypass.edges.Nodup :=
    SimpleGraph.Walk.edges_nodup_of_support_nodup (SimpleGraph.Walk.bypass_isPath q).support_nodup
  have hnr : r.bypass.edges.Nodup :=
    SimpleGraph.Walk.edges_nodup_of_support_nodup (SimpleGraph.Walk.bypass_isPath r).support_nodup
  exact ⟨m, p.bypass, q.bypass, r.bypass, hnp, hnq, hnr,
    disjoint_of_subset (SimpleGraph.Walk.edges_bypass_subset_edges p)
      (SimpleGraph.Walk.edges_bypass_subset_edges q) hpq,
    disjoint_of_subset (SimpleGraph.Walk.edges_bypass_subset_edges p)
      (SimpleGraph.Walk.edges_bypass_subset_edges r) hpr,
    disjoint_of_subset (SimpleGraph.Walk.edges_bypass_subset_edges q)
      (SimpleGraph.Walk.edges_bypass_subset_edges r) hqr⟩

/-! ## From three arms plus an attaching walk to the four-terminal structure -/

/-- The `H`-shaped five-arm structure from three trails to a common centre plus a first-hit
attachment of the fourth terminal: this is `ShapeWitness G a0 a1 a2 a3 c m` recorded in slot form
(`a0, a1` at `c`; `a2, a3` at `m`) and strengthened to trails. -/
theorem slots4_of_three_arms {G : SimpleGraph V} {a0 a1 a2 a3 m c : V}
    (N : G.Walk a0 c) (py : G.Walk a1 m) (pz : G.Walk a2 m) (pw : G.Walk a3 m)
    (hN : N.edges.Nodup) (hpy : py.edges.Nodup) (hpz : pz.edges.Nodup) (hpw : pw.edges.Nodup)
    (hyz : py.edges.Disjoint pz.edges) (hyw : py.edges.Disjoint pw.edges)
    (hzw : pz.edges.Disjoint pw.edges)
    (hc : c ∈ py.support)
    (hNd : ∀ v, v ∈ N.support → (v ∈ py.support ∨ v ∈ pz.support ∨ v ∈ pw.support) → v = c) :
    Slots4 G a0 a1 a2 a3 c m := by
  classical
  have hTill : (py.takeUntil c hc).edges ⊆ py.edges :=
    SimpleGraph.Walk.edges_takeUntil_subset_edges py hc
  have hDrop : (py.dropUntil c hc).edges ⊆ py.edges :=
    SimpleGraph.Walk.edges_dropUntil_subset_edges py hc
  have hSTill : (py.takeUntil c hc).support ⊆ py.support :=
    SimpleGraph.Walk.support_takeUntil_subset_support py hc
  have hSDrop : (py.dropUntil c hc).support ⊆ py.support :=
    SimpleGraph.Walk.support_dropUntil_subset_support py hc
  have hsplit : ((py.takeUntil c hc).edges ++ (py.dropUntil c hc).edges).Nodup := by
    rw [← SimpleGraph.Walk.edges_append, SimpleGraph.Walk.take_spec]
    exact hpy
  have htakeN : (py.takeUntil c hc).edges.Nodup := List.Nodup.of_append_left hsplit
  have hdropN : (py.dropUntil c hc).edges.Nodup := List.Nodup.of_append_right hsplit
  have htd : (py.takeUntil c hc).edges.Disjoint (py.dropUntil c hc).edges :=
    List.disjoint_of_nodup_append hsplit
  have hNtake := edges_disjoint_of_support_unique N (py.takeUntil c hc) hNd
    fun v hv => Or.inl (hSTill hv)
  have hNpz := edges_disjoint_of_support_unique N pz hNd fun v hv => Or.inr (Or.inl hv)
  have hNpw := edges_disjoint_of_support_unique N pw hNd fun v hv => Or.inr (Or.inr hv)
  have hNdrop := edges_disjoint_of_support_unique N (py.dropUntil c hc) hNd
    fun v hv => Or.inl (hSDrop hv)
  exact ⟨N, py.takeUntil c hc, pz, pw, py.dropUntil c hc,
    nodup_five hN htakeN hpz hpw hdropN hNtake hNpz hNpw hNdrop
      (disjoint_of_subset_left hTill hyz) (disjoint_of_subset_left hTill hyw) htd
      hzw (disjoint_of_subset_right hDrop hyz.symm) (disjoint_of_subset_right hDrop hyw.symm)⟩

/-- **The four-terminal binary arm decomposition.**  Four vertices in a common component of an
arbitrary graph admit the `H`-shaped five-arm binary structure, in one of the three labellings
(which pairs of terminals sit at the two branch vertices).  This is the deterministic content of
the third-moment reduction, recorded with trails and a slot order so that a fifth leaf can be
attached to any of the five arms. -/
theorem exists_slots4 {G : SimpleGraph V} (T : Fin 4 → V) (h : ∀ i, G.Reachable (T 0) (T i)) :
    (∃ u v, Slots4 G (T 0) (T 1) (T 2) (T 3) u v) ∨
      (∃ u v, Slots4 G (T 0) (T 2) (T 1) (T 3) u v) ∨
      (∃ u v, Slots4 G (T 0) (T 3) (T 1) (T 2) u v) := by
  classical
  obtain ⟨m, py, pz, pw, hpy, hpz, hpw, hyz, hyw, hzw⟩ :=
    exists_three_arms_paths ((h 1).symm.trans (h 2)) ((h 1).symm.trans (h 3))
  obtain ⟨P⟩ : Nonempty (G.Walk (T 0) m) := (h 1).trans ⟨py⟩
  obtain ⟨c, hcS, P', hP'⟩ :=
    exists_first_hit {v | v ∈ py.support ∨ v ∈ pz.support ∨ v ∈ pw.support} P
      (Or.inl (SimpleGraph.Walk.end_mem_support py))
  have hNb : P'.bypass.edges.Nodup :=
    SimpleGraph.Walk.edges_nodup_of_support_nodup (SimpleGraph.Walk.bypass_isPath P').support_nodup
  have hNs : ∀ v, v ∈ P'.bypass.support →
      (v ∈ py.support ∨ v ∈ pz.support ∨ v ∈ pw.support) → v = c :=
    fun v hv hvs => hP' v (SimpleGraph.Walk.support_bypass_subset_support P' hv) hvs
  rcases hcS with hc | hc | hc
  · exact Or.inl ⟨c, m, slots4_of_three_arms P'.bypass py pz pw hNb hpy hpz hpw hyz hyw hzw hc hNs⟩
  · exact Or.inr (Or.inl ⟨c, m, slots4_of_three_arms P'.bypass pz py pw hNb hpz hpy hpw
      hyz.symm hzw hyw hc fun v hv hvs => hNs v hv (by tauto)⟩)
  · exact Or.inr (Or.inr ⟨c, m, slots4_of_three_arms P'.bypass pw py pz hNb hpw hpy hpz
      hyw.symm hzw.symm hyz hc fun v hv hvs => hNs v hv (by tauto)⟩)

end PercLib.CriticalLRP.TreeExpansion.FivePoint
