/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
# The two-leaf tree-graph inequality on the canonical countable model

Source: Tom Hutchcroft, *Critical long-range percolation I: High effective dimension*,
arXiv:2508.18807v1, §I.2.1, equation (I.2.1) (p. 22):

  `P_β(x ↔ y ↔ z) ≤ ∑_w P_β(x↔w) P_β(w↔y) P_β(w↔z)`,

used at the end of the proof of Lemma I.4.12 (p. 39) to pass from
`∑_b P(0↔x, 0↔b) P(y↔b) P(b↔z)` to `∑_{a,b} P(0↔a) P(a↔x) P(a↔b) P(y↔b) P(b↔z)`.

The repository proves (I.2.1) for **finite edge types** (`TreeExpansion/TreeGraphInequality`,
`TreeGraph.three_point_tree_graph`, `BK/Bridge.three_point_tree_graph'`), while the canonical model
`Config V = Sym2 V → Prop` of §I.1.2 has an infinite edge set.  This file proves (I.2.1) directly on
the canonical model, so that no finite-edge transport is needed, by repeating the classical
branch-point argument:

* `exists_first_hit` (deterministic): given a walk `b → o` of open edges and a vertex set `S ∋ o`,
  there are `a ∈ S` and a walk `a → b` of open edges all of whose vertices other than `a` lie
  outside `S`;
* `exists_branch_tripleDisj` (deterministic): if `o↔x` and `o↔b` then either `x = b` (in which case
  two connections suffice) or there is a **branch point** `a` and three pairwise edge-disjoint open
  witnesses for `o↔a`, `a↔x`, `a↔b`.  Concretely, with `S` the vertex set of a simple open path
  `o → x`, the three witnesses are the two halves of that path at `a` and the path `a → b` supplied
  by `exists_first_hit`; the latter has at most one vertex in `S`, so none of its edges is an edge
  of the `o → x` path;
* `tripleDisj_le` (probabilistic): the iterated BK inequality
  `P(a↔b ∘ b↔c ∘ c↔d) ≤ P(a↔b) P(b↔c) P(c↔d)`, from `edgeMeasure_bk` applied twice;
* `twoLeaf_treeGraph` : (I.2.1) for `edgeMeasure π`, by a union bound over the branch point and
  `tripleDisj_le`;
* `twoCluster_gap` / `longRange_twoCluster_gap` : Lemma I.4.12 with **no** remaining hypothesis.

No `sorry`, no custom axioms.
-/
module

public import PercLib.CriticalLRP.Correlation.TwoClusterGap

set_option autoImplicit true

set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

@[expose] public section

open MeasureTheory Measure ProbabilityTheory unitInterval
open scoped ENNReal NNReal

namespace PercLib.CriticalLRP

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Countable V]

/-! ## A first-hit lemma for walks -/

/-- **First hit.**  Given a walk `R : b → o` of open edges and a vertex set `S` containing `o`,
there is a vertex `a ∈ S` and a walk `Q : a → b` of open edges all of whose vertices, except `a`
itself, lie outside `S`.  (Think of `a` as the last vertex of `S` visited along the walk.) -/
theorem exists_first_hit {ω : Config V} {o : V} :
    ∀ {b : V} (R : (⊤ : SimpleGraph V).Walk b o), (∀ e ∈ R.edges, e ∈ ω) →
      ∀ (S : Set V), o ∈ S →
        ∃ (a : V) (Q : (⊤ : SimpleGraph V).Walk a b),
          a ∈ S ∧ (∀ e ∈ Q.edges, e ∈ ω) ∧ ∀ v ∈ Q.support, v = a ∨ v ∉ S
  | _, .nil, _, S, ho =>
      ⟨o, .nil, ho, by simp, by
        intro v hv
        simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at hv
        subst hv
        exact Or.inl rfl⟩
  | _, .cons h R', hR, S, ho => by
      rename_i u v
      by_cases huS : u ∈ S
      · refine ⟨u, .nil, huS, by simp, ?_⟩
        intro x hx
        simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at hx
        subst hx
        exact Or.inl rfl
      · obtain ⟨a, Q, haS, hQ, hQS⟩ := exists_first_hit R'
          (fun e he => hR e (by
            rw [SimpleGraph.Walk.edges_cons]; exact List.mem_cons_of_mem _ he)) S ho
        refine ⟨a, Q.append (SimpleGraph.Walk.cons h.symm SimpleGraph.Walk.nil), haS, ?_, ?_⟩
        · intro e he
          rw [SimpleGraph.Walk.edges_append, SimpleGraph.Walk.edges_cons,
            SimpleGraph.Walk.edges_nil] at he
          rcases List.mem_append.mp he with he' | he'
          · exact hQ e he'
          · rw [List.mem_singleton] at he'
            subst he'
            rw [Sym2.eq_swap]
            exact hR _ (by rw [SimpleGraph.Walk.edges_cons]; exact List.mem_cons_self ..)
        · intro x hx
          rw [SimpleGraph.Walk.support_append, SimpleGraph.Walk.support_cons,
            SimpleGraph.Walk.support_nil] at hx
          rcases List.mem_append.mp hx with hx' | hx'
          · exact hQS x hx'
          · simp only [List.tail_cons, List.mem_singleton] at hx'
            subst hx'
            exact Or.inr huS

/-! ## Triple disjoint occurrence and the iterated BK inequality -/

/-- Three increasing events occur on three pairwise edge-disjoint finite witnesses. -/
def TripleDisj (A B C : Set (Config V)) (ω : Config V) : Prop :=
  ∃ s t u : Finset (Sym2 V), (s : Set (Sym2 V)) ⊆ ω ∧ (t : Set (Sym2 V)) ⊆ ω ∧
    (u : Set (Sym2 V)) ⊆ ω ∧ Disjoint s t ∧ Disjoint s u ∧ Disjoint t u ∧
    (s : Set (Sym2 V)) ∈ A ∧ (t : Set (Sym2 V)) ∈ B ∧ (u : Set (Sym2 V)) ∈ C

/-- `TripleDisj` implies the iterated disjoint occurrence `A ∘ (B ∘ C)`. -/
theorem tripleDisj_subset_disjointOccurrence {A B C : Set (Config V)} :
    {ω | TripleDisj A B C ω} ⊆
      Percolation.DisjointOccurrence A (Percolation.DisjointOccurrence B C) := by
  rintro ω ⟨s, t, u, hs, ht, hu, hst, hsu, htu, hA, hB, hC⟩
  refine ⟨s, t ∪ u, hs, ?_, ?_, hA, ?_⟩
  · intro e he
    rw [Finset.mem_coe, Finset.mem_union] at he
    rcases he with he | he
    · exact ht he
    · exact hu he
  · rw [Finset.disjoint_left]
    intro e he he'
    rw [Finset.mem_union] at he'
    rcases he' with he' | he'
    · exact (Finset.disjoint_left.mp hst he) he'
    · exact (Finset.disjoint_left.mp hsu he) he'
  · refine ⟨t, u, ?_, ?_, htu, hB, hC⟩
    · intro e he
      rw [Finset.mem_coe, Finset.mem_union]
      exact Or.inl he
    · intro e he
      rw [Finset.mem_coe, Finset.mem_union]
      exact Or.inr he

/-- **BK in `ℝ≥0∞` form** for increasing finitely witnessed events on the canonical model. -/
theorem bk_ennreal (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1)
    (A B : Set (Config V)) (hA : IsUpperSet A) (hB : IsUpperSet B)
    (hfA : Percolation.FiniteWitness A) (hfB : Percolation.FiniteWitness B) :
    (edgeMeasure π) (Percolation.DisjointOccurrence A B)
      ≤ (edgeMeasure π) A * (edgeMeasure π) B := by
  have h := edgeMeasure_bk π hπ A B hA hB hfA hfB
  refine (ENNReal.toReal_le_toReal (measure_ne_top _ _)
    (ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _))).mp ?_
  rw [ENNReal.toReal_mul]
  exact h

/-- **The iterated BK inequality**: `P(A ∘ B ∘ C) ≤ P(A) P(B) P(C)`. -/
theorem tripleDisj_le (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1)
    (A B C : Set (Config V)) (hA : IsUpperSet A) (hB : IsUpperSet B)
    (hC : IsUpperSet C) (hfA : Percolation.FiniteWitness A)
    (hfB : Percolation.FiniteWitness B) (hfC : Percolation.FiniteWitness C) :
    (edgeMeasure π) {ω | TripleDisj A B C ω}
      ≤ (edgeMeasure π) A * (edgeMeasure π) B * (edgeMeasure π) C := by
  have hBC_upper : IsUpperSet (Percolation.DisjointOccurrence B C) :=
    Percolation.disjointOccurrence_upper B C
  have hBC_fin : Percolation.FiniteWitness (Percolation.DisjointOccurrence B C) :=
    Percolation.finiteWitness_disjointOccurrence B C
  refine le_trans (measure_mono tripleDisj_subset_disjointOccurrence) ?_
  refine le_trans (bk_ennreal π hπ A _ hA hBC_upper hfA hBC_fin) ?_
  rw [mul_assoc]
  exact mul_le_mul' le_rfl (bk_ennreal π hπ B C hB hC hfB hfC)

/-! ## The branch-point decomposition for two connections from one vertex -/

/-- The open subgraph's edge set is contained in the configuration. -/
theorem edgeSet_subset (ω : Config V) : (openGraph ω).edgeSet ⊆ ω :=
  edgeSet_openGraph_subset

/-- **Branch point for two connections.**  If `o` is connected to `x` and to `b`, then there is a
vertex `a` with three pairwise edge-disjoint open witnesses for `o↔a`, `a↔x`, `a↔b` (the
degenerate case `x = b` is included: then `a = x` works with empty witnesses). -/
theorem exists_branch_tripleDisj {ω : Config V} {o x b : V}
    (hx : Connects ω o x) (hb : Connects ω o b) :
    ∃ a : V, TripleDisj (connSet o a) (connSet a x) (connSet a b) ω := by
  classical
  -- a simple open path from `o` to `x`
  obtain ⟨p0, hp0⟩ := pathConnects_iff.mpr hx
  have hP1path : p0.bypass.IsPath := SimpleGraph.Walk.bypass_isPath p0
  have hP1edges : ∀ e ∈ p0.bypass.edges, e ∈ ω := fun e he =>
    hp0 e (SimpleGraph.Walk.edges_bypass_subset_edges p0 he)
  set P1 : (⊤ : SimpleGraph V).Walk o x := p0.bypass with hP1def
  set S : Set V := {v | v ∈ P1.support} with hS
  have hoS : o ∈ S := SimpleGraph.Walk.start_mem_support P1
  -- a walk from `b` to `o` of open edges
  have hbo : Connects ω b o := connects_symm hb
  obtain ⟨R, hR⟩ := pathConnects_iff.mpr hbo
  obtain ⟨a, Q, haS, hQ, hQS⟩ := exists_first_hit R hR S hoS
  have haP1 : a ∈ P1.support := haS
  have hQedges : ∀ e ∈ Q.edges, e ∈ ω := hQ
  -- the three witness sets
  have hsplit : (P1.takeUntil a haP1).append (P1.dropUntil a haP1) = P1 :=
    SimpleGraph.Walk.take_spec P1 haP1
  have hnodup : ((P1.takeUntil a haP1).edges ++ (P1.dropUntil a haP1).edges).Nodup := by
    rw [← SimpleGraph.Walk.edges_append, hsplit]
    exact hP1path.isTrail.edges_nodup
  obtain ⟨-, -, hdisjP1⟩ := List.nodup_append'.mp hnodup
  have hW1 : ∀ e ∈ (P1.takeUntil a haP1).edges, e ∈ ω := fun e he =>
    hP1edges e (SimpleGraph.Walk.edges_takeUntil_subset_edges P1 haP1 he)
  have hW2 : ∀ e ∈ (P1.dropUntil a haP1).edges, e ∈ ω := fun e he =>
    hP1edges e (SimpleGraph.Walk.edges_dropUntil_subset_edges P1 haP1 he)
  -- every edge of the `o → x` path has both endpoints in `S`
  have hP1inS : ∀ e ∈ P1.edges, ∀ v ∈ e, v ∈ S := by
    intro e he v hv
    exact SimpleGraph.Walk.mem_support_iff_exists_mem_edges.mpr (Or.inr ⟨e, he, hv⟩)
  -- an edge of `Q` never is an edge of the `o → x` path
  have hQnotP1 : ∀ e ∈ Q.edges, e ∉ P1.edges := by
    intro e
    induction e using Sym2.ind with
    | _ p q =>
        intro he hmem
        have hpQ : p ∈ (s(p, q) : Sym2 V) := Sym2.mem_mk_left p q
        have hqQ : q ∈ (s(p, q) : Sym2 V) := Sym2.mem_mk_right p q
        have hpsupp : p ∈ Q.support :=
          SimpleGraph.Walk.mem_support_iff_exists_mem_edges.mpr (Or.inr ⟨_, he, hpQ⟩)
        have hqsupp : q ∈ Q.support :=
          SimpleGraph.Walk.mem_support_iff_exists_mem_edges.mpr (Or.inr ⟨_, he, hqQ⟩)
        have hpS : p ∈ S := hP1inS _ hmem p hpQ
        have hqS : q ∈ S := hP1inS _ hmem q hqQ
        have hpa : p = a := by
          rcases hQS p hpsupp with h | h
          · exact h
          · exact absurd hpS h
        have hqa : q = a := by
          rcases hQS q hqsupp with h | h
          · exact h
          · exact absurd hqS h
        have hadj : (⊤ : SimpleGraph V).Adj p q := SimpleGraph.Walk.adj_of_mem_edges Q he
        exact (SimpleGraph.top_adj p q).1 hadj (by rw [hpa, hqa])

  -- assemble
  refine ⟨a, (P1.takeUntil a haP1).edges.toFinset, (P1.dropUntil a haP1).edges.toFinset,
    Q.edges.toFinset, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro e he
    rw [Finset.mem_coe, List.mem_toFinset] at he
    exact hW1 e he
  · intro e he
    rw [Finset.mem_coe, List.mem_toFinset] at he
    exact hW2 e he
  · intro e he
    rw [Finset.mem_coe, List.mem_toFinset] at he
    exact hQedges e he
  · refine Finset.disjoint_left.mpr fun e he he' => ?_
    rw [List.mem_toFinset] at he he'
    exact hdisjP1 he he'
  · refine Finset.disjoint_left.mpr fun e he he' => ?_
    rw [List.mem_toFinset] at he he'
    exact hQnotP1 e he' (SimpleGraph.Walk.edges_takeUntil_subset_edges P1 haP1 he)
  · refine Finset.disjoint_left.mpr fun e he he' => ?_
    rw [List.mem_toFinset] at he he'
    exact hQnotP1 e he' (SimpleGraph.Walk.edges_dropUntil_subset_edges P1 haP1 he)
  · refine pathConnects_iff.mp ⟨P1.takeUntil a haP1, fun e he => ?_⟩
    exact List.mem_toFinset.mpr he
  · refine pathConnects_iff.mp ⟨P1.dropUntil a haP1, fun e he => ?_⟩
    exact List.mem_toFinset.mpr he
  · refine pathConnects_iff.mp ⟨Q, fun e he => ?_⟩
    exact List.mem_toFinset.mpr he

/-! ## The two-leaf tree-graph inequality on the canonical model -/

/-- **(I.2.1) for the canonical model**: the two connections from `o` satisfy the tree-graph
bound.  This is the inequality the printed proof of Lemma I.4.12 appeals to, proved here for the
infinite product law `edgeMeasure π` (no finite-edge transport). -/
theorem twoLeaf_treeGraph (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1) (o x b : V) :
    (edgeMeasure π) (connSet o x ∩ connSet o b)
      ≤ ∑' a : V, (edgeMeasure π) (connSet o a) * (edgeMeasure π) (connSet a x)
          * (edgeMeasure π) (connSet a b) := by
  have hcover : connSet o x ∩ connSet o b ⊆
      ⋃ a : V, {ω : Config V | TripleDisj (connSet o a) (connSet a x) (connSet a b) ω} := by
    rintro ω ⟨hx, hb⟩
    obtain ⟨a, ha⟩ := exists_branch_tripleDisj hx hb
    exact Set.mem_iUnion.mpr ⟨a, ha⟩
  refine le_trans (measure_mono hcover) ?_
  refine le_trans (measure_iUnion_le _) (ENNReal.tsum_le_tsum fun a => ?_)
  exact tripleDisj_le π hπ _ _ _ (isUpper_connSet o a) (isUpper_connSet a x)
    (isUpper_connSet a b) (finiteWitness_connSet o a) (finiteWitness_connSet a x)
    (finiteWitness_connSet a b)

/-- **Lemma I.4.12 (Hutchcroft, p. 39), with no remaining hypothesis**, in the additive `ℝ≥0∞`
form:

  `P(0↔x) P(y↔z) ≤ P(0↔x ↮ y↔z) + ∑_a ∑_b P(0↔a) P(a↔x) P(a↔b) P(y↔b) P(b↔z)`. -/
theorem twoCluster_gap (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1) (o x y z : V) :
    (edgeMeasure π) (connSet o x) * (edgeMeasure π) (connSet y z) ≤
      (edgeMeasure π) (disjSet o x y z) +
        ∑' a : V, ∑' b : V, (edgeMeasure π) (connSet o a) * (edgeMeasure π) (connSet a x)
          * (edgeMeasure π) (connSet a b) * (edgeMeasure π) (connSet y b)
          * (edgeMeasure π) (connSet b z) :=
  twoCluster_gap_le' π hπ o x y z (fun b => twoLeaf_treeGraph π hπ o x b)

/-- **Lemma I.4.12 for the law `P_β` of §I.1.2** (`β ≥ 0`, `J ≥ 0`, arbitrary vertex set), with no
remaining hypothesis.  Substituting `π = 1 − exp(−β J)` this is the paper's displayed estimate
with `P_{β,r}` the long-range bond percolation measure. -/
theorem longRange_twoCluster_gap (J : Sym2 V → ℝ) (hJ : ∀ e, 0 ≤ J e) (β : NNReal)
    (o x y z : V) :
    (longRangeMeasure J hJ β) (connSet o x) * (longRangeMeasure J hJ β) (connSet y z) ≤
      (longRangeMeasure J hJ β) (disjSet o x y z) +
        ∑' a : V, ∑' b : V, (longRangeMeasure J hJ β) (connSet o a)
          * (longRangeMeasure J hJ β) (connSet a x)
          * (longRangeMeasure J hJ β) (connSet a b)
          * (longRangeMeasure J hJ β) (connSet y b)
          * (longRangeMeasure J hJ β) (connSet b z) :=
  twoCluster_gap (bernoulliEdgeProb J hJ β) (fun e => bernoulliEdgeProb_lt_one hJ β e) o x y z

end PercLib.CriticalLRP
