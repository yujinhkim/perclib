/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
Connectivity layer for finite-edge Bernoulli bond percolation, and the three-arm
(branch-point) decomposition that underlies the first tree-graph inequality of
Aizenman--Newman, equation (I.2.1) of

  T. Hutchcroft, *Critical long-range percolation I: High effective dimension*,
  arXiv:2508.18807v1,

Section I.2 ("The tree-graph inequalities", p. 22).

Setting. `E` is a finite type of *possible* edges, `ends : E → Sym2 V` assigns to each edge
its unordered pair of endpoints (the graph underlying a "weighted graph" `G = (V,E,J)`
of the paper; no injectivity of `ends` is needed). A configuration is a `Finset E` of open
edges; the resulting open graph is `openGraph ends s`.

Main results of this file (no probability theory):
* `Conn` and its basic order/equivalence properties;
* `candF`: the finite set of vertices that can occur in a configuration;
* `exists_three_arms`: if `x`, `y`, `z` lie in a common open component, then there are a
  vertex `w` and three walks `x → w`, `y → w`, `z → w` whose edge lists are pairwise
  disjoint. This is the deterministic content of (I.2.1): the "branch point" `w` and the
  three edge-disjoint arms.

The proof of `exists_three_arms` is a minimality argument: among all triples of walks from
`x`, `y`, `z` to a common vertex, choose one of minimal total length. If two arms met at a
vertex `u ≠ w`, moving the centre to `u` and concatenating one arm with (a reverse of) the
tail of another gives a strictly shorter triple, a contradiction. It follows that any two
arms share no vertex other than `w`, hence no edge.
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Combinatorics.SimpleGraph.Walk.Decomp
public import Mathlib.Combinatorics.SimpleGraph.Walk.Maps
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Data.Sym.Sym2

set_option autoImplicit true

set_option linter.unusedSectionVars false

@[expose] public section

namespace PercLib.CriticalLRP.TreeGraph

open Finset

variable {V : Type*} [DecidableEq V]
variable {E : Type*} [Fintype E] [DecidableEq E]

/-! ### The open graph of a finite configuration -/

/-- The set of unordered pairs carried by the edges of the finite edge set `s`. -/
def edgeSetOf (ends : E → Sym2 V) (s : Finset E) : Set (Sym2 V) := {e | ∃ a ∈ s, ends a = e}

/-- The graph whose edges are the open edges of the configuration `s`. -/
def openGraph (ends : E → Sym2 V) (s : Finset E) : SimpleGraph V :=
  SimpleGraph.fromEdgeSet (edgeSetOf ends s)

theorem openGraph_adj {ends : E → Sym2 V} {s : Finset E} {u v : V} :
    (openGraph ends s).Adj u v ↔ (∃ a ∈ s, ends a = s(u, v)) ∧ u ≠ v := by
  rw [openGraph, SimpleGraph.fromEdgeSet_adj]
  simp [edgeSetOf]

/-- `u` and `v` are connected by an open path of the configuration `s`. -/
def Conn (ends : E → Sym2 V) (s : Finset E) (u v : V) : Prop :=
  (openGraph ends s).Reachable u v

theorem conn_refl (ends : E → Sym2 V) (s : Finset E) (u : V) : Conn ends s u u :=
  SimpleGraph.Reachable.refl u

theorem conn_symm {ends : E → Sym2 V} {s : Finset E} {u v : V} (h : Conn ends s u v) :
    Conn ends s v u :=
  SimpleGraph.Reachable.symm h

theorem conn_trans {ends : E → Sym2 V} {s : Finset E} {u v w : V}
    (h₁ : Conn ends s u v) (h₂ : Conn ends s v w) : Conn ends s u w :=
  SimpleGraph.Reachable.trans h₁ h₂

theorem openGraph_mono {ends : E → Sym2 V} {s t : Finset E} (hst : s ⊆ t) :
    openGraph ends s ≤ openGraph ends t := by
  intro u v huv
  rw [openGraph_adj] at huv ⊢
  obtain ⟨⟨a, ha, hva⟩, hne⟩ := huv
  exact ⟨⟨a, hst ha, hva⟩, hne⟩

theorem conn_mono {ends : E → Sym2 V} {s t : Finset E} (hst : s ⊆ t) {u v : V}
    (h : Conn ends s u v) : Conn ends t u v :=
  h.elim fun p => ⟨SimpleGraph.Walk.mapLe (openGraph_mono hst) p⟩

theorem conn_of_adj {ends : E → Sym2 V} {s : Finset E} {u v : V}
    (h : (openGraph ends s).Adj u v) : Conn ends s u v :=
  SimpleGraph.Adj.reachable h

theorem conn_iff_nonempty_walk {ends : E → Sym2 V} {s : Finset E} {u v : V} :
    Conn ends s u v ↔ Nonempty ((openGraph ends s).Walk u v) := Iff.rfl

/-! ### The vertices of a configuration -/

/-- The set of vertices that are endpoints of an edge of `s`. -/
def verts (ends : E → Sym2 V) (s : Finset E) : Finset V :=
  s.biUnion fun a => (ends a).toFinset

theorem mem_verts {ends : E → Sym2 V} {s : Finset E} {v : V} :
    v ∈ verts ends s ↔ ∃ a ∈ s, v ∈ ends a := by
  simp [verts, Sym2.mem_toFinset]

theorem mem_verts_of_adj {ends : E → Sym2 V} {s : Finset E} {u v : V}
    (h : (openGraph ends s).Adj u v) : v ∈ verts ends s := by
  obtain ⟨⟨a, ha, hva⟩, -⟩ := openGraph_adj.mp h
  exact mem_verts.mpr ⟨a, ha, by rw [hva]; exact Sym2.mem_mk_right u v⟩

/-- A finite set of vertices containing every vertex that can be connected in a
configuration of the (finite) ambient edge type `E`. -/
def candF (ends : E → Sym2 V) (x y z : V) : Finset V :=
  insert x (insert y (insert z (univ.biUnion fun a : E => (ends a).toFinset)))

theorem verts_subset_candF (ends : E → Sym2 V) (s : Finset E) (x y z : V) :
    verts ends s ⊆ candF ends x y z := by
  intro v hv
  obtain ⟨a, -, hva⟩ := mem_verts.mp hv
  exact Finset.mem_insert_of_mem
    (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
      (Finset.mem_biUnion.mpr ⟨a, Finset.mem_univ a, Sym2.mem_toFinset.mpr hva⟩)))

theorem support_subset_insert_verts {ends : E → Sym2 V} {s : Finset E} {x w : V}
    (p : (openGraph ends s).Walk x w) :
    ∀ v ∈ p.support, v ∈ insert x (verts ends s) := by
  induction p with
  | nil =>
    intro v hv
    rw [SimpleGraph.Walk.support_nil, List.mem_singleton] at hv
    subst hv
    exact Finset.mem_insert_self _ _
  | @cons x v w hadj p ih =>
    intro y hy
    rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hy
    rcases hy with rfl | hy
    · exact Finset.mem_insert_self _ _
    · rcases Finset.mem_insert.mp (ih y hy) with rfl | hmem
      · exact Finset.mem_insert_of_mem (mem_verts_of_adj hadj)
      · exact Finset.mem_insert_of_mem hmem

theorem end_mem_candF {ends : E → Sym2 V} {s : Finset E} {x w y z : V}
    (p : (openGraph ends s).Walk x w) : w ∈ candF ends x y z := by
  rcases Finset.mem_insert.mp (support_subset_insert_verts p w
    (SimpleGraph.Walk.end_mem_support p)) with rfl | h
  · exact Finset.mem_insert_self _ _
  · exact verts_subset_candF ends s x y z h

/-! ### Walks supported on a sub-configuration -/

theorem mem_support_of_mem_edges {G : SimpleGraph V} {u v : V} {p : G.Walk u v} {e : Sym2 V}
    (he : e ∈ p.edges) {a : V} (ha : a ∈ e) : a ∈ p.support := by
  rw [SimpleGraph.Walk.mem_support_iff_exists_mem_edges]
  exact Or.inr ⟨e, he, ha⟩

/-- A walk all of whose edges are realised in `W` is a walk of the graph of `W`. -/
theorem nonempty_walk_of_edges {ends : E → Sym2 V} {s W : Finset E} {u v : V}
    (p : (openGraph ends s).Walk u v) (h : ∀ e ∈ p.edges, ∃ a ∈ W, ends a = e) :
    Nonempty ((openGraph ends W).Walk u v) := by
  induction p with
  | nil => exact ⟨SimpleGraph.Walk.nil⟩
  | @cons u v w hadj p ih =>
    have hmemo : s(u, v) ∈ (SimpleGraph.Walk.cons hadj p).edges := by
      rw [SimpleGraph.Walk.edges_cons]; exact List.mem_cons_self ..
    obtain ⟨a, haW, hva⟩ := h s(u, v) hmemo
    have hadj' : (openGraph ends W).Adj u v := by
      rw [openGraph_adj]
      exact ⟨⟨a, haW, hva⟩, hadj.ne⟩
    obtain ⟨p'⟩ := ih (fun e he => h e (by
      rw [SimpleGraph.Walk.edges_cons]; exact List.mem_cons_of_mem _ he))
    exact ⟨SimpleGraph.Walk.cons hadj' p'⟩

theorem mem_walkLabels {ends : E → Sym2 V} {s : Finset E} {u v : V}
    (p : (openGraph ends s).Walk u v) {a : E} :
    a ∈ s.filter (fun a => ends a ∈ p.edges) ↔ a ∈ s ∧ ends a ∈ p.edges :=
  Finset.mem_filter

theorem walk_restrict {ends : E → Sym2 V} {s : Finset E} {u v : V}
    (p : (openGraph ends s).Walk u v) :
    Nonempty ((openGraph ends (s.filter fun a => ends a ∈ p.edges)).Walk u v) := by
  classical
  apply nonempty_walk_of_edges p
  intro e he
  have h1 : e ∈ (openGraph ends s).edgeSet := SimpleGraph.Walk.edges_subset_edgeSet p he
  rw [openGraph, SimpleGraph.edgeSet_fromEdgeSet] at h1
  obtain ⟨a, ha, rfl⟩ := h1.1
  exact ⟨a, Finset.mem_filter.mpr ⟨ha, he⟩, rfl⟩

/-! ### The three-arm decomposition -/

/-- `ArmsGood ends s x y z n` : there are walks from `x`, `y`, `z` to a common vertex whose
total length is `n`. -/
def ArmsGood (ends : E → Sym2 V) (s : Finset E) (x y z : V) (n : ℕ) : Prop :=
  ∃ (w : V) (p : (openGraph ends s).Walk x w) (q : (openGraph ends s).Walk y w)
    (r : (openGraph ends s).Walk z w), p.length + q.length + r.length = n

theorem length_pos_of_ne {G : SimpleGraph V} {u v : V} (p : G.Walk u v) (h : u ≠ v) :
    0 < p.length := by
  rcases Nat.eq_zero_or_pos p.length with h0 | h0
  · exact absurd (p.eq_of_length_eq_zero h0) h
  · exact h0

/-- Length bookkeeping for the "move the centre" step: if the arms `P` (from `a`) and `Q`
(from `b`) meet at a vertex `u ≠ w`, then the triple consisting of `P` truncated at `u`,
`Q` truncated at `u` and the arm `R` extended along the tail of `P` has strictly smaller
total length, and its three walks have the common endpoint `u`. -/
theorem shorten_total {G : SimpleGraph V} {a b c w : V}
    (P : G.Walk a w) (Q : G.Walk b w) (R : G.Walk c w) {u : V}
    (huP : u ∈ P.support) (huQ : u ∈ Q.support) (huw : u ≠ w) :
    (R.append (P.dropUntil u huP).reverse).length + (P.takeUntil u huP).length
        + (Q.takeUntil u huQ).length < P.length + Q.length + R.length := by
  have hR : (R.append (P.dropUntil u huP).reverse).length
      = R.length + (P.dropUntil u huP).length := by
    rw [SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_reverse]
  have hP : (P.takeUntil u huP).length + (P.dropUntil u huP).length = P.length := by
    have h := congrArg SimpleGraph.Walk.length (SimpleGraph.Walk.take_spec (p := P) huP)
    rwa [SimpleGraph.Walk.length_append] at h
  have hQ : (Q.takeUntil u huQ).length + (Q.dropUntil u huQ).length = Q.length := by
    have h := congrArg SimpleGraph.Walk.length (SimpleGraph.Walk.take_spec (p := Q) huQ)
    rwa [SimpleGraph.Walk.length_append] at h
  have hpos : 0 < (Q.dropUntil u huQ).length := length_pos_of_ne _ huw
  omega

/-- **Three-arm (branch point) decomposition.** If `x`, `y` and `z` lie in a common
component of the open graph of `s`, then there is a vertex `w` and three walks from
`x`, `y`, `z` to `w` whose edge lists are pairwise disjoint. -/
theorem exists_three_arms (ends : E → Sym2 V) (s : Finset E) {x y z : V}
    (hxy : Conn ends s x y) (hxz : Conn ends s x z) :
    ∃ (w : V) (p : (openGraph ends s).Walk x w) (q : (openGraph ends s).Walk y w)
      (r : (openGraph ends s).Walk z w),
      p.edges.Disjoint q.edges ∧ p.edges.Disjoint r.edges ∧ q.edges.Disjoint r.edges := by
  classical
  obtain ⟨pxy⟩ := hxy
  obtain ⟨pxz⟩ := hxz
  have hex : ∃ n, ArmsGood ends s x y z n :=
    ⟨pxy.length + pxz.length, x, SimpleGraph.Walk.nil, pxy.reverse, pxz.reverse, by
      simp [SimpleGraph.Walk.length_reverse]⟩
  obtain ⟨w, p, q, r, hlen⟩ := Nat.find_spec hex
  have hmin : ∀ (w' : V) (p' : (openGraph ends s).Walk x w')
      (q' : (openGraph ends s).Walk y w') (r' : (openGraph ends s).Walk z w'),
      Nat.find hex ≤ p'.length + q'.length + r'.length :=
    fun w' p' q' r' => Nat.find_min' hex ⟨w', p', q', r', rfl⟩
  have hpq : ∀ {u : V}, u ∈ p.support → u ∈ q.support → u = w := by
    intro u huP huQ
    by_contra hne
    have hlt := shorten_total p q r huP huQ hne
    have hge := hmin u (p.takeUntil u huP) (q.takeUntil u huQ)
      (r.append (p.dropUntil u huP).reverse)
    omega
  have hpr : ∀ {u : V}, u ∈ p.support → u ∈ r.support → u = w := by
    intro u huP huR
    by_contra hne
    have hlt := shorten_total p r q huP huR hne
    have hge := hmin u (p.takeUntil u huP) (q.append (p.dropUntil u huP).reverse)
      (r.takeUntil u huR)
    omega
  have hqr : ∀ {u : V}, u ∈ q.support → u ∈ r.support → u = w := by
    intro u huQ huR
    by_contra hne
    have hlt := shorten_total q r p huQ huR hne
    have hge := hmin u (p.append (q.dropUntil u huQ).reverse) (q.takeUntil u huQ)
      (r.takeUntil u huR)
    omega
  refine ⟨w, p, q, r, ?_, ?_, ?_⟩
  · rw [List.disjoint_left]
    intro e hep heq
    induction e using Sym2.ind with
    | h a b =>
      have hne : a ≠ b := (SimpleGraph.Walk.adj_of_mem_edges p hep).ne
      have hap : a ∈ p.support := mem_support_of_mem_edges hep (Sym2.mem_mk_left a b)
      have haq : a ∈ q.support := mem_support_of_mem_edges heq (Sym2.mem_mk_left a b)
      have hbp : b ∈ p.support := mem_support_of_mem_edges hep (Sym2.mem_mk_right a b)
      have hbq : b ∈ q.support := mem_support_of_mem_edges heq (Sym2.mem_mk_right a b)
      have h1 := hpq hap haq
      have h2 := hpq hbp hbq
      exact hne (h1.trans h2.symm)
  · rw [List.disjoint_left]
    intro e hep her
    induction e using Sym2.ind with
    | h a b =>
      have hne : a ≠ b := (SimpleGraph.Walk.adj_of_mem_edges p hep).ne
      have hap : a ∈ p.support := mem_support_of_mem_edges hep (Sym2.mem_mk_left a b)
      have har : a ∈ r.support := mem_support_of_mem_edges her (Sym2.mem_mk_left a b)
      have hbp : b ∈ p.support := mem_support_of_mem_edges hep (Sym2.mem_mk_right a b)
      have hbr : b ∈ r.support := mem_support_of_mem_edges her (Sym2.mem_mk_right a b)
      have h1 := hpr hap har
      have h2 := hpr hbp hbr
      exact hne (h1.trans h2.symm)
  · rw [List.disjoint_left]
    intro e heq her
    induction e using Sym2.ind with
    | h a b =>
      have hne : a ≠ b := (SimpleGraph.Walk.adj_of_mem_edges q heq).ne
      have haq : a ∈ q.support := mem_support_of_mem_edges heq (Sym2.mem_mk_left a b)
      have har : a ∈ r.support := mem_support_of_mem_edges her (Sym2.mem_mk_left a b)
      have hbq : b ∈ q.support := mem_support_of_mem_edges heq (Sym2.mem_mk_right a b)
      have hbr : b ∈ r.support := mem_support_of_mem_edges her (Sym2.mem_mk_right a b)
      have h1 := hqr haq har
      have h2 := hqr hbq hbr
      exact hne (h1.trans h2.symm)

end PercLib.CriticalLRP.TreeGraph
