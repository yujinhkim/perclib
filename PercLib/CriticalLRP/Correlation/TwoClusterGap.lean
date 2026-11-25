/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
# A repaired chain for Lemma I.4.12: the two-cluster difference bound

Source: Tom Hutchcroft, *Critical long-range percolation I: High effective dimension*,
arXiv:2508.18807v1, Lemma I.4.12 and its proof (p. 39):

  `P(0↔x) P(y↔z) − P(0↔x ↮ y↔z) ≤ ∑_{a,b} P(0↔a) P(a↔x) P(a↔b) P(y↔b) P(b↔z)`.

The printed proof uses the restoration coupling `ω̃ = forceOn (touchSet ω 0)ᶜ ω' ω` (the base
configuration `ω` is kept on the edges touching `K_0`, the independent copy `ω'` off them) and then
reads `K_y` as the cluster of `y` in the base configuration `ω`.  With that reading two steps of
the printed proof fail:

* `K_y ⊆ K̃_y` on `{y ∉ K_0}` is false (`not_cluster_subset_forceOn_compl`);
* consequently `{z ∈ K̃_y \ K_y}` does not carry the structure the proof uses (see also
  `not_fresh_disjoint_connections`).

The chain below keeps the printed coupling and its (proved) law preservation, but reads `K_y` as
the cluster of `y` in the **fresh** copy `ω'`.  Then everything the printed proof wants is true:

* `mem_fresh_of_forceOn_compl_of_avoid` : in `ω̃ = forceOn (touchSet ω₁ o)ᶜ ω₂ ω₁`, a walk avoiding
  `K_0(ω₁)` consists of **fresh** edges (`ω₂`), and a walk inside `K_0(ω₁)` consists of **base**
  edges — the exact fresh/base division the paper's prose describes;
* `disjointOcc_restore` : if `x ∈ K_0(ω₁)` and `ω₂` joins `y` to `z` off `K_0(ω₁)`, then the
  restored configuration has **disjoint** witnesses for `0↔x` and `y↔z`; since `ω̃` has the same
  law, this is exactly the comparison of `P(0↔x)P(y↔z)` with `P(0↔x ↮ y↔z)`;
* `exists_fresh_disjOcc_of_no_avoid` : if `ω₂` joins `y` to `z` but every fresh walk from `y` to
  `z` visits `K_0(ω₁)`, then some `b ∈ K_0(ω₁)` lies on a simple fresh path, whose two halves are
  edge-disjoint: `y↔b` and `b↔z` occur **disjointly in `ω₂`**.  This replaces the paper's "`b ∈ K_0`
  connected to `y` and `z` by disjoint paths in `ω'`" by a true statement.

The probabilistic half uses only

1. independence of `ω₁` and `ω₂` under `μ.prod μ`, so that `P(0↔x)P(y↔z)` *is* the probability of
   a joint event in the two-copy space (no independence of `ω` and `ω̃` is ever assumed, and the
   resampled cluster `K̃_0` is never claimed to be unchanged);
2. the law preservation of the printed map (`edgeMeasure_map_forceOn_touchSet_compl`);
3. BK in the fresh copy;
4. the two-leaf tree-graph inequality for the two connections from the origin.

Items 3 and 4 enter as explicit hypotheses `hBK`, `hTG`.  BK is available unconditionally in the
repository (`edgeMeasure_bk`); item 4 is the tree-graph inequality, proved in the repository for
*finite* edge types (`TreeGraph.three_point_tree_graph'`) but **not yet** transported to the
canonical countable model with an infinite edge set.  That transport is the one remaining gap in
fully formalizing Lemma I.4.12, and it is named here rather than hidden.

Conclusion (`twoCluster_gap_le`, in additive `ℝ≥0∞` form, equivalent to the paper's subtraction):

  `P(0↔x) P(y↔z) ≤ P(0↔x ↮ y↔z) + ∑_a ∑_b P(0↔a) P(a↔x) P(a↔b) P(y↔b) P(b↔z)`.

No `sorry`, no custom axioms.
-/
module

public import PercLib.CriticalLRP.BK.CanonicalBridge
public import PercLib.CriticalLRP.CountableProduct.RestorationCompl

set_option autoImplicit true

set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

@[expose] public section

open MeasureTheory Measure ProbabilityTheory unitInterval
open scoped ENNReal NNReal

namespace PercLib.CriticalLRP

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Countable V]

/-! ## Membership bookkeeping for the printed restoration map -/

/-- Membership form of `forceOn_apply_of_mem`. -/
theorem mem_forceOn_of_mem' {S : Set (Sym2 V)} {e : Sym2 V} (he : e ∈ S) (η ω : Config V) :
    (e ∈ forceOn S η ω ↔ e ∈ η) :=
  iff_of_eq (forceOn_apply_of_mem he η ω)

/-- Every vertex on an open walk from `y` lies in the cluster of `y`. -/
theorem mem_cluster_of_mem_support {ω : Config V} {y : V} :
    ∀ {z : V} (p : (⊤ : SimpleGraph V).Walk y z), (∀ e ∈ p.edges, e ∈ ω) →
      ∀ v ∈ p.support, v ∈ cluster ω y
  | _, .nil, _, v, hv => by
      simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at hv
      subst hv
      exact cluster_mem_self ω v
  | _, .cons h p', hp, v, hv => by
      rename_i z m
      have hfirst : s(y, m) ∈ ω := hp _ (by
        rw [SimpleGraph.Walk.edges_cons]; exact List.mem_cons_self ..)
      have hne : y ≠ m := (SimpleGraph.top_adj y m).1 h
      have hconn : Connects ω y m := by
        rw [Connects, SimpleGraph.reachable_iff_reflTransGen]
        exact Relation.ReflTransGen.single (by rw [openGraph_adj]; exact ⟨hne, hfirst⟩)
      have htail : ∀ e ∈ p'.edges, e ∈ ω := fun e he => hp e (by
        rw [SimpleGraph.Walk.edges_cons]; exact List.mem_cons_of_mem _ he)
      rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hv
      rcases hv with hvy | hv
      · rw [hvy]; exact cluster_mem_self ω y
      · have hmem : v ∈ cluster ω m := mem_cluster_of_mem_support p' htail v hv
        have heq : cluster ω y = cluster ω m := cluster_eq_iff.mpr hconn
        exact heq ▸ hmem

/-- Every edge of an open walk from `o` touches the cluster of `o`. -/
theorem edges_subset_touchSet {ω : Config V} {o : V} {z : V}
    (p : (⊤ : SimpleGraph V).Walk o z) (hp : ∀ e ∈ p.edges, e ∈ ω) :
    ∀ e ∈ p.edges, e ∈ touchSet ω o := by
  intro e
  induction e using Sym2.ind with
  | _ a b =>
      intro he
      refine mem_touchSet.mpr ⟨a, Sym2.mem_mk_left a b, mem_cluster_of_mem_support p hp a ?_⟩
      exact SimpleGraph.Walk.mem_support_iff_exists_mem_edges.mpr
        (Or.inr ⟨s(a, b), he, Sym2.mem_mk_left a b⟩)

/-! ## The deterministic facts for the printed coupling

`ω₁` is the base configuration, `ω₂` the fresh one, and `ω̃ = forceOn (touchSet ω₁ o)ᶜ ω₂ ω₁` the
restored configuration.  `K_0 = cluster ω₁ o` is the *old* cluster of the origin. -/

/-- **Fresh regime.**  A walk in the restored configuration whose vertices avoid the old `K_0`
consists of fresh edges. -/
theorem mem_fresh_of_forceOn_compl_of_avoid {ω₁ ω₂ : Config V} {o : V} {y z : V}
    (p : (⊤ : SimpleGraph V).Walk y z)
    (hp : ∀ e ∈ p.edges, e ∈ forceOn (touchSet ω₁ o)ᶜ ω₂ ω₁)
    (hav : ∀ v ∈ p.support, v ∉ cluster ω₁ o) :
    ∀ e ∈ p.edges, e ∈ ω₂ := by
  intro e he
  have hoff : e ∈ (touchSet ω₁ o)ᶜ := by
    rw [Set.mem_compl_iff]
    intro hmem
    obtain ⟨v, hv, hvc⟩ := mem_touchSet.mp hmem
    exact hav v (SimpleGraph.Walk.mem_support_iff_exists_mem_edges.mpr (Or.inr ⟨e, he, hv⟩)) hvc
  exact (mem_forceOn_of_mem' hoff ω₂ ω₁).mp (hp e he)

/-- **Comparing the product with the disjoint occurrence.**  If `x` lies in the old cluster `K_0`
and the fresh configuration joins `y` to `z` by a walk avoiding `K_0`, then the restored
configuration has disjoint witnesses for `0↔x` and `y↔z`. -/
theorem disjointOcc_restore {ω₁ ω₂ : Config V} {o x y z : V}
    (hx : x ∈ cluster ω₁ o)
    (p : (⊤ : SimpleGraph V).Walk y z) (hp : ∀ e ∈ p.edges, e ∈ ω₂)
    (hav : ∀ v ∈ p.support, v ∉ cluster ω₁ o) :
    Percolation.DisjointOccurrence (connSet o x) (connSet y z)
      (forceOn (touchSet ω₁ o)ᶜ ω₂ ω₁) := by
  classical
  obtain ⟨q, hq⟩ := pathConnects_iff.mpr (mem_cluster_iff.mp hx)
  have hqT : ∀ e ∈ q.edges, e ∈ touchSet ω₁ o := edges_subset_touchSet q hq
  have hqopen : ∀ e ∈ q.edges, e ∈ forceOn (touchSet ω₁ o)ᶜ ω₂ ω₁ := by
    intro e he
    exact (mem_forceOn_of_notMem (S := (touchSet ω₁ o)ᶜ) (by simpa using hqT e he) ω₂ ω₁).mpr
      (hq e he)
  have hpopen : ∀ e ∈ p.edges, e ∈ forceOn (touchSet ω₁ o)ᶜ ω₂ ω₁ := by
    intro e he
    have hoff : e ∈ (touchSet ω₁ o)ᶜ := by
      rw [Set.mem_compl_iff]
      intro hmem
      obtain ⟨v, hv, hvc⟩ := mem_touchSet.mp hmem
      exact hav v (SimpleGraph.Walk.mem_support_iff_exists_mem_edges.mpr (Or.inr ⟨e, he, hv⟩)) hvc
    exact (mem_forceOn_of_mem' hoff ω₂ ω₁).mpr (hp e he)
  refine ⟨q.edges.toFinset, p.edges.toFinset, ?_, ?_, ?_, ?_, ?_⟩
  · intro e he
    rw [Finset.mem_coe, List.mem_toFinset] at he
    exact hqopen e he
  · intro e he
    rw [Finset.mem_coe, List.mem_toFinset] at he
    exact hpopen e he
  · refine Finset.disjoint_left.mpr fun e he he' => ?_
    rw [List.mem_toFinset] at he he'
    have h1 : e ∈ touchSet ω₁ o := hqT e he
    have h2 : e ∈ (touchSet ω₁ o)ᶜ := by
      rw [Set.mem_compl_iff]
      intro hmem
      obtain ⟨v, hv, hvc⟩ := mem_touchSet.mp hmem
      exact hav v (SimpleGraph.Walk.mem_support_iff_exists_mem_edges.mpr (Or.inr ⟨e, he', hv⟩)) hvc
    exact absurd h1 h2
  · refine pathConnects_iff.mp ⟨q, fun e he => ?_⟩
    exact List.mem_toFinset.mpr he
  · refine pathConnects_iff.mp ⟨p, fun e he => ?_⟩
    exact List.mem_toFinset.mpr he

/-- **The "new connections" alternative.**  If the fresh configuration joins `y` to `z` and *no*
fresh walk from `y` to `z` avoids `K_0`, then some `b ∈ K_0` lies on a simple fresh path from `y`
to `z`; splitting that path at `b` gives edge-disjoint witnesses for `y↔b` and `b↔z` inside the
fresh configuration. -/
theorem exists_fresh_disjOcc_of_no_avoid {ω₁ ω₂ : Config V} {o y z : V}
    (hyz : Connects ω₂ y z)
    (hno : ¬ ∃ p : (⊤ : SimpleGraph V).Walk y z,
      (∀ e ∈ p.edges, e ∈ ω₂) ∧ (∀ v ∈ p.support, v ∉ cluster ω₁ o)) :
    ∃ b ∈ cluster ω₁ o,
      Percolation.DisjointOccurrence (connSet y b) (connSet b z) ω₂ := by
  classical
  obtain ⟨p, hp⟩ := pathConnects_iff.mpr hyz
  have hPopen : ∀ e ∈ p.bypass.edges, e ∈ ω₂ := fun e he =>
    hp e (SimpleGraph.Walk.edges_bypass_subset_edges p he)
  have hPpath : p.bypass.IsPath := SimpleGraph.Walk.bypass_isPath p
  have hPsub : ∀ v ∈ p.bypass.support, v ∈ p.support := fun v hv =>
    SimpleGraph.Walk.support_bypass_subset_support p hv
  have hex : ∃ b ∈ p.bypass.support, b ∈ cluster ω₁ o := by
    by_contra hcon
    exact hno ⟨p.bypass, hPopen, fun v hv => by
      by_contra hvc
      exact hcon ⟨v, hv, hvc⟩⟩
  obtain ⟨b, hbsupp, hbK⟩ := hex
  refine ⟨b, hbK, ?_⟩
  have hsplit : (p.bypass.takeUntil b hbsupp).append (p.bypass.dropUntil b hbsupp) = p.bypass :=
    SimpleGraph.Walk.take_spec p.bypass hbsupp
  have hnodup : ((p.bypass.takeUntil b hbsupp).edges ++
      (p.bypass.dropUntil b hbsupp).edges).Nodup := by
    rw [← SimpleGraph.Walk.edges_append, hsplit]
    exact hPpath.isTrail.edges_nodup
  have hdisj : List.Disjoint (p.bypass.takeUntil b hbsupp).edges
      (p.bypass.dropUntil b hbsupp).edges :=
    (List.nodup_append'.mp hnodup).2.2
  have h1 : ∀ e ∈ (p.bypass.takeUntil b hbsupp).edges, e ∈ ω₂ := fun e he =>
    hPopen e (SimpleGraph.Walk.edges_takeUntil_subset_edges p.bypass hbsupp he)
  have h2 : ∀ e ∈ (p.bypass.dropUntil b hbsupp).edges, e ∈ ω₂ := fun e he =>
    hPopen e (SimpleGraph.Walk.edges_dropUntil_subset_edges p.bypass hbsupp he)
  refine ⟨(p.bypass.takeUntil b hbsupp).edges.toFinset,
    (p.bypass.dropUntil b hbsupp).edges.toFinset, ?_, ?_, ?_, ?_, ?_⟩
  · intro e he
    rw [Finset.mem_coe, List.mem_toFinset] at he
    exact h1 e he
  · intro e he
    rw [Finset.mem_coe, List.mem_toFinset] at he
    exact h2 e he
  · refine Finset.disjoint_left.mpr fun e he he' => ?_
    rw [List.mem_toFinset] at he he'
    exact hdisj he he'
  · refine pathConnects_iff.mp ⟨p.bypass.takeUntil b hbsupp, fun e he => ?_⟩
    exact List.mem_toFinset.mpr he
  · refine pathConnects_iff.mp ⟨p.bypass.dropUntil b hbsupp, fun e he => ?_⟩
    exact List.mem_toFinset.mpr he

/-! ## Measurability and the two-copy comparison -/

/-- The restoration map in the paper's orientation: the base configuration is the second
coordinate, the fresh one the first. -/
noncomputable def restoreMap (o : V) : Config V × Config V → Config V :=
  fun p => forceOn (touchSet p.2 o)ᶜ p.1 p.2

theorem measurable_restoreMap (o : V) : Measurable (restoreMap (V := V) o) := by
  have hswap : restoreMap (V := V) o =
      (fun q : Config V × Config V => forceOn (touchSet q.1 o)ᶜ q.2 q.1) ∘ Prod.swap := rfl
  rw [hswap]
  exact (measurable_forceOn_compl_pair (S := fun ω : Config V => touchSet ω o)
    (fun e => measurableSet_mem_touchSet o e)).comp measurable_swap

theorem map_restoreMap (π : Sym2 V → unitInterval) (o : V) :
    ((edgeMeasure π).prod (edgeMeasure π)).map (restoreMap (V := V) o) = edgeMeasure π :=
  edgeMeasure_map_forceOn_touchSet_compl π o

/-- The disjoint-occurrence event `a↔b ↮ c↔d`. -/
def disjSet (a b c d : V) : Set (Config V) :=
  Percolation.DisjointOccurrence (connSet a b) (connSet c d)

theorem measurableSet_disjSet (a b c d : V) : MeasurableSet (disjSet a b c d) :=
  Percolation.measurableSet_finiteWitness _
    (Percolation.disjointOccurrence_upper _ _)
    (Percolation.finiteWitness_disjointOccurrence _ _)

/-- The two-copy event whose probability is the product `P(0↔x) P(y↔z)`: the fresh coordinate
carries `y↔z`, the base coordinate carries `0↔x`. -/
def pairSet (o x y z : V) : Set (Config V × Config V) :=
  connSet y z ×ˢ connSet o x

theorem measure_pairSet (π : Sym2 V → unitInterval) (o x y z : V) :
    ((edgeMeasure π).prod (edgeMeasure π)) (pairSet o x y z)
      = (edgeMeasure π) (connSet y z) * (edgeMeasure π) (connSet o x) :=
  Measure.prod_prod _ _

/-- Reassociation used to match the paper's display. -/
theorem mul_five_rearrange (p q r s t : ℝ≥0∞) :
    s * t * (p * q * r) = p * q * r * s * t := by
  rw [mul_comm (s * t) (p * q * r), ← mul_assoc]

/-! ## The repaired inequality -/

/-- **Lemma I.4.12, repaired.**  Write `τ(u,v) = P(u↔v)`.  Then

  `τ(o,x) τ(y,z) ≤ P(o↔x ↮ y↔z) + ∑_a ∑_b τ(o,a) τ(a,x) τ(a,b) τ(y,b) τ(b,z)`,

i.e. `τ(o,x) τ(y,z) − P(o↔x ↮ y↔z) ≤ ∑_{a,b} τ(o,a) τ(a,x) τ(a,b) τ(y,b) τ(b,z)`.

The two probabilistic inputs are the hypotheses `hBK` (BK in the fresh copy) and `hTG` (the
two-leaf tree-graph inequality for the two connections from `o`); both are stated for the measure
`edgeMeasure π`.  All deterministic and coupling content is proved. -/
theorem twoCluster_gap_le (π : Sym2 V → unitInterval) (o x y z : V)
    (hTG : ∀ b : V, (edgeMeasure π) (connSet o x ∩ connSet o b)
      ≤ ∑' a : V, (edgeMeasure π) (connSet o a) * (edgeMeasure π) (connSet a x)
          * (edgeMeasure π) (connSet a b))
    (hBK : ∀ b : V, (edgeMeasure π) (disjSet y b b z)
      ≤ (edgeMeasure π) (connSet y b) * (edgeMeasure π) (connSet b z)) :
    (edgeMeasure π) (connSet o x) * (edgeMeasure π) (connSet y z) ≤
      (edgeMeasure π) (disjSet o x y z) +
        ∑' a : V, ∑' b : V, (edgeMeasure π) (connSet o a) * (edgeMeasure π) (connSet a x)
          * (edgeMeasure π) (connSet a b) * (edgeMeasure π) (connSet y b)
          * (edgeMeasure π) (connSet b z) := by
  classical
  -- the deterministic covering of the two-copy event
  have hcover : pairSet o x y z ⊆ restoreMap o ⁻¹' disjSet o x y z ∪
      ⋃ b : V, (disjSet y b b z ×ˢ (connSet o x ∩ connSet o b)) := by
    rintro ⟨ω₂, ω₁⟩ ⟨h1, h2⟩
    -- `h1 : Connects ω₂ y z`, `h2 : Connects ω₁ o x`
    by_cases hex : ∃ p : (⊤ : SimpleGraph V).Walk y z,
        (∀ e ∈ p.edges, e ∈ ω₂) ∧ (∀ v ∈ p.support, v ∉ cluster ω₁ o)
    · exact Or.inl (disjointOcc_restore (mem_cluster_iff.mpr h2) hex.choose
        hex.choose_spec.1 hex.choose_spec.2)
    · obtain ⟨b, hbK, hb⟩ := exists_fresh_disjOcc_of_no_avoid h1 hex
      exact Or.inr (Set.mem_iUnion.mpr ⟨b, hb, h2, mem_cluster_iff.mp hbK⟩)
  -- (1) the two-copy probability is bounded by the two pieces
  have hmap : ((edgeMeasure π).prod (edgeMeasure π)) (restoreMap o ⁻¹' disjSet o x y z)
      = (edgeMeasure π) (disjSet o x y z) := by
    rw [← Measure.map_apply (measurable_restoreMap o) (measurableSet_disjSet o x y z)]
    exact congrArg (fun ν => ν (disjSet o x y z)) (map_restoreMap π o)
  have hstep1 : ((edgeMeasure π).prod (edgeMeasure π)) (pairSet o x y z) ≤
      (edgeMeasure π) (disjSet o x y z) +
        ∑' b : V, (edgeMeasure π) (disjSet y b b z)
          * (edgeMeasure π) (connSet o x ∩ connSet o b) := by
    refine le_trans (measure_mono hcover) ?_
    refine le_trans (measure_union_le _ _) (add_le_add (le_of_eq hmap) ?_)
    refine le_trans (measure_iUnion_le _) (ENNReal.tsum_le_tsum fun b => ?_)
    exact le_of_eq (Measure.prod_prod _ _)
  -- (2) combine with BK and the tree-graph inequality
  have hstep2 : (∑' b : V, (edgeMeasure π) (disjSet y b b z)
        * (edgeMeasure π) (connSet o x ∩ connSet o b)) ≤
      ∑' b : V, ((edgeMeasure π) (connSet y b) * (edgeMeasure π) (connSet b z))
        * (∑' a : V, (edgeMeasure π) (connSet o a) * (edgeMeasure π) (connSet a x)
            * (edgeMeasure π) (connSet a b)) :=
    ENNReal.tsum_le_tsum fun b => mul_le_mul' (hBK b) (hTG b)
  -- (3) reassociate into the paper's double sum
  have hstep3 : (∑' b : V, ((edgeMeasure π) (connSet y b) * (edgeMeasure π) (connSet b z))
        * (∑' a : V, (edgeMeasure π) (connSet o a) * (edgeMeasure π) (connSet a x)
            * (edgeMeasure π) (connSet a b))) =
      ∑' a : V, ∑' b : V, (edgeMeasure π) (connSet o a) * (edgeMeasure π) (connSet a x)
        * (edgeMeasure π) (connSet a b) * (edgeMeasure π) (connSet y b)
        * (edgeMeasure π) (connSet b z) := by
    have h1 : (∑' b : V, ((edgeMeasure π) (connSet y b) * (edgeMeasure π) (connSet b z))
          * (∑' a : V, (edgeMeasure π) (connSet o a) * (edgeMeasure π) (connSet a x)
              * (edgeMeasure π) (connSet a b))) =
        ∑' b : V, ∑' a : V, ((edgeMeasure π) (connSet y b) * (edgeMeasure π) (connSet b z))
          * ((edgeMeasure π) (connSet o a) * (edgeMeasure π) (connSet a x)
              * (edgeMeasure π) (connSet a b)) := by
      refine tsum_congr fun b => ?_
      rw [← ENNReal.tsum_mul_left]
    rw [h1, ENNReal.tsum_comm]
    exact tsum_congr fun a => tsum_congr fun b => mul_five_rearrange _ _ _ _ _
  calc (edgeMeasure π) (connSet o x) * (edgeMeasure π) (connSet y z)
      = ((edgeMeasure π).prod (edgeMeasure π)) (pairSet o x y z) := by
        rw [measure_pairSet, mul_comm]
    _ ≤ (edgeMeasure π) (disjSet o x y z) +
          ∑' b : V, (edgeMeasure π) (disjSet y b b z)
            * (edgeMeasure π) (connSet o x ∩ connSet o b) := hstep1
    _ ≤ (edgeMeasure π) (disjSet o x y z) +
          ∑' b : V, ((edgeMeasure π) (connSet y b) * (edgeMeasure π) (connSet b z))
            * (∑' a : V, (edgeMeasure π) (connSet o a) * (edgeMeasure π) (connSet a x)
                * (edgeMeasure π) (connSet a b)) := add_le_add le_rfl hstep2
    _ = (edgeMeasure π) (disjSet o x y z) +
          ∑' a : V, ∑' b : V, (edgeMeasure π) (connSet o a) * (edgeMeasure π) (connSet a x)
            * (edgeMeasure π) (connSet a b) * (edgeMeasure π) (connSet y b)
            * (edgeMeasure π) (connSet b z) := by rw [hstep3]

/-! ## Discharging BK, and the version for the paper's law `P_β` -/

/-- **BK for connection events, in `ℝ≥0∞` form.**  `P(a↔b ↮ c↔d) ≤ P(a↔b) P(c↔d)`; this is
`Percolation.bkEdge` transported to the canonical model by `edgeMeasure_bk`. -/
theorem bk_connSet_ennreal (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1) (a b c d : V) :
    (edgeMeasure π) (disjSet a b c d)
      ≤ (edgeMeasure π) (connSet a b) * (edgeMeasure π) (connSet c d) := by
  have h := edgeMeasure_bk π hπ (connSet a b) (connSet c d) (isUpper_connSet a b)
    (isUpper_connSet c d) (finiteWitness_connSet a b) (finiteWitness_connSet c d)
  refine (ENNReal.toReal_le_toReal (measure_ne_top _ _)
    (ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _))).mp ?_
  rw [ENNReal.toReal_mul]
  exact h

/-- **Lemma I.4.12, repaired, with BK discharged.**  Only the two-leaf tree-graph inequality
`hTG` remains as a hypothesis. -/
theorem twoCluster_gap_le' (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1) (o x y z : V)
    (hTG : ∀ b : V, (edgeMeasure π) (connSet o x ∩ connSet o b)
      ≤ ∑' a : V, (edgeMeasure π) (connSet o a) * (edgeMeasure π) (connSet a x)
          * (edgeMeasure π) (connSet a b)) :
    (edgeMeasure π) (connSet o x) * (edgeMeasure π) (connSet y z) ≤
      (edgeMeasure π) (disjSet o x y z) +
        ∑' a : V, ∑' b : V, (edgeMeasure π) (connSet o a) * (edgeMeasure π) (connSet a x)
          * (edgeMeasure π) (connSet a b) * (edgeMeasure π) (connSet y b)
          * (edgeMeasure π) (connSet b z) :=
  twoCluster_gap_le π o x y z hTG (fun b => bk_connSet_ennreal π hπ y b b z)

/-- **Lemma I.4.12, repaired, for the law `P_β` of §I.1.2** (`β ≥ 0`, `J ≥ 0`); only the
two-leaf tree-graph inequality remains as a hypothesis. -/
theorem longRange_twoCluster_gap_le (J : Sym2 V → ℝ) (hJ : ∀ e, 0 ≤ J e) (β : NNReal)
    (o x y z : V)
    (hTG : ∀ b : V, (longRangeMeasure J hJ β) (connSet o x ∩ connSet o b)
      ≤ ∑' a : V, (longRangeMeasure J hJ β) (connSet o a)
          * (longRangeMeasure J hJ β) (connSet a x)
          * (longRangeMeasure J hJ β) (connSet a b)) :
    (longRangeMeasure J hJ β) (connSet o x) * (longRangeMeasure J hJ β) (connSet y z) ≤
      (longRangeMeasure J hJ β) (disjSet o x y z) +
        ∑' a : V, ∑' b : V, (longRangeMeasure J hJ β) (connSet o a)
          * (longRangeMeasure J hJ β) (connSet a x)
          * (longRangeMeasure J hJ β) (connSet a b)
          * (longRangeMeasure J hJ β) (connSet y b)
          * (longRangeMeasure J hJ β) (connSet b z) :=
  twoCluster_gap_le' (bernoulliEdgeProb J hJ β) (fun e => bernoulliEdgeProb_lt_one hJ β e)
    o x y z hTG

end PercLib.CriticalLRP
