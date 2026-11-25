/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

module

public import PercLib.CriticalLRP.BK.Lift

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

set_option autoImplicit true

/-!
# Graph consequences of the BK inequality

This file derives, for the edge-dependent Bernoulli model `edgeLaw p` of `EdgeBK.lean` on a
countable edge set (Hutchcroft's `P_β`), the consequences
of the BK inequality that Hutchcroft, arXiv:2508.18807, records in Section I.2.1:

* `twoCluster_bk` : the two-cluster correlation inequality in event/indicator form
  (Lemma I.2.1(i));
* `twoCluster_middle`, `twoCluster_upper` : the companion inequalities of Lemma I.2.1;
* `threePoint_bk` : Lemma I.2.2;
* `bk_list` : the iterated (finite disjoint-occurrence) form of BK used in the tree-graph
  arguments, e.g. in the proof of Lemma I.4.16.
-/

@[expose] public section

namespace PercLib.CriticalLRP

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section ClusterDetermined
attribute [local instance] Classical.propDecidable

/-- An event is determined by the cluster of `x` if it only depends on that cluster.  Events of the
form `{F(K_x) ≥ t}` for an increasing functional `F` are of this type. -/
def ClusterDeterminedAt (G : BondGraph V E) (x : V) (A : Set (Set E)) : Prop :=
  ∀ ω ω' : Set E, cluster G ω x = cluster G ω' x → (ω ∈ A ↔ ω' ∈ A)

/-- The set of *open* edges whose endpoints both lie in the cluster of `x`. -/
def internalEdges (G : BondGraph V E) (ω : Set E) (x : V) : Set E :=
  {e | e ∈ ω ∧ ∀ v, v ∈ G e → v ∈ cluster G ω x}

theorem cluster_internalEdges (G : BondGraph V E) (ω : Set E) (x : V) :
    cluster G (internalEdges G ω x) x = cluster G ω x := by
  have hsub : ∀ {z : V}, Conn G (internalEdges G ω x) x z → Conn G ω x z := by
    intro z hz
    induction hz with
    | refl => exact conn_refl G ω x
    | @tail a b _ hstep ih =>
      obtain ⟨e, he, hGe⟩ := hstep
      have hb : b ∈ cluster G ω x := he.2 b (hGe ▸ Sym2.mem_mk_right a b)
      exact ih.tail ⟨e, he.1, hGe⟩
  ext y
  constructor
  · exact hsub
  · intro hy
    have hmain : ∀ {z : V}, Conn G ω x z → Conn G (internalEdges G ω x) x z := by
      intro z hz
      induction hz with
      | refl => exact conn_refl G _ _
      | @tail a b _ hstep ih =>
        obtain ⟨e, he, hGe⟩ := hstep
        have ha : a ∈ cluster G ω x := hsub ih
        have hb : b ∈ cluster G ω x := ha.tail ⟨e, he, hGe⟩
        refine ih.tail ⟨e, ⟨he, ?_⟩, hGe⟩
        intro v hv
        rw [hGe] at hv
        rcases Sym2.mem_iff.mp hv with rfl | rfl
        · exact ha
        · exact hb
    exact hmain hy

/-- Any finitely witnessed event determined by the cluster of `x` has a witness all of whose edges
are open edges internal to that cluster. -/
theorem exists_internal_witness (G : BondGraph V E) (x : V) (A : Set (Set E))
    (hA : ClusterDeterminedAt G x A) (hfA : FiniteWitness A) {ω : Set E} (hω : ω ∈ A) :
    ∃ s : Finset E, (s : Set E) ⊆ ω ∧ (s : Set E) ∈ A ∧
      ∀ e ∈ s, ∀ v, v ∈ G e → v ∈ cluster G ω x := by
  have hω' : internalEdges G ω x ∈ A :=
    (hA ω _ (cluster_internalEdges G ω x).symm).mp hω
  obtain ⟨s, hs, hsa⟩ := hfA _ hω'
  exact ⟨s, fun e he => (hs he).1, hsa, fun e he => (hs he).2⟩

theorem disjoint_of_internal (G : BondGraph V E) (ω : Set E) {x y : V}
    (hxy : ¬ Conn G ω x y) {s t : Finset E}
    (hs : ∀ e ∈ s, ∀ v, v ∈ G e → v ∈ cluster G ω x)
    (ht : ∀ e ∈ t, ∀ v, v ∈ G e → v ∈ cluster G ω y) : Disjoint s t := by
  rcases clusters_eq_or_disjoint G ω x y with heq | hdisj
  · exfalso
    apply hxy
    have hy : y ∈ cluster G ω x := by rw [heq]; exact mem_cluster_self G ω y
    exact hy
  · apply Finset.disjoint_left.mpr
    intro e hes het
    have hvx : (G e).out.1 ∈ cluster G ω x := hs e hes _ (Sym2.out_fst_mem _)
    have hvy : (G e).out.1 ∈ cluster G ω y := ht e het _ (Sym2.out_fst_mem _)
    exact Set.disjoint_left.mp hdisj hvx hvy

end ClusterDetermined

section TwoCluster
attribute [local instance] Classical.propDecidable

/-- `x ↔ y` is measurable (it is a finitely witnessed increasing event). -/
theorem measurableSet_conn [Countable E] (G : BondGraph V E) (x y : V) :
    MeasurableSet {ω | Conn G ω x y} :=
  measurableSet_finiteWitness _ (fun _ _ h hc => conn_mono G h hc) (finiteWitness_conn G x y)

/-- Splitting an event according to `x ↔ y`. -/
theorem measureReal_inter_add_inter_compl [Countable E] (G : BondGraph V E)
    (p : E → unitInterval) (x y : V) (S : Set (Set E)) :
    (edgeLaw p).real (S ∩ {ω | Conn G ω x y}) + (edgeLaw p).real (S ∩ {ω | ¬ Conn G ω x y}) =
      (edgeLaw p).real S := by
  have h := measureReal_inter_add_sdiff (μ := edgeLaw p) (s := S) (t := {ω : Set E | Conn G ω x y})
    (measurableSet_conn G x y)
  have hdiff : S ∩ {ω | ¬ Conn G ω x y} = S \ {ω | Conn G ω x y} := by
    ext ω
    simp [Set.mem_sdiff]
  rwa [hdiff]

/-- **Lemma I.2.1(i)** in indicator form: for increasing finitely witnessed events `A` determined
by the cluster of `x` and `B` determined by the cluster of `y`,
`P(A ∩ B ∩ {x ↮ y}) ≤ P(A) P(B)`. -/
theorem twoCluster_bk [Countable E] (G : BondGraph V E) (p : E → unitInterval)
    (hp : ∀ e, p e < 1) (x y : V)
    (A B : Set (Set E)) (hA : IsUpperSet A) (hfA : FiniteWitness A)
    (hdA : ClusterDeterminedAt G x A) (hB : IsUpperSet B) (hfB : FiniteWitness B)
    (hdB : ClusterDeterminedAt G y B) :
    (edgeLaw p).real (A ∩ B ∩ {ω | ¬ Conn G ω x y}) ≤ (edgeLaw p).real A * (edgeLaw p).real B := by
  have hsub : A ∩ B ∩ {ω | ¬ Conn G ω x y} ⊆ DisjointOccurrence A B := by
    rintro ω ⟨⟨hωA, hωB⟩, hxy⟩
    obtain ⟨s, hs, hsa, hsi⟩ := exists_internal_witness G x A hdA hfA hωA
    obtain ⟨t, ht, hta, hti⟩ := exists_internal_witness G y B hdB hfB hωB
    exact ⟨s, t, hs, ht, disjoint_of_internal G ω hxy hsi hti, hsa, hta⟩
  exact (measureReal_mono hsub).trans (bkEdge p hp A B hA hB hfA hfB)

/-- **Lemma I.2.1(ii)** in indicator form: `P(A)P(B) - P(A ∩ B ∩ {x ↔ y}) ≤ P(A ∩ B ∩ {x ↮ y})`. -/
theorem twoCluster_middle [Countable E] (G : BondGraph V E) (p : E → unitInterval)
    (hp : ∀ e, p e < 1) (x y : V)
    (A B : Set (Set E)) (hA : IsUpperSet A) (hfA : FiniteWitness A)
    (hB : IsUpperSet B) (hfB : FiniteWitness B) :
    (edgeLaw p).real A * (edgeLaw p).real B - (edgeLaw p).real (A ∩ B ∩ {ω | Conn G ω x y}) ≤
      (edgeLaw p).real (A ∩ B ∩ {ω | ¬ Conn G ω x y}) := by
  have hfgk := association_edge_finiteWitness p A B hA hB hfA hfB
  have hsplit := measureReal_inter_add_inter_compl G p x y (A ∩ B)
  have hset : (A ∩ B) ∩ {ω | Conn G ω x y} = A ∩ B ∩ {ω | Conn G ω x y} := by
    ext ω; simp [and_assoc]
  have hset2 : (A ∩ B) ∩ {ω | ¬ Conn G ω x y} = A ∩ B ∩ {ω | ¬ Conn G ω x y} := by
    ext ω; simp [and_assoc]
  rw [hset, hset2] at hsplit
  linarith

/-- **Lemma I.2.1(iii)** in indicator form: `0 ≤ P(A ∩ B) - P(A)P(B) ≤ P(A ∩ B ∩ {x ↔ y})`. -/
theorem twoCluster_upper [Countable E] (G : BondGraph V E) (p : E → unitInterval)
    (hp : ∀ e, p e < 1) (x y : V)
    (A B : Set (Set E)) (hA : IsUpperSet A) (hfA : FiniteWitness A)
    (hdA : ClusterDeterminedAt G x A) (hB : IsUpperSet B) (hfB : FiniteWitness B)
    (hdB : ClusterDeterminedAt G y B) :
    0 ≤ (edgeLaw p).real (A ∩ B) - (edgeLaw p).real A * (edgeLaw p).real B ∧
      (edgeLaw p).real (A ∩ B) - (edgeLaw p).real A * (edgeLaw p).real B ≤
        (edgeLaw p).real (A ∩ B ∩ {ω | Conn G ω x y}) := by
  have hfgk := association_edge_finiteWitness p A B hA hB hfA hfB
  have hmiddle := twoCluster_middle G p hp x y A B hA hfA hB hfB
  have hbk := twoCluster_bk G p hp x y A B hA hfA hdA hB hfB hdB
  have hsplit := measureReal_inter_add_inter_compl G p x y (A ∩ B)
  have hset : (A ∩ B) ∩ {ω | Conn G ω x y} = A ∩ B ∩ {ω | Conn G ω x y} := by
    ext ω; simp [and_assoc]
  have hset2 : (A ∩ B) ∩ {ω | ¬ Conn G ω x y} = A ∩ B ∩ {ω | ¬ Conn G ω x y} := by
    ext ω; simp [and_assoc]
  rw [hset, hset2] at hsplit
  constructor <;> linarith

end TwoCluster

section ThreePoint
attribute [local instance] Classical.propDecidable

/-- The event `x ↔ y`: the pair `x y` lies in one cluster. -/
abbrev connEvent (G : BondGraph V E) (x y : V) : Set (Set E) := {ω | Conn G ω x y}

/-- The event `x ↔ y ↮ z ↔ w`: `x ↔ y` and `z ↔ w` hold in different clusters. -/
def apartEvent (G : BondGraph V E) (x y z w : V) : Set (Set E) :=
  {ω | Conn G ω x y ∧ Conn G ω z w ∧ ¬ Conn G ω x z}

/-- The event `x ↔ y ↔ z ↔ w`: all four points lie in one cluster. -/
def allConnEvent (G : BondGraph V E) (x y z w : V) : Set (Set E) :=
  {ω | Conn G ω x y ∧ Conn G ω y z ∧ Conn G ω z w}

theorem connEvent_upper (G : BondGraph V E) (x y : V) : IsUpperSet (connEvent G x y) :=
  fun _ _ h hc => conn_mono G h hc

theorem connEvent_finiteWitness (G : BondGraph V E) (x y : V) :
    FiniteWitness (connEvent G x y) := finiteWitness_conn G x y

theorem connEvent_determined (G : BondGraph V E) (x y : V) :
    ClusterDeterminedAt G x (connEvent G x y) := by
  intro ω ω' h
  exact (show y ∈ cluster G ω x ↔ y ∈ cluster G ω' x by rw [h])

/-- **Lemma I.2.2** (Hutchcroft, arXiv:2508.18807): for all `x y z w`,
`0 ≤ P(x↔y) P(z↔w) - P(x↔y ↮ z↔w) ≤ P(x↔y↔z↔w)`. -/
theorem threePoint_bk [Countable E] (G : BondGraph V E) (p : E → unitInterval)
    (hp : ∀ e, p e < 1) (x y z w : V) :
    0 ≤ (edgeLaw p).real (connEvent G x y) * (edgeLaw p).real (connEvent G z w) -
          (edgeLaw p).real (apartEvent G x y z w) ∧
      (edgeLaw p).real (connEvent G x y) * (edgeLaw p).real (connEvent G z w) -
          (edgeLaw p).real (apartEvent G x y z w) ≤ (edgeLaw p).real (allConnEvent G x y z w) := by
  have hA : IsUpperSet (connEvent G x y) := connEvent_upper G x y
  have hB : IsUpperSet (connEvent G z w) := connEvent_upper G z w
  have hfA : FiniteWitness (connEvent G x y) := connEvent_finiteWitness G x y
  have hfB : FiniteWitness (connEvent G z w) := connEvent_finiteWitness G z w
  have hdA : ClusterDeterminedAt G x (connEvent G x y) := connEvent_determined G x y
  have hdB : ClusterDeterminedAt G z (connEvent G z w) := connEvent_determined G z w
  have hfgk := association_edge_finiteWitness p (connEvent G x y) (connEvent G z w) hA hB hfA hfB
  -- `A ∩ B ∩ {x ↔ z}` is `x ↔ y ↔ z ↔ w`, and the complement is `x ↔ y ↮ z ↔ w`
  have hset2 : connEvent G x y ∩ connEvent G z w ∩ {ω | Conn G ω x z} =
      allConnEvent G x y z w := by
    ext ω
    simp only [connEvent, allConnEvent, Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨⟨hxy, hzw⟩, hxz⟩
      exact ⟨hxy, conn_trans G ω (conn_symm G ω hxy) hxz, hzw⟩
    · rintro ⟨hxy, hyz, hzw⟩
      exact ⟨⟨hxy, hzw⟩, conn_trans G ω hxy hyz⟩
  have hset3 : connEvent G x y ∩ connEvent G z w ∩ {ω | ¬ Conn G ω x z} =
      apartEvent G x y z w := by
    ext ω
    simp only [apartEvent, connEvent, Set.mem_inter_iff, Set.mem_ofPred_eq]
    exact ⟨fun h => ⟨h.1.1, h.1.2, h.2⟩, fun h => ⟨⟨h.1, h.2.1⟩, h.2.2⟩⟩
  have hsplit := measureReal_inter_add_inter_compl G p x z (connEvent G x y ∩ connEvent G z w)
  have hset : (connEvent G x y ∩ connEvent G z w) ∩ {ω | Conn G ω x z} =
      connEvent G x y ∩ connEvent G z w ∩ {ω | Conn G ω x z} := by
    ext ω; simp [and_assoc]
  have hset4 : (connEvent G x y ∩ connEvent G z w) ∩ {ω | ¬ Conn G ω x z} =
      connEvent G x y ∩ connEvent G z w ∩ {ω | ¬ Conn G ω x z} := by
    ext ω; simp [and_assoc]
  rw [hset, hset4, hset2, hset3] at hsplit
  constructor
  · -- lower bound: `A ∩ B ∩ {x ↮ z} ⊆ A ∘ B`
    have hsub : apartEvent G x y z w ⊆
        DisjointOccurrence (connEvent G x y) (connEvent G z w) := by
      rintro ω ⟨hxy, hzw, hxz⟩
      obtain ⟨s, hs, hsa, hsi⟩ := exists_internal_witness G x _ hdA hfA hxy
      obtain ⟨t, ht, hta, hti⟩ := exists_internal_witness G z _ hdB hfB hzw
      exact ⟨s, t, hs, ht, disjoint_of_internal G ω hxz hsi hti, hsa, hta⟩
    have h := (measureReal_mono hsub).trans (bkEdge p hp _ _ hA hB hfA hfB)
    linarith
  · -- upper bound
    linarith

end ThreePoint

section Iterated
attribute [local instance] Classical.propDecidable

/-- The iterated disjoint-occurrence event `A₁ ∘ A₂ ∘ ⋯ ∘ Aₖ`: each `Aᵢ` has a finite witness, and
the witnesses are pairwise disjoint. -/
def DisjointOccurrenceList : List (Set (Set E)) → Set (Set E)
  | [] => Set.univ
  | A :: As => DisjointOccurrence A (DisjointOccurrenceList As)

theorem disjointOccurrenceList_upper (As : List (Set (Set E))) :
    IsUpperSet (DisjointOccurrenceList As) := by
  induction As with
  | nil => exact fun _ _ _ _ => trivial
  | cons A As ih => exact disjointOccurrence_upper A _

theorem disjointOccurrenceList_finiteWitness (As : List (Set (Set E))) :
    FiniteWitness (DisjointOccurrenceList As) := by
  induction As with
  | nil =>
    intro ω _
    exact ⟨∅, by simp, by simp [DisjointOccurrenceList]⟩
  | cons A As ih => exact finiteWitness_disjointOccurrence A _

/-- The iterated BK inequality: `P(A₁ ∘ ⋯ ∘ Aₖ) ≤ ∏ P(Aᵢ)` for increasing finitely witnessed
events.  This is the form used in the tree-graph arguments (e.g. in Lemma I.4.16). -/
theorem bk_list [Countable E] (p : E → unitInterval) (hp : ∀ e, p e < 1)
    (As : List (Set (Set E)))
    (hA : ∀ A ∈ As, IsUpperSet A) (hf : ∀ A ∈ As, FiniteWitness A) :
    (edgeLaw p).real (DisjointOccurrenceList As) ≤ (As.map (fun A => (edgeLaw p).real A)).prod := by
  induction As with
  | nil => simp [DisjointOccurrenceList]
  | cons A As ih =>
    have hA' : IsUpperSet A := hA A List.mem_cons_self
    have hfA : FiniteWitness A := hf A List.mem_cons_self
    have hAs : ∀ B ∈ As, IsUpperSet B := fun B hB => hA B (List.mem_cons_of_mem _ hB)
    have hfs : ∀ B ∈ As, FiniteWitness B := fun B hB => hf B (List.mem_cons_of_mem _ hB)
    have h1 : (edgeLaw p).real (DisjointOccurrence A (DisjointOccurrenceList As)) ≤
        (edgeLaw p).real A * (edgeLaw p).real (DisjointOccurrenceList As) :=
      bkEdge p hp A _ hA' (disjointOccurrenceList_upper As) hfA
        (disjointOccurrenceList_finiteWitness As)
    have h2 := ih hAs hfs
    have h3 : (edgeLaw p).real A * (edgeLaw p).real (DisjointOccurrenceList As) ≤
        (edgeLaw p).real A * (As.map (fun A => (edgeLaw p).real A)).prod :=
      mul_le_mul_of_nonneg_left h2 measureReal_nonneg
    calc (edgeLaw p).real (DisjointOccurrenceList (A :: As))
        = (edgeLaw p).real (DisjointOccurrence A (DisjointOccurrenceList As)) := rfl
      _ ≤ (edgeLaw p).real A * (As.map (fun A => (edgeLaw p).real A)).prod := h1.trans h3
      _ = ((A :: As).map (fun A => (edgeLaw p).real A)).prod := by rw [List.map_cons, List.prod_cons]

end Iterated

end Percolation

end PercLib.CriticalLRP
