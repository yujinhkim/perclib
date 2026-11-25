/- Integrated from independently rebuilt Ultramath work.
Base revision 8445f0b1fb57bf8fc0c08b2dfd29df64f3f01576.
Scratch source: ../../.ultramath/smwvk712v/m5/I417Gen/Defs.lean; module path rewritten.
-/

module

public import PercLib.CriticalLRP.Correlation.I417.Nonnegative.Main

/-!
# Lemma I.4.17 for arbitrary finite `p, q`: definitions of the two-copy marked expansion

Source: Tom Hutchcroft, *Critical long-range percolation I: High effective dimension*,
arXiv:2508.18807v1, Lemma I.4.17 and its proof (supplied PDF p. 45):

  0 ≤ E|K|^p E|K|^q − E[|K_x|^p |K_y|^q 1(x ↮ y)]
    ≤ ∑_{ℓ=3}^{p+q+1} C_{p,q,ℓ} T^ℓ(x,y) (E|K|)^{2p+2q+1−ℓ}.

The proof in the paper writes `ω, ω'` for the two independent copies, `K_x` for the base cluster
of `x`, `K̃_y` for the cluster of `y` in the restored configuration `ω̃ = restoreMap x (ω',ω)`, and
then uses the dichotomy

  on `{y ∉ K_x}`:  `y_1,…,y_q ∈ K̃_y` and (not all `y_j ∈ K_y`) ⟹ some `w ∈ K_x` lies on a simple
  open path of `K̃_y` from `y` to `{y_1,…,y_q}`.

This file records the **event families** of that dichotomy for *arbitrary* `p q : ℕ`, indexed by
labelled tuples `f : Fin p → V` (the `p` arms of `x`) and `g : Fin q → V` (the `q` arms of `y`):

* `prodSet x y f g` — the two-copy product event `{f ⊆ K_x(ω₁)} × {g ⊆ K_y(ω₂)}`, whose
  `(μ⊗μ)`-measure is `P(f ⊆ K_x) P(g ⊆ K_y)` and whose free sums give `E|K_x|^p E|K_y|^q`;
* `diagSet x y f g` — the *diagonal* alternative: the base copy already has `f ⊆ K_x` and
  `y ∉ K_x`, and the **restored** copy has `g ⊆ K̃_y`.  Its free sums are exactly the excluded
  moment `E[|K_x|^p |K_y|^q 1(x ↮ y)]` (Lemma I.4.17's subtracted term);
* `freshMark y g j w` — the fresh-copy event that all `q` arms `g` are in the *fresh* cluster
  `K_y(ω₂)` and that the two halves `y↔w`, `w↔g j` occur **disjointly** in `ω₂`;
* `markSet x y f g j w` — the marked two-copy event at the marked vertex `w ∈ K_x(ω₁)` and the
  terminal arm `j : Fin q`: the product of `freshMark y g j w` with
  `{f ⊆ K_x(ω₁)} ∩ {w ∈ K_x(ω₁)}`.

The mark family keeps the `q−1` other arms `g j'` inside the *fresh* cluster rather than the
restored one: on the covering event they are known to lie in `K_y(ω₂)` (they come from `prodSet`),
so nothing is lost, and the two-copy factorisation stays exact — the base factor then depends on
`(f,w)` alone and the fresh factor on `(g,j,w)` alone.  The paper's display keeps `K̃_y` in the
second factor; reading it as the fresh cluster is the repaired (provable) form of the printed
step, exactly as in `Correlation/I417/Defs.lean` for `p = 2`, `q = 1`
(`Correlation/PrintedEventFails.lean` records that `K_y ⊆ K̃_y` is false for the base cluster).

Definitions only in this file.
-/


open MeasureTheory Measure ProbabilityTheory unitInterval
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false

@[expose] public section

namespace PercLib.CriticalLRP.I417Gen

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Countable V]

/-- The two independent copies of the canonical model.  The **first** coordinate `ρ.1` is the
fresh configuration `ω₂` and the **second** coordinate `ρ.2` is the base configuration `ω₁`,
matching `restoreMap x ρ = forceOn (touchSet ρ.2 x)ᶜ ρ.1 ρ.2`. -/
abbrev TwoCopy (V : Type*) := Config V × Config V

/-- **The two-copy product event.**  The fresh copy carries `g ⊆ K_y`, the base copy `f ⊆ K_x`.
Its `(μ⊗μ)`-measure is the product `P(f ⊆ K_x) · P(g ⊆ K_y)`. -/
def prodSet (x y : V) {p q : ℕ} (f : Fin p → V) (g : Fin q → V) : Set (TwoCopy V) :=
  I417A.labelEvent y g ×ˢ I417A.labelEvent x f

/-- **The diagonal alternative.**  In the base copy `f ⊆ K_x` and `y ∉ K_x`; in the *restored*
configuration `g ⊆ K̃_y = K_y(restoreMap x ρ)`.  This is the event whose free sums are the excluded
moment `E[|K_x|^p |K_y|^q 1(x ↮ y)]`. -/
def diagSet (x y : V) {p q : ℕ} (f : Fin p → V) (g : Fin q → V) : Set (TwoCopy V) :=
  {ρ | ρ.2 ∈ I417A.labelEvent x f ∧ ρ.2 ∉ connSet x y ∧
    restoreMap x ρ ∈ I417A.labelEvent y g}

/-- **The marked fresh event** at the terminal arm `j : Fin q` and the mark `w`: the fresh copy
carries all `q` arms `g` in `K_y(ω₂)`, and the two halves of a simple path `y → w → g j` occur
*disjointly* in `ω₂` (`{y↔w} ∘ {w↔g j}`).  The disjoint occurrence is what makes the two copies
independent after `w ∈ K_x(ω₁)` is added on the base side. -/
def freshMark (y : V) {q : ℕ} (g : Fin q → V) (j : Fin q) (w : V) : Set (Config V) :=
  Percolation.DisjointOccurrence (connSet y w) (connSet w (g j)) ∩ I417A.labelEvent y g

/-- **The marked two-copy event.**  The base copy has `f ⊆ K_x` and the mark `w ∈ K_x`; the fresh
copy carries the marked fresh event `freshMark y g j w`.  The two conditions live in different
coordinates, so the `(μ⊗μ)`-measure is the product of the two one-copy probabilities. -/
def markSet (x y : V) {p q : ℕ} (f : Fin p → V) (g : Fin q → V) (j : Fin q) (w : V) :
    Set (TwoCopy V) :=
  freshMark y g j w ×ˢ (I417A.labelEvent x f ∩ connSet x w)

open scoped Classical in
/-- **The `p`-th moment of `|K_x|` through the marked vertex `w`**, `E[|K_x|^p 1(w ∈ K_x)]`.
It is the base-copy factor of the marked family, summed over the labelled `p`-tuples `f`.  Bounding
it by tree diagrams (`(2p−3)!!` rooted trees) is the diagram side of Lemma I.4.17 and is not done
in this direction. -/
noncomputable def jointPow (π : Sym2 V → unitInterval) (x : V) (p : ℕ) (w : V) : ℝ≥0∞ :=
  ∫⁻ ω, Percolation.cardFun (cluster ω x) ^ p *
    (cluster ω x).indicator (fun _ => (1 : ℝ≥0∞)) w ∂(edgeMeasure π)

/-! ## Elementary membership and measurability -/

theorem mem_prodSet_iff {x y : V} {p q : ℕ} {f : Fin p → V} {g : Fin q → V} {ρ : TwoCopy V} :
    ρ ∈ prodSet x y f g ↔ (∀ j, g j ∈ cluster ρ.1 y) ∧ (∀ i, f i ∈ cluster ρ.2 x) :=
  Iff.rfl

theorem mem_diagSet_iff {x y : V} {p q : ℕ} {f : Fin p → V} {g : Fin q → V} {ρ : TwoCopy V} :
    ρ ∈ diagSet x y f g ↔
      (∀ i, f i ∈ cluster ρ.2 x) ∧ ρ.2 ∉ connSet x y ∧
        (∀ j, g j ∈ cluster (restoreMap x ρ) y) :=
  Iff.rfl

theorem mem_markSet_iff {x y : V} {p q : ℕ} {f : Fin p → V} {g : Fin q → V} {j : Fin q} {w : V}
    {ρ : TwoCopy V} :
    ρ ∈ markSet x y f g j w ↔
      (ρ.1 ∈ Percolation.DisjointOccurrence (connSet y w) (connSet w (g j)) ∧
        (∀ j', g j' ∈ cluster ρ.1 y)) ∧
      ((∀ i, f i ∈ cluster ρ.2 x) ∧ ρ.2 ∈ connSet x w) :=
  Iff.rfl

theorem measurableSet_prodSet (x y : V) {p q : ℕ} (f : Fin p → V) (g : Fin q → V) :
    MeasurableSet (prodSet x y f g) :=
  (I417A.measurableSet_labelEvent y g).prod (I417A.measurableSet_labelEvent x f)

theorem measurableSet_diagSet (x y : V) {p q : ℕ} (f : Fin p → V) (g : Fin q → V) :
    MeasurableSet (diagSet x y f g) := by
  have h : diagSet x y f g =
      (⋂ i, {ρ : TwoCopy V | ρ.2 ∈ connSet x (f i)}) ∩
        {ρ : TwoCopy V | ρ.2 ∉ connSet x y} ∩
        (⋂ j, {ρ : TwoCopy V | restoreMap x ρ ∈ connSet y (g j)}) := by
    ext ρ
    simp only [diagSet, I417A.labelEvent, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter,
      mem_cluster_iff, connSet]
    tauto
  rw [h]
  refine ((MeasurableSet.iInter fun i => measurable_snd (measurableSet_connSet x (f i))).inter
    (measurable_snd (measurableSet_connSet x y)).compl).inter ?_
  exact MeasurableSet.iInter fun j =>
    (measurable_restoreMap x) (measurableSet_connSet y (g j))

theorem measurableSet_freshMark (y : V) {q : ℕ} (g : Fin q → V) (j : Fin q) (w : V) :
    MeasurableSet (freshMark y g j w) :=
  (Percolation.measurableSet_finiteWitness _
      (Percolation.disjointOccurrence_upper _ _)
      (Percolation.finiteWitness_disjointOccurrence _ _)).inter
    (I417A.measurableSet_labelEvent y g)

theorem measurableSet_markSet (x y : V) {p q : ℕ} (f : Fin p → V) (g : Fin q → V) (j : Fin q)
    (w : V) : MeasurableSet (markSet x y f g j w) :=
  (measurableSet_freshMark y g j w).prod
    ((I417A.measurableSet_labelEvent x f).inter (measurableSet_connSet x w))

/-! ### The empty-witness absorption `P(y↔z) ⊆ {y↔y} ∘ {y↔z}`

This is the deterministic fact that lets the paper's alternative `y ∈ K_x` be absorbed into the
marked family at the mark `w = y`: the empty walk is a witness for `y ↔ y`, disjoint from any
witness for `y ↔ z`. -/

theorem connSet_subset_disjOcc_self (y z : V) :
    connSet y z ⊆ Percolation.DisjointOccurrence (connSet y y) (connSet y z) := by
  intro ω hω
  obtain ⟨p, hp⟩ := pathConnects_iff.mpr hω
  refine ⟨(∅ : Finset (Sym2 V)), p.edges.toFinset, by simp,
    fun e he => hp e (List.mem_toFinset.mp he), by simp, ?_,
    pathConnects_iff.mp ⟨p, fun e he => List.mem_toFinset.mpr he⟩⟩
  exact mem_cluster_iff.mpr (cluster_mem_self (↑(∅ : Finset (Sym2 V)) : Set (Sym2 V)) y)

/-- The absorption at the level of the marked family: if the base copy has `w ∈ K_x` and `f ⊆ K_x`,
and the fresh copy has `g ⊆ K_y` together with `y ∈ K_x(ω₁)` (the paper's `y ∈ K_x` alternative),
then the pair belongs to the marked family at `(j, y)` for **every** terminal `j`. -/
theorem mem_markSet_of_yInKx {x y : V} {p q : ℕ} {f : Fin p → V} {g : Fin q → V} {ρ : TwoCopy V}
    (j : Fin q) (hf : ρ.2 ∈ I417A.labelEvent x f) (hy : ρ.2 ∈ connSet x y)
    (hg : ρ.1 ∈ I417A.labelEvent y g) :
    ρ ∈ markSet x y f g j y :=
  ⟨⟨connSet_subset_disjOcc_self y (g j) (mem_cluster_iff.mp (hg j)), hg⟩, hf, hy⟩

/-! ## Monotonicity and finite witnesses of the fresh marked event

These are the two hypotheses under which BK and the tree-graph inequality are available, recorded
here so that a diagram-side consumer can apply them to `freshMark` directly. -/

theorem isUpperSet_freshMark (y : V) {q : ℕ} (g : Fin q → V) (j : Fin q) (w : V) :
    IsUpperSet (freshMark y g j w) :=
  (Percolation.disjointOccurrence_upper _ _).inter (I417A.isUpperSet_labelEvent y g)

theorem finiteWitness_freshMark (y : V) {q : ℕ} (g : Fin q → V) (j : Fin q) (w : V) :
    Percolation.FiniteWitness (freshMark y g j w) := by
  intro ω hω
  obtain ⟨S₁, hS₁, hA⟩ := Percolation.finiteWitness_disjointOccurrence _ _ ω hω.1
  obtain ⟨S₂, hS₂, hB⟩ := I417A.finiteWitness_labelEvent y g ω hω.2
  refine ⟨S₁ ∪ S₂, ?_, ?_⟩
  · intro e he
    rcases Finset.mem_union.mp he with h | h
    · exact hS₁ h
    · exact hS₂ h
  · exact ⟨(Percolation.disjointOccurrence_upper _ _)
      (fun e he => Finset.mem_union_left _ he) hA,
      (I417A.isUpperSet_labelEvent y g) (fun e he => Finset.mem_union_right _ he) hB⟩

end PercLib.CriticalLRP.I417Gen
