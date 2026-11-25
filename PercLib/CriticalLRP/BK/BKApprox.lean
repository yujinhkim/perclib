/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
# BK for increasing events on infinitely many edges: the cylinder lifting

Source: Tom Hutchcroft, *Critical long-range percolation I: High effective dimension*,
arXiv:2508.18807v1, §I.2.1, pp. 20--21 and footnote 11:

  "The BK inequality states that if `A` and `B` are increasing events depending on only finitely
  many edges then `P(A ∘ B) ≤ P(A) P(B)`. ... It is usually possible to apply the BK inequality or
  Reimer's inequality to events depending on infinitely many edges via simple limiting arguments,
  and we will do this without further comment when no subtleties arise."

The repository's `Percolation.bkEdge` is the finite-witness form (footnote 11's `A ⊙ B`).  A
"simple limiting argument" does *not* by itself give BK for all increasing measurable events: the
cylinder events

  `cyl A n = {ω | ω ∩ E_n ∈ A}`

increase to `⋃ n, cyl A n`, which can be a proper subset of `A` (for `A = {ω | ω infinite}` we have
`ω ∩ E_n` finite, hence `cyl A n = ∅` for all `n`).  What the limiting argument does give, with no
hypothesis beyond monotonicity of `A` and `B`, is

  `P(A ∘ B) ≤ P(A^*) P(B^*)`,   `A^* := ⋃ n, cyl A n`,

and hence the BK inequality as stated whenever `A` and `B` are **approximable from below by
cylinders** (`A = A^*`).  That class contains every finitely witnessed increasing event
(`finiteWitness_approximableFromBelow`), and is closed under countable increasing unions of
finitely witnessed increasing events (`approximable_of_iUnion_finiteWitness`) — which is the form
in which the paper's applications use it (e.g. `{|K_x| ≥ n}`).

Everything below is for the edge-dependent Bernoulli law `edgeLaw p`, hence in particular for the
paper's `P_β`.

No `sorry`, no custom axioms.
-/
module

public import PercLib.CriticalLRP.BK.GraphConsequences

set_option autoImplicit true

set_option linter.unusedSectionVars false

@[expose] public section

open MeasureTheory Measure ProbabilityTheory unitInterval Filter
open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP

namespace Percolation

variable {E : Type*} [Countable E]

section Cylinder

attribute [local instance] Classical.propDecidable

/-- The **cylinder of `A` on the first `n` edges**: the configurations whose restriction to the
first `n` edges already lies in `A`. -/
abbrev cyl [Encodable E] (A : Set (Set E)) (n : ℕ) : Set (Set E) :=
  {ω | ω ∩ (edgeExhaustion (E := E) n : Set E) ∈ A}

/-- The union of the cylinder approximations of `A`. -/
abbrev cylUnion [Encodable E] (A : Set (Set E)) : Set (Set E) :=
  ⋃ n, cyl A n

theorem mem_cyl_iff [Encodable E] (A : Set (Set E)) (n : ℕ) (ω : Set E) :
    ω ∈ cyl A n ↔ ω ∩ (edgeExhaustion (E := E) n : Set E) ∈ A := Iff.rfl

/-- The finite set `s` restricted to the first `n` edges, as a subset of the configuration. -/
theorem coe_filter_exhaustion [Encodable E] (s : Finset E) (n : ℕ) :
    ((s.filter (fun e => e ∈ edgeExhaustion (E := E) n) : Finset E) : Set E) =
      (s : Set E) ∩ (edgeExhaustion (E := E) n : Set E) := by
  ext e
  simp only [Finset.coe_filter, Finset.mem_coe, Set.mem_ofPred_eq, Set.mem_inter_iff]

theorem filter_exhaustion_subset [Encodable E] (s : Finset E) (n : ℕ) :
    ((s.filter (fun e => e ∈ edgeExhaustion (E := E) n) : Finset E) : Set E) ⊆
      (edgeExhaustion (E := E) n : Set E) := by
  intro e he
  exact (Finset.mem_filter.1 (by simpa using he)).2

/-- Cylinder events are measurable, for an arbitrary event `A`. -/
theorem measurableSet_cyl [Encodable E] (A : Set (Set E)) (n : ℕ) :
    MeasurableSet (cyl A n) := by
  let s := edgeExhaustion (E := E) n
  have he : cyl A n = (fun ω : Set E => (Subtype.val ⁻¹' ω : Set s)) ⁻¹'
      {η | Subtype.val '' η ∈ A} := by
    ext ω
    change ω ∩ (s : Set E) ∈ A ↔ Subtype.val '' (Subtype.val ⁻¹' ω : Set s) ∈ A
    have hi : Subtype.val '' (Subtype.val ⁻¹' ω : Set s) = ω ∩ (s : Set E) := by
      ext e
      simp [and_comm]
    rw [hi]
  rw [he]
  exact MeasurableSet.preimage .of_discrete (measurable_set_restrict (s := (s : Set E)))

theorem cyl_mono [Encodable E] {A : Set (Set E)} (hA : IsUpperSet A) :
    Monotone (cyl A) := by
  intro m n hmn ω hω
  have hω' : ω ∩ (edgeExhaustion (E := E) m : Set E) ∈ A := hω
  show ω ∩ (edgeExhaustion (E := E) n : Set E) ∈ A
  refine hA ?_ hω'
  exact fun e he => ⟨he.1, edgeExhaustion_mono hmn he.2⟩

theorem cyl_upper [Encodable E] {A : Set (Set E)} (hA : IsUpperSet A) (n : ℕ) :
    IsUpperSet (cyl A n) := by
  intro ω ω' h hω
  have hω' : ω ∩ (edgeExhaustion (E := E) n : Set E) ∈ A := hω
  show ω' ∩ (edgeExhaustion (E := E) n : Set E) ∈ A
  refine hA ?_ hω'
  exact fun e he => ⟨h he.1, he.2⟩

theorem cyl_subset [Encodable E] {A : Set (Set E)} (hA : IsUpperSet A) (n : ℕ) :
    cyl A n ⊆ A := by
  intro ω hω
  have hω' : ω ∩ (edgeExhaustion (E := E) n : Set E) ∈ A := hω
  exact hA Set.inter_subset_left hω'

/-- Cylinder events have the `n`-th edge set as a finite witness. -/
theorem cyl_finiteWitness [Encodable E] (A : Set (Set E)) (n : ℕ) :
    FiniteWitness (cyl A n) := by
  intro ω hω
  have hω' : ω ∩ (edgeExhaustion (E := E) n : Set E) ∈ A := hω
  refine ⟨(edgeExhaustion (E := E) n).filter (fun e => e ∈ ω), ?_, ?_⟩
  · intro e he
    have h1 : e ∈ edgeExhaustion (E := E) n := (Finset.mem_filter.1 (by simpa using he)).1
    have h2 : e ∈ ω := (Finset.mem_filter.1 (by simpa using he)).2
    exact h2
  · show (((edgeExhaustion (E := E) n).filter (fun e => e ∈ ω) : Finset E) : Set E) ∈ cyl A n
    rw [mem_cyl_iff]
    rw [show (((edgeExhaustion (E := E) n).filter (fun e => e ∈ ω) : Finset E) : Set E) =
        ω ∩ (edgeExhaustion (E := E) n : Set E) from by
      ext e
      simp only [Finset.coe_filter, Finset.mem_coe, Set.mem_ofPred_eq, Set.mem_inter_iff]
      tauto]
    rw [Set.inter_assoc, Set.inter_self]
    exact hω'

end Cylinder

section Split

attribute [local instance] Classical.propDecidable

/-- **A disjoint occurrence is the increasing union of its cylinder restrictions.** -/
theorem iUnion_cyl_disjointOccurrence [Encodable E] (A B : Set (Set E)) :
    (⋃ n, DisjointOccurrence (cyl A n) (cyl B n)) = DisjointOccurrence A B := by
  ext ω
  constructor
  · intro hω
    obtain ⟨n, s, t, hs, ht, hd, hsa, htb⟩ := Set.mem_iUnion.1 hω
    have hsa' : (s : Set E) ∩ (edgeExhaustion (E := E) n : Set E) ∈ A := hsa
    have htb' : (t : Set E) ∩ (edgeExhaustion (E := E) n : Set E) ∈ B := htb
    refine ⟨s.filter (fun e => e ∈ edgeExhaustion (E := E) n),
      t.filter (fun e => e ∈ edgeExhaustion (E := E) n), ?_, ?_, ?_, ?_, ?_⟩
    · intro e he
      have h1 : e ∈ s := (Finset.mem_filter.1 (by simpa using he)).1
      exact hs h1
    · intro e he
      have h1 : e ∈ t := (Finset.mem_filter.1 (by simpa using he)).1
      exact ht h1
    · refine Finset.disjoint_left.mpr fun e hse hte => ?_
      exact Finset.disjoint_left.mp hd (Finset.mem_filter.1 hse).1 (Finset.mem_filter.1 hte).1
    · show (((s.filter (fun e => e ∈ edgeExhaustion (E := E) n)) : Finset E) : Set E) ∈ A
      rw [coe_filter_exhaustion]
      exact hsa'
    · show (((t.filter (fun e => e ∈ edgeExhaustion (E := E) n)) : Finset E) : Set E) ∈ B
      rw [coe_filter_exhaustion]
      exact htb'
  · rintro ⟨s, t, hs, ht, hd, hsa, htb⟩
    obtain ⟨n, hn⟩ := subset_edgeExhaustion (E := E) (s ∪ t)
    refine Set.mem_iUnion.2 ⟨n, s, t, hs, ht, hd, ?_, ?_⟩
    · have : (s : Set E) ∩ (edgeExhaustion (E := E) n : Set E) = (s : Set E) := by
        refine Set.inter_eq_left.2 ?_
        intro e he
        exact hn (Finset.mem_union_left t (by simpa using he))
      rw [mem_cyl_iff, this]
      exact hsa
    · have : (t : Set E) ∩ (edgeExhaustion (E := E) n : Set E) = (t : Set E) := by
        refine Set.inter_eq_left.2 ?_
        intro e he
        exact hn (Finset.mem_union_right s (by simpa using he))
      rw [mem_cyl_iff, this]
      exact htb

end Split

section Lifting

attribute [local instance] Classical.propDecidable

/-- **BK for increasing events on a countable edge set, via cylinder approximation.**  With no
hypothesis on `A`, `B` beyond monotonicity,
`P(A ∘ B) ≤ P(A^*) P(B^*)` where `A^* = ⋃ n, {ω | ω ∩ E_n ∈ A}` is the finitely visible part
of `A`. -/
theorem bk_approx [Encodable E] (p : E → unitInterval) (hp : ∀ e, p e < 1)
    (A B : Set (Set E)) (hA : IsUpperSet A) (hB : IsUpperSet B) :
    (edgeLaw p).real (DisjointOccurrence A B) ≤
      (edgeLaw p).real (cylUnion A) * (edgeLaw p).real (cylUnion B) := by
  have hmono : Monotone fun n => DisjointOccurrence (cyl A n) (cyl B n) :=
    fun m n hmn => disjointOccurrence_mono (cyl_mono hA hmn) (cyl_mono hB hmn)
  have hlimD : Tendsto (fun n => (edgeLaw p).real
      (DisjointOccurrence (cyl A n) (cyl B n))) atTop
      (𝓝 ((edgeLaw p).real (DisjointOccurrence A B))) := by
    have h := tendsto_measure_iUnion_atTop (μ := edgeLaw p) hmono
    rw [show (⋃ n, DisjointOccurrence (cyl A n) (cyl B n)) = DisjointOccurrence A B from
      iUnion_cyl_disjointOccurrence A B] at h
    exact (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp h
  have hlimA : Tendsto (fun n => (edgeLaw p).real (cyl A n)) atTop
      (𝓝 ((edgeLaw p).real (cylUnion A))) := by
    have h := tendsto_measure_iUnion_atTop (μ := edgeLaw p) (cyl_mono hA)
    exact (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp h
  have hlimB : Tendsto (fun n => (edgeLaw p).real (cyl B n)) atTop
      (𝓝 ((edgeLaw p).real (cylUnion B))) := by
    have h := tendsto_measure_iUnion_atTop (μ := edgeLaw p) (cyl_mono hB)
    exact (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp h
  exact le_of_tendsto_of_tendsto hlimD (hlimA.mul hlimB)
    (Filter.Eventually.of_forall fun n => bkEdge p hp _ _
      (cyl_upper hA n) (cyl_upper hB n) (cyl_finiteWitness A n) (cyl_finiteWitness B n))

/-- `A` is **approximable from below by cylinders**: membership of `ω` in `A` is already decided
by finitely many edges of `ω`. -/
def ApproximableFromBelow [Encodable E] (A : Set (Set E)) : Prop :=
  ∀ ω ∈ A, ∃ n, ω ∩ (edgeExhaustion (E := E) n : Set E) ∈ A

theorem approximable_iff_cylUnion [Encodable E] {A : Set (Set E)} (hA : IsUpperSet A) :
    ApproximableFromBelow A ↔ cylUnion A = A := by
  constructor
  · intro h
    ext ω
    constructor
    · intro hω
      obtain ⟨n, hn⟩ := Set.mem_iUnion.1 hω
      exact cyl_subset hA n hn
    · intro hω
      obtain ⟨n, hn⟩ := h ω hω
      exact Set.mem_iUnion.2 ⟨n, hn⟩
  · intro h ω hω
    have hmem : ω ∈ cylUnion A := by
      rw [show cylUnion A = A from h]
      exact hω
    exact Set.mem_iUnion.1 hmem

/-- Finitely witnessed increasing events are approximable from below. -/
theorem finiteWitness_approximableFromBelow [Encodable E] {A : Set (Set E)}
    (hA : IsUpperSet A) (hfA : FiniteWitness A) : ApproximableFromBelow A := by
  intro ω hω
  obtain ⟨s, hs, hsa⟩ := hfA ω hω
  obtain ⟨n, hn⟩ := subset_edgeExhaustion (E := E) s
  refine ⟨n, hA ?_ hsa⟩
  exact fun e he => ⟨hs he, hn he⟩

/-- **BK for increasing events approximable from below**: this is the form of the inequality in
which the paper applies it to events depending on infinitely many edges. -/
theorem bk_of_approximable [Encodable E] (p : E → unitInterval) (hp : ∀ e, p e < 1)
    (A B : Set (Set E)) (hA : IsUpperSet A) (hB : IsUpperSet B)
    (happA : ApproximableFromBelow A) (happB : ApproximableFromBelow B) :
    (edgeLaw p).real (DisjointOccurrence A B) ≤
      (edgeLaw p).real A * (edgeLaw p).real B := by
  have h := bk_approx p hp A B hA hB
  rw [(approximable_iff_cylUnion hA).1 happA,
    (approximable_iff_cylUnion hB).1 happB] at h
  exact h

/-- A countable increasing union of finitely witnessed increasing events is approximable from
below; combined with `bk_of_approximable` this gives BK for such events. -/
theorem approximable_of_iUnion_finiteWitness [Encodable E] {A : Set (Set E)}
    {As : ℕ → Set (Set E)} (hA : IsUpperSet A) (hUnion : A = ⋃ n, As n)
    (hfin : ∀ n, FiniteWitness (As n)) : ApproximableFromBelow A := by
  intro ω hω
  rw [hUnion] at hω
  obtain ⟨n, hn⟩ := Set.mem_iUnion.1 hω
  obtain ⟨s, hs, hsa⟩ := hfin n ω hn
  obtain ⟨m, hm⟩ := subset_edgeExhaustion (E := E) s
  refine ⟨m, ?_⟩
  have hsub : (s : Set E) ⊆ ω ∩ (edgeExhaustion (E := E) m : Set E) :=
    fun e he => ⟨hs he, hm he⟩
  have hmemA : (s : Set E) ∈ A := hUnion ▸ Set.mem_iUnion.2 ⟨n, hsa⟩
  exact hA hsub hmemA

end Lifting

end Percolation

end PercLib.CriticalLRP
