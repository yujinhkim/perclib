/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
# Two independent percolation configurations and the restoration (resampling) identity

Source: Tom Hutchcroft, *Critical long-range percolation I: High effective dimension*,
arXiv:2508.18807v1, proof of Lemma I.4.12 (p. 39) and of Lemma I.4.17 (p. 45):

  "Let `ω` and `ω'` be independent percolation configurations, and let `ω̃` be defined by setting
   `ω̃(e) = ω(e)` for every edge `e` touching the cluster `K_0` of `0` in `ω` and `ω̃(e) = ω'(e)`
   for every other edge `e`, so that **`ω̃` has the same law as `ω`**."

This file supplies the measure-theoretic content of the italicised claim for the canonical model
`Config V = Set (Sym2 V)` with the independent-edge law `edgeMeasure π`:

* `forceOn_apply`, `measurable_forceOn_pair` : the replacement map `(η, ω) ↦ forceOn S η ω`;
* `forceOn_preimage_cylinder` : its action on cylinder events;
* `edgeMeasure_map_forceOn` : **for every fixed `S`, replacing the coordinates in `S` of a
  `P_π`-distributed configuration by those of an independent `P_π`-distributed configuration gives
  a `P_π`-distributed configuration.**

The proof compares cylinder probabilities and uses `Measure.eq_infinitePi`; independence of the two
coordinates enters through `Measure.prod_prod`.

The random-set instance (`S = σ(ω)`, e.g. the set of edges touching `K_0(ω)`) additionally needs the
block factorization of `edgeMeasure π` along a fixed split `E = S ⊔ Sᶜ`; that is the next step and
is *not* claimed here.

No `sorry`, no custom axioms.
-/
module

public import PercLib.CriticalLRP.CountableProduct.ZeroOne

set_option autoImplicit true

set_option linter.unusedSectionVars false

@[expose] public section

open MeasureTheory Measure ProbabilityTheory unitInterval
open scoped ENNReal NNReal

namespace PercLib.CriticalLRP

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Countable V]

/-- The event that a configuration agrees with prescribed sets of states on the edges of `s`. -/
abbrev edgeCyl (s : Finset (Sym2 V)) (t : Sym2 V → Set Prop) : Set (Config V) :=
  {ω | ∀ e ∈ s, ω e ∈ t e}

theorem edgeCyl_eq_pi (s : Finset (Sym2 V)) (t : Sym2 V → Set Prop) :
    edgeCyl s t = Set.pi (s : Set (Sym2 V)) t := rfl

theorem forceOn_apply (S : Set (Sym2 V)) (η ω : Config V) (e : Sym2 V) :
    forceOn S η ω e ↔ (e ∈ S ∧ η e) ∨ (e ∉ S ∧ ω e) := by
  have h : e ∈ forceOn S η ω ↔ (e ∈ S ∧ e ∈ η) ∨ (e ∉ S ∧ e ∈ ω) := by
    simp only [forceOn, Set.mem_union, Set.mem_sdiff, Set.mem_inter_iff]
    tauto
  exact h

/-- The replacement map `(η, ω) ↦ forceOn S η ω` is measurable for the product σ-algebra. -/
theorem measurable_forceOn_pair (S : Set (Sym2 V)) :
    Measurable (fun p : Config V × Config V => forceOn S p.1 p.2) := by
  refine measurable_pi_iff.mpr fun e => ?_
  by_cases he : e ∈ S
  · have h : (fun p : Config V × Config V => forceOn S p.1 p.2 e) = fun p => e ∈ p.1 := by
      funext p
      rw [forceOn_apply]
      simp [he]
      exact Iff.rfl
    rw [h]
    exact (measurable_pi_apply e).comp measurable_fst
  · have h : (fun p : Config V × Config V => forceOn S p.1 p.2 e) = fun p => e ∈ p.2 := by
      funext p
      rw [forceOn_apply]
      simp [he]
      exact Iff.rfl
    rw [h]
    exact (measurable_pi_apply e).comp measurable_snd

/-- The propositional value of the replacement map at an edge in `S`. -/
theorem forceOn_apply_of_mem {S : Set (Sym2 V)} {e : Sym2 V} (he : e ∈ S) (η ω : Config V) :
    forceOn S η ω e = η e := by
  apply propext
  rw [forceOn_apply]
  exact ⟨fun h => h.elim (fun h' => h'.2) (fun h' => absurd he h'.1),
    fun h => Or.inl ⟨he, h⟩⟩

/-- The propositional value of the replacement map at an edge outside `S`. -/
theorem forceOn_apply_of_notMem {S : Set (Sym2 V)} {e : Sym2 V} (he : e ∉ S) (η ω : Config V) :
    forceOn S η ω e = ω e := by
  apply propext
  rw [forceOn_apply]
  exact ⟨fun h => h.elim (fun h' => absurd h'.1 he) (fun h' => h'.2),
    fun h => Or.inr ⟨he, h⟩⟩

/-- The preimage of a cylinder under the replacement map is a rectangle of cylinders. -/
theorem forceOn_preimage_cylinder (S : Set (Sym2 V)) (s : Finset (Sym2 V))
    (t : Sym2 V → Set Prop) :
    (fun p : Config V × Config V => forceOn S p.1 p.2) ⁻¹' (edgeCyl s t) =
      edgeCyl (s.filter (fun e => e ∈ S)) t ×ˢ edgeCyl (s.filter (fun e => e ∉ S)) t := by
  ext p
  simp only [Set.mem_preimage, edgeCyl, Set.mem_prod, Finset.mem_filter]
  constructor
  · rintro h
    refine ⟨fun e he => ?_, fun e he => ?_⟩
    · have hmem : forceOn S p.1 p.2 e ∈ t e := h e he.1
      rwa [forceOn_apply_of_mem he.2] at hmem
    · have hmem : forceOn S p.1 p.2 e ∈ t e := h e he.1
      rwa [forceOn_apply_of_notMem he.2] at hmem
  · rintro ⟨h1, h2⟩ e he
    by_cases hS : e ∈ S
    · rw [forceOn_apply_of_mem hS]
      exact h1 e ⟨he, hS⟩
    · rw [forceOn_apply_of_notMem hS]
      exact h2 e ⟨he, hS⟩

/-- The probability of a cylinder event under `edgeMeasure π`. -/
theorem edgeMeasure_edgeCyl (π : Sym2 V → unitInterval) (s : Finset (Sym2 V))
    (t : Sym2 V → Set Prop) (ht : ∀ e, MeasurableSet (t e)) :
    edgeMeasure π (edgeCyl s t) =
      ∏ e ∈ s, bernoulliMeasure (True : Prop) (False : Prop) (π e) (t e) := by
  rw [edgeCyl_eq_pi, edgeMeasure_eq_infinitePi π]
  exact Measure.infinitePi_pi (μ := fun e : Sym2 V =>
    bernoulliMeasure (True : Prop) (False : Prop) (π e)) (s := s) (t := t) (fun i _ => ht i)

/-- A probability measure on `Config V` whose cylinder probabilities are those of `edgeMeasure π`
**is** `edgeMeasure π`. -/
theorem eq_edgeMeasure_of_cyl (π : Sym2 V → unitInterval) (ν : Measure (Config V))
    (h : ∀ (s : Finset (Sym2 V)) (t : Sym2 V → Set Prop), (∀ e, MeasurableSet (t e)) →
      ν (edgeCyl s t) = ∏ e ∈ s, bernoulliMeasure True False (π e) (t e)) :
    ν = edgeMeasure π := by
  rw [edgeMeasure_eq_infinitePi π]
  exact Measure.eq_infinitePi (μ := fun e => bernoulliMeasure (True : Prop) (False : Prop) (π e))
    (ν := ν) (fun s t ht => by
      rw [← edgeCyl_eq_pi]
      exact h s t ht)

/-- **Restoration at a fixed edge set.**  If `η` and `ω` are independent with law `edgeMeasure π`,
then replacing the coordinates of `ω` on `S` by those of `η` leaves the law `edgeMeasure π`
unchanged. -/
theorem edgeMeasure_map_forceOn (π : Sym2 V → unitInterval) (S : Set (Sym2 V)) :
    ((edgeMeasure π).prod (edgeMeasure π)).map (fun p : Config V × Config V => forceOn S p.1 p.2) =
      edgeMeasure π := by
  refine eq_edgeMeasure_of_cyl π _ ?_
  intro s t ht
  have hpi : MeasurableSet (edgeCyl s t) := by
    rw [edgeCyl_eq_pi]
    exact MeasurableSet.pi s.countable_toSet (fun i _ => ht i)
  have hprod : ((edgeMeasure π).prod (edgeMeasure π))
      (edgeCyl (s.filter (fun e => e ∈ S)) t ×ˢ edgeCyl (s.filter (fun e => e ∉ S)) t) =
      (edgeMeasure π) (edgeCyl (s.filter (fun e => e ∈ S)) t) *
        (edgeMeasure π) (edgeCyl (s.filter (fun e => e ∉ S)) t) :=
    Measure.prod_prod _ _
  rw [Measure.map_apply (measurable_forceOn_pair S) hpi, forceOn_preimage_cylinder, hprod,
    edgeMeasure_edgeCyl π _ t ht, edgeMeasure_edgeCyl π _ t ht,
    Finset.prod_filter_mul_prod_filter_not]

/-- The restoration identity with the coordinates of the pair exchanged. -/
theorem edgeMeasure_map_forceOn' (π : Sym2 V → unitInterval) (S : Set (Sym2 V)) :
    ((edgeMeasure π).prod (edgeMeasure π)).map (fun p : Config V × Config V => forceOn S p.2 p.1) =
      edgeMeasure π := by
  have h := edgeMeasure_map_forceOn π S
  have hswap : (fun p : Config V × Config V => forceOn S p.2 p.1) =
      (fun p : Config V × Config V => forceOn S p.1 p.2) ∘ Prod.swap := rfl
  rw [hswap, ← Measure.map_map (measurable_forceOn_pair S) measurable_swap,
    Measure.prod_swap, h]

end PercLib.CriticalLRP
