/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
# The BK inequality for arbitrary increasing events (general Borel form)

Hutchcroft, arXiv:2508.18807, Section I.2.1 and footnote 11: the BK inequality
`P(A ∘ B) ≤ P(A) P(B)` holds for *all* increasing (Borel) events, not only for events that have a
finite witness.  The repository's `bkEdge` proves the finitely witnessed case; this file removes
that hypothesis.

The mathematical idea (no inside cylinder approximation, which fails: an increasing event such as
"infinitely many open edges" has no large increasing cylinder subset):

* Transport the configuration space `Set E` to the Cantor space `E → Bool`; the product law
  `edgeLaw p` becomes a Borel probability measure `boolLaw p` on `E → Bool`.
* As a finite Borel measure on a compact metric space, `boolLaw p` is inner regular for compact
  sets (Mathlib's `InnerRegular` instance): every measurable `A` has a compact `K ⊆ A` with
  `μ A ≤ μ K + ε`.
* Every *closed* (in particular compact) subset `K` of Cantor space is finitely witnessed: for
  `x ∈ K` the finite approximations `x ⊓ 1_{F_n}` tend to `x`, so they lie in `K` eventually.
* The increasing hull `{y | ∃ x ∈ K, x ≤ y}` of a compact `K ⊆ A` is increasing, finitely
  witnessed and contained in `A` whenever `A` is increasing.
* Applying `bkEdge` to the two hulls and letting `ε → 0` gives the general inequality.

-/
module

public import PercLib.CriticalLRP.BK.GraphConsequences
public import PercLib.CriticalLRP.BK.FunctionalIndicator

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

set_option autoImplicit true

set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.dupNamespace false

@[expose] public section

namespace PercLib.CriticalLRP

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section Transport
attribute [local instance] Classical.propDecidable

/-- The `Bool`-coding of a configuration: edge `e` is open iff `x e = true`. -/
noncomputable def boolOf (ω : Set E) : E → Bool := fun e => decide (e ∈ ω)

/-- The configuration coded by a `Bool`-valued function on the edge set. -/
def setOfBool (x : E → Bool) : Set E := {e | x e = true}

@[simp] theorem setOfBool_boolOf (ω : Set E) : setOfBool (boolOf ω) = ω := by
  ext e; simp [setOfBool, boolOf]

@[simp] theorem boolOf_setOfBool (x : E → Bool) : boolOf (setOfBool x) = x := by
  funext e
  by_cases h : x e = true
  · simp [boolOf, setOfBool, h]
  · simp [boolOf, setOfBool, h]

/-- The identification of configurations with `Bool`-valued functions on the edge set. -/
noncomputable def boolEquiv : (E → Bool) ≃ Set E where
  toFun := setOfBool
  invFun := boolOf
  left_inv := boolOf_setOfBool
  right_inv := setOfBool_boolOf

@[simp] theorem boolEquiv_apply_apply (x : E → Bool) : boolEquiv x = setOfBool x := rfl

@[simp] theorem boolEquiv_symm_apply_apply (ω : Set E) : boolEquiv.symm ω = boolOf ω := rfl

/-- The `Bool`-configuration of a finite set of edges. -/
noncomputable def indFinset (s : Finset E) : E → Bool := fun e => decide (e ∈ s)

@[simp] theorem setOfBool_indFinset (s : Finset E) : setOfBool (indFinset s) = (s : Set E) := by
  ext e; simp [setOfBool, indFinset]

theorem subset_setOfBool_iff {x : E → Bool} {s : Finset E} :
    (s : Set E) ⊆ setOfBool x ↔ ∀ e ∈ s, x e = true := by
  simp only [setOfBool, Set.subset_def, Set.mem_ofPred_eq, Finset.mem_coe]

theorem setOfBool_subset_iff {x y : E → Bool} :
    setOfBool x ⊆ setOfBool y ↔ ∀ e, x e ≤ y e := by
  simp only [setOfBool, Set.subset_def, Set.mem_ofPred_eq, Bool.le_iff_imp]

/-- The pointwise order on `Bool`-configurations, expressed through configurations. -/
def Ble (x y : E → Bool) : Prop := setOfBool x ⊆ setOfBool y

theorem ble_iff {x y : E → Bool} : Ble x y ↔ ∀ e, x e = true → y e = true := by
  simp only [Ble, setOfBool, Set.subset_def, Set.mem_ofPred_eq]

theorem ble_indFinset_iff {s : Finset E} {x : E → Bool} :
    Ble (indFinset s) x ↔ ∀ e ∈ s, x e = true := by
  simp only [Ble, subset_setOfBool_iff, setOfBool_indFinset]

theorem ble_refl (x : E → Bool) : Ble x x := subset_rfl

theorem ble_trans {x y z : E → Bool} (h₁ : Ble x y) (h₂ : Ble y z) : Ble x z :=
  h₁.trans h₂

/-- Increasing events, in `Bool`-coding. -/
def BoolUpper (A : Set (E → Bool)) : Prop :=
  ∀ x y : E → Bool, Ble x y → x ∈ A → y ∈ A

/-- Finitely witnessed events, in `Bool`-coding. -/
def BoolWitness (A : Set (E → Bool)) : Prop :=
  ∀ x ∈ A, ∃ s : Finset E, (∀ e ∈ s, x e = true) ∧ indFinset s ∈ A

/-- Disjoint occurrence, in `Bool`-coding. -/
def BoolDisjoint (A B : Set (E → Bool)) : Set (E → Bool) :=
  {x | ∃ s t : Finset E, (∀ e ∈ s, x e = true) ∧ (∀ e ∈ t, x e = true) ∧
    Disjoint s t ∧ indFinset s ∈ A ∧ indFinset t ∈ B}

/-- The increasing hull of a set of configurations. -/
def boolHull (K : Set (E → Bool)) : Set (E → Bool) :=
  {x | ∃ y ∈ K, Ble y x}

theorem mem_image_boolEquiv_iff {A : Set (E → Bool)} {s : Finset E} :
    (s : Set E) ∈ boolEquiv '' A ↔ indFinset s ∈ A := by
  constructor
  · rintro ⟨x, hx, hxs⟩
    have hbs : boolOf (s : Set E) = indFinset s := by
      rw [show (s : Set E) = setOfBool (indFinset s) from (setOfBool_indFinset s).symm,
        boolOf_setOfBool]
    have hx' : x = indFinset s := by
      rw [← hbs]
      simpa using congrArg (⇑boolEquiv.symm) hxs
    rwa [hx'] at hx
  · intro h
    simpa using Set.mem_image_of_mem (⇑boolEquiv) h

theorem isUpperSet_image_iff {A : Set (E → Bool)} :
    IsUpperSet (boolEquiv '' A) ↔ BoolUpper A := by
  constructor
  · intro h x y hxy hx
    have hsub : setOfBool x ⊆ setOfBool y := hxy
    have hx' : setOfBool x ∈ boolEquiv '' A := by simpa using Set.mem_image_of_mem (⇑boolEquiv) hx
    simpa using h hsub hx'
  · rintro h a b hab ⟨x, hx, rfl⟩
    have hab' : setOfBool x ⊆ setOfBool (boolOf b) := by simpa using hab
    have hle : Ble x (boolOf b) := hab'
    simpa using Set.mem_image_of_mem (⇑boolEquiv) (h x (boolOf b) hle hx)

theorem finiteWitness_image_iff {A : Set (E → Bool)} :
    FiniteWitness (boolEquiv '' A) ↔ BoolWitness A := by
  constructor
  · rintro h x hx
    have hx' : setOfBool x ∈ boolEquiv '' A := by simpa using Set.mem_image_of_mem (⇑boolEquiv) hx
    obtain ⟨s, hs, hsa⟩ := h (setOfBool x) hx'
    exact ⟨s, subset_setOfBool_iff.1 hs, mem_image_boolEquiv_iff.1 hsa⟩
  · rintro h ω ⟨x, hx, rfl⟩
    obtain ⟨s, hs, hsa⟩ := h x hx
    exact ⟨s, subset_setOfBool_iff.2 hs, by simpa using Set.mem_image_of_mem (⇑boolEquiv) hsa⟩

theorem boolDisjoint_image (A B : Set (E → Bool)) :
    DisjointOccurrence (boolEquiv '' A) (boolEquiv '' B) = boolEquiv '' (BoolDisjoint A B) := by
  ext ω
  constructor
  · rintro ⟨s, t, hs, ht, hd, ha, hb⟩
    refine ⟨boolOf ω, ?_, by simp⟩
    exact ⟨s, t, fun e he => by simpa [boolOf] using hs he,
      fun e he => by simpa [boolOf] using ht he, hd,
      mem_image_boolEquiv_iff.1 ha, mem_image_boolEquiv_iff.1 hb⟩
  · rintro ⟨x, ⟨s, t, hs, ht, hd, ha, hb⟩, rfl⟩
    exact ⟨s, t, fun e he => hs e he, fun e he => ht e he, hd,
      by simpa using Set.mem_image_of_mem (⇑boolEquiv) ha,
      by simpa using Set.mem_image_of_mem (⇑boolEquiv) hb⟩

theorem boolHull_upper (K : Set (E → Bool)) : BoolUpper (boolHull K) := by
  rintro x y hxy ⟨z, hz, hzx⟩
  exact ⟨z, hz, ble_trans hzx hxy⟩

theorem boolHull_mono {K L : Set (E → Bool)} (h : K ⊆ L) : boolHull K ⊆ boolHull L := by
  rintro x ⟨y, hy, hyx⟩
  exact ⟨y, h hy, hyx⟩

theorem subset_boolHull (K : Set (E → Bool)) : K ⊆ boolHull K := by
  intro x hx
  exact ⟨x, hx, ble_refl x⟩

theorem boolHull_subset_of_subset {A : Set (E → Bool)} (hA : BoolUpper A) {K : Set (E → Bool)}
    (hK : K ⊆ A) : boolHull K ⊆ A := by
  rintro x ⟨y, hy, hyx⟩
  exact hA y x hyx (hK hy)

theorem boolDisjoint_mono {A A' B B' : Set (E → Bool)} (hA : A ⊆ A') (hB : B ⊆ B') :
    BoolDisjoint A B ⊆ BoolDisjoint A' B' := by
  rintro x ⟨s, t, hs, ht, hd, ha, hb⟩
  exact ⟨s, t, hs, ht, hd, hA ha, hB hb⟩

/-- For increasing `A`, the disjoint occurrence of the hulls of `K ⊆ A`, `L ⊆ B` is contained in
the disjoint occurrence of `A`, `B`; only the *finite* witnesses are pushed up. -/
theorem boolDisjoint_hull_subset {A B K L : Set (E → Bool)} (hA : BoolUpper A) (hB : BoolUpper B)
    (hK : K ⊆ A) (hL : L ⊆ B) :
    BoolDisjoint (boolHull K) (boolHull L) ⊆ BoolDisjoint A B := by
  rintro x ⟨s, t, hs, ht, hd, ha, hb⟩
  have ha' : indFinset s ∈ A := by
    obtain ⟨y, hy, hys⟩ := ha
    exact hA y _ hys (hK hy)
  have hb' : indFinset t ∈ B := by
    obtain ⟨y, hy, hyt⟩ := hb
    exact hB y _ hyt (hL hy)
  exact ⟨s, t, hs, ht, hd, ha', hb'⟩

end Transport

section Measurable
variable [Countable E]
attribute [local instance] Classical.propDecidable

theorem measurableSet_ble_const (c : E → Bool) : MeasurableSet {x : E → Bool | Ble c x} := by
  have h : {x : E → Bool | Ble c x} = ⋂ (e : E) (_ : c e = true), {x : E → Bool | x e = true} := by
    ext x
    simp only [Set.mem_ofPred_eq, ble_iff, Set.mem_iInter]
  rw [h]
  exact MeasurableSet.iInter fun e => MeasurableSet.iInter fun _ => by
    have h2 : {x : E → Bool | x e = true} = (fun x : E → Bool => x e) ⁻¹' {true} := rfl
    rw [h2]
    exact (measurable_pi_apply e) (measurableSet_singleton true)

theorem measurableSet_of_boolUpper_witness {A : Set (E → Bool)} (hA : BoolUpper A)
    (hfA : BoolWitness A) : MeasurableSet A := by
  have hset : A = ⋃ s : {s : Finset E // indFinset s ∈ A},
      {x : E → Bool | Ble (indFinset (s : Finset E)) x} := by
    ext x
    constructor
    · intro hx
      obtain ⟨s, hs, hsa⟩ := hfA x hx
      exact Set.mem_iUnion.mpr ⟨⟨s, hsa⟩, ble_indFinset_iff (s := s) (x := x) |>.2 hs⟩
    · intro hx
      obtain ⟨⟨s, hsa⟩, hxs⟩ := Set.mem_iUnion.mp hx
      exact hA _ _ hxs hsa
  rw [hset]
  exact MeasurableSet.iUnion fun s => measurableSet_ble_const _

theorem measurableSet_boolDisjoint {A B : Set (E → Bool)} :
    MeasurableSet (BoolDisjoint A B) := by
  have hset : BoolDisjoint A B = ⋃ p : {p : Finset E × Finset E //
      indFinset p.1 ∈ A ∧ indFinset p.2 ∈ B ∧ Disjoint p.1 p.2},
      ({x : E → Bool | Ble (indFinset (p : Finset E × Finset E).1) x} ∩
        {x : E → Bool | Ble (indFinset (p : Finset E × Finset E).2) x}) := by
    ext x
    constructor
    · rintro ⟨s, t, hs, ht, hd, ha, hb⟩
      exact Set.mem_iUnion.mpr ⟨⟨(s, t), ha, hb, hd⟩,
        ble_indFinset_iff (s := s) (x := x) |>.2 hs,
        ble_indFinset_iff (s := t) (x := x) |>.2 ht⟩
    · intro hx
      obtain ⟨⟨⟨s, t⟩, ha, hb, hd⟩, hs, ht⟩ := Set.mem_iUnion.mp hx
      exact ⟨s, t, ble_indFinset_iff (s := s) (x := x) |>.1 hs,
        ble_indFinset_iff (s := t) (x := x) |>.1 ht, hd, ha, hb⟩
  rw [hset]
  exact MeasurableSet.iUnion fun p =>
    (measurableSet_ble_const _).inter (measurableSet_ble_const _)

theorem BoolWitness_boolHull {K : Set (E → Bool)} (hK : BoolWitness K) :
    BoolWitness (boolHull K) := by
  rintro x ⟨y, hy, hyx⟩
  obtain ⟨s, hs, hsa⟩ := hK y hy
  exact ⟨s, fun e he => ble_iff.1 hyx e (hs e he), subset_boolHull K hsa⟩

end Measurable

end Percolation

end PercLib.CriticalLRP

namespace PercLib.CriticalLRP
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

/-- **Disjoint occurrence with partition witnesses** (the general form of BK, Hutchcroft
arXiv:2508.18807 Section I.2.1 / footnote 11): `ω ∈ A □ B` if two disjoint sub-configurations of
`ω` belong to `A` and `B`.  This is the notion for which BK holds for *all* increasing events;
for finitely witnessed increasing events it coincides with `DisjointOccurrence`. -/
def DisjointOccurrencePart (A B : Set (Set E)) : Set (Set E) :=
  {ω | ∃ η η' : Set E, η ⊆ ω ∧ η' ⊆ ω ∧ Disjoint η η' ∧ η ∈ A ∧ η' ∈ B}

section PartTransport
attribute [local instance] Classical.propDecidable

/-- Disjointness of `Bool`-configurations. -/
def BDisj (η η' : E → Bool) : Prop := ∀ e, η e = true → η' e = true → False

theorem bdisj_iff (η η' : E → Bool) : BDisj η η' ↔ Disjoint (setOfBool η) (setOfBool η') := by
  simp only [BDisj, setOfBool, Set.disjoint_left, Set.mem_ofPred_eq]

/-- Disjoint occurrence with partition witnesses, in `Bool`-coding. -/
def BoolSplit (A B : Set (E → Bool)) : Set (E → Bool) :=
  {x | ∃ η η' : E → Bool, Ble η x ∧ Ble η' x ∧ BDisj η η' ∧ η ∈ A ∧ η' ∈ B}

theorem boolSplit_preimage (A B : Set (E → Bool)) :
    boolOf ⁻¹' BoolSplit A B = DisjointOccurrencePart (boolOf ⁻¹' A) (boolOf ⁻¹' B) := by
  ext ω
  constructor
  · rintro ⟨η, η', hη, hη', hd, hA, hB⟩
    have h1 : setOfBool η ⊆ ω := by
      have h := hη; simp only [Ble, setOfBool_boolOf] at h; exact h
    have h2 : setOfBool η' ⊆ ω := by
      have h := hη'; simp only [Ble, setOfBool_boolOf] at h; exact h
    exact ⟨setOfBool η, setOfBool η', h1, h2, (bdisj_iff η η').1 hd,
      Set.mem_preimage.mpr (by simpa using hA), Set.mem_preimage.mpr (by simpa using hB)⟩
  · rintro ⟨ζ, ζ', hζ, hζ', hd, hA, hB⟩
    refine ⟨boolOf ζ, boolOf ζ', ?_, ?_, ?_, ?_, ?_⟩
    · show setOfBool (boolOf ζ) ⊆ setOfBool (boolOf ω)
      rwa [setOfBool_boolOf, setOfBool_boolOf]
    · show setOfBool (boolOf ζ') ⊆ setOfBool (boolOf ω)
      rwa [setOfBool_boolOf, setOfBool_boolOf]
    · rw [bdisj_iff]
      rwa [setOfBool_boolOf, setOfBool_boolOf]
    · exact Set.mem_preimage.mpr (by simpa using hA)
    · exact Set.mem_preimage.mpr (by simpa using hB)

theorem boolOf_coe_finset (s : Finset E) : boolOf (s : Set E) = indFinset s := by
  funext e; simp [boolOf, indFinset]

theorem boolDisjoint_preimage (A B : Set (E → Bool)) :
    boolOf ⁻¹' BoolDisjoint A B = DisjointOccurrence (boolOf ⁻¹' A) (boolOf ⁻¹' B) := by
  ext ω
  constructor
  · rintro ⟨s, t, hs, ht, hd, hA, hB⟩
    exact ⟨s, t, fun e he => by simpa [boolOf] using hs e he,
      fun e he => by simpa [boolOf] using ht e he, hd,
      Set.mem_preimage.mpr (by rw [boolOf_coe_finset]; exact hA),
      Set.mem_preimage.mpr (by rw [boolOf_coe_finset]; exact hB)⟩
  · rintro ⟨s, t, hs, ht, hd, hA, hB⟩
    exact ⟨s, t, fun e he => by simpa [boolOf] using hs he,
      fun e he => by simpa [boolOf] using ht he, hd,
      (by have h := Set.mem_preimage.mp hA; rwa [boolOf_coe_finset] at h),
      (by have h := Set.mem_preimage.mp hB; rwa [boolOf_coe_finset] at h)⟩

theorem isUpperSet_preimage_iff {A : Set (E → Bool)} :
    IsUpperSet (boolOf ⁻¹' A) ↔ BoolUpper A := by
  constructor
  · intro h x y hxy hx
    have hsub : setOfBool x ⊆ setOfBool y := hxy
    have hx' : setOfBool x ∈ boolOf ⁻¹' A := by simpa using hx
    have hy' : setOfBool y ∈ boolOf ⁻¹' A := h hsub hx'
    simpa using hy'
  · rintro h ω ω' hsub hmem
    have hsub' : Ble (boolOf ω) (boolOf ω') := by
      show setOfBool (boolOf ω) ⊆ setOfBool (boolOf ω')
      rwa [setOfBool_boolOf, setOfBool_boolOf]
    exact h _ _ hsub' (by simpa using hmem)

theorem finiteWitness_preimage_iff {A : Set (E → Bool)} :
    FiniteWitness (boolOf ⁻¹' A) ↔ BoolWitness A := by
  constructor
  · rintro h x hx
    have hx' : setOfBool x ∈ boolOf ⁻¹' A := by simpa using hx
    obtain ⟨s, hs, hsa⟩ := h (setOfBool x) hx'
    refine ⟨s, subset_setOfBool_iff.1 hs, ?_⟩
    have h := Set.mem_preimage.mp hsa
    rwa [boolOf_coe_finset] at h
  · rintro h ω hω
    have hω' : boolOf ω ∈ A := Set.mem_preimage.mp hω
    obtain ⟨s, hs, hsa⟩ := h (boolOf ω) hω'
    exact ⟨s, fun e he => by simpa [boolOf] using hs e he,
      Set.mem_preimage.mpr (by rwa [boolOf_coe_finset])⟩

/-- For increasing finitely witnessed events, partition witnesses can be replaced by finite
witnesses: the two disjoint-occurrence events coincide. -/
theorem boolSplit_eq_boolDisjoint {A B : Set (E → Bool)} (hA : BoolUpper A) (hB : BoolUpper B)
    (hfA : BoolWitness A) (hfB : BoolWitness B) :
    BoolSplit A B = BoolDisjoint A B := by
  ext x
  constructor
  · rintro ⟨η, η', hη, hη', hd, hA', hB'⟩
    obtain ⟨s, hs, hsa⟩ := hfA η hA'
    obtain ⟨t, ht, hta⟩ := hfB η' hB'
    exact ⟨s, t, fun e he => ble_iff.1 hη e (hs e he),
      fun e he => ble_iff.1 hη' e (ht e he),
      Finset.disjoint_left.mpr fun e hes het =>
        hd e (hs e hes) (ht e het), hsa, hta⟩
  · rintro ⟨s, t, hs, ht, hd, hsa, hta⟩
    exact ⟨indFinset s, indFinset t, ble_indFinset_iff.2 hs, ble_indFinset_iff.2 ht,
      fun e he he' => by
        have hes : e ∈ s := by simpa [indFinset] using he
        have het : e ∈ t := by simpa [indFinset] using he'
        exact Finset.disjoint_left.mp hd hes het,
      hsa, hta⟩

end PartTransport

end Percolation
end PercLib.CriticalLRP

namespace PercLib.CriticalLRP
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section CylHull
variable [Countable E]
attribute [local instance] Classical.propDecidable

theorem opensMeasurableSpace_boolConfig : OpensMeasurableSpace (E → Bool) := by
  refine ⟨?_⟩
  rw [BorelSpace.measurable_eq (α := E → Bool)]

/-- The cylinder hull of `A` along the finite edge set `s`: the set of configurations that contain
the `s`-part of some member of `A`.  For increasing `A` this is increasing, and it is determined by
the coordinates in `s`, hence closed. -/
def cylHull (s : Finset E) (A : Set (E → Bool)) : Set (E → Bool) :=
  {x | ∃ z ∈ A, ∀ e ∈ s, z e = true → x e = true}

theorem subset_cylHull (s : Finset E) (A : Set (E → Bool)) : A ⊆ cylHull s A := by
  rintro x hx
  exact ⟨x, hx, fun _ _ h => h⟩

theorem cylHull_mono {A A' : Set (E → Bool)} (h : A ⊆ A') (s : Finset E) :
    cylHull s A ⊆ cylHull s A' := by
  rintro x ⟨z, hz, hzx⟩
  exact ⟨z, h hz, hzx⟩

theorem cylHull_antitone {s t : Finset E} (h : s ⊆ t) (A : Set (E → Bool)) :
    cylHull t A ⊆ cylHull s A := by
  rintro x ⟨z, hz, hzx⟩
  exact ⟨z, hz, fun e he => hzx e (h he)⟩

theorem cylHull_upper {A : Set (E → Bool)} (hA : BoolUpper A) (s : Finset E) :
    BoolUpper (cylHull s A) := by
  rintro x y hxy ⟨z, hz, hzx⟩
  exact ⟨z, hz, fun e he hze => ble_iff.1 hxy e (hzx e he hze)⟩

theorem cylHull_depends {s : Finset E} {A : Set (E → Bool)} {x y : E → Bool}
    (h : ∀ e ∈ s, x e = y e) : x ∈ cylHull s A ↔ y ∈ cylHull s A := by
  constructor <;> rintro ⟨z, hz, hzx⟩
  · exact ⟨z, hz, fun e he hze => (h e he).symm ▸ hzx e he hze⟩
  · exact ⟨z, hz, fun e he hze => (h e he) ▸ hzx e he hze⟩

theorem isClosed_cylHull (s : Finset E) (A : Set (E → Bool)) : IsClosed (cylHull s A) := by
  have h : cylHull s A =
      (fun x : E → Bool => fun e : s => x e.1) ⁻¹' ((fun x : E → Bool => fun e : s => x e.1) '' cylHull s A) := by
    ext x
    constructor
    · intro hx
      exact ⟨x, hx, rfl⟩
    · rintro ⟨y, hy, hxy⟩
      have hd : ∀ e ∈ s, x e = y e := fun e he => by
        have := congrFun hxy ⟨e, he⟩
        simpa using this.symm
      exact (cylHull_depends (A := A) hd).2 hy
  rw [h]
  exact (Set.toFinite _).isClosed.preimage (continuous_pi fun e => continuous_apply e.1)

theorem measurableSet_cylHull (s : Finset E) (A : Set (E → Bool)) :
    MeasurableSet (cylHull s A) :=
  (isClosed_cylHull s A).measurableSet

/-- The cylinder hull of any set is finitely witnessed. -/
theorem BoolWitness_cylHull (s : Finset E) (A : Set (E → Bool)) :
    BoolWitness (cylHull s A) := by
  rintro x ⟨z, hz, hzx⟩
  refine ⟨s.filter (fun e => x e = true), fun e he => (Finset.mem_filter.mp he).2, ?_⟩
  refine ⟨z, hz, fun e he hze => ?_⟩
  have hxe : x e = true := hzx e he hze
  have : e ∈ s.filter (fun e => x e = true) := Finset.mem_filter.mpr ⟨he, hxe⟩
  simp [indFinset, this]

theorem cylHull_boolHull (s : Finset E) (K : Set (E → Bool)) :
    cylHull s (boolHull K) = cylHull s K := by
  ext x
  constructor
  · rintro ⟨z, ⟨y, hy, hyz⟩, hzx⟩
    exact ⟨y, hy, fun e he hye => hzx e he (ble_iff.1 hyz e hye)⟩
  · rintro ⟨y, hy, hyx⟩
    exact ⟨y, subset_boolHull K hy, hyx⟩

end CylHull

end Percolation
end PercLib.CriticalLRP

namespace PercLib.CriticalLRP
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section FIP
variable [Countable E]
attribute [local instance] Classical.propDecidable

theorem isClosed_ble_const (c : E → Bool) : IsClosed {x : E → Bool | Ble c x} := by
  have h : {x : E → Bool | Ble c x} = ⋂ (e : E) (_ : c e = true), {x : E → Bool | x e = true} := by
    ext x
    simp only [Set.mem_ofPred_eq, ble_iff, Set.mem_iInter]
  rw [h]
  refine isClosed_iInter fun e => isClosed_iInter fun _ => ?_
  have h2 : {x : E → Bool | x e = true} = (fun x : E → Bool => x e) ⁻¹' {true} := rfl
  rw [h2]
  exact isClosed_singleton.preimage (continuous_apply e)

/-- The principal down-set `{η | η ⊆ x}` of a configuration is closed. -/
theorem isClosed_ble_const' (x : E → Bool) : IsClosed {η : E → Bool | Ble η x} := by
  have h : {η : E → Bool | Ble η x} = ⋂ e : E, {η : E → Bool | η e ≤ x e} := by
    ext η
    simp only [Set.mem_ofPred_eq, ble_iff, Set.mem_iInter, Bool.le_iff_imp]
  rw [h]
  refine isClosed_iInter fun e => ?_
  have h2 : {η : E → Bool | η e ≤ x e} =
      (fun η : E → Bool => (η e, x e)) ⁻¹' {q : Bool × Bool | q.1 ≤ q.2} := rfl
  rw [h2]
  exact (Set.toFinite _).isClosed.preimage
    ((continuous_apply e).prodMk continuous_const)

/-- The set of pairs of disjoint sub-configurations of `x` is closed (hence compact). -/
theorem isClosed_pairSet (x : E → Bool) :
    IsClosed {p : (E → Bool) × (E → Bool) | Ble p.1 x ∧ Ble p.2 x ∧ BDisj p.1 p.2} := by
  have h : {p : (E → Bool) × (E → Bool) | Ble p.1 x ∧ Ble p.2 x ∧ BDisj p.1 p.2} =
      {p : (E → Bool) × (E → Bool) | Ble p.1 x} ∩ {p : (E → Bool) × (E → Bool) | Ble p.2 x} ∩
      {p : (E → Bool) × (E → Bool) | ∀ e, ¬(p.1 e = true ∧ p.2 e = true)} := by
    ext p
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, BDisj]
    tauto
  rw [h]
  have h1 : {p : (E → Bool) × (E → Bool) | Ble p.1 x} =
      (fun p : (E → Bool) × (E → Bool) => p.1) ⁻¹' {η : E → Bool | Ble η x} := rfl
  have h2 : {p : (E → Bool) × (E → Bool) | Ble p.2 x} =
      (fun p : (E → Bool) × (E → Bool) => p.2) ⁻¹' {η : E → Bool | Ble η x} := rfl
  rw [h1, h2]
  refine ((isClosed_ble_const' x).preimage continuous_fst |>.inter
    ((isClosed_ble_const' x).preimage continuous_snd)).inter ?_
  have h3 : {p : (E → Bool) × (E → Bool) | ∀ e, ¬(p.1 e = true ∧ p.2 e = true)} =
      ⋂ e : E, {p : (E → Bool) × (E → Bool) | ¬(p.1 e = true ∧ p.2 e = true)} := by
    ext p; simp
  rw [h3]
  refine isClosed_iInter fun e => ?_
  have h4 : {p : (E → Bool) × (E → Bool) | ¬(p.1 e = true ∧ p.2 e = true)} =
      (fun p : (E → Bool) × (E → Bool) => (p.1 e, p.2 e)) ⁻¹'
        ({q : Bool × Bool | ¬(q.1 = true ∧ q.2 = true)}) := rfl
  rw [h4]
  exact (Set.toFinite _).isClosed.preimage
    ((continuous_apply e).comp continuous_fst |>.prodMk ((continuous_apply e).comp continuous_snd))

/-- **The cylinder hulls of a compact set shrink to its increasing hull.** -/
theorem iInter_cylHull [Encodable E] {K : Set (E → Bool)} (hK : IsCompact K) :
    (⋂ n, cylHull (edgeExhaustion (E := E) n) K) = boolHull K := by
  ext x
  constructor
  · intro hx
    set V : ℕ → Set (E → Bool) := fun n =>
      K ∩ {y : E → Bool | Ble y (fun e => if e ∈ edgeExhaustion (E := E) n then x e else true)} with hV
    have hVanti : ∀ n, V (n + 1) ⊆ V n := by
      intro n y hy
      refine ⟨hy.1, ble_iff.2 fun e hye => ?_⟩
      have h2 : (if e ∈ edgeExhaustion (E := E) (n + 1) then x e else true) = true :=
        ble_iff.1 hy.2 e hye
      by_cases he : e ∈ edgeExhaustion (E := E) n
      · rw [ite_eq_left he]
        rwa [ite_eq_left (edgeExhaustion_mono (Nat.le_succ n) he)] at h2
      · rw [ite_eq_right he]
    have hVne : ∀ n, (V n).Nonempty := by
      intro n
      obtain ⟨z, hz, hzx⟩ := Set.mem_iInter.mp hx n
      refine ⟨z, hz, ble_iff.2 fun e hze => ?_⟩
      by_cases he : e ∈ edgeExhaustion (E := E) n
      · rw [ite_eq_left he]; exact hzx e he hze
      · rw [ite_eq_right he]
    have hVclosed : ∀ n, IsClosed (V n) := by
      intro n
      exact hK.isClosed.inter (isClosed_ble_const' _)
    obtain ⟨y, hy⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed V hVanti hVne
      (hK.of_isClosed_subset (hVclosed 0) Set.inter_subset_left) hVclosed
    refine ⟨y, (Set.mem_iInter.mp hy 0).1, ble_iff.2 fun e hye => ?_⟩
    obtain ⟨n, hn⟩ := subset_edgeExhaustion ({e} : Finset E)
    have hy2 := ble_iff.1 (Set.mem_iInter.mp hy n).2 e hye
    rwa [ite_eq_left (hn (by simp))] at hy2
  · intro hx
    refine Set.mem_iInter.mpr fun n => ?_
    obtain ⟨y, hy, hyx⟩ := hx
    exact ⟨y, hy, fun e _ hye => ble_iff.1 hyx e hye⟩

end FIP

end Percolation
end PercLib.CriticalLRP

namespace PercLib.CriticalLRP
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section SplitFIP
variable [Countable E]
attribute [local instance] Classical.propDecidable

theorem boolSplit_mono {A A' B B' : Set (E → Bool)} (hA : A ⊆ A') (hB : B ⊆ B') :
    BoolSplit A B ⊆ BoolSplit A' B' := by
  rintro x ⟨η, η', h1, h2, h3, h4, h5⟩
  exact ⟨η, η', h1, h2, h3, hA h4, hB h5⟩

/-- On cylinder hulls the partition disjoint occurrence is a countable union of closed sets, hence
measurable. -/
theorem boolSplit_cylHull_eq (s : Finset E) (A B : Set (E → Bool)) :
    BoolSplit (cylHull s A) (cylHull s B) =
      ⋃ p : {q : Finset E × Finset E //
          indFinset q.1 ∈ cylHull s A ∧ indFinset q.2 ∈ cylHull s B ∧ Disjoint q.1 q.2},
        {x : E → Bool | Ble (indFinset ((p : Finset E × Finset E).1 ∪
          (p : Finset E × Finset E).2)) x} := by
  ext x
  constructor
  · rintro ⟨η, η', hη, hη', hd, hA, hB⟩
    have hAs : indFinset (s.filter (fun e => η e = true)) ∈ cylHull s A := by
      obtain ⟨z, hz, hzx⟩ := hA
      refine ⟨z, hz, fun e he hze => ?_⟩
      have hηe : η e = true := hzx e he hze
      have hmem : e ∈ s.filter (fun e => η e = true) := Finset.mem_filter.mpr ⟨he, hηe⟩
      simp [indFinset, hmem]
    have hBs : indFinset (s.filter (fun e => η' e = true)) ∈ cylHull s B := by
      obtain ⟨z, hz, hzx⟩ := hB
      refine ⟨z, hz, fun e he hze => ?_⟩
      have hηe : η' e = true := hzx e he hze
      have hmem : e ∈ s.filter (fun e => η' e = true) := Finset.mem_filter.mpr ⟨he, hηe⟩
      simp [indFinset, hmem]
    have hds : Disjoint (s.filter (fun e => η e = true)) (s.filter (fun e => η' e = true)) := by
      rw [Finset.disjoint_left]
      intro e he he'
      exact hd e (Finset.mem_filter.mp he).2 (Finset.mem_filter.mp he').2
    refine Set.mem_iUnion.mpr ⟨⟨(s.filter (fun e => η e = true), s.filter (fun e => η' e = true)),
      hAs, hBs, hds⟩, ?_⟩
    refine ble_iff.2 fun e he => ?_
    have hmem : e ∈ s.filter (fun e => η e = true) ∨ e ∈ s.filter (fun e => η' e = true) := by
      simpa [indFinset, Finset.mem_union] using he
    rcases hmem with h | h
    · exact ble_iff.1 hη e (Finset.mem_filter.mp h).2
    · exact ble_iff.1 hη' e (Finset.mem_filter.mp h).2
  · rw [Set.mem_iUnion]
    rintro ⟨p, hp⟩
    obtain ⟨hA, hB, hd⟩ := p.property
    have hp' : Ble (indFinset ((p : Finset E × Finset E).1 ∪
        (p : Finset E × Finset E).2)) x := hp
    refine ⟨indFinset (p : Finset E × Finset E).1, indFinset (p : Finset E × Finset E).2,
      ?_, ?_, ?_, hA, hB⟩
    · refine ble_iff.2 fun e he => ble_iff.1 hp' e ?_
      have h : e ∈ (p : Finset E × Finset E).1 := by simpa [indFinset] using he
      simp [indFinset, Finset.mem_union, h]
    · refine ble_iff.2 fun e he => ble_iff.1 hp' e ?_
      have h : e ∈ (p : Finset E × Finset E).2 := by simpa [indFinset] using he
      simp [indFinset, Finset.mem_union, h]
    · intro e he he'
      have hes : e ∈ (p : Finset E × Finset E).1 := by simpa [indFinset] using he
      have het : e ∈ (p : Finset E × Finset E).2 := by simpa [indFinset] using he'
      exact (Finset.disjoint_left.mp hd hes) het

theorem measurableSet_boolSplit_cylHull (s : Finset E) (A B : Set (E → Bool)) :
    MeasurableSet (BoolSplit (cylHull s A) (cylHull s B)) := by
  rw [boolSplit_cylHull_eq]
  exact MeasurableSet.iUnion fun p => measurableSet_ble_const _

/-- The sets of the approximating sequence in the finite intersection argument are closed. -/
theorem isClosed_splitLe (x : E → Bool) (s : Finset E) (K L : Set (E → Bool)) :
    IsClosed {p : (E → Bool) × (E → Bool) | Ble p.1 x ∧ Ble p.2 x ∧ BDisj p.1 p.2 ∧
      p.1 ∈ cylHull s K ∧ p.2 ∈ cylHull s L} := by
  have h : {p : (E → Bool) × (E → Bool) | Ble p.1 x ∧ Ble p.2 x ∧ BDisj p.1 p.2 ∧
      p.1 ∈ cylHull s K ∧ p.2 ∈ cylHull s L} =
      {p : (E → Bool) × (E → Bool) | Ble p.1 x ∧ Ble p.2 x ∧ BDisj p.1 p.2} ∩
      ((fun p : (E → Bool) × (E → Bool) => p.1) ⁻¹' cylHull s K) ∩
      ((fun p : (E → Bool) × (E → Bool) => p.2) ⁻¹' cylHull s L) := by
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage]
    tauto
  rw [h]
  exact ((isClosed_pairSet x).inter (IsClosed.preimage continuous_fst (isClosed_cylHull s K))).inter
    (IsClosed.preimage continuous_snd (isClosed_cylHull s L))

theorem boolHull_subset_cylHull (s : Finset E) (K : Set (E → Bool)) :
    boolHull K ⊆ cylHull s K := by
  rintro x ⟨y, hy, hyx⟩
  exact ⟨y, hy, fun e _ hye => ble_iff.1 hyx e hye⟩

/-- **Finite intersection property step**: the partition disjoint occurrence of the hulls of two
compact sets is the decreasing intersection of the level-`n` occurrences. -/
theorem boolSplit_eq_iInter [Encodable E] {K L : Set (E → Bool)} (hK : IsCompact K)
    (hL : IsCompact L) :
    BoolSplit (boolHull K) (boolHull L) =
      ⋂ n, BoolSplit (cylHull (edgeExhaustion (E := E) n) K)
        (cylHull (edgeExhaustion (E := E) n) L) := by
  ext x
  constructor
  · intro hx
    exact Set.mem_iInter.mpr fun n =>
      boolSplit_mono (boolHull_subset_cylHull _ K) (boolHull_subset_cylHull _ L) hx
  · intro hx
    set S : ℕ → Set ((E → Bool) × (E → Bool)) := fun n =>
      {p : (E → Bool) × (E → Bool) | Ble p.1 x ∧ Ble p.2 x ∧ BDisj p.1 p.2 ∧
        p.1 ∈ cylHull (edgeExhaustion (E := E) n) K ∧
        p.2 ∈ cylHull (edgeExhaustion (E := E) n) L} with hS
    have hanti : ∀ n, S (n + 1) ⊆ S n := by
      intro n p hp
      obtain ⟨h1, h2, h3, h4, h5⟩ := hp
      exact ⟨h1, h2, h3, cylHull_antitone (edgeExhaustion_mono (Nat.le_succ n)) K h4,
        cylHull_antitone (edgeExhaustion_mono (Nat.le_succ n)) L h5⟩
    have hne : ∀ n, (S n).Nonempty := by
      intro n
      have := Set.mem_iInter.mp hx n
      obtain ⟨η, η', h1, h2, h3, h4, h5⟩ := this
      exact ⟨(η, η'), h1, h2, h3, h4, h5⟩
    have hclosed : ∀ n, IsClosed (S n) := fun n => isClosed_splitLe x _ K L
    have hcomp : IsCompact (S 0) := (hclosed 0).isCompact
    obtain ⟨p, hp⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed S hanti hne
      hcomp hclosed
    obtain ⟨h1, h2, h3, h4, h5⟩ := Set.mem_iInter.mp hp 0
    refine ⟨p.1, p.2, h1, h2, h3, ?_, ?_⟩
    · rw [← iInter_cylHull (E := E) hK]
      exact Set.mem_iInter.mpr fun n => (Set.mem_iInter.mp hp n).2.2.2.1
    · rw [← iInter_cylHull (E := E) hL]
      exact Set.mem_iInter.mpr fun n => (Set.mem_iInter.mp hp n).2.2.2.2

end SplitFIP

end Percolation
end PercLib.CriticalLRP

namespace PercLib.CriticalLRP

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section BoolLaw
variable [Countable E]
attribute [local instance] Classical.propDecidable

theorem measurable_decide_mem (e : E) : Measurable (fun ω : Set E => decide (e ∈ ω)) :=
  (Measurable.of_discrete (f := fun p : Prop => decide p)).comp (measurable_set_mem e)

theorem measurable_boolOf : Measurable (fun ω : Set E => boolOf ω) := by
  rw [measurable_pi_iff]
  intro e
  exact measurable_decide_mem e

/-- The edge law transported to the Cantor space `E → Bool`. -/
noncomputable def boolLaw (p : E → unitInterval) : Measure (E → Bool) :=
  (edgeLaw p).map (fun ω => boolOf ω)

theorem boolOf_preimage_eq (S : Set (E → Bool)) : boolOf ⁻¹' S = boolEquiv '' S := by
  ext ω
  constructor
  · intro h
    exact ⟨boolOf ω, h, by simp⟩
  · rintro ⟨x, hx, rfl⟩
    simpa using hx

theorem boolLaw_apply (p : E → unitInterval) {S : Set (E → Bool)} (hS : MeasurableSet S) :
    boolLaw p S = (edgeLaw p) (boolEquiv '' S) := by
  rw [boolLaw, Measure.map_apply measurable_boolOf hS, boolOf_preimage_eq]

theorem boolLaw_real (p : E → unitInterval) {S : Set (E → Bool)} (hS : MeasurableSet S) :
    (boolLaw p).real S = (edgeLaw p).real (boolEquiv '' S) := by
  rw [Measure.real, Measure.real, boolLaw_apply p hS]

instance boolLaw_isProbabilityMeasure (p : E → unitInterval) : IsProbabilityMeasure (boolLaw p) := by
  constructor
  rw [boolLaw_apply p MeasurableSet.univ]
  simp

instance boolLaw_innerRegular (p : E → unitInterval) : (boolLaw p).InnerRegular :=
  MeasureTheory.instInnerRegularOfIsCompletelyPseudoMetrizableSpace _

/-- Inner regularity of the transported law, in `ℝ` form: measurable sets are approximated from
inside by compact sets. -/
theorem exists_isCompact_subset_measureReal_le_add (p : E → unitInterval) {S : Set (E → Bool)}
    (hS : MeasurableSet S) {ε : ℝ} (hε : 0 < ε) :
    ∃ K, K ⊆ S ∧ IsCompact K ∧ (boolLaw p).real S ≤ (boolLaw p).real K + ε := by
  obtain ⟨K, hKS, hKc, hlt⟩ := MeasurableSet.exists_isCompact_lt_add (μ := boolLaw p) hS
    (measure_ne_top _ _) (ENNReal.ofReal_ne_zero_iff.mpr hε)
  refine ⟨K, hKS, hKc, ?_⟩
  have hfin : boolLaw p K ≠ ⊤ := measure_ne_top _ _
  have h2 : ((boolLaw p) K + ENNReal.ofReal ε).toReal = (boolLaw p).real K + ε := by
    rw [ENNReal.toReal_add hfin ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hε.le]
    rfl
  calc (boolLaw p).real S ≤ ((boolLaw p) K + ENNReal.ofReal ε).toReal :=
        (ENNReal.toReal_le_toReal (measure_ne_top _ _) (by simp)).mpr hlt.le
    _ = (boolLaw p).real K + ε := h2

/-- **BK for increasing finitely witnessed events** under the transported law, with finite
witnesses (this is the repository's `bkEdge`, transported). -/
theorem bool_bk_witness (p : E → unitInterval) (hp : ∀ e, p e < 1)
    {A B : Set (E → Bool)} (hA : BoolUpper A) (hB : BoolUpper B)
    (hfA : BoolWitness A) (hfB : BoolWitness B) :
    (boolLaw p).real (BoolDisjoint A B) ≤ (boolLaw p).real A * (boolLaw p).real B := by
  have hmA : MeasurableSet A := measurableSet_of_boolUpper_witness hA hfA
  have hmB : MeasurableSet B := measurableSet_of_boolUpper_witness hB hfB
  have hmD : MeasurableSet (BoolDisjoint A B) := measurableSet_boolDisjoint
  have hbk := bkEdge p hp (boolOf ⁻¹' A) (boolOf ⁻¹' B)
    (isUpperSet_preimage_iff.mpr hA) (isUpperSet_preimage_iff.mpr hB)
    (finiteWitness_preimage_iff.mpr hfA) (finiteWitness_preimage_iff.mpr hfB)
  rw [← boolDisjoint_preimage, boolOf_preimage_eq, boolOf_preimage_eq, boolOf_preimage_eq] at hbk
  rw [← boolLaw_real p hmD, ← boolLaw_real p hmA, ← boolLaw_real p hmB] at hbk
  exact hbk

/-- **BK with partition witnesses for increasing finitely witnessed events.** -/
theorem bool_bk_split_witness (p : E → unitInterval) (hp : ∀ e, p e < 1)
    {A B : Set (E → Bool)} (hA : BoolUpper A) (hB : BoolUpper B)
    (hfA : BoolWitness A) (hfB : BoolWitness B) :
    (boolLaw p).real (BoolSplit A B) ≤ (boolLaw p).real A * (boolLaw p).real B := by
  rw [boolSplit_eq_boolDisjoint hA hB hfA hfB]
  exact bool_bk_witness p hp hA hB hfA hfB

end BoolLaw

end Percolation
end PercLib.CriticalLRP

namespace PercLib.CriticalLRP

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section GeneralBK
variable [Countable E] [Encodable E]
attribute [local instance] Classical.propDecidable

theorem boolUpper_cylHull' (s : Finset E) (K : Set (E → Bool)) :
    BoolUpper (cylHull s K) := by
  rw [← cylHull_boolHull (K := K)]
  exact cylHull_upper (boolHull_upper K) s

/-- **BK for the increasing hulls of compact sets** (the infinite-witness/partition form). -/
theorem bool_bk_hull (p : E → unitInterval) (hp : ∀ e, p e < 1)
    {K L : Set (E → Bool)} (hK : IsCompact K) (hL : IsCompact L) :
    (boolLaw p).real (BoolSplit (boolHull K) (boolHull L)) ≤
      (boolLaw p).real (boolHull K) * (boolLaw p).real (boolHull L) := by
  have hlimK : Tendsto (fun n => (boolLaw p).real (cylHull (edgeExhaustion (E := E) n) K)) atTop
      (𝓝 ((boolLaw p).real (boolHull K))) := by
    have h := tendsto_measure_iInter_atTop (μ := boolLaw p)
      (fun n => (measurableSet_cylHull _ _).nullMeasurableSet)
      (fun m n hmn => cylHull_antitone (edgeExhaustion_mono hmn) K) ⟨0, measure_ne_top _ _⟩
    rw [iInter_cylHull hK] at h
    exact (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp h
  have hlimL : Tendsto (fun n => (boolLaw p).real (cylHull (edgeExhaustion (E := E) n) L)) atTop
      (𝓝 ((boolLaw p).real (boolHull L))) := by
    have h := tendsto_measure_iInter_atTop (μ := boolLaw p)
      (fun n => (measurableSet_cylHull _ _).nullMeasurableSet)
      (fun m n hmn => cylHull_antitone (edgeExhaustion_mono hmn) L) ⟨0, measure_ne_top _ _⟩
    rw [iInter_cylHull hL] at h
    exact (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp h
  have hlimD : Tendsto (fun n => (boolLaw p).real
      (BoolSplit (cylHull (edgeExhaustion (E := E) n) K) (cylHull (edgeExhaustion (E := E) n) L)))
      atTop (𝓝 ((boolLaw p).real (BoolSplit (boolHull K) (boolHull L)))) := by
    have h := tendsto_measure_iInter_atTop (μ := boolLaw p)
      (fun n => (measurableSet_boolSplit_cylHull _ _ _).nullMeasurableSet)
      (fun m n hmn => boolSplit_mono (cylHull_antitone (edgeExhaustion_mono hmn) K)
        (cylHull_antitone (edgeExhaustion_mono hmn) L)) ⟨0, measure_ne_top _ _⟩
    rw [← boolSplit_eq_iInter hK hL] at h
    exact (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp h
  refine le_of_tendsto_of_tendsto' hlimD (hlimK.mul hlimL) fun n => ?_
  exact bool_bk_split_witness p hp (boolUpper_cylHull' _ K) (boolUpper_cylHull' _ L)
    (BoolWitness_cylHull _ _) (BoolWitness_cylHull _ _)

end GeneralBK

end Percolation
end PercLib.CriticalLRP

namespace PercLib.CriticalLRP

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section OpenCase
variable [Countable E] [Encodable E]
attribute [local instance] Classical.propDecidable

/-- The set of configurations whose full `s`-cylinder is contained in `A`. -/
def cylIn (A : Set (E → Bool)) (s : Finset E) : Set (E → Bool) :=
  {x | ∀ y : E → Bool, (∀ e ∈ s, y e = x e) → y ∈ A}

theorem cylIn_subset (A : Set (E → Bool)) (s : Finset E) : cylIn A s ⊆ A :=
  fun x hx => hx x fun _ _ => rfl

theorem cylIn_upper {A : Set (E → Bool)} (hA : BoolUpper A) (s : Finset E) :
    BoolUpper (cylIn A s) := by
  rintro x y hxy hx z hz
  set w : E → Bool := fun e => if e ∈ s then x e else z e with hw
  have hwA : w ∈ A := hx w (fun e he => by simp [hw, he])
  refine hA w z (ble_iff.2 fun e hwe => ?_) hwA
  by_cases he : e ∈ s
  · have hwe' : x e = true := by simpa [hw, he] using hwe
    rw [hz e he]
    exact ble_iff.1 hxy e hwe'
  · exact by simpa [hw, he] using hwe

theorem cylIn_mono_finset {A : Set (E → Bool)} {s t : Finset E} (h : s ⊆ t) :
    cylIn A s ⊆ cylIn A t := by
  intro x hx y hy
  exact hx y fun e he => hy e (h he)

theorem cylIn_mono {A A' : Set (E → Bool)} (h : A ⊆ A') (s : Finset E) :
    cylIn A s ⊆ cylIn A' s :=
  fun x hx y hy => h (hx y hy)

theorem cylIn_depends {A : Set (E → Bool)} {s : Finset E} {x y : E → Bool}
    (h : ∀ e ∈ s, x e = y e) : x ∈ cylIn A s ↔ y ∈ cylIn A s := by
  constructor
  · intro hx z hz
    exact hx z fun e he => (h e he).symm ▸ hz e he
  · intro hy z hz
    exact hy z fun e he => (h e he) ▸ hz e he

theorem isClosed_cylIn (A : Set (E → Bool)) (s : Finset E) : IsClosed (cylIn A s) := by
  have h : cylIn A s = (fun x : E → Bool => fun e : s => x e.1) ⁻¹'
      ((fun x : E → Bool => fun e : s => x e.1) '' cylIn A s) := by
    ext x
    constructor
    · intro hx; exact ⟨x, hx, rfl⟩
    · rintro ⟨y, hy, hxy⟩
      have hd : ∀ e ∈ s, x e = y e := fun e he => by
        have := congrFun hxy ⟨e, he⟩
        simpa using this.symm
      exact (cylIn_depends hd).2 hy
  rw [h]
  exact (Set.toFinite _).isClosed.preimage (continuous_pi fun e => continuous_apply e.1)

theorem measurableSet_cylIn (A : Set (E → Bool)) (s : Finset E) : MeasurableSet (cylIn A s) :=
  (isClosed_cylIn A s).measurableSet

theorem BoolWitness_cylIn (A : Set (E → Bool)) (s : Finset E) : BoolWitness (cylIn A s) := by
  rintro x hx
  refine ⟨s.filter (fun e => x e = true), fun e he => (Finset.mem_filter.mp he).2, ?_⟩
  intro y hy
  refine hx y fun e he => ?_
  have h1 := hy e he
  by_cases hxe : x e = true
  · have hmem : e ∈ s.filter (fun e => x e = true) := Finset.mem_filter.mpr ⟨he, hxe⟩
    rw [h1]
    simp [indFinset, hmem, hxe]
  · have hxf : x e = false := by simpa using hxe
    have hnot : e ∉ s.filter (fun e => x e = true) := by
      simp [Finset.mem_filter, hxf]
    rw [h1]
    simp [indFinset, hnot, hxf]

/-- In a space of `Bool`-configurations, every point of an open set has a finite cylinder inside. -/
theorem exists_cylIn_of_isOpen {A : Set (E → Bool)} (hA : IsOpen A) {x : E → Bool}
    (hx : x ∈ A) : ∃ s : Finset E, x ∈ cylIn A s := by
  obtain ⟨v, ⟨U, F, hU, rfl⟩, hxv, hvA⟩ :=
    (isTopologicalBasis_pi (X := fun _ : E => Bool)
      (fun _ => TopologicalSpace.isTopologicalBasis_opens)).exists_subset_of_mem_open hx hA
  refine ⟨F, fun y hy => hvA ?_⟩
  simp only [Set.mem_pi] at hxv ⊢
  intro i hi
  rw [hy i hi]
  exact hxv i hi

/-- For an open set, the cylinders inside it increase to it along the edge exhaustion. -/
theorem iUnion_cylIn {A : Set (E → Bool)} (hA : IsOpen A) :
    (⋃ n, cylIn A (edgeExhaustion (E := E) n)) = A := by
  ext x
  constructor
  · intro hx
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx
    exact hn x fun e he => rfl
  · intro hx
    obtain ⟨s, hs⟩ := exists_cylIn_of_isOpen hA hx
    obtain ⟨n, hn⟩ := subset_edgeExhaustion s
    exact Set.mem_iUnion.mpr ⟨n, cylIn_mono_finset hn hs⟩

theorem boolSplit_cylIn_eq {A B : Set (E → Bool)} (hA : IsOpen A) (hB : IsOpen B) :
    BoolSplit A B = ⋃ n, BoolSplit (cylIn A (edgeExhaustion (E := E) n))
      (cylIn B (edgeExhaustion (E := E) n)) := by
  ext x
  constructor
  · rintro ⟨η, η', h1, h2, h3, h4, h5⟩
    obtain ⟨s, hs⟩ := exists_cylIn_of_isOpen hA h4
    obtain ⟨t, ht⟩ := exists_cylIn_of_isOpen hB h5
    obtain ⟨m, hm⟩ := subset_edgeExhaustion s
    obtain ⟨k, hk⟩ := subset_edgeExhaustion t
    refine Set.mem_iUnion.mpr ⟨max m k, η, η', h1, h2, h3, ?_, ?_⟩
    · exact cylIn_mono_finset (fun e he => edgeExhaustion_mono (le_max_left m k) (hm he)) hs
    · exact cylIn_mono_finset (fun e he => edgeExhaustion_mono (le_max_right m k) (hk he)) ht
  · intro hx
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx
    exact boolSplit_mono (cylIn_subset A _) (cylIn_subset B _) hn

end OpenCase

end Percolation
end PercLib.CriticalLRP

namespace PercLib.CriticalLRP

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section GeneralCase
variable [Countable E] [Encodable E]
attribute [local instance] Classical.propDecidable

theorem boolSplit_cylIn_eq' (s : Finset E) (A B : Set (E → Bool)) :
    BoolSplit (cylIn A s) (cylIn B s) =
      ⋃ p : {q : Finset E × Finset E //
          indFinset q.1 ∈ cylIn A s ∧ indFinset q.2 ∈ cylIn B s ∧ Disjoint q.1 q.2},
        {x : E → Bool | Ble (indFinset ((p : Finset E × Finset E).1 ∪
          (p : Finset E × Finset E).2)) x} := by
  ext x
  constructor
  · rintro ⟨η, η', hη, hη', hd, hA, hB⟩
    have hAt : indFinset (s.filter (fun e => η e = true)) ∈ cylIn A s := by
      refine (cylIn_depends (A := A) (s := s) (x := η) (y := indFinset (s.filter (fun e => η e = true))) ?_).1 hA
      intro e he
      by_cases hηe : η e = true
      · have hmem : e ∈ s.filter (fun e => η e = true) := Finset.mem_filter.mpr ⟨he, hηe⟩
        simp [indFinset, hmem, hηe]
      · have hηf : η e = false := by simpa using hηe
        have hnot : e ∉ s.filter (fun e => η e = true) := by simp [Finset.mem_filter, hηf]
        simp [indFinset, hnot, hηf]
    have hBt : indFinset (s.filter (fun e => η' e = true)) ∈ cylIn B s := by
      refine (cylIn_depends (A := B) (s := s) (x := η') (y := indFinset (s.filter (fun e => η' e = true))) ?_).1 hB
      intro e he
      by_cases hηe : η' e = true
      · have hmem : e ∈ s.filter (fun e => η' e = true) := Finset.mem_filter.mpr ⟨he, hηe⟩
        simp [indFinset, hmem, hηe]
      · have hηf : η' e = false := by simpa using hηe
        have hnot : e ∉ s.filter (fun e => η' e = true) := by simp [Finset.mem_filter, hηf]
        simp [indFinset, hnot, hηf]
    have hds : Disjoint (s.filter (fun e => η e = true)) (s.filter (fun e => η' e = true)) := by
      rw [Finset.disjoint_left]
      intro e he he'
      exact hd e (Finset.mem_filter.mp he).2 (Finset.mem_filter.mp he').2
    refine Set.mem_iUnion.mpr ⟨⟨(s.filter (fun e => η e = true), s.filter (fun e => η' e = true)),
      hAt, hBt, hds⟩, ?_⟩
    refine ble_iff.2 fun e he => ?_
    have hmem : e ∈ s.filter (fun e => η e = true) ∨ e ∈ s.filter (fun e => η' e = true) := by
      simpa [indFinset, Finset.mem_union] using he
    rcases hmem with h | h
    · exact ble_iff.1 hη e (Finset.mem_filter.mp h).2
    · exact ble_iff.1 hη' e (Finset.mem_filter.mp h).2
  · rw [Set.mem_iUnion]
    rintro ⟨p, hp⟩
    obtain ⟨hA, hB, hd⟩ := p.property
    have hp' : Ble (indFinset ((p : Finset E × Finset E).1 ∪
        (p : Finset E × Finset E).2)) x := hp
    refine ⟨indFinset (p : Finset E × Finset E).1, indFinset (p : Finset E × Finset E).2,
      ?_, ?_, ?_, hA, hB⟩
    · refine ble_iff.2 fun e he => ble_iff.1 hp' e ?_
      have h : e ∈ (p : Finset E × Finset E).1 := by simpa [indFinset] using he
      simp [indFinset, Finset.mem_union, h]
    · refine ble_iff.2 fun e he => ble_iff.1 hp' e ?_
      have h : e ∈ (p : Finset E × Finset E).2 := by simpa [indFinset] using he
      simp [indFinset, Finset.mem_union, h]
    · intro e he he'
      have hes : e ∈ (p : Finset E × Finset E).1 := by simpa [indFinset] using he
      have het : e ∈ (p : Finset E × Finset E).2 := by simpa [indFinset] using he'
      exact (Finset.disjoint_left.mp hd hes) het

theorem measurableSet_boolSplit_cylIn (s : Finset E) (A B : Set (E → Bool)) :
    MeasurableSet (BoolSplit (cylIn A s) (cylIn B s)) := by
  rw [boolSplit_cylIn_eq']
  exact MeasurableSet.iUnion fun p => measurableSet_ble_const _

/-- **BK for increasing open events** (partition form), by the cylinder approximation from below. -/
theorem bool_bk_open (p : E → unitInterval) (hp : ∀ e, p e < 1)
    {A B : Set (E → Bool)} (hA : BoolUpper A) (hB : BoolUpper B)
    (hAo : IsOpen A) (hBo : IsOpen B) :
    (boolLaw p).real (BoolSplit A B) ≤ (boolLaw p).real A * (boolLaw p).real B := by
  have hlimD : Tendsto (fun n => (boolLaw p).real
      (BoolSplit (cylIn A (edgeExhaustion (E := E) n)) (cylIn B (edgeExhaustion (E := E) n))))
      atTop (𝓝 ((boolLaw p).real (BoolSplit A B))) := by
    have h := tendsto_measure_iUnion_atTop (μ := boolLaw p)
      (s := fun n => BoolSplit (cylIn A (edgeExhaustion (E := E) n))
        (cylIn B (edgeExhaustion (E := E) n)))
      (fun m n hmn => boolSplit_mono (cylIn_mono_finset (edgeExhaustion_mono hmn))
        (cylIn_mono_finset (edgeExhaustion_mono hmn)))
    rw [← boolSplit_cylIn_eq hAo hBo] at h
    exact (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp h
  have hlimA : Tendsto (fun n => (boolLaw p).real (cylIn A (edgeExhaustion (E := E) n)))
      atTop (𝓝 ((boolLaw p).real A)) := by
    have h := tendsto_measure_iUnion_atTop (μ := boolLaw p)
      (s := fun n => cylIn A (edgeExhaustion (E := E) n))
      (fun m n hmn => cylIn_mono_finset (edgeExhaustion_mono hmn))
    rw [iUnion_cylIn hAo] at h
    exact (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp h
  have hlimB : Tendsto (fun n => (boolLaw p).real (cylIn B (edgeExhaustion (E := E) n)))
      atTop (𝓝 ((boolLaw p).real B)) := by
    have h := tendsto_measure_iUnion_atTop (μ := boolLaw p)
      (s := fun n => cylIn B (edgeExhaustion (E := E) n))
      (fun m n hmn => cylIn_mono_finset (edgeExhaustion_mono hmn))
    rw [iUnion_cylIn hBo] at h
    exact (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp h
  refine le_of_tendsto_of_tendsto' hlimD (hlimA.mul hlimB) fun n => ?_
  exact bool_bk_split_witness p hp (cylIn_upper hA _) (cylIn_upper hB _)
    (BoolWitness_cylIn _ _) (BoolWitness_cylIn _ _)

end GeneralCase

end Percolation
end PercLib.CriticalLRP

namespace PercLib.CriticalLRP

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section GeneralMeasurable
variable [Countable E] [Encodable E]
attribute [local instance] Classical.propDecidable

/-- Decreasing events. -/
def BoolLower (A : Set (E → Bool)) : Prop := ∀ x y : E → Bool, Ble x y → y ∈ A → x ∈ A

theorem BoolLower_compl {A : Set (E → Bool)} (hA : BoolUpper A) : BoolLower Aᶜ := by
  rintro x y hxy hy hx
  exact hy (hA x y hxy hx)

theorem continuous_boolInf :
    Continuous (fun p : (E → Bool) × (E → Bool) => fun e => p.1 e && p.2 e) := by
  refine continuous_pi fun e => ?_
  have h1 : Continuous (fun p : (E → Bool) × (E → Bool) => p.1 e) :=
    (continuous_apply e).comp continuous_fst
  have h2 : Continuous (fun p : (E → Bool) × (E → Bool) => p.2 e) :=
    (continuous_apply e).comp continuous_snd
  exact (continuous_of_discreteTopology : Continuous fun q : Bool × Bool => q.1 && q.2).comp
    (h1.prodMk h2)

/-- The decreasing hull of a compact set of configurations is compact. -/
theorem isCompact_lowerHull {K : Set (E → Bool)} (hK : IsCompact K) :
    IsCompact {x : E → Bool | ∃ y ∈ K, Ble x y} := by
  have h : {x : E → Bool | ∃ y ∈ K, Ble x y} =
      (fun p : (E → Bool) × (E → Bool) => fun e => p.1 e && p.2 e) '' (Set.univ ×ˢ K) := by
    ext x
    constructor
    · rintro ⟨y, hy, hxy⟩
      refine ⟨(x, y), ⟨trivial, hy⟩, ?_⟩
      funext e
      by_cases hx : x e = true
      · simp [hx, ble_iff.1 hxy e hx]
      · have hxf : x e = false := by simpa using hx
        simp [hxf]
    · rintro ⟨⟨x, y⟩, ⟨-, hy⟩, rfl⟩
      exact ⟨y, hy, ble_iff.2 fun e he => by
        by_cases hye : y e = true
        · simp [hye]
        · have hyf : y e = false := by simpa using hye
          simp at he
          exact absurd he (by simp [hyf])⟩
  rw [h]
  exact (isCompact_univ.prod hK).image continuous_boolInf

/-- Outer approximation of an increasing measurable event by an *increasing* open event. -/
theorem exists_isOpen_upper_superset (p : E → unitInterval) {A : Set (E → Bool)}
    (hmA : MeasurableSet A) (hA : BoolUpper A) {ε : ℝ} (hε : 0 < ε) :
    ∃ O, A ⊆ O ∧ IsOpen O ∧ BoolUpper O ∧ (boolLaw p).real O ≤ (boolLaw p).real A + ε := by
  obtain ⟨K, hK, hKc, hKlt⟩ := MeasurableSet.exists_isCompact_lt_add (μ := boolLaw p) hmA.compl
    (measure_ne_top _ _) (ENNReal.ofReal_ne_zero_iff.mpr hε)
  have h2 : (boolLaw p).real Aᶜ ≤ (boolLaw p).real K + ε := by
    calc (boolLaw p).real Aᶜ ≤ ((boolLaw p) K + ENNReal.ofReal ε).toReal :=
          (ENNReal.toReal_le_toReal (measure_ne_top _ _) (by simp)).mpr hKlt.le
      _ = (boolLaw p).real K + ε := by
          rw [ENNReal.toReal_add (measure_ne_top _ _) ENNReal.ofReal_ne_top,
            ENNReal.toReal_ofReal hε.le]
          rfl
  have hK'c : IsCompact {x : E → Bool | ∃ y ∈ K, Ble x y} := isCompact_lowerHull hKc
  have hKK' : K ⊆ {x : E → Bool | ∃ y ∈ K, Ble x y} := fun y hy => ⟨y, hy, ble_refl y⟩
  have hK'sub : {x : E → Bool | ∃ y ∈ K, Ble x y} ⊆ Aᶜ := by
    rintro x ⟨y, hy, hxy⟩
    exact BoolLower_compl hA x y hxy (hK hy)
  refine ⟨{x : E → Bool | ∃ y ∈ K, Ble x y}ᶜ, ?_, hK'c.isClosed.isOpen_compl, ?_, ?_⟩
  · intro x hx hx'
    exact hK'sub hx' hx
  · rintro x y hxy hy ⟨z, hz, hyz⟩
    exact hy ⟨z, hz, ble_trans hxy hyz⟩
  · have h1 : (boolLaw p).real K ≤ (boolLaw p).real {x : E → Bool | ∃ y ∈ K, Ble x y} :=
      measureReal_mono hKK'
    have h3 : (boolLaw p).real {x : E → Bool | ∃ y ∈ K, Ble x y}ᶜ =
        1 - (boolLaw p).real {x : E → Bool | ∃ y ∈ K, Ble x y} := by
      rw [measureReal_compl hK'c.isClosed.measurableSet]
      simp
    have h4 : (boolLaw p).real Aᶜ = 1 - (boolLaw p).real A := by
      rw [measureReal_compl hmA]
      simp
    linarith

/-- **The BK inequality in partition form for all increasing measurable events.** -/
theorem bool_bk_measurable (p : E → unitInterval) (hp : ∀ e, p e < 1)
    {A B : Set (E → Bool)} (hA : BoolUpper A) (hB : BoolUpper B)
    (hmA : MeasurableSet A) (hmB : MeasurableSet B) :
    (boolLaw p).real (BoolSplit A B) ≤ (boolLaw p).real A * (boolLaw p).real B := by
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  set ε := min (δ / 3) 1 with hεdef
  have hε : 0 < ε := lt_min (by positivity) (by norm_num)
  have hεδ : 3 * ε ≤ δ := by
    have h1 : ε ≤ δ / 3 := min_le_left _ _
    linarith
  have hε1 : ε ≤ 1 := min_le_right _ _
  obtain ⟨O, hAO, hOo, hOup, hO⟩ := exists_isOpen_upper_superset p hmA hA hε
  obtain ⟨O', hAO', hO'o, hO'up, hO'⟩ := exists_isOpen_upper_superset p hmB hB hε
  have h1 : (boolLaw p).real (BoolSplit A B) ≤ (boolLaw p).real (BoolSplit O O') :=
    measureReal_mono (boolSplit_mono hAO hAO')
  have h2 : (boolLaw p).real (BoolSplit O O') ≤ (boolLaw p).real O * (boolLaw p).real O' :=
    bool_bk_open p hp hOup hO'up hOo hO'o
  have h3 : (boolLaw p).real O * (boolLaw p).real O' ≤
      ((boolLaw p).real A + ε) * ((boolLaw p).real B + ε) :=
    mul_le_mul hO hO' measureReal_nonneg
      (by linarith [measureReal_nonneg (μ := boolLaw p) (s := A)])
  have hAle : (boolLaw p).real A ≤ 1 := by
    have := measureReal_mono (μ := boolLaw p) (Set.subset_univ A)
    simpa using this
  have hBle : (boolLaw p).real B ≤ 1 := by
    have := measureReal_mono (μ := boolLaw p) (Set.subset_univ B)
    simpa using this
  have ha0 : 0 ≤ (boolLaw p).real A := measureReal_nonneg
  have hb0 : 0 ≤ (boolLaw p).real B := measureReal_nonneg
  have hkey : ((boolLaw p).real A + ε) * ((boolLaw p).real B + ε) ≤
      (boolLaw p).real A * (boolLaw p).real B + δ := by
    nlinarith [hεδ, hε1, hε, ha0, hb0, hAle, hBle,
      mul_nonneg hε.le hε.le]
  linarith

end GeneralMeasurable

end Percolation
end PercLib.CriticalLRP

namespace PercLib.CriticalLRP

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section SetEVersion
variable [Countable E]
attribute [local instance] Classical.propDecidable

theorem boolOf_injective : Function.Injective (fun ω : Set E => boolOf ω) := by
  intro ω ω' h
  have := congrArg setOfBool h
  simpa using this

theorem boolEquiv_image_boolOf (A : Set (Set E)) : boolEquiv '' (boolOf '' A) = A := by
  ext ω
  constructor
  · rintro ⟨x, ⟨ω', hω', rfl⟩, hx⟩
    rw [← hx]
    simpa using hω'
  · intro hω
    exact ⟨boolOf ω, ⟨ω, hω, rfl⟩, by simp⟩

theorem boolOf_preimage_image (A : Set (Set E)) : boolOf ⁻¹' (boolOf '' A) = A :=
  Set.preimage_image_eq A boolOf_injective

/-- **The BK inequality with partition witnesses for increasing Borel events**
(Hutchcroft, arXiv:2508.18807, Section I.2.1 and footnote 11), in the form used downstream: any
Borel subset of the disjoint-occurrence event has measure at most the product of the
probabilities.  (`MeasurableSet (boolOf '' A)` is measurability of `A` for the product σ-algebra
of the configuration space.) -/
theorem bk_borel_subset (p : E → unitInterval) (hp : ∀ e, p e < 1)
    {A B : Set (Set E)} (hA : IsUpperSet A) (hB : IsUpperSet B)
    (hmA : MeasurableSet (boolOf '' A)) (hmB : MeasurableSet (boolOf '' B))
    {C : Set (Set E)} (hC : C ⊆ DisjointOccurrencePart A B)
    (hmC : MeasurableSet (boolOf '' C)) :
    (edgeLaw p).real C ≤ (edgeLaw p).real A * (edgeLaw p).real B := by
  have : Encodable E := Encodable.ofCountable E
  have hpreA : boolOf ⁻¹' (boolOf '' A) = A := boolOf_preimage_image A
  have hpreB : boolOf ⁻¹' (boolOf '' B) = B := boolOf_preimage_image B
  have hA'up : BoolUpper (boolOf '' A) := by
    refine isUpperSet_preimage_iff (A := boolOf '' A) |>.1 ?_
    rw [hpreA]; exact hA
  have hB'up : BoolUpper (boolOf '' B) := by
    refine isUpperSet_preimage_iff (A := boolOf '' B) |>.1 ?_
    rw [hpreB]; exact hB
  have hC'sub : boolOf '' C ⊆ BoolSplit (boolOf '' A) (boolOf '' B) := by
    intro x hx
    obtain ⟨ω, hω, rfl⟩ := hx
    have h1 : ω ∈ boolOf ⁻¹' BoolSplit (boolOf '' A) (boolOf '' B) := by
      rw [boolSplit_preimage, hpreA, hpreB]
      exact hC hω
    exact h1
  calc (edgeLaw p).real C = (boolLaw p).real (boolOf '' C) := by
        rw [boolLaw_real p hmC, boolEquiv_image_boolOf C]
    _ ≤ (boolLaw p).real (BoolSplit (boolOf '' A) (boolOf '' B)) := measureReal_mono hC'sub
    _ ≤ (boolLaw p).real (boolOf '' A) * (boolLaw p).real (boolOf '' B) :=
        bool_bk_measurable p hp hA'up hB'up hmA hmB
    _ = (edgeLaw p).real A * (edgeLaw p).real B := by
        rw [boolLaw_real p hmA, boolLaw_real p hmB, boolEquiv_image_boolOf A,
          boolEquiv_image_boolOf B]

/-- **The BK inequality in partition form for increasing Borel events** (when the
disjoint-occurrence event itself is Borel). -/
theorem bk_borel (p : E → unitInterval) (hp : ∀ e, p e < 1)
    {A B : Set (Set E)} (hA : IsUpperSet A) (hB : IsUpperSet B)
    (hmA : MeasurableSet (boolOf '' A)) (hmB : MeasurableSet (boolOf '' B))
    (hmD : MeasurableSet (boolOf '' (DisjointOccurrencePart A B))) :
    (edgeLaw p).real (DisjointOccurrencePart A B) ≤
      (edgeLaw p).real A * (edgeLaw p).real B :=
  bk_borel_subset p hp hA hB hmA hmB (Set.Subset.refl _) hmD

end SetEVersion

end Percolation
end PercLib.CriticalLRP

namespace PercLib.CriticalLRP

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section Consistency
variable [Countable E]
attribute [local instance] Classical.propDecidable

/-- **Consistency with the finitely witnessed form**: for increasing finitely witnessed events,
partition witnesses and finite witnesses give the same disjoint-occurrence event, so the general BK
inequality specialises to `bkEdge`. -/
theorem disjointOccurrencePart_eq_disjointOccurrence {A B : Set (Set E)} (hA : IsUpperSet A)
    (hB : IsUpperSet B) (hfA : FiniteWitness A) (hfB : FiniteWitness B) :
    DisjointOccurrencePart A B = DisjointOccurrence A B := by
  have : Encodable E := Encodable.ofCountable E
  have hpreA : boolOf ⁻¹' (boolOf '' A) = A := boolOf_preimage_image A
  have hpreB : boolOf ⁻¹' (boolOf '' B) = B := boolOf_preimage_image B
  have hA'up : BoolUpper (boolOf '' A) := by
    refine isUpperSet_preimage_iff (A := boolOf '' A) |>.1 ?_
    rw [hpreA]; exact hA
  have hB'up : BoolUpper (boolOf '' B) := by
    refine isUpperSet_preimage_iff (A := boolOf '' B) |>.1 ?_
    rw [hpreB]; exact hB
  have hfA' : BoolWitness (boolOf '' A) := by
    refine finiteWitness_preimage_iff (A := boolOf '' A) |>.1 ?_
    rw [hpreA]; exact hfA
  have hfB' : BoolWitness (boolOf '' B) := by
    refine finiteWitness_preimage_iff (A := boolOf '' B) |>.1 ?_
    rw [hpreB]; exact hfB
  rw [show DisjointOccurrencePart A B
      = boolOf ⁻¹' BoolSplit (boolOf '' A) (boolOf '' B) from by
    rw [boolSplit_preimage, hpreA, hpreB],
    show DisjointOccurrence A B
      = boolOf ⁻¹' BoolDisjoint (boolOf '' A) (boolOf '' B) from by
    rw [boolDisjoint_preimage, hpreA, hpreB],
    boolSplit_eq_boolDisjoint hA'up hB'up hfA' hfB']

/-- The partition-form BK inequality for increasing finitely witnessed events, in the form
`P (A □ B) ≤ P A * P B` on the original configuration space. -/
theorem bk_part_finiteWitness (p : E → unitInterval) (hp : ∀ e, p e < 1)
    {A B : Set (Set E)} (hA : IsUpperSet A) (hB : IsUpperSet B)
    (hfA : FiniteWitness A) (hfB : FiniteWitness B) :
    (edgeLaw p).real (DisjointOccurrencePart A B) ≤
      (edgeLaw p).real A * (edgeLaw p).real B := by
  rw [disjointOccurrencePart_eq_disjointOccurrence hA hB hfA hfB]
  exact bkEdge p hp A B hA hB hfA hfB

end Consistency

end Percolation
end PercLib.CriticalLRP

namespace PercLib.CriticalLRP

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section Usability
variable [Countable E]

/-- Events pulled back from the `Bool`-coding satisfy the measurability hypothesis of
`bk_borel_subset` as soon as the `Bool`-side event is measurable. -/
theorem measurableSet_boolOf_image_preimage {S : Set (E → Bool)} (hS : MeasurableSet S) :
    MeasurableSet (boolOf '' (boolOf ⁻¹' S)) := by
  rw [Set.image_preimage_eq _ (fun x => ⟨setOfBool x, by simp⟩)]
  exact hS

theorem boolOf_preimage_upper_iff {S : Set (E → Bool)} :
    IsUpperSet (boolOf ⁻¹' S) ↔ BoolUpper S :=
  isUpperSet_preimage_iff

end Usability

end Percolation
end PercLib.CriticalLRP

namespace PercLib.CriticalLRP

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section TwoClusterGeneral
attribute [local instance] Classical.propDecidable

/-- Removing the edges internal to the cluster of `x` does not change the cluster of `y`, provided
`x` and `y` are not connected. -/
theorem cluster_sdiff_internalEdges (G : BondGraph V E) (ω : Set E) {x y : V}
    (hxy : ¬ Conn G ω x y) :
    cluster G (ω \ internalEdges G ω x) y = cluster G ω y := by
  have hmono : cluster G (ω \ internalEdges G ω x) y ⊆ cluster G ω y :=
    cluster_mono Set.sdiff_subset y
  ext z
  refine ⟨fun hzz => hmono hzz, fun hz => ?_⟩
  have hmain : ∀ {z : V}, Conn G ω y z → Conn G (ω \ internalEdges G ω x) y z := by
    intro z hz
    induction hz with
    | refl => exact conn_refl G _ y
    | @tail a b hprev hstep ih =>
      obtain ⟨e, he, hGe⟩ := hstep
      have hnotmem : e ∉ internalEdges G ω x := by
        intro hee
        have hax : a ∈ cluster G ω x :=
          hee.2 a (hGe ▸ Sym2.mem_mk_left a b)
        exact hxy (conn_trans G ω hax (conn_symm G ω hprev))
      exact ih.tail ⟨e, ⟨he, hnotmem⟩, hGe⟩
  exact hmain hz

/-- **Cluster locality: the two-cluster indicator event is contained in the partition disjoint
occurrence** of the two cluster-determined increasing events, with no finite-witness hypothesis. -/
theorem twoCluster_subset_disjointOccurrencePart (G : BondGraph V E) (x y : V)
    {A B : Set (Set E)} (hA : IsUpperSet A) (hB : IsUpperSet B)
    (hdA : ClusterDeterminedAt G x A) (hdB : ClusterDeterminedAt G y B) :
    A ∩ B ∩ {ω | ¬ Conn G ω x y} ⊆ DisjointOccurrencePart A B := by
  rintro ω ⟨⟨hωA, hωB⟩, hxy⟩
  have hηA : internalEdges G ω x ∈ A :=
    (hdA ω _ (cluster_internalEdges G ω x).symm).mp hωA
  have hη'B : ω \ internalEdges G ω x ∈ B :=
    (hdB ω _ (cluster_sdiff_internalEdges G ω hxy).symm).mp hωB
  exact ⟨internalEdges G ω x, ω \ internalEdges G ω x, fun e he => he.1, Set.sdiff_subset,
    Set.disjoint_left.mpr fun e he he' => he'.2 he, hηA, hη'B⟩

/-- **Lemma I.2.1(i) in indicator form, for *all* increasing cluster-determined events** (no
finite-witness hypothesis): `P(A ∩ B ∩ {x ↮ y}) ≤ P(A) P(B)`. -/
theorem twoCluster_bk_general [Countable E] (G : BondGraph V E) (p : E → unitInterval)
    (hp : ∀ e, p e < 1) (x y : V)
    {A B : Set (Set E)} (hA : IsUpperSet A) (hB : IsUpperSet B)
    (hdA : ClusterDeterminedAt G x A) (hdB : ClusterDeterminedAt G y B)
    (hmA : MeasurableSet (boolOf '' A)) (hmB : MeasurableSet (boolOf '' B))
    (hmC : MeasurableSet (boolOf '' (A ∩ B ∩ {ω | ¬ Conn G ω x y}))) :
    (edgeLaw p).real (A ∩ B ∩ {ω | ¬ Conn G ω x y}) ≤
      (edgeLaw p).real A * (edgeLaw p).real B :=
  bk_borel_subset p hp hA hB hmA hmB
    (twoCluster_subset_disjointOccurrencePart G x y hA hB hdA hdB) hmC

/-- **Lemma I.2.1(i) in indicator form**, ENNReal version (the form in which
`BK/BorelReduction.twoCluster_functional_of_borelBK` consumes it). -/
theorem twoCluster_bk_general_ennreal [Countable E] (G : BondGraph V E) (p : E → unitInterval)
    (hp : ∀ e, p e < 1) (x y : V)
    {A B : Set (Set E)} (hA : IsUpperSet A) (hB : IsUpperSet B)
    (hdA : ClusterDeterminedAt G x A) (hdB : ClusterDeterminedAt G y B)
    (hmA : MeasurableSet (boolOf '' A)) (hmB : MeasurableSet (boolOf '' B))
    (hmC : MeasurableSet (boolOf '' (A ∩ B ∩ {ω | ¬ Conn G ω x y}))) :
    (edgeLaw p) (A ∩ B ∩ {ω | ¬ Conn G ω x y}) ≤ (edgeLaw p) A * (edgeLaw p) B := by
  refine (ENNReal.toReal_le_toReal (measure_ne_top _ _)
    (ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _))).mp ?_
  rw [ENNReal.toReal_mul]
  exact twoCluster_bk_general G p hp x y hA hB hdA hdB hmA hmB hmC

end TwoClusterGeneral

end Percolation
end PercLib.CriticalLRP
