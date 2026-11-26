/- Independently rebuilt from `smwx3hvzx`, member `m1` finding f1.
Production integration revision: `c491c66109f24f38fa27cbccbcc52d11a14a8c33`.

The source's hub-indexed diagram at `p = 3`, `k = 1`: identification with production's
`StarPairEvent`, the collapse to `jointP`, and the BK evaluation `jointP * τ * τ`.

Source: Lemma I.4.16 of T. Hutchcroft, *Critical long-range percolation I: High effective
dimension*, arXiv:2508.18807v1, p. 44: at the branch point `w` the source uses the events
`{0 <-> x, w}`, `{w <-> y}`, `{w <-> z}`, pairwise in disjoint occurrence, and after BK the
three-point function `P(0 <-> x, w)` together with two two-point factors `P(w <-> y)`,
`P(w <-> z)`.

## Content

* `hubDiagJoint_eq_starPairEvent` -- the hub-indexed joint event `hubDiagJoint o x y z w` (one
  witness set for the joint pair `o, x` at `w`, one for `w <-> y`, one for `w <-> z`, pairwise
  edge-disjoint) is *literally* production's `StarPairEvent o x y z w`.  So the walk-based object
  used by the existing cubic assembly and the canonical hub layer's slot assignment are the same
  event; the identification keeps the pair slot joint.
* `edgeMeasure_hubDiagJoint_le_jointP` -- dropping the disjointness requirement, the whole diagram
  is contained in the single three-point event `o <-> w` and `x <-> w`; hence its measure is at
  most `jointP π o x w`.  This is the comparison with `jointP π a b c` that the source's notation
  `P(0 <-> x, w)` means, at the *same* hub `w` as centre.
* `edgeMeasure_hubDiagJoint_le_hubSplitValue` -- the threefold BK: the diagram costs
  `jointP π o x w * (τ w y * τ w z)`.  One factor is a joint (three-point) quantity, two are
  single two-point factors; the first factor is *not* `τ (0,w) * τ (x,w)`.
-/
module

public import PercLib.CriticalLRP.TreeExpansion.AtlasRealization.Canonical.Hub.Evaluation.Bridge

/-!
# The hub-indexed source diagram
-/

@[expose] public section

open MeasureTheory Measure
open scoped ENNReal BigOperators

open PercLib.CriticalLRP (Config Connects connSet edgeMeasure)
open PercLib.CriticalLRP.Percolation (DisjFam bk_disjFam)
open PercLib.CriticalLRP.TreeExpansion (StarPairEvent)
open PercLib.CriticalLRP.TreeExpansion.FivePoint (jointP)

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace HubJointEval

variable {V : Type*}

/-! ### Basic facts about the hub pair event -/

/-- The hub pair event is increasing. -/
theorem isUpperSet_hubPairJoint [Countable V] (a b c : V) :
    IsUpperSet (hubPairJoint a b c) :=
  fun _ _ h hin =>
    ⟨PercLib.CriticalLRP.isUpper_connSet a c h hin.1,
      PercLib.CriticalLRP.isUpper_connSet b c h hin.2⟩

/-- The hub pair event is finitely witnessed: the union of the two witnesses witnesses both
connections. -/
theorem finiteWitness_hubPairJoint [Countable V] (a b c : V) :
    PercLib.CriticalLRP.Percolation.FiniteWitness (hubPairJoint a b c) := by
  classical
  intro ω hω
  obtain ⟨s, hs, hsa⟩ := PercLib.CriticalLRP.finiteWitness_connSet a c ω hω.1
  obtain ⟨t, ht, htb⟩ := PercLib.CriticalLRP.finiteWitness_connSet b c ω hω.2
  exact ⟨s ∪ t, by simpa only [Finset.coe_union] using Set.union_subset hs ht,
    ⟨PercLib.CriticalLRP.isUpper_connSet a c (by simp) hsa,
      PercLib.CriticalLRP.isUpper_connSet b c (by simp) htb⟩⟩

/-- `edgeMeasure π (connSet x y) = τ x y`. -/
theorem edgeMeasure_connSet_eq_tau [Countable V] (π : Sym2 V → unitInterval) (x y : V) :
    edgeMeasure π (connSet x y) = PercLib.Percolation.Bond.tau π x y := by
  rw [PercLib.Percolation.Bond.tau, connSet_eq_conn]

/-- A product over `Fin 3` of a three-entry vector, in the shape produced by
`Fin.prod_univ_three`. -/
theorem prod_fin3_vec (F : Set (Config V) → ℝ≥0∞) (a b c : Set (Config V)) :
    (∏ i : Fin 3, F (![a, b, c] i)) = F a * (F b * F c) := by
  rw [Fin.prod_univ_three]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons]
  rw [mul_assoc]

/-! ### Identification with production's `StarPairEvent` -/

/-- **The hub-indexed source diagram is production's `StarPairEvent`.**  Both are the event that
one finite open witness set certifies the *joint* pair `o, x` at `w` and two further finite open
witness sets certify `w <-> y` and `w <-> z`, the three being pairwise edge-disjoint.

The pair slot is not split, so this is a genuine three-slot object: the identification is with the
`o <-> x, w` slot of the source, not with a product of two two-point events. -/
theorem hubDiagJoint_eq_starPairEvent [Countable V] (o x y z w : V) :
    hubDiagJoint o x y z w = StarPairEvent o x y z w := by
  ext ω
  constructor
  · rintro ⟨W, hsub, hmem, hdisj⟩
    have h0 := hmem 0
    have h1 := hmem 1
    have h2 := hmem 2
    simp only [Matrix.cons_val_zero, hubPairJoint, connSet_eq_conn] at h0
    simp only [Matrix.cons_val_one, connSet_eq_conn] at h1
    simp only [Matrix.cons_val_two, Matrix.tail_cons, connSet_eq_conn] at h2
    exact ⟨(W 0 : Set (Sym2 V)), (W 1 : Set (Sym2 V)), (W 2 : Set (Sym2 V)),
      (W 0).finite_toSet, (W 1).finite_toSet, (W 2).finite_toSet,
      hsub 0, hsub 1, hsub 2, h0, h1, h2,
      Finset.disjoint_coe.mpr (hdisj 0 1 (by decide)),
      Finset.disjoint_coe.mpr (hdisj 0 2 (by decide)),
      Finset.disjoint_coe.mpr (hdisj 1 2 (by decide))⟩
  · rintro ⟨U, W₁, W₂, hfU, hf1, hf2, hU, h1, h2, hmU, hm1, hm2, hdU1, hdU2, hd12⟩
    classical
    have hU' : ((hfU.toFinset : Finset (Sym2 V)) : Set (Sym2 V)) = U := hfU.coe_toFinset
    have h1' : ((hf1.toFinset : Finset (Sym2 V)) : Set (Sym2 V)) = W₁ := hf1.coe_toFinset
    have h2' : ((hf2.toFinset : Finset (Sym2 V)) : Set (Sym2 V)) = W₂ := hf2.coe_toFinset
    have hs0 : ((hfU.toFinset : Finset (Sym2 V)) : Set (Sym2 V)) ⊆ ω := by rw [hU']; exact hU
    have hs1 : ((hf1.toFinset : Finset (Sym2 V)) : Set (Sym2 V)) ⊆ ω := by rw [h1']; exact h1
    have hs2 : ((hf2.toFinset : Finset (Sym2 V)) : Set (Sym2 V)) ⊆ ω := by rw [h2']; exact h2
    have hm0 : ((hfU.toFinset : Finset (Sym2 V)) : Set (Sym2 V)) ∈ hubPairJoint o x w := by
      rw [hU', hubPairJoint, connSet_eq_conn]
      exact hmU
    have hm1 : ((hf1.toFinset : Finset (Sym2 V)) : Set (Sym2 V)) ∈ connSet w y := by
      rw [h1', connSet_eq_conn]
      exact hm1
    have hm2 : ((hf2.toFinset : Finset (Sym2 V)) : Set (Sym2 V)) ∈ connSet w z := by
      rw [h2', connSet_eq_conn]
      exact hm2
    have d01 : Disjoint hfU.toFinset hf1.toFinset := by
      rw [← Finset.disjoint_coe, hU', h1']; exact hdU1
    have d02 : Disjoint hfU.toFinset hf2.toFinset := by
      rw [← Finset.disjoint_coe, hU', h2']; exact hdU2
    have d12 : Disjoint hf1.toFinset hf2.toFinset := by
      rw [← Finset.disjoint_coe, h1', h2']; exact hd12
    refine ⟨![hfU.toFinset, hf1.toFinset, hf2.toFinset], ?_, ?_, ?_⟩
    · intro i
      fin_cases i
      exacts [hs0, hs1, hs2]
    · intro i
      fin_cases i
      exacts [hm0, hm1, hm2]
    · intro i j hij
      fin_cases i
      · fin_cases j
        · exact absurd rfl hij
        · exact d01
        · exact d02
      · fin_cases j
        · exact d01.symm
        · exact absurd rfl hij
        · exact d12
      · fin_cases j
        · exact d02.symm
        · exact d12.symm
        · exact absurd rfl hij

/-! ### The collapse to the three-point function `jointP` -/

/-- **The diagram is contained in the three-point event at its hub.**  If the hub `w` is joined to
both `o` and `x` (with pairwise disjoint witnesses for the leaf arms too, which is extra
information), then in particular `w` is joined to `o` and to `x`.  The resulting event is
`hubPairJoint o x w`, whose measure is `jointP π o x w`.

So the selected hub joint event is *at most* the source's three-point function, with the hub as
its centre and the pair `(o, x)` as its two points.  The converse fails in general: the
three-point event puts no disjointness requirement on the paths, so it can hold with no
edge-disjoint witness at all (documented in `HubJointEval/Notes.md`; the obstruction is
`HubJointEval/Obstruction.lean`). -/
theorem hubDiagJoint_subset_pair [Countable V] (o x y z w : V) :
    hubDiagJoint o x y z w ⊆ hubPairJoint o x w :=
  disjFam_subset_of_isUpperSet
    (A := fun i : Fin 3 => ![hubPairJoint o x w, connSet w y, connSet w z] i)
    (fun i => by
      fin_cases i
      · exact isUpperSet_hubPairJoint o x w
      · exact PercLib.CriticalLRP.isUpper_connSet w y
      · exact PercLib.CriticalLRP.isUpper_connSet w z) 0

/-- **The hub diagram costs at most the three-point function at the hub.** -/
theorem edgeMeasure_hubDiagJoint_le_jointP [Countable V] (π : Sym2 V → unitInterval)
    (o x y z w : V) :
    edgeMeasure π (hubDiagJoint o x y z w) ≤ jointP π o x w := by
  rw [jointP_eq_edgeMeasure_hubPairJoint]
  exact measure_mono (hubDiagJoint_subset_pair o x y z w)

/-! ### The threefold BK evaluation `jointP * τ * τ` -/

/-- **The per-hub threefold BK.**  The joint three-arm diagram at the hub `w` costs the
three-point function `jointP π o x w` and the two two-point factors `τ w y`, `τ w z`.

The first factor is joint: it is *not* replaced by `τ o w * τ x w`, and the two remaining factors
are single (not joint) two-point functions, exactly as in the source's
`P(0 <-> x, w) P(w <-> y) P(w <-> z)`. -/
theorem edgeMeasure_hubDiagJoint_le_hubSplitValue [Countable V]
    (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1) (o x y z w : V) :
    edgeMeasure π (hubDiagJoint o x y z w) ≤ hubSplitValue π o x y z w := by
  have h := bk_disjFam π hπ
    (A := fun i : Fin 3 => ![hubPairJoint o x w, connSet w y, connSet w z] i)
    (fun i => by
      fin_cases i
      · exact isUpperSet_hubPairJoint o x w
      · exact PercLib.CriticalLRP.isUpper_connSet w y
      · exact PercLib.CriticalLRP.isUpper_connSet w z)
    (fun i => by
      fin_cases i
      · exact finiteWitness_hubPairJoint o x w
      · exact PercLib.CriticalLRP.finiteWitness_connSet w y
      · exact PercLib.CriticalLRP.finiteWitness_connSet w z)
  refine h.trans (le_of_eq ?_)
  rw [prod_fin3_vec]
  rw [← jointP_eq_edgeMeasure_hubPairJoint, edgeMeasure_connSet_eq_tau,
    edgeMeasure_connSet_eq_tau]
  rfl

end HubJointEval
