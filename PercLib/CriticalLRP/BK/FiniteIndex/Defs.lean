/-
Independently built definitions for the finite-index canonical BK bridge.
Swarm smwwtd5t5, member m2 (direction B).  Production is read only and is *not* modified:
the file base is production HEAD 4c53bb5a8e76a4358a426adf71169b916b90f51f
(`.scratch/critical-lrp-orchestration`), whose relevant modules are
`PercLib.CriticalLRP.BK.CanonicalBridge` (canonical law `edgeMeasure`, `connSet`,
`Percolation.DisjointOccurrenceList`, `edgeMeasure_bk_list`) and
`PercLib.CriticalLRP.TreeExpansion.AtlasRealization.{Defs,Realize,Cover}` (the atlas diagrams).
-/

/-
# Finite-indexed disjoint occurrence on a configuration space

Production's iterated BK (`Percolation.bk_list`) is stated for an *iterated binary* disjoint
occurrence over a `List (Set (Set E))`.  The atlas of Lemma I.4.16 needs the index to be the
finite set of atlas edges of one shape, carrying *pairwise* disjoint witness sets, so the object
we need is the family form below.  It is the edge-set analogue of
`PercLib.CriticalLRP.TreeExpansion.Real.DisjOcc` (which is stated on `Set (Finset E)`, i.e. for
a finite edge type `E`), lifted to `Set (Set E)` so that it applies to the canonical countable
model `Config V = Set (Sym2 V)` of §I.1.2, where `Sym2 V` is *not* finite.

`DisjFam A` says: there is a family of finite sets of open edges, one for each index `i`, each
already satisfying `A i`, and pairwise disjoint.  Every index gets its own edges, so this is the
event that a whole edge-disjoint atlas exists.

## Exact relation to `Percolation.DisjointOccurrenceList`

`DisjointOccurrenceList [A 0, A 1, …, A (n-1)]` is the *nested* event
`A 0 ∘ (A 1 ∘ (… ∘ A (n-1)))`: at each level one witness has to be disjoint from the *union* of
the witnesses of the levels below it.  The two formulations are not merely related but the same
event:

  `DisjFam A = DisjointOccurrenceList (List.ofFn A)`  (`FiniteBK.lean`, both inclusions)

The nontrivial direction is `DisjointOccurrenceList … ⊆ DisjFam A`: at level `i` the witness `sᵢ`
is disjoint from `tᵢ`, and every deeper witness lies inside `tᵢ`, so `sᵢ ⊥ sⱼ` for `i ≠ j` and the
nesting already selects a pairwise-disjoint family.  Hence iterated BK (`bk_list`) applies to
`DisjFam` with no loss, and the `List` form is not a weaker surrogate.

## Degenerate edges

The empty finite set is allowed as a witness, so an index whose event holds with no open edges
(e.g. `connSet u u`, which is `univ`) is witnessed by `∅`, disjoint from everything.  Such an
index therefore consumes no edge and contributes the factor `P(u ↔ u) = 1`; see
`disjFam_option_univ` below and `edgeMeasure_connSet_self`, `disjFam_connSet_self_option` in
`Canonical.lean`.
-/

module

public import PercLib.CriticalLRP.BK.CanonicalBridge

/-!
# Finite-indexed disjoint occurrence
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace PercLib.CriticalLRP

namespace Percolation

variable {E : Type*} {ι : Type*} {κ : Type*}

/-- **Finite-indexed disjoint occurrence.**  `ω` contains pairwise-disjoint finite witness sets
`W i ⊆ ω`, one for each index `i`, with `W i` itself satisfying `A i`.  For the canonical model
(`E = Sym2 V`) this is the event that a finite family of connection events is realised by
edge-disjoint open paths in one configuration; the index type is the finite set of atlas edges,
while `V` stays countable. -/
def DisjFam (A : ι → Set (Set E)) : Set (Set E) :=
  {ω | ∃ W : ι → Finset E, (∀ i, (W i : Set E) ⊆ ω) ∧ (∀ i, (W i : Set E) ∈ A i) ∧
    ∀ i j, i ≠ j → Disjoint (W i) (W j)}

/-- `DisjFam` is monotone in its events. -/
theorem disjFam_mono {A B : ι → Set (Set E)} (h : ∀ i, A i ⊆ B i) : DisjFam A ⊆ DisjFam B := by
  rintro ω ⟨W, hsub, hmem, hdisj⟩
  exact ⟨W, hsub, fun i => h i (hmem i), hdisj⟩

/-- `DisjFam` is an increasing event, since a witness set that is open in `ω` is open in every
larger configuration. -/
theorem disjFam_upper (A : ι → Set (Set E)) : IsUpperSet (DisjFam A) := by
  rintro ω η hωη ⟨W, hsub, hmem, hdisj⟩
  exact ⟨W, fun i => (hsub i).trans hωη, hmem, hdisj⟩

/-- `DisjFam` is finitely witnessed: the union of the witnesses is a witness. -/
theorem disjFam_finiteWitness [DecidableEq E] [Fintype ι] (A : ι → Set (Set E)) :
    FiniteWitness (DisjFam A) := by
  rintro ω ⟨W, hsub, hmem, hdisj⟩
  refine ⟨Finset.univ.biUnion W, ?_, W, ?_, hmem, hdisj⟩
  · intro e he
    obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.mp he
    exact hsub i hi
  · intro i e he
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, he⟩

/-- Disjoint occurrence only depends on the events, up to a relabelling of the index type.  This
is the family analogue of production's `Percolation.disjOcc_congr` and is what carries the
canonical atlas edge type `AEdge t` to `Fin (2 * p - 1)`. -/
theorem disjFam_congr (e : ι ≃ κ) (A : ι → Set (Set E)) (B : κ → Set (Set E))
    (hAB : ∀ i, A i = B (e i)) : DisjFam A = DisjFam B := by
  ext ω
  constructor
  · rintro ⟨W, hsub, hmem, hdisj⟩
    refine ⟨fun k => W (e.symm k), fun k => hsub _, ?_, fun k k' hkk' => ?_⟩
    · intro k
      have h := hmem (e.symm k)
      rw [hAB (e.symm k)] at h
      simpa using h
    · exact hdisj _ _ (fun h => hkk' (e.symm.injective h))
  · rintro ⟨W, hsub, hmem, hdisj⟩
    refine ⟨fun i => W (e i), fun i => hsub _, ?_, fun i i' hii' => ?_⟩
    · intro i
      rw [hAB i]
      exact hmem (e i)
    · exact hdisj _ _ (fun h => hii' (e.injective h))

/-- An empty index set makes the event certain: the empty atlas needs no open edge at all.  This
is the honest handling of the degenerate case of zero labelled leaves (`p = 0`), where the empty
product of connection probabilities is `1`. -/
theorem disjFam_isEmpty [IsEmpty ι] (A : ι → Set (Set E)) : DisjFam A = Set.univ := by
  ext ω
  refine ⟨fun _ => Set.mem_univ ω, fun _ => ⟨fun i => isEmptyElim i, ?_, ?_, ?_⟩⟩
  · intro i; exact isEmptyElim i
  · intro i; exact isEmptyElim i
  · intro i; exact isEmptyElim i

/-- **A degenerate index costs nothing.**  Adding a *certain* event to a finite family does not
change the disjoint-occurrence event: it is witnessed by the empty set of edges, which is
disjoint from every other witness.  Applied to `A i = connSet (u i) (u i) = univ` this is the
statement that an atlas edge whose two ends coincide contributes the factor `P(u ↔ u) = 1` and
no open edge. -/
theorem disjFam_option_univ (A : ι → Set (Set E)) :
    DisjFam (fun o : Option ι => match o with | none => Set.univ | some i => A i) = DisjFam A := by
  ext ω
  constructor
  · rintro ⟨W, hsub, hmem, hdisj⟩
    refine ⟨fun i => W (some i), fun i => hsub _, fun i => hmem (some i), fun i j hij => ?_⟩
    exact hdisj _ _ (fun h => hij (Option.some_injective ι h))
  · rintro ⟨W, hsub, hmem, hdisj⟩
    refine ⟨fun o => match o with | none => ∅ | some i => W i, ?_, ?_, ?_⟩
    · rintro (_ | i)
      · simp
      · simpa using hsub i
    · rintro (_ | i)
      · exact Set.mem_univ _
      · simpa using hmem i
    · rintro (_ | i) (_ | j) hij
      · exact absurd rfl hij
      · exact Finset.disjoint_empty_left _
      · exact Finset.disjoint_empty_right _
      · exact hdisj i j (fun h => hij (by rw [h]))

end Percolation

end PercLib.CriticalLRP
