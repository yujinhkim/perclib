/- Independently rebuilt and integrated from accepted UltraMath solution `smwwzy3xm` m1.
Production integration revision: `ca165b334f2970daf35034762d79fa32b83639d2`.

UltraMath swarm `smwwzy3xm`, member `m1`.  Lean 4.35.0.
Production read-only reference
`/workspace/nucleus/work/projects/p-80652143d93744198f28e95ad14b4477/repo/.scratch/`
`critical-lrp-orchestration`, committed revision
`4478d0f5a412be93a92b607d6e30a20cbd89bdb6` plus the focused-built uncommitted
`Correlation/I417/MarkedJoint/Transversal/{Transversal,Main,Depth}.lean` sources.
Nothing outside `.ultramath/smwwzy3xm/m1/` is written; there is no commit and no package build.
-/

module

public import PercLib.CriticalLRP.Correlation.I417.MarkedJoint.Transversal.PerDepth.Defs

/-!
# The per-depth marked shape identity `markedCount p ℓ = 2 ^ p * nonplaneMarkedCount p ℓ`

Source: T. Hutchcroft, *Critical long-range percolation I: High effective dimension*,
arXiv:2508.18807v1, Lemma I.4.17, marked (base) side.

Production stores the marked coefficient of the depth-`ℓ` diagram twice:

* `I417Marked.markedCount p ℓ`, the number of fully labelled **plane** trees over
  `Label p = Fin p ⊕ PUnit` with the marking label `markLabel p = Sum.inr ⟨⟩` at depth `ℓ`;
* `I417MarkedTransversal.nonplaneMarkedCount p ℓ`, the number of child-swap **orbits** of fully
  labelled `Fin (p+1)`-labelled trees with the marking label `Fin.last p` at depth `ℓ`.

Both families have `p+1` labels and the label equivalence `finLabelEquiv p` sends the last index
to the mark, so the plane family is the orbit family with every orbit inflated by its `2 ^ p`
plane presentations.  This file proves that statement *depth by depth*, which the existing total
identities do not give.

## The four steps

1. `markedCount_eq_card_markedFilterLabel`: the production count is the cardinality of the
   depth-filtered `LTon (Label p) univ` family.  This is `markedCount`'s definition read through
   the injective image `A ↦ ⟨A.1, markPos (markLabel p) A.1⟩` and the reindexing
   `I417Marked.sum_markedShapes`.
2. `card_markedFilterLabel_eq_markedFilterFin`: `finLabelEquiv p` transports the family to the
   `Fin (p+1)` labelling with the mark on `Fin.last p`, with the marked leaf position and its
   depth preserved (`markPos_mapLabel`, `depth_markPos_mapLabel`).
3. `card_markedFilterFin_eq_planeMarkedFiber`: `LTon` and `RTree.LT` are the same family on
   `Fin (p+1)`; the depth filter is unchanged.
4. `card_planeMarkedFiber_eq_two_pow_mul_nonplaneMarkedCount`: the orbit decomposition.  Child
   swaps preserve the marked depth (`depth_markPos_eq_of_mem_swapFiber`), so the depth filter
   cuts the child-swap partition into filtered pieces, each with exactly `2 ^ p` plane
   representatives (`RTree.swapOrbits_card`), and the filtered transversal has one element per
   filtered orbit (`RTree.transversal_spec`).  The count is taken on the transversal itself
   through the native-`ℕ` orbit sum `sum_LT_eq_pow_mul_sum_transversal_nat`; no finite family is
   divided by `2 ^ p`.

Nothing here is probabilistic, and `p = 0` (a single mark and no arms) is included: the identity
then reads `1 = 1`.
-/

set_option autoImplicit false

@[expose] public section

namespace PercLib.CriticalLRP.I417MarkedPerDepth

open PercLib.CriticalLRP.TreeExpansion
open PercLib.CriticalLRP.I417Marked (Label markLabel markPos markPos_spec markPos_unique
  markedCount sum_markedShapes)
open PercLib.CriticalLRP.I417MarkedRelabel (finLabelEquiv finLabelEquiv_last ltOnMapLabel
  ltOnMapLabelEquiv ltOnMapLabelEquiv_apply ltOnMapLabel_coe)

universe u

variable {α : Type u} {β : Type u}

/-! ### The leaf-position transport commutes with labels and with depth -/

/-- **The transported leaf position carries the transported label.** -/
theorem leafOfPos_leafPosMapLabel (f : α → β) :
    ∀ (t : RTree α) (q : RTree.LeafPos t),
      RTree.leafOfPos (t.mapLabel f) (leafPosMapLabel f t q) = f (RTree.leafOfPos t q)
  | RTree.leaf _, _ => rfl
  | RTree.node l r, q => by
      rcases q with q | q
      · exact leafOfPos_leafPosMapLabel f l q
      · exact leafOfPos_leafPosMapLabel f r q

/-- **The transported leaf position has the same depth.**  `RTree.mapLabel` changes labels only,
so the path from the root to a transported leaf is the original path. -/
theorem depth_leafPosMapLabel (f : α → β) :
    ∀ (t : RTree α) (q : RTree.LeafPos t),
      RTree.depth (t.mapLabel f) (leafPosMapLabel f t q) = RTree.depth t q
  | RTree.leaf _, _ => rfl
  | RTree.node l r, q => by
      rcases q with q | q
      · exact congrArg (· + 1) (depth_leafPosMapLabel f l q)
      · exact congrArg (· + 1) (depth_leafPosMapLabel f r q)

/-! ### The marked leaf position and the marked depth along a label equivalence -/

/-- **The marked leaf position is transported by a label equivalence**: the leaf carrying `m` in
`t.mapLabel e` is the transport of the leaf carrying `e.symm m` in `t`.  Uniqueness of the leaf
carrying a label on an injectively labelled tree (`I417Marked.markPos_unique`) is what makes the
classically chosen position `markPos` equivariant. -/
theorem markPos_mapLabel [Fintype β] [DecidableEq α] [DecidableEq β] (e : α ≃ β)
    {t : RTree α} (hmap : RTree.FullyLabelled (t.mapLabel (⇑e))) (m : β) :
    markPos m (t.mapLabel (⇑e)) = leafPosMapLabel (⇑e) t (markPos (e.symm m) t) := by
  have hnd : t.leaves.Nodup := by
    have h := hmap.1
    rw [RTree.leaves_mapLabel] at h
    exact h.of_map
  have hm' : e.symm m ∈ t.leaves := by
    have hm : m ∈ (t.mapLabel (⇑e)).leaves := RTree.mem_leaves_of_fullyLabelled hmap m
    rw [RTree.leaves_mapLabel, List.mem_map] at hm
    obtain ⟨a, ha, rfl⟩ := hm
    rwa [Equiv.symm_apply_apply]
  have hq : RTree.leafOfPos (t.mapLabel (⇑e)) (markPos m (t.mapLabel (⇑e))) = m :=
    markPos_spec (RTree.mem_leaves_of_fullyLabelled hmap m)
  have key : e (RTree.leafOfPos t
      ((leafPosMapLabel (⇑e) t).symm (markPos m (t.mapLabel (⇑e))))) = m := by
    rw [← leafOfPos_leafPosMapLabel (⇑e) t
      ((leafPosMapLabel (⇑e) t).symm (markPos m (t.mapLabel (⇑e)))),
      Equiv.apply_symm_apply, hq]
  have h1 : RTree.leafOfPos t
      ((leafPosMapLabel (⇑e) t).symm (markPos m (t.mapLabel (⇑e)))) = e.symm m := by
    refine e.injective ?_
    rw [key, e.apply_symm_apply]
  have h2 : (leafPosMapLabel (⇑e) t).symm (markPos m (t.mapLabel (⇑e)))
      = markPos (e.symm m) t :=
    markPos_unique hnd h1 hm'
  calc markPos m (t.mapLabel (⇑e))
      = leafPosMapLabel (⇑e) t
          ((leafPosMapLabel (⇑e) t).symm (markPos m (t.mapLabel (⇑e)))) :=
        (Equiv.apply_symm_apply (leafPosMapLabel (⇑e) t) _).symm
    _ = leafPosMapLabel (⇑e) t (markPos (e.symm m) t) := by rw [h2]

/-- **The marked depth is preserved by a label equivalence.** -/
theorem depth_markPos_mapLabel [Fintype β] [DecidableEq α] [DecidableEq β]
    (e : α ≃ β) {t : RTree α} (hmap : RTree.FullyLabelled (t.mapLabel (⇑e))) (m : β) :
    RTree.depth (t.mapLabel (⇑e)) (markPos m (t.mapLabel (⇑e)))
      = RTree.depth t (markPos (e.symm m) t) := by
  rw [markPos_mapLabel e hmap m, depth_leafPosMapLabel]


/-! ### Child swaps: leaf positions, labels and depths

A child swap changes the left/right address of a leaf but not the length of its path, so the
marked depth is a function of the child-swap orbit.  The transport is an equivalence of leaf
position types, proved by recursion on the tree and packaged through an existential statement so
that the dependent position types need not be unfolded at every use. -/

/-- **Swapping children transports leaf positions, preserving labels and depths.**  For
`t' ∈ RTree.swapFiber t` there is a bijection from the leaves of `t'` to the leaves of `t` that
keeps the leaf label and the path length. -/
theorem exists_leafPosSwap [DecidableEq α] (t : RTree α) :
    ∀ (t' : RTree α), t' ∈ RTree.swapFiber t →
      ∃ e : RTree.LeafPos t' ≃ RTree.LeafPos t,
        (∀ q, RTree.leafOfPos t (e q) = RTree.leafOfPos t' q) ∧
        (∀ q, RTree.depth t (e q) = RTree.depth t' q) := by
  induction t with
  | leaf a =>
      intro t' h
      rw [RTree.swapFiber_leaf, Finset.mem_singleton] at h
      rw [h]
      exact ⟨Equiv.refl PUnit, fun q => rfl, fun q => rfl⟩
  | node l r ihl ihr =>
      intro t' h
      rw [RTree.swapFiber_node, Finset.mem_union] at h
      rcases h with h | h
      · obtain ⟨p, hp, hpt⟩ := Finset.mem_image.mp h
        obtain ⟨h1, h2⟩ := Finset.mem_product.mp hp
        obtain ⟨e1, ho1, hd1⟩ := ihl p.1 h1
        obtain ⟨e2, ho2, hd2⟩ := ihr p.2 h2
        rw [← hpt]
        refine ⟨e1.sumCongr e2, ?_, ?_⟩
        · intro q
          rcases q with q | q
          · exact ho1 q
          · exact ho2 q
        · intro q
          rcases q with q | q
          · exact congrArg (· + 1) (hd1 q)
          · exact congrArg (· + 1) (hd2 q)
      · obtain ⟨p, hp, hpt⟩ := Finset.mem_image.mp h
        obtain ⟨h1, h2⟩ := Finset.mem_product.mp hp
        obtain ⟨e1, ho1, hd1⟩ := ihl p.1 h1
        obtain ⟨e2, ho2, hd2⟩ := ihr p.2 h2
        rw [← hpt]
        refine ⟨(e2.sumCongr e1).trans
          (Equiv.sumComm (RTree.LeafPos l) (RTree.LeafPos r)).symm, ?_, ?_⟩
        · intro q
          rcases q with q | q
          · change RTree.leafOfPos r (e2 q) = RTree.leafOfPos p.2 q
            exact ho2 q
          · change RTree.leafOfPos l (e1 q) = RTree.leafOfPos p.1 q
            exact ho1 q
        · intro q
          rcases q with q | q
          · change RTree.depth r (e2 q) + 1 = RTree.depth p.2 q + 1
            exact congrArg (· + 1) (hd2 q)
          · change RTree.depth l (e1 q) + 1 = RTree.depth p.1 q + 1
            exact congrArg (· + 1) (hd1 q)

/-- Fully labelled trees are closed under child swaps: the leaf list is only permuted. -/
theorem fullyLabelled_of_mem_swapFiber [Fintype α] [DecidableEq α] {t t' : RTree α}
    (ht : RTree.FullyLabelled t) (h : t' ∈ RTree.swapFiber t) : RTree.FullyLabelled t' := by
  obtain ⟨h1, h2⟩ := ht
  have hp := RTree.perm_of_mem_swapFiber h
  exact ⟨hp.nodup_iff.mpr h1, by rw [hp.length_eq, h2]⟩

/-- Being fully labelled is a child-swap invariant, in both directions. -/
theorem fullyLabelled_iff_of_mem_swapFiber [Fintype α] [DecidableEq α] {t t' : RTree α}
    (h : t' ∈ RTree.swapFiber t) : RTree.FullyLabelled t' ↔ RTree.FullyLabelled t :=
  ⟨fun h' => fullyLabelled_of_mem_swapFiber h' (RTree.swapFiber_symm h),
    fun h' => fullyLabelled_of_mem_swapFiber h' h⟩

/-- **The marked depth depends only on the child-swap orbit.**  The leaf carrying the marking
label is unique on a fully labelled tree, and a child swap transports the marked leaf to the
marked leaf of the swapped tree without changing its depth. -/
theorem depth_markPos_eq_of_mem_swapFiber [Fintype α] [DecidableEq α] {m : α} {t t' : RTree α}
    (ht : RTree.FullyLabelled t) (h : t' ∈ RTree.swapFiber t) :
    RTree.depth t' (markPos m t') = RTree.depth t (markPos m t) := by
  have ht' : RTree.FullyLabelled t' := fullyLabelled_of_mem_swapFiber ht h
  obtain ⟨e, hof, hdep⟩ := exists_leafPosSwap t t' h
  have h1 : RTree.leafOfPos t' (markPos m t') = m :=
    markPos_spec (RTree.mem_leaves_of_fullyLabelled ht' m)
  have h2 : RTree.leafOfPos t (e (markPos m t')) = m := by
    rw [hof (markPos m t'), h1]
  have h3 : e (markPos m t') = markPos m t :=
    markPos_unique ht.1 h2 (RTree.mem_leaves_of_fullyLabelled ht m)
  rw [← hdep (markPos m t'), h3]

/-- The chosen representative of a child-swap orbit of the fully labelled family is fully
labelled. -/
theorem fullyLabelled_orbitRep [Fintype α] [DecidableEq α] [Fintype (RTree.LT α)]
    (S : {S : Finset (RTree α) // S ∈ RTree.swapOrbits α}) :
    RTree.FullyLabelled (RTree.orbitRep α S) := by
  obtain ⟨t, ht⟩ := RTree.mem_swapOrbits.mp S.2
  refine fullyLabelled_of_mem_swapFiber t.2 ?_
  rw [ht]
  exact RTree.orbitRep_mem S

/-- Every element of the transversal is fully labelled. -/
theorem fullyLabelled_of_mem_transversal [Fintype α] [DecidableEq α] [Fintype (RTree.LT α)]
    {r : RTree α} (hr : r ∈ RTree.transversal α) : RTree.FullyLabelled r := by
  obtain ⟨S, rfl⟩ := RTree.mem_transversal.mp hr
  exact fullyLabelled_orbitRep S

/-! ### The orbit sum, natively in `ℕ`

The depth filter is a cardinality, so the orbit decomposition is used with `ℕ`-valued
indicators; casting a real-valued orbit sum back would be an unnecessary detour.  The three
lemmas below are the `ℕ`-valued copies of `RTree.sum_LT_eq_sum_orbits`,
`RTree.sum_transversal_eq_sum_orbits` and `RTree.sum_LT_eq_two_pow_mul_sum_transversal`. -/

/-- Summing over the fully labelled family is summing the orbit sums. -/
theorem sum_LT_eq_sum_orbits_nat [Fintype α] [DecidableEq α] [Fintype (RTree.LT α)]
    (f : RTree α → ℕ) :
    (∑ t : RTree.LT α, f t.val) = ∑ S ∈ RTree.swapOrbits α, ∑ u ∈ S, f u := by
  have h := Finset.sum_biUnion (s := RTree.swapOrbits α) (t := id) (f := f)
    RTree.swapOrbits_pairwiseDisjoint
  rw [RTree.biUnion_swapOrbits] at h
  rw [Finset.sum_image (s := (Finset.univ : Finset (RTree.LT α)))
    (g := fun t : RTree.LT α => t.val) (f := f) (fun x _ y _ hxy => Subtype.ext hxy)] at h
  have h' : (∑ S ∈ RTree.swapOrbits α, ∑ u ∈ S, f u)
      = ∑ S ∈ RTree.swapOrbits α, ∑ u ∈ id S, f u := rfl
  rw [h']
  exact h

/-- Summing over the transversal is summing over the chosen orbit representatives. -/
theorem sum_transversal_eq_sum_orbits_nat [Fintype α] [DecidableEq α] [Fintype (RTree.LT α)]
    (f : RTree α → ℕ) :
    (∑ r ∈ RTree.transversal α, f r)
      = ∑ S ∈ (RTree.swapOrbits α).attach, f (RTree.orbitRep α S) := by
  rw [RTree.transversal]
  exact Finset.sum_image (f := f) (g := RTree.orbitRep α) RTree.orbitRep_injOn

/-- **The plane multiplicity is exactly the orbit size**, natively in `ℕ`.  For a function
constant on child-swap classes, the sum over the fully labelled plane family is `2 ^ (#α - 1)`
times the sum over one representative per orbit. -/
theorem sum_LT_eq_pow_mul_sum_transversal_nat [Fintype α] [DecidableEq α]
    [Fintype (RTree.LT α)] (f : RTree α → ℕ)
    (hf : ∀ t t' : RTree α, t' ∈ RTree.swapFiber t → f t' = f t) :
    (∑ t : RTree.LT α, f t.val)
      = 2 ^ (Fintype.card α - 1) * ∑ r ∈ RTree.transversal α, f r := by
  have hconst : ∀ (S : {S : Finset (RTree α) // S ∈ RTree.swapOrbits α}) (u : RTree α),
      u ∈ S.1 → f u = f (RTree.orbitRep α S) := by
    intro S u hu
    exact hf (RTree.orbitRep α S) u (by rw [RTree.orbitRep_spec S]; exact hu)
  calc (∑ t : RTree.LT α, f t.val)
      = ∑ S ∈ RTree.swapOrbits α, ∑ u ∈ S, f u := sum_LT_eq_sum_orbits_nat f
    _ = ∑ S ∈ (RTree.swapOrbits α).attach, ∑ u ∈ (S : Finset (RTree α)), f u :=
        (Finset.sum_attach _ _).symm
    _ = ∑ S ∈ (RTree.swapOrbits α).attach,
          (S : Finset (RTree α)).card * f (RTree.orbitRep α S) := by
        refine Finset.sum_congr rfl fun S _ => ?_
        rw [Finset.sum_congr rfl (hconst S), Finset.sum_const, nsmul_eq_mul]
        rfl
    _ = ∑ S ∈ (RTree.swapOrbits α).attach,
          2 ^ (Fintype.card α - 1) * f (RTree.orbitRep α S) := by
        refine Finset.sum_congr rfl fun S _ => ?_
        rw [RTree.swapOrbits_card S.2]
    _ = 2 ^ (Fintype.card α - 1) *
          ∑ S ∈ (RTree.swapOrbits α).attach, f (RTree.orbitRep α S) :=
        (Finset.mul_sum _ _ _).symm
    _ = 2 ^ (Fintype.card α - 1) * ∑ r ∈ RTree.transversal α, f r := by
        rw [sum_transversal_eq_sum_orbits_nat f]


/-! ### Step 1: `markedCount` is the cardinality of the depth-filtered `Label p` family -/

/-- **The production marked count is a filtered `LTon` cardinality.**  `markedShapes p` is the
injective image of `LTon (Label p) univ` under `A ↦ ⟨A.1, markPos (markLabel p) A.1⟩`, so the
depth filter can be pulled back along that bijection (`I417Marked.sum_markedShapes`). -/
theorem markedCount_eq_card_markedFilterLabel (p ℓ : ℕ) :
    markedCount p ℓ = (markedFilterLabel p ℓ).card := by
  classical
  rw [markedCount]
  rw [Finset.card_filter]
  rw [sum_markedShapes
    (fun A : PercLib.CriticalLRP.I417Marked.MarkedShape p =>
      if RTree.depth A.1 A.2 = ℓ then (1 : ℕ) else 0)]
  rw [markedFilterLabel]
  exact (Finset.card_filter (fun t : LTon (Label p) (Finset.univ : Finset (Label p)) =>
    RTree.depth t.1 (markPos (markLabel p) t.1) = ℓ) Finset.univ).symm

/-! ### Step 2: transport along `finLabelEquiv` -/

/-- A fully labelled tree is an `LTon` tree on the whole label set. -/
theorem fullyLabelled_of_ltOn [Fintype α] [DecidableEq α] {t : RTree α}
    (h : t.leaves.Nodup ∧ t.leaves.toFinset = Finset.univ) : RTree.FullyLabelled t :=
  ⟨h.1, by rw [← List.toFinset_card_of_nodup h.1, h.2, Finset.card_univ]⟩

/-- **`finLabelEquiv p` transports the depth filter** from the `Fin (p+1)` labelling with the
mark on `Fin.last p` to the `Fin p ⊕ PUnit` labelling with the mark `markLabel p`.  The marked
leaf position and its depth are preserved (`markPos_mapLabel`,
`depth_markPos_mapLabel`), not merely the internal positions or the leaf count. -/
theorem card_markedFilterLabel_eq_markedFilterFin (p ℓ : ℕ) :
    (markedFilterLabel p ℓ).card = (markedFilterFin p ℓ).card := by
  classical
  have hlast : (finLabelEquiv p).symm (markLabel p) = Fin.last p := by
    rw [← finLabelEquiv_last p]
    exact (finLabelEquiv p).symm_apply_apply (Fin.last p)
  have hdep : ∀ a : LTon (Fin (p + 1)) (Finset.univ : Finset (Fin (p + 1))),
      RTree.depth (ltOnMapLabelEquiv (finLabelEquiv p) a).1
          (markPos (markLabel p) (ltOnMapLabelEquiv (finLabelEquiv p) a).1)
        = RTree.depth a.1 (markPos (Fin.last p) a.1) := by
    intro a
    have hfull : RTree.FullyLabelled a.1 := fullyLabelled_of_ltOn a.2
    rw [ltOnMapLabelEquiv_apply, ltOnMapLabel_coe]
    refine (depth_markPos_mapLabel (finLabelEquiv p)
      (RTree.fullyLabelled_mapLabel hfull) (markLabel p)).trans ?_
    rw [hlast]
  rw [markedFilterLabel, markedFilterFin]
  rw [← Fintype.card_subtype (fun t : LTon (Label p) (Finset.univ : Finset (Label p)) =>
    RTree.depth t.1 (markPos (markLabel p) t.1) = ℓ)]
  rw [← Fintype.card_subtype (fun t : LTon (Fin (p + 1)) (Finset.univ : Finset (Fin (p + 1))) =>
    RTree.depth t.1 (markPos (Fin.last p) t.1) = ℓ)]
  refine Fintype.card_congr (Equiv.subtypeEquiv (ltOnMapLabelEquiv (finLabelEquiv p)) ?_).symm
  intro a
  constructor
  · intro h
    rwa [hdep a]
  · intro h
    rwa [hdep a] at h

/-! ### Step 3: `LTon` and `RTree.LT` are the same family on `Fin (p+1)` -/

/-- **The depth-filtered `LTon` family and the depth-filtered `RTree.LT` family coincide.**
`LTon (Fin (p+1)) univ` and `RTree.LT (Fin (p+1))` are the same fully labelled trees, and
`LTon.equivLT` is the identity on the underlying tree. -/
theorem card_markedFilterFin_eq_planeMarkedFiber (p ℓ : ℕ) :
    (markedFilterFin p ℓ).card = (planeMarkedFiber p ℓ).card := by
  classical
  rw [markedFilterFin, planeMarkedFiber]
  rw [← Fintype.card_subtype (fun t : LTon (Fin (p + 1)) (Finset.univ : Finset (Fin (p + 1))) =>
    RTree.depth t.1 (markPos (Fin.last p) t.1) = ℓ)]
  rw [← Fintype.card_subtype (fun t : RTree.LT (Fin (p + 1)) =>
    RTree.depth t.val (markPos (Fin.last p) t.val) = ℓ)]
  exact Fintype.card_congr (Equiv.subtypeEquiv (ltOnFinEquivLT p) (fun _ => Iff.rfl))

/-! ### Step 4: the orbit decomposition of the filtered plane family -/

/-- **The per-depth orbit count**: the depth-`ℓ` marked plane family has exactly `2 ^ p` plane
presentations per depth-`ℓ` child-swap orbit, so its cardinality is `2 ^ p` times the number of
those orbits.  The count is evaluated on the transversal itself, not by dividing a finite
family cardinality, and no tree is deleted: the depth filter is monotone with respect to the
orbit partition because child swaps preserve the marked depth. -/
theorem card_planeMarkedFiber_eq_two_pow_mul_nonplaneMarkedCount (p ℓ : ℕ) :
    (planeMarkedFiber p ℓ).card
      = 2 ^ p * PercLib.CriticalLRP.I417MarkedTransversal.nonplaneMarkedCount p ℓ := by
  classical
  set f : RTree (Fin (p + 1)) → ℕ := fun r =>
    if RTree.FullyLabelled r ∧ RTree.depth r (markPos (Fin.last p) r) = ℓ then 1 else 0
    with hfdef
  have hf : ∀ t t' : RTree (Fin (p + 1)), t' ∈ RTree.swapFiber t → f t' = f t := by
    intro t t' h
    by_cases ht : RTree.FullyLabelled t
    · have ht' : RTree.FullyLabelled t' := fullyLabelled_of_mem_swapFiber ht h
      have hd : RTree.depth t' (markPos (Fin.last p) t')
          = RTree.depth t (markPos (Fin.last p) t) :=
        depth_markPos_eq_of_mem_swapFiber ht h
      simp only [hfdef, ht, ht', true_and, hd]
    · have ht' : ¬ RTree.FullyLabelled t' := fun h' =>
        ht ((fullyLabelled_iff_of_mem_swapFiber h).mp h')
      simp only [hfdef, ht, ht', false_and]
  have hsum := sum_LT_eq_pow_mul_sum_transversal_nat (α := Fin (p + 1)) f hf
  have hL : (∑ t : RTree.LT (Fin (p + 1)), f t.val) = (planeMarkedFiber p ℓ).card := by
    rw [planeMarkedFiber]
    have hstep : (∑ t : RTree.LT (Fin (p + 1)), f t.val)
        = ∑ t : RTree.LT (Fin (p + 1)),
            (if RTree.depth t.val (markPos (Fin.last p) t.val) = ℓ then (1 : ℕ) else 0) := by
      refine Finset.sum_congr rfl fun t _ => ?_
      simp only [hfdef, t.2, true_and]
    rw [hstep]
    exact (Finset.card_filter
      (fun t : RTree.LT (Fin (p + 1)) =>
        RTree.depth t.val (markPos (Fin.last p) t.val) = ℓ) Finset.univ).symm
  have hR : (∑ r ∈ RTree.transversal (Fin (p + 1)), f r)
      = ((RTree.transversal (Fin (p + 1))).filter
          (fun r => RTree.depth r (markPos (Fin.last p) r) = ℓ)).card := by
    rw [Finset.card_filter]
    refine Finset.sum_congr rfl fun r hr => ?_
    have hfl : RTree.FullyLabelled r := fullyLabelled_of_mem_transversal hr
    simp only [hfdef, hfl, true_and]
  rw [hR] at hsum
  rw [show Fintype.card (Fin (p + 1)) - 1 = p by rw [Fintype.card_fin]; omega] at hsum
  rw [show PercLib.CriticalLRP.I417MarkedTransversal.nonplaneMarkedCount p ℓ
      = ((RTree.transversal (Fin (p + 1))).filter
          (fun r => RTree.depth r (markPos (Fin.last p) r) = ℓ)).card from rfl]
  exact hL.symm.trans hsum

/-! ### The per-depth identity -/

/-- **`markedCount p ℓ = 2 ^ p * nonplaneMarkedCount p ℓ` for every `p` and `ℓ`.**

This is the per-depth refinement of the total identities
`I417Marked.sum_markedCount_eq_plane_count` and
`I417MarkedTransversal.sum_nonplaneMarkedCount`: the plane marked coefficient at depth `ℓ` is
exactly `2 ^ p` — the number of plane presentations of a non-plane `(p+1)`-leaf tree, i.e. the
size of a child-swap orbit with `p` internal vertices — times the non-plane coefficient at the
same depth.  Neither side is a weighted sum, and the equality holds at every depth separately,
including the boundary depths `ℓ = 1` and `ℓ = p + 1` and the degenerate `p = 0`. -/
theorem markedCount_eq_two_pow_mul_nonplaneMarkedCount (p ℓ : ℕ) :
    PercLib.CriticalLRP.I417Marked.markedCount p ℓ
      = 2 ^ p * PercLib.CriticalLRP.I417MarkedTransversal.nonplaneMarkedCount p ℓ := by
  rw [markedCount_eq_card_markedFilterLabel, card_markedFilterLabel_eq_markedFilterFin]
  exact card_markedFilterFin_eq_planeMarkedFiber p ℓ |>.trans
    (card_planeMarkedFiber_eq_two_pow_mul_nonplaneMarkedCount p ℓ)

/-- **Agreement at `p = 1`, `ℓ = 2` with the two independently computed values.**  Production
proves `markedCount 1 2 = 2` from the plane total and `nonplaneMarkedCount 1 2 = 1` from the
transversal total; the per-depth identity reproduces them. -/
theorem markedCount_one_two_consistency :
    PercLib.CriticalLRP.I417Marked.markedCount 1 2
      = 2 ^ 1 * PercLib.CriticalLRP.I417MarkedTransversal.nonplaneMarkedCount 1 2 := by
  rw [PercLib.CriticalLRP.I417Marked.markedCount_one_two,
    PercLib.CriticalLRP.I417MarkedTransversal.nonplaneMarkedCount_one_two]
  norm_num


/-! ### Boundary consistency: `p = 0` and the depth range -/

/-- **The non-plane coefficient at `p = 0` is `1`, computed from the transversal itself.**  The
`Fin 1`-labelled family has the single fully labelled tree `leaf 0`, hence a single child-swap
orbit, whose marked leaf has depth `1`.  Together with `I417Marked.markedCount_zero_one` this
verifies the identity `1 = 2 ^ 0 * 1` at the degenerate end without going through the general
theorem. -/
theorem nonplaneMarkedCount_zero_one :
    PercLib.CriticalLRP.I417MarkedTransversal.nonplaneMarkedCount 0 1 = 1 := by
  classical
  have hcard : (RTree.transversal (Fin 1)).card = 1 := by
    rw [RTree.transversal_card]
    have hmul := RTree.card_swapOrbits_mul (α := Fin 1)
    rw [Fintype.card_fin, RTree.card_LT_fin_one] at hmul
    simpa using hmul
  rw [PercLib.CriticalLRP.I417MarkedTransversal.nonplaneMarkedCount]
  rw [Finset.filter_true_of_mem]
  · exact hcard
  · intro r hr
    have hfl : RTree.FullyLabelled r := fullyLabelled_of_mem_transversal hr
    have hnum : r.numLeaves = 1 := by
      rw [RTree.numLeaves, hfl.2, Fintype.card_fin]
    cases r with
    | leaf _ => rfl
    | node l rr =>
        have h1 := RTree.numLeaves_pos l
        have h2 := RTree.numLeaves_pos rr
        rw [RTree.numLeaves_node] at hnum
        omega

/-- **The non-plane coefficient vanishes below depth one**, as the plane one does. -/
theorem nonplaneMarkedCount_eq_zero_of_lt (p ℓ : ℕ) (h : ℓ < 1) :
    PercLib.CriticalLRP.I417MarkedTransversal.nonplaneMarkedCount p ℓ = 0 := by
  have h0 := markedCount_eq_two_pow_mul_nonplaneMarkedCount p ℓ
  rw [PercLib.CriticalLRP.I417Marked.markedCount_eq_zero_of_lt p ℓ h] at h0
  rcases Nat.mul_eq_zero.mp h0.symm with h1 | h1
  · exact absurd h1 (pow_ne_zero p (by norm_num))
  · exact h1

/-- **The non-plane coefficient vanishes above depth `p + 1`**, as the plane one does: every
transversal element has `p + 1` leaves. -/
theorem nonplaneMarkedCount_eq_zero_of_gt (p ℓ : ℕ) (h : p + 1 < ℓ) :
    PercLib.CriticalLRP.I417MarkedTransversal.nonplaneMarkedCount p ℓ = 0 := by
  have h0 := markedCount_eq_two_pow_mul_nonplaneMarkedCount p ℓ
  rw [PercLib.CriticalLRP.I417Marked.markedCount_eq_zero_of_gt p ℓ h] at h0
  rcases Nat.mul_eq_zero.mp h0.symm with h1 | h1
  · exact absurd h1 (pow_ne_zero p (by norm_num))
  · exact h1

end PercLib.CriticalLRP.I417MarkedPerDepth

/-! ### Axiom audit -/

set_option linter.hashCommand false

namespace PercLib.CriticalLRP.I417MarkedPerDepth

#print axioms leafOfPos_leafPosMapLabel
#print axioms depth_leafPosMapLabel
#print axioms markPos_mapLabel
#print axioms depth_markPos_mapLabel
#print axioms exists_leafPosSwap
#print axioms depth_markPos_eq_of_mem_swapFiber
#print axioms sum_LT_eq_sum_orbits_nat
#print axioms sum_LT_eq_pow_mul_sum_transversal_nat
#print axioms markedCount_eq_card_markedFilterLabel
#print axioms card_markedFilterLabel_eq_markedFilterFin
#print axioms card_markedFilterFin_eq_planeMarkedFiber
#print axioms card_planeMarkedFiber_eq_two_pow_mul_nonplaneMarkedCount
#print axioms markedCount_eq_two_pow_mul_nonplaneMarkedCount
#print axioms markedCount_one_two_consistency
#print axioms nonplaneMarkedCount_zero_one
#print axioms nonplaneMarkedCount_eq_zero_of_lt
#print axioms nonplaneMarkedCount_eq_zero_of_gt

end PercLib.CriticalLRP.I417MarkedPerDepth
