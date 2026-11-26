/-
Independently reviewed and integrated UltraMath finding f1: swarm `smwwyd7lg`, member `m2`,
direction A. Production integration revision:
`80951640d68930030716cfd90af38fee830518f2`, Lean 4.35.0.
The independently rebuilt candidate was `.ultramath/smwwyd7lg/m2/LeafSum.lean`.
-/

/-
# The leaf sum of the canonical tree weight: exact value `χ ^ (2q - 1)`

`AtlasRealization/Canonical/Transversal.lean` reduces the probability that a root `x` is joined to
`q` labelled terminals to a sum over one plane representative per child-swap orbit of the canonical
tree weight `I417Base.wtE`.  What that file does *not* do is evaluate the inner sums: the weight of
a single diagram still has its leaf labels and internal positions free.

This file performs exactly that evaluation, in the canonical countable model and over `ℝ≥0∞`
(so no `toReal` and no summability side conditions), and then combines it with the shape count.

## Results

* `RTree.tsum_wtE_eq`: for a kernel `k : V → V → ℝ≥0∞` whose row sums are all the same number `S`
  (translation invariance), every rooted binary tree `t` with `p` leaves satisfies
  `∑' y : t.LeafPos → V, wtE k t y v = S ^ (2p - 1)` — the tree weight, summed over the values at
  *every* vertex except the root, is `S` per free vertex, so `S ^ #edges` with `#edges = 2p - 1`.
  The identity is independent of the shape of `t`, which is the point: no non-plane shape is
  collapsed and no shape is identified with another.
* `RTree.tsum_wtE_labelled`: the same with the leaves labelled by `Fin p`, for a fully labelled `t`.
* `RTree.transversal_card_fin_eq_dfactorial`: the transversal has exactly `(2q-3)!!` elements.
* `CanonAtlas.Measure.tsum_labelEvent_le_dfactorial`: the `k = 0` case of Lemma I.4.16 in the
  canonical countable model,
  `E|K_x|^q ≤ (2q - 3)!! · χ ^ (2q - 1)`, `χ = E|K|`.

No definitions are introduced; every declaration is a theorem.
-/
module

public import PercLib.CriticalLRP.TreeExpansion.AtlasRealization.Canonical.Transversal
public import PercLib.CriticalLRP.TreeExpansion.AtlasRealization.ExactCount.Exact
public import PercLib.CriticalLRP.Correlation.I417.Nonnegative.Main

/-! The exact leaf-sum of a canonical tree weight, the transversal count, and the
resulting arbitrary-order ordinary moment bound. -/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

open Finset

open scoped ENNReal

namespace PercLib.CriticalLRP.TreeExpansion

namespace RTree

variable {α : Type*} {V : Type*}

/-! ### Summing a triple product, over `ℝ≥0∞` -/

/-- The `ℝ≥0∞` version of `sum_sum_sum_factor`: over arbitrary index types (no finiteness, no
summability), a triple sum of a product separates the two outer sums at each `u`.  All the
manipulations are the unconditional `ℝ≥0∞` ones (`ENNReal.tsum_comm`, `ENNReal.tsum_mul_left`,
`ENNReal.tsum_mul_right`), so no hypothesis on `V` or on the summands is needed. -/
theorem tsum_tsum_tsum_factor {ι κ : Type*} (f : V → ℝ≥0∞) (A : ι → V → ℝ≥0∞)
    (B : κ → V → ℝ≥0∞) :
    (∑' i, ∑' j, ∑' u, f u * A i u * B j u)
      = ∑' u, f u * ((∑' i, A i u) * (∑' j, B j u)) := by
  have h1 : (∑' i, ∑' j, ∑' u, f u * A i u * B j u)
      = ∑' i, ∑' u, ∑' j, f u * A i u * B j u :=
    tsum_congr fun i => ENNReal.tsum_comm
  have h2 : (∑' i, ∑' u, ∑' j, f u * A i u * B j u)
      = ∑' u, ∑' i, ∑' j, f u * A i u * B j u := ENNReal.tsum_comm
  have h3 : (∑' u, ∑' i, ∑' j, f u * A i u * B j u)
      = ∑' u, (∑' i, f u * A i u) * (∑' j, B j u) := by
    refine tsum_congr fun u => ?_
    rw [← ENNReal.tsum_mul_right]
    refine tsum_congr fun i => ?_
    exact ENNReal.tsum_mul_left
  have h4 : (∑' u, (∑' i, f u * A i u) * (∑' j, B j u))
      = ∑' u, f u * ((∑' i, A i u) * (∑' j, B j u)) := by
    refine tsum_congr fun u => ?_
    rw [ENNReal.tsum_mul_left, mul_assoc]
  rw [h1, h2, h3, h4]

/-! ### The exact leaf sum of the canonical tree weight -/

/-- **The tree-weight identity of Lemma I.4.16, over `ℝ≥0∞` and for an arbitrary type `V`.**

For a kernel `k` whose row sums are all the same number `S` (the translation-invariance input
`∑_y k v y = S`, independent of `v`), and for *every* rooted binary tree `t` with `p` leaves, the
canonical tree weight summed over the values at all free vertices is exactly `S ^ (2p - 1)`.

The tree has `2p - 1` edges and `2p - 1` free vertices (all vertices except the root), so the value
is one factor of `S` per edge; the identity is exactly the statement that each hidden vertex sum can
be performed bottom-up, and it is **shape-independent** — no two distinct trees are identified and
no non-plane shape is collapsed.  The induction is the recursion of `wtE` itself. -/
theorem tsum_wtE_eq (k : V → V → ℝ≥0∞) (S : ℝ≥0∞) (hS : ∀ v : V, ∑' y : V, k v y = S) :
    ∀ (t : RTree α) (v : V),
      (∑' y : t.LeafPos → V, PercLib.CriticalLRP.I417Base.wtE k t y v)
        = S ^ (2 * t.numLeaves - 1) := by
  intro t
  induction t with
  | leaf a =>
    intro v
    have h : (∑' y : (leaf a).LeafPos → V,
        PercLib.CriticalLRP.I417Base.wtE k (leaf a) y v) = S := by
      refine (Equiv.tsum_eq (Equiv.funUnique PUnit V) (fun z : V => k v z)).trans ?_
      exact hS v
    rw [h]
    simp
  | node l r ihl ihr =>
    intro v
    have hsplit : (∑' y : (node l r).LeafPos → V,
        PercLib.CriticalLRP.I417Base.wtE k (node l r) y v)
        = ∑' p : (l.LeafPos → V) × (r.LeafPos → V),
            ∑' u : V, k v u * PercLib.CriticalLRP.I417Base.wtE k l p.1 u
              * PercLib.CriticalLRP.I417Base.wtE k r p.2 u := by
      refine (Equiv.tsum_eq (Equiv.sumArrowEquivProdArrow l.LeafPos r.LeafPos V).symm
        (fun y : (l.LeafPos ⊕ r.LeafPos) → V =>
          ∑' u : V, k v u
            * PercLib.CriticalLRP.I417Base.wtE k l (fun p => y (Sum.inl p)) u
            * PercLib.CriticalLRP.I417Base.wtE k r (fun p => y (Sum.inr p)) u)).symm.trans ?_
      exact tsum_congr fun p => rfl
    have hprod : (∑' p : (l.LeafPos → V) × (r.LeafPos → V),
            ∑' u : V, k v u * PercLib.CriticalLRP.I417Base.wtE k l p.1 u
              * PercLib.CriticalLRP.I417Base.wtE k r p.2 u)
        = ∑' y1 : l.LeafPos → V, ∑' y2 : r.LeafPos → V,
            ∑' u : V, k v u * PercLib.CriticalLRP.I417Base.wtE k l y1 u
              * PercLib.CriticalLRP.I417Base.wtE k r y2 u := by
      rw [ENNReal.tsum_prod']
    rw [hsplit, hprod,
      tsum_tsum_tsum_factor (fun u => k v u)
        (fun y1 u => PercLib.CriticalLRP.I417Base.wtE k l y1 u)
        (fun y2 u => PercLib.CriticalLRP.I417Base.wtE k r y2 u)]
    have hstep : (∑' u : V, k v u * ((∑' y1 : l.LeafPos → V,
          PercLib.CriticalLRP.I417Base.wtE k l y1 u)
          * (∑' y2 : r.LeafPos → V, PercLib.CriticalLRP.I417Base.wtE k r y2 u)))
        = ∑' u : V, k v u * (S ^ (2 * l.numLeaves - 1) * S ^ (2 * r.numLeaves - 1)) :=
      tsum_congr fun u => by rw [ihl u, ihr u]
    rw [hstep, ENNReal.tsum_mul_right, hS v, numLeaves_node, ← pow_add, ← pow_succ']
    congr 1
    have hl : 0 < l.numLeaves := numLeaves_pos l
    have hr : 0 < r.numLeaves := numLeaves_pos r
    omega

/-! ### The same sum with the leaves labelled by `Fin p` -/

/-- **The leaf sum with the paper's labelling.**  For a fully labelled tree the leaf-position map
`leafOfPos t : t.LeafPos → α` is a bijection, so summing over the labels `x : α → V` is the same as
summing over the leaf positions, and `tsum_wtE_eq` applies. -/
theorem tsum_wtE_labelled [Fintype α] (k : V → V → ℝ≥0∞) (S : ℝ≥0∞)
    (hS : ∀ v : V, ∑' y : V, k v y = S) {t : RTree α} (ht : FullyLabelled t) (v : V) :
    (∑' x : α → V,
        PercLib.CriticalLRP.I417Base.wtE k t (fun p => x (leafOfPos t p)) v)
      = S ^ (2 * t.numLeaves - 1) := by
  have hbij : Function.Bijective (leafOfPos t) :=
    ⟨leafOfPos_injective ht.1,
      fun a => exists_leafOfPos t a (mem_leaves_of_fullyLabelled ht a)⟩
  set e : t.LeafPos ≃ α := Equiv.ofBijective (leafOfPos t) hbij with he
  have h1 : (∑' x : α → V,
        PercLib.CriticalLRP.I417Base.wtE k t (fun p => x (leafOfPos t p)) v)
      = ∑' x : α → V,
          PercLib.CriticalLRP.I417Base.wtE k t
            ((Equiv.arrowCongr e (Equiv.refl V)).symm x) v := by
    exact tsum_congr fun x => rfl
  rw [h1]
  exact (Equiv.tsum_eq (Equiv.arrowCongr e (Equiv.refl V)).symm
      (fun y : t.LeafPos → V => PercLib.CriticalLRP.I417Base.wtE k t y v)).trans
      (tsum_wtE_eq k S hS t v)

/-! ### Every transversal representative is fully labelled -/

section Transversal

variable [Fintype α] [DecidableEq α] [Fintype (LT α)]

/-- **A child-swap transversal consists of fully labelled trees.**  Child swaps only permute the
left-to-right order of the leaves (`perm_of_mem_swapFiber`), so `Nodup` and the leaf count survive,
and every orbit is the child-swap orbit of a fully labelled tree by definition of `swapOrbits`. -/
theorem fullyLabelled_of_mem_transversal {r : RTree α} (hr : r ∈ transversal α) :
    FullyLabelled r := by
  obtain ⟨S, rfl⟩ := mem_transversal.mp hr
  have hex : ∃ t : LT α, swapFiber t.val = (S : Finset (RTree α)) := by
    have h := S.2
    simpa only [swapOrbits, Finset.mem_image, Finset.mem_univ, true_and] using h
  obtain ⟨t, ht⟩ := hex
  have hmem : orbitRep α S ∈ swapFiber t.val := by
    rw [ht, ← orbitRep_spec S]
    exact swapFiber_self _
  have hperm : (orbitRep α S).leaves.Perm t.val.leaves := perm_of_mem_swapFiber hmem
  refine ⟨hperm.nodup_iff.mpr t.2.1, ?_⟩
  rw [hperm.length_eq]
  exact t.2.2

/-- **The exact transversal count**: one representative per non-plane rooted binary tree with `q`
distinctly labelled leaves, i.e. `(2q - 3)!!`. -/
theorem transversal_card_fin_eq_dfactorial (q : ℕ) (hq : 1 ≤ q) :
    (transversal (Fin q)).card = PercLib.CriticalLRP.VolumeMoments.M (q - 1) := by
  rw [transversal_card]
  exact card_swapOrbits_fin_eq_dfactorial q hq

end Transversal

end RTree

end PercLib.CriticalLRP.TreeExpansion

namespace CanonAtlas

open PercLib.CriticalLRP.TreeExpansion (RTree)

namespace Measure

variable {V : Type*} [DecidableEq V]

/-- **The `k = 0` case of Lemma I.4.16 in the canonical countable model.**

For an arbitrary countable vertex type `V`, an opening `π` with `π e < 1`, a root `x`, `q ≥ 1`
terminals, and a two-point function with *constant row sum* `S` (the translation-invariance input,
discharged from translation invariance of the kernel by `rowSum_const_of_translationInvariant`
below), the `q`-th ordinary moment of the cluster is bounded by `(2q-3)!! · S^(2q-1)`.

The proof is the honest cover/union bound of the integrated
`measure_labelEvent_le_wtE_transversal_bk` — one plane representative per child-swap orbit, so the
plane multiplicity `2^(q-1)` does not appear — followed by the *exact* evaluation of the tree weight
of each representative (`RTree.tsum_wtE_labelled`), which is `S^(2q-1)` for every shape, and the
exact orbit count `RTree.transversal_card_fin_eq_dfactorial` (`(2q-3)!!`).  No shape is collapsed:
the sum over the transversal has one term per non-plane tree, and each term is evaluated
separately. -/
theorem tsum_labelEvent_le_dfactorial [Countable V]
    (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1) {q : ℕ} (hq : 1 ≤ q)
    (x : V) (S : ℝ≥0∞)
    (hS : ∀ v : V,
      ∑' y : V, PercLib.CriticalLRP.edgeMeasure π (PercLib.CriticalLRP.connSet v y) = S) :
    (∑' f : Fin q → V,
        PercLib.CriticalLRP.edgeMeasure π (PercLib.CriticalLRP.I417A.labelEvent x f))
      ≤ (PercLib.CriticalLRP.VolumeMoments.M (q - 1) : ℝ≥0∞) * S ^ (2 * q - 1) := by
  classical
  have hstep : (∑' f : Fin q → V,
        PercLib.CriticalLRP.edgeMeasure π (PercLib.CriticalLRP.I417A.labelEvent x f))
      ≤ ∑' f : Fin q → V, ∑ r ∈ RTree.transversal (Fin q),
          PercLib.CriticalLRP.I417Base.wtE
            (fun a b => PercLib.CriticalLRP.edgeMeasure π
              (PercLib.CriticalLRP.connSet a b)) r
            (fun p => f (RTree.leafOfPos r p)) x :=
    ENNReal.tsum_le_tsum fun f =>
      measure_labelEvent_le_wtE_transversal_bk π hπ hq x f
  refine hstep.trans ?_
  have hswap : (∑' f : Fin q → V, ∑ r ∈ RTree.transversal (Fin q),
        PercLib.CriticalLRP.I417Base.wtE
          (fun a b => PercLib.CriticalLRP.edgeMeasure π
            (PercLib.CriticalLRP.connSet a b)) r
          (fun p => f (RTree.leafOfPos r p)) x)
      = ∑ r ∈ RTree.transversal (Fin q), ∑' f : Fin q → V,
          PercLib.CriticalLRP.I417Base.wtE
            (fun a b => PercLib.CriticalLRP.edgeMeasure π
              (PercLib.CriticalLRP.connSet a b)) r
            (fun p => f (RTree.leafOfPos r p)) x := by
    calc (∑' f : Fin q → V, ∑ r ∈ RTree.transversal (Fin q),
          PercLib.CriticalLRP.I417Base.wtE
            (fun a b => PercLib.CriticalLRP.edgeMeasure π
              (PercLib.CriticalLRP.connSet a b)) r
            (fun p => f (RTree.leafOfPos r p)) x)
        = ∑' f : Fin q → V,
            ∑' r : {r : RTree (Fin q) // r ∈ RTree.transversal (Fin q)},
              PercLib.CriticalLRP.I417Base.wtE
                (fun a b => PercLib.CriticalLRP.edgeMeasure π
                  (PercLib.CriticalLRP.connSet a b)) r.1
                (fun p => f (RTree.leafOfPos r.1 p)) x := by
          refine tsum_congr fun f => ?_
          rw [tsum_fintype]
          exact (Finset.sum_coe_sort _ _).symm
      _ = ∑' r : {r : RTree (Fin q) // r ∈ RTree.transversal (Fin q)},
            ∑' f : Fin q → V,
              PercLib.CriticalLRP.I417Base.wtE
                (fun a b => PercLib.CriticalLRP.edgeMeasure π
                  (PercLib.CriticalLRP.connSet a b)) r.1
                (fun p => f (RTree.leafOfPos r.1 p)) x :=
          ENNReal.tsum_comm
      _ = ∑ r ∈ RTree.transversal (Fin q), ∑' f : Fin q → V,
              PercLib.CriticalLRP.I417Base.wtE
                (fun a b => PercLib.CriticalLRP.edgeMeasure π
                  (PercLib.CriticalLRP.connSet a b)) r
                (fun p => f (RTree.leafOfPos r p)) x := by
          rw [tsum_fintype]
          exact Finset.sum_coe_sort (RTree.transversal (Fin q))
            (fun r => ∑' f : Fin q → V,
              PercLib.CriticalLRP.I417Base.wtE
                (fun a b => PercLib.CriticalLRP.edgeMeasure π
                  (PercLib.CriticalLRP.connSet a b)) r
                (fun p => f (RTree.leafOfPos r p)) x)
  rw [hswap]
  have hinner : ∀ r ∈ RTree.transversal (Fin q),
      (∑' f : Fin q → V,
          PercLib.CriticalLRP.I417Base.wtE
            (fun a b => PercLib.CriticalLRP.edgeMeasure π
              (PercLib.CriticalLRP.connSet a b)) r
            (fun p => f (RTree.leafOfPos r p)) x) = S ^ (2 * q - 1) := by
    intro r hr
    have hfull : RTree.FullyLabelled r := RTree.fullyLabelled_of_mem_transversal hr
    have hnum : r.numLeaves = q := by
      have h2 := hfull.2
      rw [Fintype.card_fin] at h2
      exact h2
    have := RTree.tsum_wtE_labelled
      (fun a b => PercLib.CriticalLRP.edgeMeasure π (PercLib.CriticalLRP.connSet a b))
      S hS hfull x
    rwa [hnum] at this
  rw [Finset.sum_congr rfl hinner, Finset.sum_const, nsmul_eq_mul,
    RTree.transversal_card_fin_eq_dfactorial q hq]

/-- **The `k = 0` case of Lemma I.4.16 as a bound on the cluster moment itself.**
`E|K_x|^q ≤ (2q-3)!! · χ^(2q-1)`, where `E|K_x|^q` is the `ℝ≥0∞` integral of `|K_x|^q`
(`I417A.lintegral_cardFun_pow_eq_tsum` identifies it with the labelled-vertex sum). -/
theorem lintegral_cardFun_pow_le_dfactorial [Countable V]
    (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1) {q : ℕ} (hq : 1 ≤ q)
    (x : V) (S : ℝ≥0∞)
    (hS : ∀ v : V,
      ∑' y : V, PercLib.CriticalLRP.edgeMeasure π (PercLib.CriticalLRP.connSet v y) = S) :
    ∫⁻ ω, PercLib.CriticalLRP.Percolation.cardFun
        (PercLib.Percolation.Bond.cluster ω x) ^ q ∂(PercLib.CriticalLRP.edgeMeasure π)
      ≤ (PercLib.CriticalLRP.VolumeMoments.M (q - 1) : ℝ≥0∞) * S ^ (2 * q - 1) := by
  rw [PercLib.CriticalLRP.I417A.lintegral_cardFun_pow_eq_tsum]
  exact tsum_labelEvent_le_dfactorial π hπ hq x S hS

/-- **Non-vacuity check at `q = 1`**: the bound reads `E|K_x| ≤ χ`, with coefficient `M 0 = 1`
and exponent `2 · 1 - 1 = 1`; no factor is lost or gained at `q = 1`. -/
theorem tsum_labelEvent_one_le [Countable V]
    (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1) (x : V) (S : ℝ≥0∞)
    (hS : ∀ v : V,
      ∑' y : V, PercLib.CriticalLRP.edgeMeasure π (PercLib.CriticalLRP.connSet v y) = S) :
    (∑' f : Fin 1 → V,
        PercLib.CriticalLRP.edgeMeasure π (PercLib.CriticalLRP.I417A.labelEvent x f)) ≤ S := by
  simpa using tsum_labelEvent_le_dfactorial π hπ (q := 1) le_rfl x S hS

/-- **Constant row sums from translation invariance of the kernel.**  For an additive commutative
group `V`, a two-point function of the form `k a b = ρ (b - a)` has row sum `∑_z ρ z` at every
vertex; this is the hypothesis `hS` of the moment bound, so the moment bound only needs the
translation invariance of the canonical kernel and not a separate row-sum assumption. -/
theorem rowSum_const_of_translationInvariant {V : Type*} [AddCommGroup V]
    (π : Sym2 V → unitInterval) (ρ : V → ℝ≥0∞)
    (hk : ∀ a b : V,
      PercLib.CriticalLRP.edgeMeasure π (PercLib.CriticalLRP.connSet a b) = ρ (b - a)) :
    ∀ v : V, ∑' y : V,
      PercLib.CriticalLRP.edgeMeasure π (PercLib.CriticalLRP.connSet v y) = ∑' z : V, ρ z := by
  intro v
  simp only [hk, sub_eq_add_neg]
  exact Equiv.tsum_eq (Equiv.addRight (-v)) ρ

end Measure

end CanonAtlas

/-! ### Axiom audit -/

namespace LeafSumAudit

set_option linter.hashCommand false

#print axioms PercLib.CriticalLRP.TreeExpansion.RTree.tsum_tsum_tsum_factor
#print axioms PercLib.CriticalLRP.TreeExpansion.RTree.tsum_wtE_eq
#print axioms PercLib.CriticalLRP.TreeExpansion.RTree.tsum_wtE_labelled
#print axioms PercLib.CriticalLRP.TreeExpansion.RTree.fullyLabelled_of_mem_transversal
#print axioms PercLib.CriticalLRP.TreeExpansion.RTree.transversal_card_fin_eq_dfactorial
#print axioms CanonAtlas.Measure.tsum_labelEvent_le_dfactorial
#print axioms CanonAtlas.Measure.lintegral_cardFun_pow_le_dfactorial
#print axioms CanonAtlas.Measure.tsum_labelEvent_one_le
#print axioms CanonAtlas.Measure.rowSum_const_of_translationInvariant

/-! Production declarations consumed above, audited as well. -/
#print axioms CanonAtlas.Measure.measure_labelEvent_le_wtE_transversal_bk
#print axioms PercLib.CriticalLRP.I417A.lintegral_cardFun_pow_eq_tsum
#print axioms PercLib.CriticalLRP.TreeExpansion.RTree.card_swapOrbits_fin_eq_dfactorial
#print axioms PercLib.CriticalLRP.TreeExpansion.RTree.transversal_card

end LeafSumAudit

