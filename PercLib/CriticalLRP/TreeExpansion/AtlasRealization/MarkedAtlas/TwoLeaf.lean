/- Independently rebuilt and verified at production revision
    eb9b71a3cf20a0fe9906271415f5b17efd80f5ad.
    Original scratch source is recorded below. -/
/-
Direction A of swarm `smwwt6noq`: the concrete `p = 1` instantiation of the finite marked atlas
bound — the two-leaf diagram evaluation.

At `p = 1` the marked label type is `Fin 1 ⊕ PUnit`, which has exactly two elements, so every
labelled shape is a two-leaf tree `node (leaf a) (leaf b)` with `{a, b}` the two labels in some
order.  Each such shape has three atlas edges: the two down edges of the root branch point `u`
(to `y a` and to `y b`) and the root edge from the root vertex `x` to `u`.  Summing the internal
position `u` over the finite vertex set therefore makes the marked diagram of one shape the
three-point diagram `∑_u P(x↔u) P(u↔y a) P(u↔y b)`, and the two orderings of the two labels
give the same diagram, whence the factor `2`.
-/
module

public import PercLib.CriticalLRP.TreeExpansion.AtlasRealization.MarkedAtlas.Example

/-! # The `p = 1` marked diagram evaluation -/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
-- `haveI` is needed: the facts below are type-class instances for `rw`, not hypotheses.
set_option linter.style.haveILetI false

namespace PercLib.CriticalLRP.MarkedAtlas

open Finset
open PercLib.CriticalLRP.TreeExpansion (RTree LTon)
open PercLib.CriticalLRP.TreeExpansion.Real
open PercLib.CriticalLRP.TreeGraph (Conn prob BKIncreasing)

variable {V : Type*} [Fintype V] [DecidableEq V] {E : Type*} [Fintype E] [DecidableEq E]
variable {α : Type*} [DecidableEq α]

/-! ## The three atlas edges of a two-leaf shape -/

/-- The root branch point of the two-leaf shape `node (leaf a) (leaf b)`. -/
theorem srcPos_twoLeafEdgeA (a b : α) (φ : (RTree.node (RTree.leaf a) (RTree.leaf b)).IPos → V)
    (c : V) :
    srcPos (RTree.node (RTree.leaf a) (RTree.leaf b)) φ c (twoLeafEdgeA a b)
      = φ (twoLeafRoot a b) := rfl

theorem dstPos_twoLeafEdgeA (a b : α) (φ : (RTree.node (RTree.leaf a) (RTree.leaf b)).IPos → V)
    (y : α → V) :
    dstPos (RTree.node (RTree.leaf a) (RTree.leaf b)) φ y (twoLeafEdgeA a b) = y a := rfl

theorem srcPos_twoLeafEdgeB (a b : α) (φ : (RTree.node (RTree.leaf a) (RTree.leaf b)).IPos → V)
    (c : V) :
    srcPos (RTree.node (RTree.leaf a) (RTree.leaf b)) φ c (twoLeafEdgeB a b)
      = φ (twoLeafRoot a b) := rfl

theorem dstPos_twoLeafEdgeB (a b : α) (φ : (RTree.node (RTree.leaf a) (RTree.leaf b)).IPos → V)
    (y : α → V) :
    dstPos (RTree.node (RTree.leaf a) (RTree.leaf b)) φ y (twoLeafEdgeB a b) = y b := rfl

theorem srcPos_twoLeafEdgeRoot (a b : α)
    (φ : (RTree.node (RTree.leaf a) (RTree.leaf b)).IPos → V) (c : V) :
    srcPos (RTree.node (RTree.leaf a) (RTree.leaf b)) φ c (twoLeafEdgeRoot a b) = c := rfl

theorem dstPos_twoLeafEdgeRoot (a b : α)
    (φ : (RTree.node (RTree.leaf a) (RTree.leaf b)).IPos → V) (y : α → V) :
    dstPos (RTree.node (RTree.leaf a) (RTree.leaf b)) φ y (twoLeafEdgeRoot a b)
      = φ (twoLeafRoot a b) := rfl

/-! ## The branch point is the only internal vertex -/

/-- The internal-vertex type of a two-leaf shape is a singleton, so a function out of it is
determined by its value at the root branch point. -/
theorem ipos_twoLeaf_subsingleton (a b : α) :
    Subsingleton ((RTree.node (RTree.leaf a) (RTree.leaf b)).IPos) := by
  refine ⟨fun x y => ?_⟩
  rcases x with (x | x | ⟨⟩) <;> rcases y with (y | y | ⟨⟩)
  all_goals first | rfl | exact x.elim | exact y.elim

theorem fun_eq_const_root (a b : α)
    (φ : (RTree.node (RTree.leaf a) (RTree.leaf b)).IPos → V) :
    φ = fun _ => φ (twoLeafRoot a b) := by
  haveI := ipos_twoLeaf_subsingleton a b
  funext i
  exact congrArg φ (Subsingleton.elim i (twoLeafRoot a b))

theorem eval_root_injective (a b : α) :
    Function.Injective (fun φ : (RTree.node (RTree.leaf a) (RTree.leaf b)).IPos → V =>
      φ (twoLeafRoot a b)) := by
  intro φ ψ h
  have h' : φ (twoLeafRoot a b) = ψ (twoLeafRoot a b) := h
  rw [fun_eq_const_root a b φ, fun_eq_const_root a b ψ, h']

/-- **The sum over internal positions of a two-leaf shape is a sum over the vertex set.** -/
theorem sum_ipos_twoLeaf (a b : α)
    (F : ((RTree.node (RTree.leaf a) (RTree.leaf b)).IPos → V) → ℝ) :
    ∑ φ, F φ = ∑ u : V, F (fun _ => u) := by
  refine Fintype.sum_bijective
    (fun φ : (RTree.node (RTree.leaf a) (RTree.leaf b)).IPos → V =>
      φ (twoLeafRoot a b)) ⟨eval_root_injective a b, ?_⟩ F (fun u => F (fun _ => u)) ?_
  · intro u
    exact ⟨fun _ => u, rfl⟩
  · intro φ
    rw [fun_eq_const_root a b φ]

/-! ## The product over the three atlas edges -/

/-- The atlas-edge type of a two-leaf shape splits, along the production bijection
`Real.aedgeSumEquiv`, into the (singleton) atlas-edge types of the two leaves and the root edge;
each of the two leaves has a single atlas edge, so the product has exactly three factors. -/
theorem prod_aedge_twoLeaf_aux (a b : α)
    (F : AEdge (RTree.leaf a) ⊕ AEdge (RTree.leaf b) ⊕ PUnit → ℝ) :
    (∏ s, F s) = F (Sum.inl (Sum.inr ⟨⟩))
      * (F (Sum.inr (Sum.inl (Sum.inr ⟨⟩))) * F (Sum.inr (Sum.inr ⟨⟩))) := by
  have hsplit : (∏ s : AEdge (RTree.leaf a) ⊕ (AEdge (RTree.leaf b) ⊕ PUnit), F s)
      = (∏ x : AEdge (RTree.leaf a), F (Sum.inl x))
        * (∏ y : AEdge (RTree.leaf b) ⊕ PUnit, F (Sum.inr y)) :=
    Fintype.prod_sum_type F
  rw [hsplit]
  have hsplit2 : (∏ y : AEdge (RTree.leaf b) ⊕ PUnit, F (Sum.inr y))
      = (∏ y1 : AEdge (RTree.leaf b), F (Sum.inr (Sum.inl y1)))
        * (∏ y2 : PUnit, F (Sum.inr (Sum.inr y2))) :=
    Fintype.prod_sum_type (fun y => F (Sum.inr y))
  rw [hsplit2]
  haveI : Subsingleton (AEdge (RTree.leaf a)) := aedge_leaf_subsingleton a
  haveI : Subsingleton (AEdge (RTree.leaf b)) := aedge_leaf_subsingleton b
  have ha : (∏ x : AEdge (RTree.leaf a), F (Sum.inl x))
      = F (Sum.inl (Sum.inr ⟨⟩ : AEdge (RTree.leaf a))) :=
    Fintype.prod_subsingleton _ _
  have hb : (∏ y1 : AEdge (RTree.leaf b), F (Sum.inr (Sum.inl y1)))
      = F (Sum.inr (Sum.inl (Sum.inr ⟨⟩ : AEdge (RTree.leaf b)))) :=
    Fintype.prod_subsingleton _ _
  have hr : (∏ y2 : PUnit, F (Sum.inr (Sum.inr y2))) = F (Sum.inr (Sum.inr ⟨⟩)) :=
    Fintype.prod_unique _
  rw [ha, hb, hr]

/-- **The product of atlas-edge connection probabilities of a two-leaf shape is the three-point
diagram.** -/
theorem prod_aedge_twoLeaf (pr : E → ℝ) (ends : E → Sym2 V) (x : V) (y : α → V) (a b : α)
    (φ : (RTree.node (RTree.leaf a) (RTree.leaf b)).IPos → V) :
    ∏ e : AEdge (RTree.node (RTree.leaf a) (RTree.leaf b)),
        prob pr (ConnEvent ends y x (RTree.node (RTree.leaf a) (RTree.leaf b)) φ e)
      = pconn pr ends (φ (twoLeafRoot a b)) (y a)
        * (pconn pr ends (φ (twoLeafRoot a b)) (y b) * pconn pr ends x (φ (twoLeafRoot a b))) := by
  have h1 : ∏ e : AEdge (RTree.node (RTree.leaf a) (RTree.leaf b)),
        prob pr (ConnEvent ends y x (RTree.node (RTree.leaf a) (RTree.leaf b)) φ e)
      = ∏ s : AEdge (RTree.leaf a) ⊕ AEdge (RTree.leaf b) ⊕ PUnit,
        prob pr (ConnEvent ends y x (RTree.node (RTree.leaf a) (RTree.leaf b)) φ
          (aedgeSumInv s)) := by
    refine Fintype.prod_equiv (aedgeSumEquiv (RTree.leaf a) (RTree.leaf b))
      (fun e => prob pr (ConnEvent ends y x (RTree.node (RTree.leaf a) (RTree.leaf b)) φ e))
      (fun s => prob pr (ConnEvent ends y x (RTree.node (RTree.leaf a) (RTree.leaf b)) φ
        (aedgeSumInv s))) ?_
    intro e
    change prob pr (ConnEvent ends y x (RTree.node (RTree.leaf a) (RTree.leaf b)) φ e)
      = prob pr (ConnEvent ends y x (RTree.node (RTree.leaf a) (RTree.leaf b)) φ
        (aedgeSumInv (aedgeSumFun e)))
    rw [aedgeSumInv_fun]
  rw [h1, prod_aedge_twoLeaf_aux]
  rfl

/-! ## The marked diagram of a two-leaf shape -/

/-- **The marked diagram of the two-leaf shape `node (leaf a) (leaf b)` is the sum of the
three-point diagram over the branch point.** -/
theorem markDiag_twoLeaf (pr : E → ℝ) (ends : E → Sym2 V) (x : V) (y : α → V) (a b : α)
    {Z : Finset α}
    (h : (RTree.node (RTree.leaf a) (RTree.leaf b)).leaves.Nodup ∧
      (RTree.node (RTree.leaf a) (RTree.leaf b)).leaves.toFinset = Z) :
    markDiag pr ends x y (⟨RTree.node (RTree.leaf a) (RTree.leaf b), h⟩ : LTon α Z)
      = ∑ u : V, threePoint pr ends x u (y a) (y b) := by
  simp only [markDiag]
  rw [sum_ipos_twoLeaf]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [prod_aedge_twoLeaf]
  simp only [threePoint]
  ring

/-! ## The two labelled shapes at `p = 1` -/

/-- The first `p = 1` shape: the unmarked arm on the left. -/
theorem markShapeP1a_ne_markShapeP1b : markShapeP1a ≠ markShapeP1b := by
  intro h'
  have h2 := congrArg Subtype.val h'
  simp only [markShapeP1a, markShapeP1b] at h2
  have h3 := (RTree.node.injEq (RTree.leaf (Sum.inl 0)) (RTree.leaf (markLabelOf (p := 1)))
    (RTree.leaf (markLabelOf (p := 1))) (RTree.leaf (Sum.inl 0))).mp h2
  exact absurd h3.1 (by simp [markLabelOf])

/-- **Every labelled shape at `p = 1` is one of the two orderings of the two labels.** -/
theorem eq_markShapeP1 (t : LTon (MarkLabel 1) (markLabels 1)) :
    t = markShapeP1a ∨ t = markShapeP1b := by
  obtain ⟨u, hu⟩ := t
  have hnum : u.numLeaves = 2 := by
    rw [RTree.numLeaves, ← List.toFinset_card_of_nodup hu.1, hu.2]
    simp [markLabels]
  obtain ⟨a, b, hab⟩ := eq_node_leaf_leaf_of_numLeaves_eq_two u hnum
  subst hab
  have hnd : ([a, b] : List (MarkLabel 1)).Nodup := by simpa [RTree.leaves_node] using hu.1
  have hne : a ≠ b := by
    intro h
    exact (List.nodup_cons.mp hnd).1 (by simp [h])
  rcases a with (i | ⟨⟩) <;> rcases b with (j | ⟨⟩)
  · have hi : i = 0 := Subsingleton.elim i 0
    have hj : j = 0 := Subsingleton.elim j 0
    subst hi
    subst hj
    exact absurd rfl hne
  · have hi : i = 0 := Subsingleton.elim i 0
    subst hi
    exact Or.inl (Subtype.ext rfl)
  · have hj : j = 0 := Subsingleton.elim j 0
    subst hj
    exact Or.inr (Subtype.ext rfl)
  · exact absurd rfl hne

/-- **The `p = 1` shape sum is twice the three-point diagram.** -/
theorem sum_markDiag_p1 (pr : E → ℝ) (ends : E → Sym2 V) (x : V) (f : Fin 1 → V) (w : V) :
    (∑ t : LTon (MarkLabel 1) (markLabels 1), markDiag pr ends x (markTerm f w) t)
      = 2 * ∑ u : V, threePoint pr ends x u (f 0) w := by
  have huniv : (Finset.univ : Finset (LTon (MarkLabel 1) (markLabels 1)))
      = {markShapeP1a, markShapeP1b} := by
    symm
    rw [Finset.eq_univ_iff_forall]
    intro t
    simp only [Finset.mem_insert, Finset.mem_singleton]
    exact eq_markShapeP1 t
  rw [huniv, Finset.sum_insert (by simp [markShapeP1a_ne_markShapeP1b]), Finset.sum_singleton]
  have hA : markDiag pr ends x (markTerm f w) markShapeP1a
      = ∑ u : V, threePoint pr ends x u (f 0) w := by
    have h := markDiag_twoLeaf (pr := pr) (ends := ends) (x := x) (y := markTerm f w)
      (a := Sum.inl 0) (b := markLabelOf (p := 1)) (Z := markLabels 1) markShapeP1a.2
    simpa [markShapeP1a] using h
  have hB : markDiag pr ends x (markTerm f w) markShapeP1b
      = ∑ u : V, threePoint pr ends x u (f 0) w := by
    have h := markDiag_twoLeaf (pr := pr) (ends := ends) (x := x) (y := markTerm f w)
      (a := markLabelOf (p := 1)) (b := Sum.inl 0) (Z := markLabels 1) markShapeP1b.2
    have h1 : markDiag pr ends x (markTerm f w) markShapeP1b
        = ∑ u : V, threePoint pr ends x u w (f 0) := by
      simpa [markShapeP1b] using h
    rw [h1]
    refine Finset.sum_congr rfl fun u _ => ?_
    simp only [threePoint]
    ring
  rw [hA, hB]
  ring

/-- **The `p = 1` marked atlas bound.**  The probability that the root `x` is connected to the
single arm `f 0` and to the mark `w` is at most twice the sum over branch points `u` of
`P(x↔u) P(u↔f 0) P(u↔w)`. -/
theorem prob_markedBase_le_threePoint_p1 (pr : E → ℝ) (hp : ∀ e, 0 ≤ pr e)
    (hp1 : ∀ e, pr e ≤ 1) (hBK : BKIncreasing pr) (ends : E → Sym2 V) (x : V) (f : Fin 1 → V)
    (w : V) :
    prob pr (MarkedBaseEvent ends x f w) ≤ 2 * ∑ u : V, threePoint pr ends x u (f 0) w := by
  refine le_trans (prob_markedBase_le_shapeSum pr hp hp1 hBK ends x f w) ?_
  exact le_of_eq (sum_markDiag_p1 pr ends x f w)

/-! ## Summing the ordinary (unmarked) leaf values at `p = 1` -/

/-- Summing over the single arm position `f : Fin 1 → V` is summing over `V`. -/
theorem sum_fin_one (F : V → ℝ) : (∑ f : Fin 1 → V, F (f 0)) = ∑ v : V, F v := by
  refine Fintype.sum_equiv (Equiv.funUnique (Fin 1) V) (fun f : Fin 1 → V => F (f 0))
    (fun v => F v) ?_
  intro f
  rfl

/-- **The `p = 1` diagram with the ordinary leaf summed and the mark pinned.**  Summing the
marked diagram over the single arm position `f 0` reduces it, through the row sum
`rowSum u = ∑_v P(u↔v)` at the branch point, to a coefficient that depends on the law only
through the root-to-branch probability, the branch-to-mark probability, and `rowSum u`: the
finite analogue of `T^ℓ(x,w) χ^(2p+1-ℓ)` at `p = 1`, `ℓ = 2`. -/
theorem sum_f_markDiag_p1 (pr : E → ℝ) (ends : E → Sym2 V) (x : V) (w : V) :
    (∑ f : Fin 1 → V, ∑ t : LTon (MarkLabel 1) (markLabels 1),
        markDiag pr ends x (markTerm f w) t)
      = 2 * ∑ u : V, pconn pr ends x u * pconn pr ends u w * rowSum pr ends u := by
  have h1 : ∀ f : Fin 1 → V, (∑ t : LTon (MarkLabel 1) (markLabels 1),
      markDiag pr ends x (markTerm f w) t) = 2 * ∑ u : V, threePoint pr ends x u (f 0) w :=
    fun f => sum_markDiag_p1 pr ends x f w
  simp only [h1]
  rw [← Finset.mul_sum, Finset.sum_comm]
  refine congrArg (fun z => 2 * z) ?_
  refine Finset.sum_congr rfl fun u _ => ?_
  have hsum : (∑ f : Fin 1 → V, pconn pr ends u (f 0)) = rowSum pr ends u :=
    sum_fin_one (fun v => pconn pr ends u v)
  calc (∑ f : Fin 1 → V, threePoint pr ends x u (f 0) w)
      = ∑ f : Fin 1 → V,
          (pconn pr ends x u * pconn pr ends u w) * pconn pr ends u (f 0) := by
        refine Finset.sum_congr rfl fun f _ => ?_
        simp only [threePoint]
        ring
    _ = (pconn pr ends x u * pconn pr ends u w) * ∑ f : Fin 1 → V, pconn pr ends u (f 0) := by
        rw [Finset.mul_sum]
    _ = pconn pr ends x u * pconn pr ends u w * rowSum pr ends u := by
        rw [hsum]

/-- **The `p = 1` marked moment bound**, with the single ordinary leaf summed and the mark
pinned at `w`. -/
theorem sum_prob_markedBase_le_rowSum_p1 (pr : E → ℝ) (hp : ∀ e, 0 ≤ pr e)
    (hp1 : ∀ e, pr e ≤ 1) (hBK : BKIncreasing pr) (ends : E → Sym2 V) (x : V) (w : V) :
    (∑ f : Fin 1 → V, prob pr (MarkedBaseEvent ends x f w))
      ≤ 2 * ∑ u : V, pconn pr ends x u * pconn pr ends u w * rowSum pr ends u := by
  have h1 : (∑ f : Fin 1 → V, prob pr (MarkedBaseEvent ends x f w))
      ≤ ∑ f : Fin 1 → V, ∑ t : LTon (MarkLabel 1) (markLabels 1),
          markDiag pr ends x (markTerm f w) t :=
    Finset.sum_le_sum fun f _ => prob_markedBase_le_shapeSum pr hp hp1 hBK ends x f w
  rw [sum_f_markDiag_p1] at h1
  exact h1

/-! ## The marked depth at `p = 1` and the depth-decomposed bound -/

/-- Every leaf of a two-leaf shape hangs at depth `2`. -/
theorem depth_twoLeaf (a b : α) (q : (RTree.node (RTree.leaf a) (RTree.leaf b)).LeafPos) :
    RTree.depth (RTree.node (RTree.leaf a) (RTree.leaf b)) q = 2 := by
  rcases q with (q | q) <;> rfl

/-- **The marked depth is `2` at `p = 1`**: the mark is a child of the root branch point. -/
theorem markDepth_p1_eq_two (t : LTon (MarkLabel 1) (markLabels 1))
    (hc : markLabelOf (p := 1) ∈ markLabels 1) :
    markDepth (markLabelOf (p := 1)) t hc = 2 := by
  obtain ⟨u, hu⟩ := t
  have hnum : u.numLeaves = 2 := by
    rw [RTree.numLeaves, ← List.toFinset_card_of_nodup hu.1, hu.2]
    simp [markLabels]
  obtain ⟨a, b, hab⟩ := eq_node_leaf_leaf_of_numLeaves_eq_two u hnum
  subst hab
  rw [markDepth]
  exact depth_twoLeaf a b _

theorem markCoeff_p1_zero (pr : E → ℝ) (ends : E → Sym2 V) (x : V) (f : Fin 1 → V) (w : V) :
    markCoeff pr ends x (markTerm f w) (markLabelOf (p := 1)) (markLabelOf_mem 1) 0 = 0 := by
  rw [markCoeff]
  have hempty : (Finset.univ.filter (fun t : LTon (MarkLabel 1) (markLabels 1) =>
      markDepth (markLabelOf (p := 1)) t (markLabelOf_mem 1) = 0)) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro t _
    rw [markDepth_p1_eq_two t]
    omega
  rw [hempty, Finset.sum_empty]

theorem markCoeff_p1_one (pr : E → ℝ) (ends : E → Sym2 V) (x : V) (f : Fin 1 → V) (w : V) :
    markCoeff pr ends x (markTerm f w) (markLabelOf (p := 1)) (markLabelOf_mem 1) 1 = 0 := by
  rw [markCoeff]
  have hempty : (Finset.univ.filter (fun t : LTon (MarkLabel 1) (markLabels 1) =>
      markDepth (markLabelOf (p := 1)) t (markLabelOf_mem 1) = 1)) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro t _
    rw [markDepth_p1_eq_two t]
    omega
  rw [hempty, Finset.sum_empty]

/-- At `p = 1` every shape has marked depth `2`, so the depth-`2` coefficient is the whole
labelled-shape sum. -/
theorem markCoeff_p1_two (pr : E → ℝ) (ends : E → Sym2 V) (x : V) (f : Fin 1 → V) (w : V) :
    markCoeff pr ends x (markTerm f w) (markLabelOf (p := 1)) (markLabelOf_mem 1) 2
      = ∑ t : LTon (MarkLabel 1) (markLabels 1), markDiag pr ends x (markTerm f w) t := by
  rw [markCoeff]
  have hfilter : (Finset.univ.filter (fun t : LTon (MarkLabel 1) (markLabels 1) =>
      markDepth (markLabelOf (p := 1)) t (markLabelOf_mem 1) = 2)) = Finset.univ := by
    refine Finset.filter_true_of_mem ?_
    intro t _
    rw [markDepth_p1_eq_two t]
  rw [hfilter]

/-- **The finite marked diagram expression at `p = 1`**: the depth-decomposed bound
`markedBound` evaluates to twice the three-point diagram. -/
theorem markedBound_p1 (pr : E → ℝ) (ends : E → Sym2 V) (x : V) (f : Fin 1 → V) (w : V) :
    markedBound pr ends x f w = 2 * ∑ u : V, threePoint pr ends x u (f 0) w := by
  rw [markedBound, markBound, markLabels_card]
  rw [show (1 + 1 + 1 : ℕ) = 2 + 1 from rfl, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_one, markCoeff_p1_zero, markCoeff_p1_one, markCoeff_p1_two,
    sum_markDiag_p1]
  ring

/-- **The `p = 1` marked atlas bound through the depth-decomposed expression.**  This is
`prob_markedBase_le_markedBound` with its finite marked diagram expression evaluated. -/
theorem prob_markedBase_le_markedBound_p1 (pr : E → ℝ) (hp : ∀ e, 0 ≤ pr e)
    (hp1 : ∀ e, pr e ≤ 1) (hBK : BKIncreasing pr) (ends : E → Sym2 V) (x : V) (f : Fin 1 → V)
    (w : V) :
    prob pr (MarkedBaseEvent ends x f w) ≤ 2 * ∑ u : V, threePoint pr ends x u (f 0) w := by
  have h := prob_markedBase_le_markedBound pr hp hp1 hBK ends x f w
  rwa [markedBound_p1] at h

end PercLib.CriticalLRP.MarkedAtlas
