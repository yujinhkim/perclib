/- Integrated from independently rebuilt Ultramath work.
Production base 50c2eed0682a7e1b078ae771dbef463ebe00701d.
Scratch source: repository-root .ultramath/.
-/

/-
The weight/positions bridge: the atlas-side weight equals the ordinary tree weight.
-/
module

public import PercLib.CriticalLRP.TreeExpansion.AtlasRealization.WeightBridge.Defs
public import PercLib.CriticalLRP.TreeExpansion.Weight
public import PercLib.CriticalLRP.Correlation.I417.Base.Marked

/-!
# The bridge from atlas edges to tree edges

`AtlasRealization.Cover.prob_le_sum_shapes` bounds the probability that a root is connected to
all terminals of a finite label set `Z` by

  `∑ t : LTon α Z, ∑ φ : t.IPos → V, ∏ e : AEdge t, P(srcPos t φ v e ↔ dstPos t φ y e)`,

a sum over shapes, internal positions and the `2p - 1` **atlas** edges of the shape.  The source
then regroups this as a sum of **tree** weights.  This file proves the identity that performs
the regrouping.

## Why there is no double counting

The atlas `AEdge t` of a composite shape `node l r` splits (`aedgeSumFun`) into the atlas edges
of `l`, the atlas edges of `r`, and one new root edge.  The root edge of the **whole** shape is
the edge `c → rootPos`; the down edge of the root internal vertex into the root of the child `l`
is the **root edge of `l`**, i.e. the piece of `AEdge l` that carries `srcPos = w` where `w` is
the position of the root internal vertex.  `aedgeSumFun` sends these two to different summands
(`Sum.inr (Sum.inr _)` and `Sum.inl (Sum.inr _)`), so every atlas edge of `node l r` belongs to
exactly one of the three factors, and the child's root edge occurs exactly once — inside the
child's factor, with `c` replaced by `w`.  This is exactly the recursion

  `wt k (node l r) y v = ∑ w, k v w * wt k l y w * wt k r y w`,

whose factor `k v w` is the parent edge and whose two remaining factors each begin with their own
root edge.  Hence the two sides agree term by term, with no repeated-path correction and no
missing factor, for **every** shape and **every** label map — not only up to a constant.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

open scoped ENNReal

namespace PercLib.CriticalLRP.TreeExpansion.Real

open Finset

variable {α : Type*} [DecidableEq α]

/-! ## Splitting a product over the atlas edges of a composite shape -/

section ProdSplit

variable {M : Type*} [CommMonoid M]
variable {W : Type*}

/-- The atlas of a leaf has a single edge, the root edge. -/
theorem prod_aedge_leaf (a : α) (F : AEdge (RTree.leaf a) → M) :
    (∏ e, F e) = F (Sum.inr PUnit.unit) := by
  refine Finset.prod_eq_single (a := (Sum.inr PUnit.unit : AEdge (RTree.leaf a))) ?_ ?_
  · intro e _ he
    rcases e with (⟨u, b⟩ | x)
    · exact Empty.elim u
    · exact absurd rfl he
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- **The product over the atlas edges of `node l r` splits into the three pieces.**  The left
child's root edge carries the new vertex `w` as its *source*, the right child's likewise, and the
root edge of the composite carries `c → w`.  Each atlas edge of the composite occurs in exactly
one of the three factors. -/
theorem prod_aedge_node (k : W → W → M) (l r : RTree α) (y : α → W) (c w : W)
    (φL : l.IPos → W) (φR : r.IPos → W) :
    (∏ e : AEdge (RTree.node l r),
        k (srcPos (RTree.node l r) (pushPhi w φL φR) c e)
          (dstPos (RTree.node l r) (pushPhi w φL φR) y e))
      = k c w * (∏ a : AEdge l, k (srcPos l φL w a) (dstPos l φL y a))
          * (∏ b : AEdge r, k (srcPos r φR w b) (dstPos r φR y b)) := by
  classical
  set K : AEdge (RTree.node l r) → M := fun e =>
    k (srcPos (RTree.node l r) (pushPhi w φL φR) c e)
      (dstPos (RTree.node l r) (pushPhi w φL φR) y e) with hK
  have step1 : (∏ e : AEdge (RTree.node l r), K e)
      = ∏ s : AEdge l ⊕ AEdge r ⊕ PUnit, K (aedgeSumInv s) :=
    Fintype.prod_equiv (aedgeSumEquiv l r) K (fun s => K (aedgeSumInv s))
      (fun e => by
        have h : (aedgeSumEquiv l r) e = aedgeSumFun e := rfl
        rw [h, aedgeSumInv_fun])
  have hA : (∏ a : AEdge l, K (aedgeSumInv (Sum.inl a)))
      = ∏ a : AEdge l, k (srcPos l φL w a) (dstPos l φL y a) := by
    refine Finset.prod_congr rfl fun a _ => ?_
    simp only [hK]
    rw [srcPos_piece_inl, dstPos_piece_inl]
  have hB : (∏ b : AEdge r, K (aedgeSumInv (Sum.inr (Sum.inl b))))
      = ∏ b : AEdge r, k (srcPos r φR w b) (dstPos r φR y b) := by
    refine Finset.prod_congr rfl fun b _ => ?_
    simp only [hK]
    rw [srcPos_piece_inr_inl, dstPos_piece_inr_inl]
  have hC : K (aedgeSumInv (Sum.inr (Sum.inr PUnit.unit))) = k c w := by
    simp only [hK]
    rw [srcPos_piece_none, dstPos_piece_none]
  have step2 : (∏ s : AEdge l ⊕ AEdge r ⊕ PUnit, K (aedgeSumInv s))
      = (∏ a : AEdge l, k (srcPos l φL w a) (dstPos l φL y a))
          * (∏ b : AEdge r, k (srcPos r φR w b) (dstPos r φR y b)) * k c w := by
    rw [Fintype.prod_sum_type (f := fun s : AEdge l ⊕ AEdge r ⊕ PUnit => K (aedgeSumInv s))]
    rw [Fintype.prod_sum_type
      (f := fun s : AEdge r ⊕ PUnit => K (aedgeSumInv (Sum.inr s)))]
    rw [Fintype.prod_unique (f := fun x : PUnit => K (aedgeSumInv (Sum.inr (Sum.inr x))))]
    rw [hA, hB, hC]
    ac_rfl
  rw [step1, step2]
  ac_rfl

end ProdSplit

/-! ## Reindexing the sum over the internal positions -/

section SumReindex

variable {W : Type*} [Fintype W]
variable {M : Type*} [AddCommMonoid M]

/-- There is only one function `Empty → W`. -/
theorem sum_pempty_arrow (f : (Empty → W) → M) :
    (∑ φ : Empty → W, f φ) = f (fun e => e.elim) := by
  refine Finset.sum_eq_single (fun e : Empty => e.elim) ?_ ?_
  · intro b _ hb
    exact absurd (funext fun e => e.elim) hb
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- **Reindexing**: the internal positions of `node l r` are the internal positions of `l`, the
internal positions of `r`, and the position of the new root vertex.  This is the index-level
statement behind `aedgeSumFun`: the value at the new root vertex is passed to the two pieces as
their *root leaf* vertex, which is what makes the recursion of `wt` come out. -/
theorem sum_ipos_node {l r : RTree α} (G : ((RTree.node l r).IPos → W) → M) :
    (∑ φ : (RTree.node l r).IPos → W, G φ)
      = ∑ φL : l.IPos → W, ∑ φR : r.IPos → W, ∑ w : W, G (pushPhi w φL φR) := by
  change (∑ φ : (l.IPos ⊕ r.IPos ⊕ PUnit) → W, G φ)
      = ∑ φL : l.IPos → W, ∑ φR : r.IPos → W, ∑ w : W, G (pushPhi w φL φR)
  refine Eq.trans (Fintype.sum_equiv (Equiv.sumArrowEquivProdArrow l.IPos (r.IPos ⊕ PUnit) W) G
    (fun p : (l.IPos → W) × ((r.IPos ⊕ PUnit) → W) => G (fun i => Sum.elim p.1 p.2 i))
    (fun φ => by congr 1; funext i; rcases i with u | v | ⟨⟩ <;> rfl)) ?_
  rw [Fintype.sum_prod_type]
  simp only []
  refine Finset.sum_congr rfl fun φL _ => ?_
  refine Eq.trans (Fintype.sum_equiv (Equiv.sumArrowEquivProdArrow r.IPos PUnit W)
    (fun z : (r.IPos ⊕ PUnit) → W => G (fun i => Sum.elim φL z i))
    (fun q : (r.IPos → W) × (PUnit → W) =>
      G (fun i => Sum.elim φL (fun j => Sum.elim q.1 q.2 j) i))
    (fun z => by congr 1; funext i; rcases i with u | v | ⟨⟩ <;> rfl)) ?_
  rw [Fintype.sum_prod_type]
  simp only []
  refine Finset.sum_congr rfl fun φR _ => ?_
  refine Eq.trans (Fintype.sum_equiv (Equiv.funUnique PUnit W)
    (fun x : PUnit → W => G (fun i => Sum.elim φL (fun j => Sum.elim φR x j) i))
    (fun w : W => G (fun i => Sum.elim φL (fun j => Sum.elim φR (fun _ => w) j) i))
    (fun x => by congr 1)) ?_
  refine Finset.sum_congr rfl fun w _ => ?_
  congr 1
  funext i
  rcases i with u | v | ⟨⟩ <;> rfl

end SumReindex

/-! ## The finite bridge -/

section Finite

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Threefold factorisation: the `w`-dependence of the two child products separates. -/
theorem sum_triple_factor {ι κ : Type*} [Fintype ι] [Fintype κ]
    (f : V → ℝ) (A : ι → V → ℝ) (B : κ → V → ℝ) :
    (∑ i : ι, ∑ j : κ, ∑ w : V, f w * A i w * B j w)
      = ∑ w : V, f w * ((∑ i, A i w) * (∑ j, B j w)) := by
  have hkey : ∀ w : V, f w * ((∑ i, A i w) * (∑ j, B j w))
      = ∑ i : ι, ∑ j : κ, f w * A i w * B j w := by
    intro w
    rw [Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [mul_assoc]
  have hstep : (∑ i : ι, ∑ j : κ, ∑ w : V, f w * A i w * B j w)
      = ∑ i : ι, ∑ w : V, ∑ j : κ, f w * A i w * B j w :=
    Finset.sum_congr rfl fun i _ => Finset.sum_comm
  rw [hstep, Finset.sum_comm]
  exact Finset.sum_congr rfl fun w _ => (hkey w).symm

/-- The atlas-side weight of a leaf shape. -/
theorem posSumWt_leaf (k : V → V → ℝ) (a : α) (y : α → V) (c : V) :
    posSumWt k (RTree.leaf a) y c = k c (y a) := by
  rw [posSumWt]
  change (∑ φ : Empty → V, ∏ e : AEdge (RTree.leaf a),
    k (srcPos (RTree.leaf a) φ c e) (dstPos (RTree.leaf a) φ y e)) = k c (y a)
  rw [sum_pempty_arrow, prod_aedge_leaf a]
  rfl

/-- **The one-step recursion of the atlas-side weight.**  This is the *same* recursion as the
ordinary tree weight `RTree.wtL`: the new root vertex `w` is summed over once, it is the source
of both children's root edges and the target of the parent edge `c → w`. -/
theorem posSumWt_node (k : V → V → ℝ) (l r : RTree α) (y : α → V) (c : V) :
    posSumWt k (RTree.node l r) y c
      = ∑ w : V, k c w * posSumWt k l y w * posSumWt k r y w := by
  rw [posSumWt,
    sum_ipos_node (G := fun φ =>
      ∏ e : AEdge (RTree.node l r),
        k (srcPos (RTree.node l r) φ c e) (dstPos (RTree.node l r) φ y e))]
  refine Eq.trans (Finset.sum_congr rfl fun φL _ => Finset.sum_congr rfl fun φR _ =>
    Finset.sum_congr rfl fun w _ => prod_aedge_node k l r y c w φL φR) ?_
  rw [sum_triple_factor
    (A := fun (φL : l.IPos → V) (w : V) =>
      ∏ a : AEdge l, k (srcPos l φL w a) (dstPos l φL y a))
    (B := fun (φR : r.IPos → V) (w : V) =>
      ∏ b : AEdge r, k (srcPos r φR w b) (dstPos r φR y b))
    (f := fun w : V => k c w)]
  exact Finset.sum_congr rfl fun w _ => by simp only [posSumWt]; rw [mul_assoc]

/-- **The weight/positions bridge** (finite vertex set, real kernel): for every rooted binary
shape `t`, every labelling `y` of the leaves and every vertex `c` at the root leaf, the sum over
the internal positions of the product of `k` over the `2p - 1` atlas edges of `t` equals the
ordinary tree weight of `t`. -/
theorem posSumWt_eq_wtL (k : V → V → ℝ) (t : RTree α) (y : α → V) (c : V) :
    posSumWt k t y c = RTree.wtL k t y c := by
  induction t generalizing c with
  | leaf a => rw [posSumWt_leaf, RTree.wtL_leaf]
  | node l r ihl ihr =>
      rw [posSumWt_node, RTree.wtL_node]
      exact Finset.sum_congr rfl fun w _ => by rw [ihl w, ihr w]

/-- The bridge in the leaf-position form of `RTree.wt`. -/
theorem posSumWt_eq_wt (k : V → V → ℝ) (t : RTree α) (y : α → V) (c : V) :
    posSumWt k t y c = RTree.wt k t (fun p => y (RTree.leafOfPos t p)) c := by
  rw [posSumWt_eq_wtL, ← RTree.wt_eq_wtL]

end Finite

/-! ## The infinite bridge, in `ℝ≥0∞` -/

section Infinite

variable {W : Type*}

/-- There is only one function `Empty → W`. -/
theorem tsum_pempty_arrow (f : (Empty → W) → ℝ≥0∞) :
    (∑' φ : Empty → W, f φ) = f (fun e => e.elim) := by
  refine tsum_eq_single (fun e : Empty => e.elim) ?_
  intro b hb
  exact absurd (Subsingleton.elim b _) hb

/-- Three nested `tsum`s commute. -/
theorem tsum_three_comm {ι κ : Type*} (F : ι → κ → W → ℝ≥0∞) :
    (∑' i : ι, ∑' j : κ, ∑' w : W, F i j w)
      = ∑' w : W, ∑' i : ι, ∑' j : κ, F i j w := by
  have h1 : (∑' i : ι, ∑' j : κ, ∑' w : W, F i j w)
      = ∑' i : ι, ∑' w : W, ∑' j : κ, F i j w :=
    tsum_congr fun i => ENNReal.tsum_comm
  have h2 : (∑' i : ι, ∑' w : W, ∑' j : κ, F i j w)
      = ∑' w : W, ∑' i : ι, ∑' j : κ, F i j w := ENNReal.tsum_comm
  rw [h1, h2]

/-- The `Sum.elim` form of `pushPhi`, as a function. -/
theorem elim_pushPhi {l r : RTree α} (a : l.IPos → W) (b : r.IPos → W) (w : W) :
    (fun i => Sum.elim a (fun j => Sum.elim b (fun _ => w) j) i) = pushPhi w a b := by
  funext i
  rcases i with u | v | ⟨⟩ <;> rfl

/-- Reindexing the internal positions of a composite shape, for `ℝ≥0∞`-valued `tsum`s (so with
no countability or finiteness assumption on the vertex set). -/
theorem tsum_ipos_node {l r : RTree α} (G : ((RTree.node l r).IPos → W) → ℝ≥0∞) :
    (∑' φ : (RTree.node l r).IPos → W, G φ)
      = ∑' φL : l.IPos → W, ∑' φR : r.IPos → W, ∑' w : W, G (pushPhi w φL φR) := by
  have hsplit : ∀ φ : (l.IPos ⊕ r.IPos ⊕ PUnit) → W,
      G φ = (fun a z => G (fun i => Sum.elim a z i))
        (fun u => φ (Sum.inl u)) (fun p => φ (Sum.inr p)) := by
    intro φ
    congr 1
    funext i
    rcases i with u | v | ⟨⟩ <;> rfl
  have hgen : ∀ (a : l.IPos → W) (z : (r.IPos ⊕ PUnit) → W),
      G (fun i => Sum.elim a z i)
        = (fun (b : r.IPos → W) (x : PUnit → W) =>
            G (fun i => Sum.elim a (fun j => Sum.elim b x j) i))
          (fun v => z (Sum.inl v)) (fun p => z (Sum.inr p)) := by
    intro a z
    congr 1
    funext i
    rcases i with u | v | ⟨⟩ <;> rfl
  calc (∑' φ : (RTree.node l r).IPos → W, G φ)
      = ∑' φ : (l.IPos ⊕ r.IPos ⊕ PUnit) → W, G φ := rfl
    _ = ∑' φ : (l.IPos ⊕ (r.IPos ⊕ PUnit)) → W,
          (fun a z => G (fun i => Sum.elim a z i))
            (fun u => φ (Sum.inl u)) (fun p => φ (Sum.inr p)) := tsum_congr hsplit
    _ = ∑' a : l.IPos → W, ∑' z : (r.IPos ⊕ PUnit) → W, G (fun i => Sum.elim a z i) :=
          I417Base.tsum_sumArrow (F := fun a z => G (fun i => Sum.elim a z i))
    _ = ∑' a : l.IPos → W, ∑' b : r.IPos → W, ∑' w : W, G (pushPhi w a b) := by
          refine tsum_congr fun (a : l.IPos → W) => ?_
          refine Eq.trans (tsum_congr fun z => hgen a z) ?_
          refine Eq.trans (I417Base.tsum_sumArrow
            (F := fun (b : r.IPos → W) (x : PUnit → W) =>
              G (fun i => Sum.elim a (fun j => Sum.elim b x j) i))) ?_
          refine tsum_congr fun (b : r.IPos → W) => ?_
          refine Eq.trans (tsum_congr fun (x : PUnit → W) =>
            congrArg G (elim_pushPhi a b (x ⟨⟩))) ?_
          exact Equiv.tsum_eq (Equiv.funUnique PUnit W) (fun w : W => G (pushPhi w a b))

/-- The atlas-side weight of a leaf shape, `ℝ≥0∞`-valued. -/
theorem posSumWtE_leaf (k : W → W → ℝ≥0∞) (a : α) (y : α → W) (c : W) :
    posSumWtE k (RTree.leaf a) y c = k c (y a) := by
  rw [posSumWtE]
  change (∑' φ : Empty → W, ∏ e : AEdge (RTree.leaf a),
    k (srcPos (RTree.leaf a) φ c e) (dstPos (RTree.leaf a) φ y e)) = k c (y a)
  rw [tsum_pempty_arrow, prod_aedge_leaf a]
  rfl

/-- The one-step recursion of the `ℝ≥0∞`-valued atlas-side weight. -/
theorem posSumWtE_node (k : W → W → ℝ≥0∞) (l r : RTree α) (y : α → W) (c : W) :
    posSumWtE k (RTree.node l r) y c
      = ∑' w : W, k c w * posSumWtE k l y w * posSumWtE k r y w := by
  rw [posSumWtE,
    tsum_ipos_node (G := fun φ =>
      ∏ e : AEdge (RTree.node l r),
        k (srcPos (RTree.node l r) φ c e) (dstPos (RTree.node l r) φ y e))]
  have stepA : (∑' φL : l.IPos → W, ∑' φR : r.IPos → W, ∑' w : W,
        ∏ e : AEdge (RTree.node l r),
          k (srcPos (RTree.node l r) (pushPhi w φL φR) c e)
            (dstPos (RTree.node l r) (pushPhi w φL φR) y e))
      = ∑' φL : l.IPos → W, ∑' φR : r.IPos → W, ∑' w : W,
          k c w * (∏ a : AEdge l, k (srcPos l φL w a) (dstPos l φL y a))
            * (∏ b : AEdge r, k (srcPos r φR w b) (dstPos r φR y b)) :=
    tsum_congr fun φL => tsum_congr fun φR => tsum_congr fun w =>
      prod_aedge_node k l r y c w φL φR
  rw [stepA,
    tsum_three_comm (F := fun (φL : l.IPos → W) (φR : r.IPos → W) (w : W) =>
      k c w * (∏ a : AEdge l, k (srcPos l φL w a) (dstPos l φL y a))
        * (∏ b : AEdge r, k (srcPos r φR w b) (dstPos r φR y b)))]
  refine tsum_congr fun (w : W) => ?_
  have hm1 : (∑' φL : l.IPos → W, ∑' φR : r.IPos → W,
        (k c w * (∏ a : AEdge l, k (srcPos l φL w a) (dstPos l φL y a)))
          * (∏ b : AEdge r, k (srcPos r φR w b) (dstPos r φR y b)))
      = ∑' φL : l.IPos → W,
          (k c w * (∏ a : AEdge l, k (srcPos l φL w a) (dstPos l φL y a)))
            * (∑' φR : r.IPos → W,
                ∏ b : AEdge r, k (srcPos r φR w b) (dstPos r φR y b)) :=
    tsum_congr fun φL => ENNReal.tsum_mul_left
  rw [hm1, ENNReal.tsum_mul_right, ENNReal.tsum_mul_left]
  rfl

/-- **The weight/positions bridge for `ℝ≥0∞` and an arbitrary vertex set**: the
`2p - 1`-fold atlas product summed over the internal positions is the marked diagram weight
`I417Base.wtE` of the same shape.  This is the form needed for the countable canonical model of
Lemma I.4.17, where `V` is infinite and the two-point function may take the value `⊤`. -/
theorem posSumWtE_eq_wtE (k : W → W → ℝ≥0∞) (t : RTree α) (y : α → W) (c : W) :
    posSumWtE k t y c = I417Base.wtE k t (fun p => y (RTree.leafOfPos t p)) c := by
  induction t generalizing c with
  | leaf a =>
      rw [posSumWtE_leaf]
      rfl
  | node l r ihl ihr =>
      rw [posSumWtE_node]
      refine tsum_congr fun w => ?_
      rw [ihl w, ihr w]
      rfl

end Infinite

end PercLib.CriticalLRP.TreeExpansion.Real
