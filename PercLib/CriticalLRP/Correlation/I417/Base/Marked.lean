/- Integrated from independently rebuilt Ultramath work.
Production base 38371c8354fd1b28220794b007003710ea155dea.
Scratch source: ../../.ultramath/smwvlmbqa/m6/Marked.lean; module paths rewritten.
-/

module

public import PercLib.CriticalLRP.Correlation.I417.Base.Defs

/-!
# The marked-leaf diagram value depends only on the marked path length

This file proves the diagram identity that the proof of Lemma I.4.17 in
Hutchcroft, *Critical long-range percolation I* (arXiv:2508.18807v1, p. 45) uses silently:

> "In each case, `C_{p,q,ℓ}` counts the number of diagrams in the bound in which the path
> connecting `x` and `y` has length `ℓ`."

The main result `tsum_wtE_marked` states that a rooted binary tree diagram on `p+1` leaves
with **one** leaf pinned at `w` (the mark), all other leaves and all internal vertices summed
over, is worth

  `χ^(2p+1-ℓ) · T^ℓ(x,w)`,  `χ` the constant cluster volume, `ℓ` the depth of the marked leaf,

**independently of the shape of the tree** — which is exactly why the whole marked family
collapses to the finite polygon/two-point matrix sum `∑_ℓ C_{p,ℓ} χ^(2p+1-ℓ) T^ℓ(x,w)` with
integer coefficients `C_{p,ℓ}` the marked-leaf-depth counts.  Its companion
`pathW_eq_iterPow` identifies the marked path weight with the `ℓ`-fold power of the kernel.

Everything here is unconditional: the only hypothesis is that the kernel `k` has a
**constant** row sum `χ` (the abstract form of transitivity, `E|K_v| = E|K|`), and the model
side is `ℝ≥0∞`-valued, so no moment finiteness is needed.
-/

open scoped ENNReal NNReal

@[expose] public section

namespace PercLib.CriticalLRP.I417Base

open PercLib.CriticalLRP.TreeExpansion

variable {V : Type*}

/-! ## Splitting a leaf assignment at a node -/

/-- The values of the leaf positions of `node l r` are the same thing as a pair of
assignments to the two children. -/
theorem tsum_sumArrow {α β : Type*} (F : (α → V) → (β → V) → ℝ≥0∞) :
    (∑' y : α ⊕ β → V, F (fun p => y (Sum.inl p)) (fun p => y (Sum.inr p)))
      = ∑' a, ∑' b, F a b := by
  rw [← ENNReal.tsum_prod]
  exact Equiv.tsum_eq (Equiv.sumArrowEquivProdArrow α β V) (fun p => F p.1 p.2)

/-- A single leaf value pinned at `w`. -/
theorem tsum_indicator_mul [DecidableEq V] (f : V → ℝ≥0∞) (w : V) :
    (∑' z : V, (if z = w then 1 else 0) * f z) = f w := by
  rw [tsum_eq_single w]
  · simp
  · intro b hb
    simp [hb]

/-! ## The unmarked tree sum -/

/-- **Every diagram is worth `χ^(2p-1)`.**  For a kernel with constant row sum `χ`, the sum of
the tree weight of a rooted binary tree with `p` leaves over all leaf values and all internal
vertices is `χ^(2p-1)`, whatever the shape of the tree.

This is the `ℝ≥0∞`/countable analogue of `RTree.sum_wt` (`TreeExpansion/Weight.lean`). -/
theorem tsum_wtE {α : Type*} (k : V → V → ℝ≥0∞) (χ : ℝ≥0∞)
    (hχ : ∀ v, ∑' y, k v y = χ) :
    ∀ (t : RTree α) (v : V),
      (∑' y : t.LeafPos → V, wtE k t y v) = χ ^ (2 * t.numLeaves - 1)
  | .leaf a, v => by
      have h : (∑' y : (RTree.leaf a).LeafPos → V, wtE k (RTree.leaf a) y v)
          = ∑' z : V, k v z :=
        Equiv.tsum_eq (Equiv.funUnique PUnit V) (fun z => k v z)
      rw [h, hχ v]
      simp
  | .node l r, v => by
      have ihR : ∀ u : V, (∑' b : RTree.LeafPos r → V, wtE k r b u) = χ ^ (2 * r.numLeaves - 1) :=
        fun u => tsum_wtE k χ hχ r u
      have ihL : ∀ u : V, (∑' a : RTree.LeafPos l → V, wtE k l a u) = χ ^ (2 * l.numLeaves - 1) :=
        fun u => tsum_wtE k χ hχ l u
      set CL : ℝ≥0∞ := χ ^ (2 * l.numLeaves - 1) with hCL
      set CR : ℝ≥0∞ := χ ^ (2 * r.numLeaves - 1) with hCR
      have hsplit : (∑' y : RTree.LeafPos (RTree.node l r) → V,
            wtE k (RTree.node l r) y v)
          = ∑' a, ∑' b, ∑' u, k v u * wtE k l a u * wtE k r b u := by
        simp only [wtE]
        exact tsum_sumArrow (F := fun a b => ∑' u, k v u * wtE k l a u * wtE k r b u)
      rw [hsplit]
      calc (∑' a, ∑' b, ∑' u, k v u * wtE k l a u * wtE k r b u)
          = ∑' a, ∑' u, ∑' b, k v u * wtE k l a u * wtE k r b u :=
              tsum_congr fun a => ENNReal.tsum_comm
        _ = ∑' a, ∑' u, k v u * wtE k l a u * CR := by
              refine tsum_congr fun a => tsum_congr fun u => ?_
              rw [ENNReal.tsum_mul_left, ihR u]
        _ = ∑' u, ∑' a, k v u * wtE k l a u * CR := ENNReal.tsum_comm
        _ = ∑' u, (k v u * CL) * CR := by
              refine tsum_congr fun u => ?_
              rw [ENNReal.tsum_mul_right, ENNReal.tsum_mul_left, ihL u]
        _ = (∑' u, k v u * CL) * CR := ENNReal.tsum_mul_right
        _ = ((∑' u, k v u) * CL) * CR := by rw [ENNReal.tsum_mul_right]
        _ = χ ^ (2 * (RTree.node l r).numLeaves - 1) := by
              rw [hχ v, hCL, hCR, RTree.numLeaves_node]
              have h1 : 1 ≤ l.numLeaves := RTree.numLeaves_pos l
              have h2 : 1 ≤ r.numLeaves := RTree.numLeaves_pos r
              rw [← pow_succ' χ (2 * l.numLeaves - 1), ← pow_add]
              congr 1
              omega

/-! ## The marked tree sum: the value depends only on the marked depth -/

/-- **The marked-leaf diagram value.**  For a rooted binary tree `t` on `p+1` leaves with the
leaf position `q` pinned at `w`, the sum of the tree weight over all values of the **other**
leaves and all internal vertices (encoded by the indicator `1[y q = w]`) is

  `χ^(2(p+1)-1-depth t q) · pathW k t q v w`,

i.e. `χ^(2p+1-ℓ) T^ℓ(v,w)` with `ℓ = depth t q`, independently of the shape of `t`. -/
theorem tsum_wtE_marked {α : Type*} [DecidableEq V] (k : V → V → ℝ≥0∞) (χ : ℝ≥0∞)
    (hχ : ∀ v, ∑' y, k v y = χ) :
    ∀ (t : RTree α) (q : t.LeafPos) (v w : V),
      (∑' y : t.LeafPos → V, (if y q = w then 1 else 0) * wtE k t y v)
        = χ ^ (2 * t.numLeaves - 1 - RTree.depth t q) * pathW k t q v w
  | .leaf a, q, v, w => by
      have hsub : Subsingleton (RTree.LeafPos (RTree.leaf a)) :=
        inferInstanceAs (Subsingleton PUnit)
      have hq : q = (⟨⟩ : RTree.LeafPos (RTree.leaf a)) :=
        @Subsingleton.elim _ hsub q _
      rw [hq]
      have h : (∑' y : (RTree.leaf a).LeafPos → V,
            (if y ⟨⟩ = w then 1 else 0) * wtE k (RTree.leaf a) y v)
          = ∑' z : V, (if z = w then 1 else 0) * k v z :=
        Equiv.tsum_eq (Equiv.funUnique PUnit V)
          (fun z => (if z = w then 1 else 0) * k v z)
      rw [h, tsum_indicator_mul]
      have h0 : 2 * (RTree.leaf a).numLeaves - 1 - RTree.depth (RTree.leaf a) ⟨⟩ = 0 := by
        simp [RTree.depth]
      rw [h0, pow_zero, one_mul]
      simp [pathW]
  | .node l r, Sum.inl q', v, w => by
      have ihL : ∀ (q : RTree.LeafPos l) (u : V),
          (∑' a : RTree.LeafPos l → V, (if a q = w then 1 else 0) * wtE k l a u)
            = χ ^ (2 * l.numLeaves - 1 - RTree.depth l q) * pathW k l q u w :=
        fun q u => tsum_wtE_marked k χ hχ l q u w
      have ihR : ∀ u : V, (∑' b : RTree.LeafPos r → V, wtE k r b u)
          = χ ^ (2 * r.numLeaves - 1) := fun u => tsum_wtE k χ hχ r u
      set CR : ℝ≥0∞ := χ ^ (2 * r.numLeaves - 1) with hCR
      set CL : ℝ≥0∞ := χ ^ (2 * l.numLeaves - 1 - RTree.depth l q') with hCL
      calc (∑' y : RTree.LeafPos (RTree.node l r) → V,
              (if y (Sum.inl q') = w then 1 else 0) * wtE k (RTree.node l r) y v)
          = ∑' a, ∑' b, (if a q' = w then 1 else 0) *
                (∑' u, k v u * wtE k l a u * wtE k r b u) := by
              simp only [wtE]
              exact tsum_sumArrow (F := fun a b => (if a q' = w then 1 else 0) *
                (∑' u, k v u * wtE k l a u * wtE k r b u))
        _ = ∑' a, ∑' u, (if a q' = w then 1 else 0) * (k v u * wtE k l a u * CR) := by
              refine tsum_congr fun a => ?_
              refine Eq.trans (tsum_congr fun b => (ENNReal.tsum_mul_left).symm) ?_
              rw [ENNReal.tsum_comm]
              refine tsum_congr fun u => ?_
              rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_left, ihR u]
        _ = ∑' u, ∑' a, (if a q' = w then 1 else 0) * (k v u * wtE k l a u * CR) :=
              ENNReal.tsum_comm
        _ = ∑' u, (CL * CR) * (k v u * pathW k l q' u w) := by
              refine tsum_congr fun u => ?_
              have hstep : (∑' a : RTree.LeafPos l → V,
                    (if a q' = w then 1 else 0) * (k v u * wtE k l a u * CR))
                  = (∑' a : RTree.LeafPos l → V,
                      (if a q' = w then 1 else 0) * wtE k l a u) * (k v u * CR) := by
                rw [← ENNReal.tsum_mul_right]
                exact tsum_congr fun a => by ring
              rw [hstep, ihL q' u]
              ring
        _ = (CL * CR) * ∑' u, k v u * pathW k l q' u w := ENNReal.tsum_mul_left
        _ = χ ^ (2 * (RTree.node l r).numLeaves - 1
                - RTree.depth (RTree.node l r) (Sum.inl q')) *
              pathW k (RTree.node l r) (Sum.inl q') v w := by
              have hp : pathW k (RTree.node l r) (Sum.inl q') v w
                  = ∑' u, k v u * pathW k l q' u w := rfl
              have hexp : (2 * l.numLeaves - 1 - RTree.depth l q') + (2 * r.numLeaves - 1)
                  = 2 * (RTree.node l r).numLeaves - 1
                    - RTree.depth (RTree.node l r) (Sum.inl q') := by
                have h1 : 1 ≤ l.numLeaves := RTree.numLeaves_pos l
                have h2 : 1 ≤ r.numLeaves := RTree.numLeaves_pos r
                have h3 : RTree.depth l q' ≤ l.numLeaves := RTree.depth_le_numLeaves l q'
                have h4 : RTree.depth (RTree.node l r) (Sum.inl q') = RTree.depth l q' + 1 := rfl
                have h5 : (RTree.node l r).numLeaves = l.numLeaves + r.numLeaves :=
                  RTree.numLeaves_node l r
                omega
              rw [hp, hCL, hCR, ← pow_add, hexp]
  | .node l r, Sum.inr q', v, w => by
      have ihR : ∀ (q : RTree.LeafPos r) (u : V),
          (∑' b : RTree.LeafPos r → V, (if b q = w then 1 else 0) * wtE k r b u)
            = χ ^ (2 * r.numLeaves - 1 - RTree.depth r q) * pathW k r q u w :=
        fun q u => tsum_wtE_marked k χ hχ r q u w
      have ihL : ∀ u : V, (∑' a : RTree.LeafPos l → V, wtE k l a u)
          = χ ^ (2 * l.numLeaves - 1) := fun u => tsum_wtE k χ hχ l u
      set CL : ℝ≥0∞ := χ ^ (2 * l.numLeaves - 1) with hCL
      set CR : ℝ≥0∞ := χ ^ (2 * r.numLeaves - 1 - RTree.depth r q') with hCR
      calc (∑' y : RTree.LeafPos (RTree.node l r) → V,
              (if y (Sum.inr q') = w then 1 else 0) * wtE k (RTree.node l r) y v)
          = ∑' a, ∑' b, (if b q' = w then 1 else 0) *
                (∑' u, k v u * wtE k l a u * wtE k r b u) := by
              simp only [wtE]
              exact tsum_sumArrow (F := fun a b => (if b q' = w then 1 else 0) *
                (∑' u, k v u * wtE k l a u * wtE k r b u))
        _ = ∑' a, ∑' u, (CR * pathW k r q' u w) * (k v u * wtE k l a u) := by
              refine tsum_congr fun a => ?_
              refine Eq.trans (tsum_congr fun b => (ENNReal.tsum_mul_left).symm) ?_
              rw [ENNReal.tsum_comm]
              refine tsum_congr fun u => ?_
              have hstep : (∑' b : RTree.LeafPos r → V,
                    (if b q' = w then 1 else 0) * (k v u * wtE k l a u * wtE k r b u))
                  = (∑' b : RTree.LeafPos r → V,
                      (if b q' = w then 1 else 0) * wtE k r b u) * (k v u * wtE k l a u) := by
                rw [← ENNReal.tsum_mul_right]
                exact tsum_congr fun b => by ring
              rw [hstep, ihR q' u]
        _ = ∑' u, (CR * pathW k r q' u w) * (k v u * CL) := by
              rw [ENNReal.tsum_comm]
              refine tsum_congr fun u => ?_
              rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_left, ihL u]
        _ = (CL * CR) * ∑' u, k v u * pathW k r q' u w := by
              rw [show (∑' u : V, (CR * pathW k r q' u w) * (k v u * CL))
                  = ∑' u : V, (CL * CR) * (k v u * pathW k r q' u w) from
                tsum_congr fun u => by ring]
              rw [ENNReal.tsum_mul_left]
        _ = χ ^ (2 * (RTree.node l r).numLeaves - 1
                - RTree.depth (RTree.node l r) (Sum.inr q')) *
              pathW k (RTree.node l r) (Sum.inr q') v w := by
              have hp : pathW k (RTree.node l r) (Sum.inr q') v w
                  = ∑' u, k v u * pathW k r q' u w := rfl
              have hexp : (2 * l.numLeaves - 1) + (2 * r.numLeaves - 1 - RTree.depth r q')
                  = 2 * (RTree.node l r).numLeaves - 1
                    - RTree.depth (RTree.node l r) (Sum.inr q') := by
                have h1 : 1 ≤ l.numLeaves := RTree.numLeaves_pos l
                have h2 : 1 ≤ r.numLeaves := RTree.numLeaves_pos r
                have h3 : RTree.depth r q' ≤ r.numLeaves := RTree.depth_le_numLeaves r q'
                have h4 : RTree.depth (RTree.node l r) (Sum.inr q') = RTree.depth r q' + 1 := rfl
                have h5 : (RTree.node l r).numLeaves = l.numLeaves + r.numLeaves :=
                  RTree.numLeaves_node l r
                omega
              rw [hp, hCL, hCR, ← pow_add, hexp]

end PercLib.CriticalLRP.I417Base
