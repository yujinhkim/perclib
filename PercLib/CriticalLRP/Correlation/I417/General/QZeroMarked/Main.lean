/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Accepted from Ultramath `smwzg77c3`, member `m2`, independently rebuilt.
Production integration based on commit `81c6038182e9a883ffcd3d870aed7cd4829649d4`.
Original direction `d5`.

# The `q = 0`, `p = 3` gap from the landed marked route: one residual class

Source: Tom Hutchcroft, *Critical long-range percolation I*, arXiv:2508.18807v1,
Lemma I.4.17 with its printed proof (pp. 45-46) and the Case-3 use (p. 47).

## What is proved here

The landed marked route gives, at the literal cutoff model,

```lean
E[|K_0|³ 1(y ∈ K_0)] ≤ ∑_{ℓ=1}^{4} markedCount 3 ℓ · χ^(7-ℓ) · T^ℓ_{β_c,r}(0,y)
```

(`SourceModelData.connCubeVertexMass_toReal_le_markedPolygon`).  This file proves that at
`p = 3` the `ℓ = 1` class is **empty**, so the landed bound is exactly

```lean
E[|K_0|³ 1(y ∈ K_0)] ≤ m2 χ^5 T²(0,y) + m3 χ^4 T³(0,y) + m4 χ^3 T⁴(0,y),
```

with `m ℓ = markedCount 3 ℓ`.  Two of the three classes already have the target's shape; the
whole distance between the landed marked bound and the source's two-term estimate is therefore
the *single* class `ℓ = 2`:

```lean
twoTermBound_of_ellTwoAbsorbed :
  qzeroEllTwoAbsorbed M A3 A4 → qzeroTwoTermBound M (A3 + m3) (A4 + m4)
```

(`qzeroEllTwoAbsorbed` says `m2 χ^5 T² ≤ A3 χ^4 T³ + A4 χ^3 T⁴`).  Monotonicity of the cutoff
matrix powers (`T² ≤ T³`, proved here as `tpow_succ_ge` from `T(y,y) = 1` and the row sum) is
*not* enough: it upgrades the class to `χ · (χ⁴ T³)` and leaves exactly one factor of `χ`
(`ellTwoClass_le_chi_mul_three`).  The residual condition `qzeroChiMulSquareLe M K`, i.e.
`χ T²(0,y) ≤ K T³(0,y)`, is a pure two-point statement and does close the gap:

```lean
twoTermBound_of_chi_mul_square_le :
  qzeroChiMulSquareLe M K → qzeroTwoTermBound M (K * m2 + m3) m4
```

So no cancellation or deletion of the `ℓ = 2` class exists (the class is a genuine,
nonnegative, strictly positive-coefficient summand of an *upper* bound), and the marked route is
exactly one two-point comparison away from the source's two-term estimate.  The numerical
coefficients are `m1 = 0`, `m2 = 24`, `m3 = 48`, `m4 = 48` (hand computation over the five plane
shapes with four leaves; `markedCoeff_sum_four` below machine-checks their total `120 = 2³·15`
against the landed total identity).  They are deliberately *not* baked into any definition.

## Scope

* No torus, no finite-window surrogate and no inhomogeneous analogue is claimed: `qzeroTpow` is
  the full `tsum` matrix power of the cutoff two-point kernel, and every theorem is per-vertex
  for the cutoff law `M.cutLaw r` at `r ≥ 1`.
* No `sorry`, `admit`, `native_decide`, custom axiom, or invented source hypothesis.  The
  finiteness `M.cutMassAt r 0 ≠ ⊤` is an explicit hypothesis of every `toReal` statement.
-/
module

public import PercLib.CriticalLRP.Correlation.I417.General.QZeroMarked.Defs
public import PercLib.CriticalLRP.Correlation.I417.MarkedJoint.Transversal.PerDepth.Main
public import PercLib.CriticalLRP.TreeExpansion.MarkedLeaf
public import PercLib.CriticalLRP.Analysis.SecondMomentCase3.SummedThree.Main

/-! # The residual class of the marked route at `p = 3`, `q = 0` -/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open MeasureTheory Measure Filter
open scoped ENNReal NNReal BigOperators Topology

@[expose] public section

noncomputable section

namespace PercLib.CriticalLRP.TreeExpansion

variable {α : Type*}

-- The lower-depth bound `RTree.one_le_depth` is reused from
-- `PercLib.CriticalLRP.TreeExpansion.MarkedLeaf`, avoiding a duplicate global declaration.

/-- A tree that is a node has all leaves at depth at least `2`. -/
theorem RTree.two_le_depth_node (l r : RTree α) (q : (RTree.node l r).LeafPos) :
    2 ≤ RTree.depth (RTree.node l r) q := by
  rcases q with q | q
  · have := RTree.one_le_depth l q
    change 2 ≤ RTree.depth l q + 1
    omega
  · have := RTree.one_le_depth r q
    change 2 ≤ RTree.depth r q + 1
    omega

/-- **Depth one forces a single leaf**: a leaf at depth `1` is the whole tree. -/
theorem RTree.numLeaves_eq_one_of_depth_eq_one :
    ∀ (t : RTree α) (q : t.LeafPos), RTree.depth t q = 1 → t.numLeaves = 1
  | RTree.leaf _, _, _ => rfl
  | RTree.node l r, q, h => by
      have h2 := RTree.two_le_depth_node l r q
      omega

end PercLib.CriticalLRP.TreeExpansion

namespace PercLib.CriticalLRP.QZeroGap

open PercLib.CriticalLRP.Orchestration
open PercLib.CriticalLRP.Orchestration.SourceModelData

/-- A four-term `Icc 1 4` sum with vanishing first term. -/
theorem sum_Icc_one_four {A : Type*} [AddCommMonoid A] (f : ℕ → A) (h1 : f 1 = 0) :
    ∑ ℓ ∈ Finset.Icc 1 4, f ℓ = f 2 + f 3 + f 4 := by
  have hset : (Finset.Icc 1 4 : Finset ℕ) = {1, 2, 3, 4} := by decide
  rw [hset, Finset.sum_insert (by decide : (1 : ℕ) ∉ ({2, 3, 4} : Finset ℕ)),
    Finset.sum_insert (by decide : (2 : ℕ) ∉ ({3, 4} : Finset ℕ)),
    Finset.sum_insert (by decide : (3 : ℕ) ∉ ({4} : Finset ℕ)),
    Finset.sum_singleton, h1, zero_add]
  abel

/-! ## The `ℓ = 1` class of the landed marked bound is empty -/

/-- **`markedCount 3 1 = 0`**: the marked leaf of a fully labelled plane tree on `4` leaves
cannot sit at depth `1`, because a depth-one leaf is the whole tree and has `numLeaves = 1`.

Consequently the landed four-term marked polygon bound at `p = 3` has no `T^1` summand. -/
theorem markedCoeff_one_eq_zero : PercLib.CriticalLRP.QZeroGap.markedCoeff 1 = 0 := by
  classical
  have hempty : (PercLib.CriticalLRP.I417Marked.markedShapes 3).filter
      (fun A => PercLib.CriticalLRP.TreeExpansion.RTree.depth A.1 A.2 = 1) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro A hA heq
    have h4 := PercLib.CriticalLRP.I417Marked.markedShapes_numLeaves 3 A hA
    have h1 := PercLib.CriticalLRP.TreeExpansion.RTree.numLeaves_eq_one_of_depth_eq_one
      A.1 A.2 heq
    omega
  change PercLib.CriticalLRP.I417Marked.markedCount 3 1 = 0
  rw [PercLib.CriticalLRP.I417Marked.markedCount, hempty, Finset.card_empty]

/-- The marked coefficients at `p = 3` sum to the plane-family total `2³ · 5!! = 120`
(cross-check against the landed `I417Marked.sum_markedCount`). -/
theorem markedCoeff_sum_four :
    PercLib.CriticalLRP.QZeroGap.markedCoeff 1
      + PercLib.CriticalLRP.QZeroGap.markedCoeff 2
      + PercLib.CriticalLRP.QZeroGap.markedCoeff 3
      + PercLib.CriticalLRP.QZeroGap.markedCoeff 4 = 120 := by
  classical
  have htotal := PercLib.CriticalLRP.I417Marked.sum_markedCount_eq_two_pow_mul_dfactorial 3
  rw [show (3 + 1 : ℕ) = 4 by norm_num,
    sum_Icc_one_four (fun ℓ => PercLib.CriticalLRP.I417Marked.markedCount 3 ℓ)
      markedCoeff_one_eq_zero] at htotal
  have hnum : (2 : ℕ) ^ 3 * Nat.doubleFactorial (2 * 3 - 1) = 120 := by decide
  rw [hnum] at htotal
  have h1z : PercLib.CriticalLRP.I417Marked.markedCount 3 1 = 0 := markedCoeff_one_eq_zero
  simp only [PercLib.CriticalLRP.QZeroGap.markedCoeff]
  omega

variable (M : PercLib.CriticalLRP.Orchestration.SourceModelData)

/-! ## Collapse of the landed marked bound to three classes -/

/-- **The landed marked bound at `p = 3` in its collapsed form.**  The `ℓ = 1` summand vanishes
(`markedCoeff_one_eq_zero`), and the remaining exponents are `2·3+1-2 = 5`, `2·3+1-3 = 4`,
`2·3+1-4 = 3`, so the marked polygon bound reads

`E[|K_0|³ 1(y ∈ K_0)] ≤ m2 χ⁵ T² + m3 χ⁴ T³ + m4 χ³ T⁴`.

The `ℓ = 2` summand is the only class whose `χ`-power is not the target's. -/
theorem connCubeVertexMass_toReal_le_threeClass (r : ℝ) (hχ : M.cutMassAt r 0 ≠ ⊤)
    (y : M.V) :
    (M.connCubeVertexMass r y).toReal ≤
      (PercLib.CriticalLRP.QZeroGap.markedCoeff 2 : ℝ) *
          ((M.qzeroChi r) ^ 5 * M.qzeroTpow r 2 y)
      + (PercLib.CriticalLRP.QZeroGap.markedCoeff 3 : ℝ) *
          ((M.qzeroChi r) ^ 4 * M.qzeroTpow r 3 y)
      + (PercLib.CriticalLRP.QZeroGap.markedCoeff 4 : ℝ) *
          ((M.qzeroChi r) ^ 3 * M.qzeroTpow r 4 y) := by
  have hmain := M.connCubeVertexMass_toReal_le_markedPolygon r hχ y
  simp only [qzeroChi, qzeroTpow,
    PercLib.CriticalLRP.QZeroGap.markedCoeff]
  have hz : (PercLib.CriticalLRP.I417Marked.markedCount 3 1 : ℝ) = 0 := by
    have h : PercLib.CriticalLRP.I417Marked.markedCount 3 1 = 0 := markedCoeff_one_eq_zero
    rw [h]
    norm_num
  have h1 : (PercLib.CriticalLRP.I417Marked.markedCount 3 1 : ℝ) *
      ((M.cutMassAt r 0).toReal ^ (2 * 3 + 1 - 1) *
        PercLib.CriticalLRP.I418C.polyK (M.cutTwoPoint r) 1 0 y) = 0 := by
    rw [hz, zero_mul]
  rw [sum_Icc_one_four
    (fun ℓ => (PercLib.CriticalLRP.I417Marked.markedCount 3 ℓ : ℝ) *
      ((M.cutMassAt r 0).toReal ^ (2 * 3 + 1 - ℓ) *
        PercLib.CriticalLRP.I418C.polyK (M.cutTwoPoint r) ℓ 0 y)) h1] at hmain
  rw [show (2 * 3 + 1 - 2 : ℕ) = 5 by norm_num,
    show (2 * 3 + 1 - 3 : ℕ) = 4 by norm_num,
    show (2 * 3 + 1 - 4 : ℕ) = 3 by norm_num] at hmain
  exact hmain

/-! ## Monotonicity of the cutoff matrix powers

`T^ℓ(0,y)` is nondecreasing in `ℓ`, because `T(y,y) = 1` and all entries are nonnegative.  This
is the *only* monotone input available without a new two-point estimate, and it is exactly one
factor of `χ` short of absorbing the `ℓ = 2` class. -/

theorem tpow_succ_ge (r : ℝ) (hχ : M.cutMassAt r 0 ≠ ⊤) (n : ℕ) (y : M.V) :
    M.qzeroTpow r n y ≤ M.qzeroTpow r (n + 1) y := by
  have hnn : ∀ z : M.V, 0 ≤ PercLib.CriticalLRP.I418C.polyK (M.cutTwoPoint r) n 0 z := fun z =>
    PercLib.CriticalLRP.I418C.polyK_nonneg _ (fun a b => M.cutTwoPoint_nonneg r a b) n 0 z
  have hsum : Summable (fun z : M.V =>
      PercLib.CriticalLRP.I418C.polyK (M.cutTwoPoint r) n 0 z) :=
    M.polyK_summable_colSum r hχ n
  have hprod : Summable (fun z : M.V =>
      PercLib.CriticalLRP.I418C.polyK (M.cutTwoPoint r) n 0 z * M.cutTwoPoint r z y) := by
    refine Summable.of_nonneg_of_le (fun z => ?_) (fun z => ?_) hsum
    · exact mul_nonneg (hnn z) (M.cutTwoPoint_nonneg r z y)
    · exact mul_le_of_le_one_right (hnn z) (M.cutTwoPoint_le_one r z y)
  have hle := hprod.sum_le_tsum ({y} : Finset M.V)
    (fun z _ => mul_nonneg (hnn z) (M.cutTwoPoint_nonneg r z y))
  have hsingle : ∑ z ∈ ({y} : Finset M.V),
      PercLib.CriticalLRP.I418C.polyK (M.cutTwoPoint r) n 0 z * M.cutTwoPoint r z y
      = PercLib.CriticalLRP.I418C.polyK (M.cutTwoPoint r) n 0 y := by
    rw [Finset.sum_singleton, M.cutTwoPoint_self_eq_one r y, mul_one]
  rw [hsingle] at hle
  have hstep : PercLib.CriticalLRP.I418C.polyK (M.cutTwoPoint r) (n + 1) 0 y
      = ∑' z, PercLib.CriticalLRP.I418C.polyK (M.cutTwoPoint r) n 0 z * M.cutTwoPoint r z y :=
    PercLib.CriticalLRP.I418C.polyK_succ _ n 0 y
  rw [qzeroTpow, qzeroTpow, hstep]
  exact hle

/-- **The best monotone bound on the `ℓ = 2` class**: `m2 χ⁵ T² ≤ m2 · χ · (χ⁴ T³)`.

Monotonicity of the cutoff matrix powers therefore leaves *exactly* one factor of `χ` standing
between the marked bound and the source's two-term shape.  No further manipulation of the landed
marked bound produces the missing `χ`: it has to come from a two-point estimate. -/
theorem ellTwoClass_le_chi_mul_three (r : ℝ) (hχ : M.cutMassAt r 0 ≠ ⊤) (y : M.V) :
    M.qzeroEllTwoClass r y ≤
      (PercLib.CriticalLRP.QZeroGap.markedCoeff 2 : ℝ) *
        (M.qzeroChi r * ((M.qzeroChi r) ^ 4 * M.qzeroTpow r 3 y)) := by
  have hm : (0 : ℝ) ≤ (PercLib.CriticalLRP.QZeroGap.markedCoeff 2 : ℝ) := Nat.cast_nonneg _
  have hχ0 : (0 : ℝ) ≤ M.qzeroChi r := ENNReal.toReal_nonneg
  have h23 := tpow_succ_ge M r hχ 2 y
  have h23' : M.qzeroTpow r 2 y ≤ M.qzeroTpow r 3 y := by
    have := h23
    simpa using this
  have hχ4 : (0 : ℝ) ≤ (M.qzeroChi r) ^ 4 := pow_nonneg hχ0 4
  have hstep : M.qzeroEllTwoClass r y
      = (PercLib.CriticalLRP.QZeroGap.markedCoeff 2 : ℝ) *
          ((M.qzeroChi r) ^ 4 * (M.qzeroChi r * M.qzeroTpow r 2 y)) := by
    rw [qzeroEllTwoClass]; ring
  rw [hstep]
  calc (PercLib.CriticalLRP.QZeroGap.markedCoeff 2 : ℝ) *
        ((M.qzeroChi r) ^ 4 * (M.qzeroChi r * M.qzeroTpow r 2 y))
      ≤ (PercLib.CriticalLRP.QZeroGap.markedCoeff 2 : ℝ) *
          ((M.qzeroChi r) ^ 4 * (M.qzeroChi r * M.qzeroTpow r 3 y)) := by
        refine mul_le_mul_of_nonneg_left ?_ hm
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h23' hχ0) hχ4
    _ = (PercLib.CriticalLRP.QZeroGap.markedCoeff 2 : ℝ) *
          (M.qzeroChi r * ((M.qzeroChi r) ^ 4 * M.qzeroTpow r 3 y)) := by ring

/-! ## The reduction: absorption of `ℓ = 2` gives the source's two-term estimate -/

/-- **Absorbing the `ℓ = 2` class yields the target two-term bound.**  The `ℓ = 3` and `ℓ = 4`
classes already have the target's own shape, so their coefficients are simply added to `A3` and
`A4`; no inequality beyond the absorption is used. -/
theorem twoTermBound_of_ellTwoAbsorbed (A3 A4 : ℝ)
    (hχ : ∀ r : ℝ, 1 ≤ r → M.cutMassAt r 0 ≠ ⊤) (habs : M.qzeroEllTwoAbsorbed A3 A4) :
    M.qzeroTwoTermBound (A3 + (PercLib.CriticalLRP.QZeroGap.markedCoeff 3 : ℝ))
      (A4 + (PercLib.CriticalLRP.QZeroGap.markedCoeff 4 : ℝ)) := by
  intro r hr y
  have h1 := connCubeVertexMass_toReal_le_threeClass M r (hχ r hr) y
  have h2 := habs r hr y
  have h2' : (PercLib.CriticalLRP.QZeroGap.markedCoeff 2 : ℝ) *
        ((M.qzeroChi r) ^ 5 * M.qzeroTpow r 2 y)
      ≤ A3 * (M.qzeroChi r) ^ 4 * M.qzeroTpow r 3 y
        + A4 * (M.qzeroChi r) ^ 3 * M.qzeroTpow r 4 y := by
    rw [qzeroEllTwoClass] at h2
    calc (PercLib.CriticalLRP.QZeroGap.markedCoeff 2 : ℝ) *
          ((M.qzeroChi r) ^ 5 * M.qzeroTpow r 2 y)
        = (PercLib.CriticalLRP.QZeroGap.markedCoeff 2 : ℝ) *
            (M.qzeroChi r) ^ 5 * M.qzeroTpow r 2 y := by ring
      _ ≤ _ := h2
  have hstep :
      (PercLib.CriticalLRP.QZeroGap.markedCoeff 2 : ℝ) *
          ((M.qzeroChi r) ^ 5 * M.qzeroTpow r 2 y)
        + (PercLib.CriticalLRP.QZeroGap.markedCoeff 3 : ℝ) *
            ((M.qzeroChi r) ^ 4 * M.qzeroTpow r 3 y)
        + (PercLib.CriticalLRP.QZeroGap.markedCoeff 4 : ℝ) *
            ((M.qzeroChi r) ^ 3 * M.qzeroTpow r 4 y)
      ≤ (A3 + (PercLib.CriticalLRP.QZeroGap.markedCoeff 3 : ℝ)) *
            (M.qzeroChi r) ^ 4 * M.qzeroTpow r 3 y
        + (A4 + (PercLib.CriticalLRP.QZeroGap.markedCoeff 4 : ℝ)) *
            (M.qzeroChi r) ^ 3 * M.qzeroTpow r 4 y := by
    nlinarith [h2']
  exact h1.trans hstep

/-- **The two-point residual closes the gap.**  If `χ · T²(0,y) ≤ K · T³(0,y)` uniformly (the
`qzeroChiMulSquareLe` residual), then the source's two-term per-vertex estimate holds with the
explicit constants `C3 = K · markedCount 3 2 + markedCount 3 3` and `C4 = markedCount 3 4`
(so with the hand-computed coefficients: `C3 = 24K + 48`, `C4 = 48`). -/
theorem twoTermBound_of_chi_mul_square_le (K : ℝ)
    (hχ : ∀ r : ℝ, 1 ≤ r → M.cutMassAt r 0 ≠ ⊤) (hreg : M.qzeroChiMulSquareLe K) :
    M.qzeroTwoTermBound (K * (PercLib.CriticalLRP.QZeroGap.markedCoeff 2 : ℝ)
        + (PercLib.CriticalLRP.QZeroGap.markedCoeff 3 : ℝ))
      (PercLib.CriticalLRP.QZeroGap.markedCoeff 4 : ℝ) := by
  have habs : M.qzeroEllTwoAbsorbed (K * (PercLib.CriticalLRP.QZeroGap.markedCoeff 2 : ℝ)) 0 := by
    intro r hr y
    have hχ0 : (0 : ℝ) ≤ M.qzeroChi r := ENNReal.toReal_nonneg
    have hm : (0 : ℝ) ≤ (PercLib.CriticalLRP.QZeroGap.markedCoeff 2 : ℝ) := Nat.cast_nonneg _
    have h4 : (0 : ℝ) ≤ (M.qzeroChi r) ^ 4 := pow_nonneg hχ0 4
    have hreg' := hreg r hr y
    have hkey : M.qzeroEllTwoClass r y
        ≤ (PercLib.CriticalLRP.QZeroGap.markedCoeff 2 : ℝ) *
            ((M.qzeroChi r) ^ 4 * (K * M.qzeroTpow r 3 y)) := by
      have h5 : M.qzeroEllTwoClass r y
          = (PercLib.CriticalLRP.QZeroGap.markedCoeff 2 : ℝ) *
              ((M.qzeroChi r) ^ 4 * (M.qzeroChi r * M.qzeroTpow r 2 y)) := by
        rw [qzeroEllTwoClass]; ring
      rw [h5]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hreg' h4) hm
    refine hkey.trans (le_of_eq ?_)
    ring
  have hmain := twoTermBound_of_ellTwoAbsorbed M _ 0 hχ habs
  simpa using hmain

/-- **The fourth-power two-point residual also closes the gap.**  If
`χ² · T²(0,y) ≤ K · T⁴(0,y)` uniformly, the source's two-term per-vertex estimate holds with
`C3 = markedCount 3 3` and `C4 = K · markedCount 3 2 + markedCount 3 4`
(so `C3 = 48`, `C4 = 24K + 48` with the hand-computed coefficients).  This is the variant that
pairs with the landed `ℓ = 4` polygon machinery rather than with an `ℓ = 3` input. -/
theorem twoTermBound_of_chi_sq_mul_square_le (K : ℝ)
    (hχ : ∀ r : ℝ, 1 ≤ r → M.cutMassAt r 0 ≠ ⊤) (hreg : M.qzeroChiSqMulSquareLe K) :
    M.qzeroTwoTermBound (PercLib.CriticalLRP.QZeroGap.markedCoeff 3 : ℝ)
      (K * (PercLib.CriticalLRP.QZeroGap.markedCoeff 2 : ℝ)
        + (PercLib.CriticalLRP.QZeroGap.markedCoeff 4 : ℝ)) := by
  have habs : M.qzeroEllTwoAbsorbed 0 (K * (PercLib.CriticalLRP.QZeroGap.markedCoeff 2 : ℝ)) := by
    intro r hr y
    have hm : (0 : ℝ) ≤ (PercLib.CriticalLRP.QZeroGap.markedCoeff 2 : ℝ) := Nat.cast_nonneg _
    have hreg' := hreg r hr y
    have hkey : M.qzeroEllTwoClass r y
        ≤ (PercLib.CriticalLRP.QZeroGap.markedCoeff 2 : ℝ) *
            ((M.qzeroChi r) ^ 3 * (K * M.qzeroTpow r 4 y)) := by
      have h5 : M.qzeroEllTwoClass r y
          = (PercLib.CriticalLRP.QZeroGap.markedCoeff 2 : ℝ) *
              ((M.qzeroChi r) ^ 3 * (M.qzeroChi r * M.qzeroChi r * M.qzeroTpow r 2 y)) := by
        rw [qzeroEllTwoClass]; ring
      rw [h5]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hreg' (pow_nonneg ENNReal.toReal_nonneg 3)) hm
    refine hkey.trans (le_of_eq ?_)
    ring
  have hmain := twoTermBound_of_ellTwoAbsorbed M 0 _ hχ habs
  simpa using hmain


/-! ## Integration: the target *is* the `hgap` of the repaired Case-3 chain -/

/-- **`qzeroTwoTermBound` is the production `hgap`.**  The repaired Case-3 consumer
`SourceModelData.connCubeMass_toReal_le_of_splitGap` carries the per-vertex hypothesis

`F r y ≤ C3 * T³(0,y) * χ⁴ + C4 * T⁴(0,y) * χ³`,

which is this module's `qzeroTwoTermBound` with the two products commuted.  No other conversion is
involved, so the target of this direction discharges that hypothesis verbatim. -/
theorem hgap_of_twoTermBound (C3 C4 : ℝ) (h : M.qzeroTwoTermBound C3 C4) :
    ∀ r : ℝ, 1 ≤ r → ∀ y ∈ PercLib.CriticalLRP.E1Sign.ballF M r,
      (M.connCubeVertexMass r y).toReal ≤
        C3 * PercLib.CriticalLRP.I418C.polyK (M.cutTwoPoint r) 3 0 y *
            (M.cutMassAt r 0).toReal ^ 4
          + C4 * PercLib.CriticalLRP.I418C.polyK (M.cutTwoPoint r) 4 0 y *
              (M.cutMassAt r 0).toReal ^ 3 := by
  intro r hr y _
  have h1 := h r hr y
  have h2 : C3 * (M.qzeroChi r) ^ 4 * M.qzeroTpow r 3 y
        + C4 * (M.qzeroChi r) ^ 3 * M.qzeroTpow r 4 y
      = C3 * PercLib.CriticalLRP.I418C.polyK (M.cutTwoPoint r) 3 0 y *
            (M.cutMassAt r 0).toReal ^ 4
          + C4 * PercLib.CriticalLRP.I418C.polyK (M.cutTwoPoint r) 4 0 y *
              (M.cutMassAt r 0).toReal ^ 3 := by
    rw [qzeroChi, qzeroTpow, qzeroTpow]
    ring
  rw [qzeroTwoTermBound] at h
  rw [qzeroChi, qzeroTpow, qzeroTpow] at h1
  linarith [h1, h2]

/-- **Case-3 numerator from the two-term gap alone.**  Plugging `hgap_of_twoTermBound` into the
landed repaired consumer `connCubeMass_toReal_le_of_splitGap`: if the source's per-vertex
two-term estimate holds with constants `C3, C4`, the windowed `ℓ = 3` sum and the `ℓ = 4`
polygon input are as in the landed bundle, then

`E[|K_0|³ |K_0 ∩ B_r|] ≤ (C3 · Bthree r + C4 · Cp · drv r) · |B_r| · χ⁴`.

No per-vertex `ℓ = 3` supremum (`hT3`, refuted at this base) is used. -/
theorem connCubeMass_toReal_le_of_twoTermBound {C3 C4 Cp c : ℝ} {Bthree : ℝ → ℝ}
    (hC3 : 0 ≤ C3) (hC4 : 0 ≤ C4) (h : M.qzeroTwoTermBound C3 C4)
    (hc : ∀ r : ℝ, 1 ≤ r → M.connCubeMass r ≠ ⊤)
    (hT3sum : ∀ r : ℝ, 1 ≤ r → ∑ y ∈ PercLib.CriticalLRP.E1Sign.ballF M r,
      PercLib.CriticalLRP.I418C.polyK (M.cutTwoPoint r) 3 0 y
        ≤ ((PercLib.CriticalLRP.E1Sign.ballF M r).card : ℝ) * Bthree r)
    (hpoly4 : ∀ r : ℝ, 1 ≤ r → ∀ x : M.V,
      PercLib.CriticalLRP.I418C.polyK (M.cutTwoPoint r) 4 0 x ≤
        Cp * M.case3Driver c r * (M.cutMassAt r 0).toReal) :
    ∀ᶠ r : ℝ in atTop, (M.connCubeMass r).toReal ≤
      (C3 * Bthree r + C4 * Cp * M.case3Driver c r) * ((M.ball r).ncard : ℝ)
        * (M.cutMassAt r 0).toReal ^ 4 :=
  M.connCubeMass_toReal_le_of_splitGap (F := fun r y => (M.connCubeVertexMass r y).toReal)
    hC3 hC4 (fun r hr => M.connCubeMass_toReal_eq_sum_vertex r (hc r hr))
    (hgap_of_twoTermBound M C3 C4 h) hT3sum hpoly4

end PercLib.CriticalLRP.QZeroGap

/-! ## Axiom audit -/

namespace PercLib.CriticalLRP.QZeroGapAudit

set_option linter.hashCommand false

#print axioms PercLib.CriticalLRP.TreeExpansion.RTree.one_le_depth
#print axioms PercLib.CriticalLRP.TreeExpansion.RTree.numLeaves_eq_one_of_depth_eq_one
#print axioms PercLib.CriticalLRP.QZeroGap.sum_Icc_one_four
#print axioms PercLib.CriticalLRP.QZeroGap.markedCoeff_one_eq_zero
#print axioms PercLib.CriticalLRP.QZeroGap.markedCoeff_sum_four
#print axioms PercLib.CriticalLRP.QZeroGap.connCubeVertexMass_toReal_le_threeClass
#print axioms PercLib.CriticalLRP.QZeroGap.tpow_succ_ge
#print axioms PercLib.CriticalLRP.QZeroGap.ellTwoClass_le_chi_mul_three
#print axioms PercLib.CriticalLRP.QZeroGap.twoTermBound_of_ellTwoAbsorbed
#print axioms PercLib.CriticalLRP.QZeroGap.twoTermBound_of_chi_mul_square_le
#print axioms PercLib.CriticalLRP.QZeroGap.twoTermBound_of_chi_sq_mul_square_le
#print axioms PercLib.CriticalLRP.QZeroGap.hgap_of_twoTermBound
#print axioms PercLib.CriticalLRP.QZeroGap.connCubeMass_toReal_le_of_twoTermBound

end PercLib.CriticalLRP.QZeroGapAudit
