/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
# The source-faithful correction of the marked-leaf tree-sum input, and its consumer

`WeightedTreeSum` (`TreeExpansion/SpatialTreeGraph.lean`), the marked-leaf input to Lemma
I.5.9 besides the tree-graph inequality (I.2.2), was stated with an *additive* functional
`φ : V →+ ℝ` on a finite abelian group `V`. Every such `φ` is zero
(`addMonoidHom_eq_zero_of_finite`), so for `p > 0` both sides of `WeightedTreeSum` vanish: the
interface is vacuous, and so is the derived `spatial_tree_graph_printed`.

This file names the non-vacuous correction used by `MarkedLeaf`: a nonnegative weight
`A : V → ℝ` with `A 0 = 0` and ordinary subadditivity `A (a+b) ≤ A a + A b`. On an
infinite additive group this is the hypothesis satisfied by the source's `A y = |⟨y,u⟩|`;
on a finite abelian group the theorem instead uses metric or other genuinely subadditive
weights, since nonzero real-valued additive functionals do not exist there. The theorem
`subadditiveTreeSum` discharges the corrected input for all `n`, and the final BK consumer
therefore needs no `WeightedTreeSum` hypothesis. That class is *not* vacuous on a finite group (any
translation-invariant metric gives such an `A`, e.g. the circular distance on `ZMod 4`, and
`|φ|` for additive `φ` is a (degenerate) member), whereas `{|φ| : φ : V →+ ℝ}` is `{0}`.

Contents:

* `TreeSumAt pr ends o n` — the marked-leaf estimate at a *single* number `n` of labels, with a
  general subadditive weight; `SubadditiveTreeSum` is the `∀ n` form.
* `weightedTreeSum_of_subadditive` — the corrected input implies the artificial one, so no
  existing theorem is lost: it is a strengthening, not a replacement.
* `subadditiveTreeSum_one` / `treeSumAt_one` — the corrected input at `n = 1` is the
  *identity* `∑_x A (x 0)^p treeSum k 1 o x = ∑_y A y ^ p twoPoint o y` for *arbitrary* `A`
  (no hypotheses), so the base case of the correction is a theorem, not an assumption.
* `treeSumAt_zero_exponent` — for `p = 0` the corrected inequality holds for every `n` and
  every `A`, again with no hypothesis on `A`.
* `spatial_tree_graph_of_subadditive` / `spatial_tree_graph_printed_of_subadditive` — Lemma
  I.5.9 (both the weighted-two-point and the printed `|K|^{n-1}` shape) for **arbitrary
  subadditive weights `A_i`**, `i < n`, with the tree estimate consumed only at the given `n`.
  This strictly generalises `spatial_tree_graph_printed`, which asks for additive `Φ_i` and is
  vacuous because of it.
* `spatial_tree_graph_printed_of_additiveTreeSum` — the old consumer, obtained from the
  corrected input with no `WeightedTreeSum` hypothesis (the artificial signature is *derived*).
* `exists_nonvacuous_subadditive_weight` — a kernel-checked non-vacuity witness.
-/
module

public import PercLib.CriticalLRP.TreeExpansion.MarkedLeaf
public import PercLib.CriticalLRP.TreeExpansion.FiniteWeightedTreeSum
public import PercLib.CriticalLRP.TreeExpansion.WeightedTreeSumTwo

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

set_option autoImplicit true

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000
set_option linter.deprecated false

@[expose] public section

namespace PercLib.CriticalLRP.TreeExpansion

open Finset
open PercLib.CriticalLRP.TreeGraph

variable {V : Type*} [AddCommGroup V] [Fintype V] [DecidableEq V]
variable {E : Type*} [Fintype E] [DecidableEq E]

/-! ## 1. The explicitly named correction -/

/-- **The source-faithful marked-leaf tree-sum estimate at a single label count `n`.**

With `S = clusterVolume pr ends o` and `Q = ∑_y A y ^ p * twoPoint pr ends o y`, the marked-leaf
tree sum with the weight `A (x i₀)^p` on the label `i₀` is at most
`(2n-3)!! * n^(max p 1) * S^(2n-2) * Q`.  The weight `A` is any nonnegative subadditive
function vanishing at `0`. On an infinite additive group this includes the source's
`A = |⟨·,u⟩|`; on the finite groups treated here, metric weights supply non-vacuous examples. -/
def TreeSumAt (pr : E → ℝ) (ends : E → Sym2 V) (o : V) (n : ℕ) : Prop :=
  ∀ (i₀ : Fin n) (A : V → ℝ) (p : ℝ), 0 ≤ p →
    (∀ y : V, 0 ≤ A y) → A 0 = 0 → (∀ a b : V, A (a + b) ≤ A a + A b) →
    (∀ a b : V, twoPoint pr ends a b = twoPoint pr ends o (b - a)) →
    (∑ x : Fin n → V, A (x i₀) ^ p * treeSum (twoPoint pr ends) n o x)
      ≤ (VolumeMoments.M (n - 1) : ℝ) * (n : ℝ) ^ (max p 1) *
          (clusterVolume pr ends o) ^ (2 * n - 2) *
          ∑ y : V, A y ^ p * twoPoint pr ends o y

/-- **The corrected input, all label counts.**  For every `n ≥ 1`, `i₀ : Fin n` and every
nonnegative subadditive `A` with `A 0 = 0`, the marked-leaf tree-sum estimate holds. -/
def SubadditiveTreeSum (pr : E → ℝ) (ends : E → Sym2 V) (o : V) : Prop :=
  ∀ n : ℕ, 1 ≤ n → TreeSumAt pr ends o n

/-- The `∀ n` form is the conjunction of the single-`n` forms. -/
theorem subadditiveTreeSum_iff (pr : E → ℝ) (ends : E → Sym2 V) (o : V) :
    SubadditiveTreeSum pr ends o ↔ ∀ n : ℕ, 1 ≤ n → TreeSumAt pr ends o n :=
  Iff.rfl

/-- The corrected weighted-tree-sum input is proved for every label count by
`markedLeaf_treeSum_bound`; it is not an additional hypothesis. -/
theorem subadditiveTreeSum (pr : E → ℝ) (hp : ∀ e, 0 ≤ pr e) (hp1 : ∀ e, pr e ≤ 1)
    (ends : E → Sym2 V) (o : V) : SubadditiveTreeSum pr ends o := by
  intro n hn i₀ A p hp0 hAn hA0 hsub hinv
  exact markedLeaf_treeSum_bound pr hp hp1 ends o hinv A hAn hA0 hsub hp0 hn i₀

/-! ## 2. The correction is a strengthening: it implies the artificial input

For an additive `φ` the weight `A = |φ ·|` is nonnegative, vanishes at `0` and is subadditive
(`|φ (a+b)| = |φ a + φ b| ≤ |φ a| + |φ b|`), so every instance of `WeightedTreeSum` is an
instance of `TreeSumAt`.  Hence everything proved from `WeightedTreeSum` survives, with the
artificial hypothesis *derived* rather than assumed. -/

theorem abs_addHom_subadditive (φ : V →+ ℝ) : ∀ a b : V, |φ (a + b)| ≤ |φ a| + |φ b| := by
  intro a b
  rw [map_add]
  exact abs_add_le _ _

theorem abs_addHom_zero (φ : V →+ ℝ) : |φ (0 : V)| = 0 := by simp

/-- **The corrected input implies the artificial one.** -/
theorem weightedTreeSum_of_subadditive (pr : E → ℝ) (ends : E → Sym2 V) (o : V)
    (h : SubadditiveTreeSum pr ends o) : WeightedTreeSum pr ends o := by
  intro n hn i₀ φ p hp hinv
  exact h n hn i₀ (fun y => |φ y|) p hp (fun y => abs_nonneg _) (abs_addHom_zero φ)
    (abs_addHom_subadditive φ) hinv

/-! ## 3. The base case of the correction is a theorem, not an assumption

At `n = 1` the tree sum is the two-point function (`treeSum_one`), so the corrected estimate is
an identity for an **arbitrary** weight `A` — in particular for every nonnegative subadditive
`A`, with no hypothesis on `A` at all. -/

/-- **`n = 1`: the corrected marked-leaf estimate is an identity** for an arbitrary weight. -/
theorem subadditiveTreeSum_one (pr : E → ℝ) (ends : E → Sym2 V) (o : V) (A : V → ℝ) (p : ℝ) :
    (∑ x : Fin 1 → V, A (x 0) ^ p * treeSum (twoPoint pr ends) 1 o x)
      = (VolumeMoments.M 0 : ℝ) * (1 : ℝ) ^ (max p 1) *
          (clusterVolume pr ends o) ^ (2 * 1 - 2) *
          ∑ y : V, A y ^ p * twoPoint pr ends o y := by
  classical
  have hL : (∑ x : Fin 1 → V, A (x 0) ^ p * treeSum (twoPoint pr ends) 1 o x)
      = ∑ y : V, A y ^ p * twoPoint pr ends o y := by
    rw [Finset.sum_congr rfl fun x _ => by rw [treeSum_one]]
    refine Fintype.sum_equiv (Equiv.funUnique (Fin 1) V)
      (fun x : Fin 1 → V => A (x 0) ^ p * twoPoint pr ends o (x 0))
      (fun y : V => A y ^ p * twoPoint pr ends o y) ?_
    intro x
    simp [Equiv.funUnique]
  rw [hL]
  simp

/-- **`TreeSumAt` at `n = 1`, unconditionally.** -/
theorem treeSumAt_one (pr : E → ℝ) (ends : E → Sym2 V) (o : V) : TreeSumAt pr ends o 1 := by
  intro i₀ A p _hp _hA0 _hA00 _hsub _hinv
  obtain rfl : i₀ = 0 := Subsingleton.elim i₀ 0
  rw [subadditiveTreeSum_one]
  simp

/-! ## 4. The exponent-`0` case of the correction, unconditionally

For `p = 0` the weight is `A ^ 0 = 1` and the claim reduces to the unmarked tree-sum evaluation
`sum_treeSum_le`, `∑_x treeSum = (2n-3)!! S^(2n-1)`, which the factor `n^(max 0 1) = n` of the
target makes room for.  So this instance of the corrected input holds for every `n` and every
`A`, with no subadditivity needed. -/

theorem treeSumAt_zero_exponent (pr : E → ℝ) (hp : ∀ e, 0 ≤ pr e) (hp1 : ∀ e, pr e ≤ 1)
    (ends : E → Sym2 V) (o : V)
    (hinv : ∀ a b : V, twoPoint pr ends a b = twoPoint pr ends o (b - a))
    {n : ℕ} (hn : 1 ≤ n) (i₀ : Fin n) (A : V → ℝ) :
    (∑ x : Fin n → V, A (x i₀) ^ (0 : ℝ) * treeSum (twoPoint pr ends) n o x)
      ≤ (VolumeMoments.M (n - 1) : ℝ) * (n : ℝ) ^ (max (0 : ℝ) 1) *
          (clusterVolume pr ends o) ^ (2 * n - 2) *
          ∑ y : V, A y ^ (0 : ℝ) * twoPoint pr ends o y := by
  classical
  set S : ℝ := clusterVolume pr ends o with hSdef
  have hS0 : 0 ≤ S := by
    rw [hSdef, clusterVolume]
    exact Finset.sum_nonneg fun y _ => twoPoint_nonneg hp hp1 ends o y
  have hS : (∑ y : V, A y ^ (0 : ℝ) * twoPoint pr ends o y) = S := by
    rw [hSdef, clusterVolume]
    exact Finset.sum_congr rfl fun y _ => by rw [Real.rpow_zero, one_mul]
  have hL : (∑ x : Fin n → V, A (x i₀) ^ (0 : ℝ) * treeSum (twoPoint pr ends) n o x)
      = ∑ x : Fin n → V, treeSum (twoPoint pr ends) n o x :=
    Finset.sum_congr rfl fun x _ => by rw [Real.rpow_zero, one_mul]
  rw [hL, hS]
  have hmax : max (0 : ℝ) 1 = 1 := max_eq_right zero_le_one
  rw [hmax, Real.rpow_one]
  have hSexp : S ^ (2 * n - 2) * S = S ^ (2 * n - 1) := by
    have h2 : 2 * n - 1 = (2 * n - 2) + 1 := by omega
    rw [h2, pow_succ, mul_comm]
  rw [mul_assoc, hSexp]
  have h1 := sum_treeSum_le pr hp hp1 ends o hinv hn
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hM0 : (0 : ℝ) ≤ (VolumeMoments.M (n - 1) : ℝ) := Nat.cast_nonneg _
  have hSpow : (0 : ℝ) ≤ S ^ (2 * n - 1) := pow_nonneg hS0 _
  calc (∑ x : Fin n → V, treeSum (twoPoint pr ends) n o x)
      ≤ (VolumeMoments.M (n - 1) : ℝ) * S ^ (2 * n - 1) := h1
    _ ≤ (VolumeMoments.M (n - 1) : ℝ) * (n : ℝ) * S ^ (2 * n - 1) := by
        have : (VolumeMoments.M (n - 1) : ℝ) * 1 ≤ (VolumeMoments.M (n - 1) : ℝ) * (n : ℝ) :=
          mul_le_mul_of_nonneg_left hn1 hM0
        nlinarith [mul_nonneg hM0 hSpow]


/-! ## 4b. Anchor independence: `hinv` makes the two-point kernel `o`-periodic

`hinv` read at `a = o` says `twoPoint o y = twoPoint o (y - o)`, so the kernel `T = twoPoint o ·`
is periodic with the basepoint as period; read at `a = 0` it says `twoPoint 0 y = twoPoint o y`.
Consequently `treeSum` and `clusterVolume` do not depend on which vertex the translation
invariance is read off at, and the stored `n = 2` bound (anchored at `0`) transfers to an
arbitrary basepoint. -/

theorem twoPoint_period (pr : E → ℝ) (ends : E → Sym2 V) (o : V)
    (hinv : ∀ a b : V, twoPoint pr ends a b = twoPoint pr ends o (b - a)) (y : V) :
    twoPoint pr ends o (y - o) = twoPoint pr ends o y :=
  (hinv o y).symm

theorem twoPoint_zero_eq (pr : E → ℝ) (ends : E → Sym2 V) (o : V)
    (hinv : ∀ a b : V, twoPoint pr ends a b = twoPoint pr ends o (b - a)) (y : V) :
    twoPoint pr ends (0 : V) y = twoPoint pr ends o y := by
  rw [hinv 0 y, sub_zero]

/-- The kernel has constant row sums at every basepoint. -/
theorem twoPoint_row_sum (pr : E → ℝ) (ends : E → Sym2 V) (o : V)
    (hinv : ∀ a b : V, twoPoint pr ends a b = twoPoint pr ends o (b - a)) (w : V) :
    (∑ x : V, twoPoint pr ends w x) = ∑ y : V, twoPoint pr ends o y := by
  classical
  rw [Finset.sum_congr rfl fun x _ => hinv w x]
  refine (Fintype.sum_equiv (Equiv.addRight w) (fun z : V => twoPoint pr ends o z)
    (fun x : V => twoPoint pr ends o (x - w)) ?_).symm
  intro z
  show twoPoint pr ends o z = twoPoint pr ends o (z + w - w)
  rw [add_sub_cancel_right]

theorem clusterVolume_anchor_indep (pr : E → ℝ) (ends : E → Sym2 V) (o : V)
    (hinv : ∀ a b : V, twoPoint pr ends a b = twoPoint pr ends o (b - a)) :
    clusterVolume pr ends (0 : V) = clusterVolume pr ends o := by
  refine Finset.sum_congr rfl fun y _ => ?_
  exact twoPoint_zero_eq pr ends o hinv y

/-! ## 4c. The `n = 2` case of the corrected input, at an arbitrary basepoint

The stored `weightedTreeSum_two_of_prob` is anchored at `0`.  Re-running its argument with the
basepoint `o` (only the row sums `∑_x k w x = S` and the two-term estimate are used) discharges
the `n = 2` instance of `TreeSumAt` for every `o`. -/

theorem weightedTreeSum_two_anchored (k : V → V → ℝ) (o : V)
    (hinv : ∀ a b : V, k a b = k o (b - a)) (hk0 : ∀ a b : V, 0 ≤ k a b)
    (A : V → ℝ) (hA0 : ∀ y : V, 0 ≤ A y) {p : ℝ} (hp : 0 ≤ p)
    (hsub : ∀ a b : V, A (a + b) ^ p ≤ (2 : ℝ) ^ (max (p - 1) 0) * (A a ^ p + A b ^ p)) :
    (∑ x : Fin 2 → V, A (x 1) ^ p * treeSum k 2 o x)
      ≤ (2 : ℝ) ^ (max p 1) * (∑ y : V, k o y) ^ 2 * ∑ y : V, A y ^ p * k o y := by
  classical
  set S : ℝ := ∑ y : V, k o y with hSdef
  set Q : ℝ := ∑ y : V, A y ^ p * k o y with hQdef
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun y _ => hk0 o y
  have hQ0 : 0 ≤ Q :=
    Finset.sum_nonneg fun y _ => mul_nonneg (Real.rpow_nonneg (hA0 y) p) (hk0 o y)
  have hrow : ∀ w : V, ∑ x : V, k w x = S := by
    intro w
    rw [hSdef, Finset.sum_congr rfl fun x _ => hinv w x]
    have hb : (∑ x : V, k o (x + -w)) = ∑ z : V, k o z := by
      refine (Fintype.sum_equiv (Equiv.addRight w) (fun z : V => k o z)
        (fun x : V => k o (x + -w)) ?_).symm
      intro z
      show k o z = k o (z + w + -w)
      rw [add_assoc, add_neg_cancel, add_zero]
    simpa [sub_eq_add_neg] using hb
  have hinner : ∀ w : V, ∑ x : V, A x ^ p * k w x
      ≤ (2 : ℝ) ^ (max (p - 1) 0) * (Q + A w ^ p * S) := by
    intro w
    have h1 : (∑ x : V, A x ^ p * k w x) = ∑ x : V, A x ^ p * k o (x + -w) := by
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [hinv w x, sub_eq_add_neg]
    have h2 : (∑ x : V, A x ^ p * k o (x + -w)) = ∑ z : V, A (z + w) ^ p * k o z := by
      refine (Fintype.sum_equiv (Equiv.addRight w)
        (fun z : V => A (z + w) ^ p * k o z)
        (fun x : V => A x ^ p * k o (x + -w)) ?_).symm
      intro z
      show A (z + w) ^ p * k o z = A (z + w) ^ p * k o (z + w + -w)
      rw [add_assoc, add_neg_cancel, add_zero]
    rw [h1, h2]
    calc ∑ z : V, A (z + w) ^ p * k o z
        ≤ ∑ z : V, ((2 : ℝ) ^ (max (p - 1) 0) * (A z ^ p + A w ^ p)) * k o z :=
          Finset.sum_le_sum fun z _ => mul_le_mul_of_nonneg_right (hsub z w) (hk0 o z)
      _ = (2 : ℝ) ^ (max (p - 1) 0) * (Q + A w ^ p * S) := by
          have hz : ∀ z : V, ((2 : ℝ) ^ (max (p - 1) 0) * (A z ^ p + A w ^ p)) * k o z
              = (2 : ℝ) ^ (max (p - 1) 0) * (A z ^ p * k o z)
                + (2 : ℝ) ^ (max (p - 1) 0) * (A w ^ p) * k o z := by
            intro z
            ring
          rw [Finset.sum_congr rfl fun z _ => hz z, Finset.sum_add_distrib, ← Finset.mul_sum,
            ← Finset.mul_sum, ← hQdef, ← hSdef]
          ring
  have hmain : (∑ x : Fin 2 → V, A (x 1) ^ p * treeSum k 2 o x)
      = ∑ w : V, k o w * ((∑ a : V, k w a) * ∑ b : V, A b ^ p * k w b) := by
    rw [sum_finTwoArrow]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    have hstep : ∀ a b : V, A b ^ p * treeSum k 2 o ![a, b]
        = ∑ w : V, k o w * (k w a * (A b ^ p * k w b)) := by
      intro a b
      rw [treeSum_two, Finset.mul_sum]
      refine Finset.sum_congr rfl fun w _ => ?_
      show A b ^ p * (k o w * k w (![a, b] 0) * k w (![a, b] 1)) = _
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      ring
    rw [Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => hstep a b]
    calc ∑ a : V, ∑ b : V, ∑ w : V, k o w * (k w a * (A b ^ p * k w b))
        = ∑ a : V, ∑ w : V, ∑ b : V, k o w * (k w a * (A b ^ p * k w b)) := by
          refine Finset.sum_congr rfl fun a _ => ?_
          exact Finset.sum_comm
      _ = ∑ w : V, ∑ a : V, ∑ b : V, k o w * (k w a * (A b ^ p * k w b)) :=
          Finset.sum_comm
      _ = ∑ w : V, k o w * ((∑ a : V, k w a) * ∑ b : V, A b ^ p * k w b) := by
          refine Finset.sum_congr rfl fun w _ => ?_
          have e1 : (∑ a : V, ∑ b : V, k o w * (k w a * (A b ^ p * k w b)))
              = k o w * ∑ a : V, ∑ b : V, k w a * (A b ^ p * k w b) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun a _ => ?_
            rw [Finset.mul_sum]
          have e2 : (∑ a : V, ∑ b : V, k w a * (A b ^ p * k w b))
              = (∑ a : V, k w a) * ∑ b : V, A b ^ p * k w b := by
            rw [Fintype.sum_mul_sum]
          rw [e1, e2]
  have hmain' : (∑ x : Fin 2 → V, A (x 1) ^ p * treeSum k 2 o x)
      = ∑ w : V, k o w * (S * ∑ b : V, A b ^ p * k w b) := by
    rw [hmain]
    exact Finset.sum_congr rfl fun w _ => by rw [hrow w]
  rw [hmain']
  calc ∑ w : V, k o w * (S * ∑ b : V, A b ^ p * k w b)
      ≤ ∑ w : V, k o w * (S * ((2 : ℝ) ^ (max (p - 1) 0) * (Q + A w ^ p * S))) := by
        refine Finset.sum_le_sum fun w _ => ?_
        refine mul_le_mul_of_nonneg_left ?_ (hk0 o w)
        exact mul_le_mul_of_nonneg_left (hinner w) hS0
    _ = (2 : ℝ) ^ (max (p - 1) 0) * (S * (Q * S) + S * S * Q) := by
        have hz : ∀ w : V,
            k o w * (S * ((2 : ℝ) ^ (max (p - 1) 0) * (Q + A w ^ p * S)))
              = (2 : ℝ) ^ (max (p - 1) 0) * (S * (Q * k o w)) +
                (2 : ℝ) ^ (max (p - 1) 0) * (S * S * (A w ^ p * k o w)) := by
          intro w
          ring
        rw [Finset.sum_congr rfl fun w _ => hz w, Finset.sum_add_distrib]
        have hsum1 : (∑ w : V, (2 : ℝ) ^ (max (p - 1) 0) * (S * (Q * k o w)))
            = (2 : ℝ) ^ (max (p - 1) 0) * (S * (Q * S)) := by
          rw [← Finset.mul_sum]
          congr 1
          rw [← Finset.mul_sum]
          congr 1
          rw [← Finset.mul_sum, ← hSdef]
        have hsum2 : (∑ w : V, (2 : ℝ) ^ (max (p - 1) 0) * (S * S * (A w ^ p * k o w)))
            = (2 : ℝ) ^ (max (p - 1) 0) * (S * S * Q) := by
          rw [← Finset.mul_sum]
          congr 1
          rw [← Finset.mul_sum, ← hQdef]
        rw [hsum1, hsum2]
        ring
    _ = (2 : ℝ) ^ (max p 1) * S ^ 2 * Q := by
        rw [two_rpow_max]
        ring

/-- **The `n = 2` instance of the corrected input, at every basepoint.** -/
theorem treeSumAt_two (pr : E → ℝ) (_hp : ∀ e, 0 ≤ pr e) (hp1 : ∀ e, pr e ≤ 1)
    (ends : E → Sym2 V) (o : V)
    (hinv : ∀ a b : V, twoPoint pr ends a b = twoPoint pr ends o (b - a)) :
    TreeSumAt pr ends o 2 := by
  intro i₀ A p hp0 hAn hA00 hsub hinv'
  set S : ℝ := clusterVolume pr ends o with hSdef
  set Q : ℝ := ∑ y : V, A y ^ p * twoPoint pr ends o y with hQdef
  have hmain := weightedTreeSum_two_anchored (k := twoPoint pr ends) o
    (fun a b => hinv' a b) (fun a b => twoPoint_nonneg _hp hp1 ends a b) A hAn hp0
    (hsub_of_subadd hAn hsub hp0)
  have hswap : (∑ x : Fin 2 → V, A (x 0) ^ p * treeSum (twoPoint pr ends) 2 o x)
      = (∑ x : Fin 2 → V, A (x 1) ^ p * treeSum (twoPoint pr ends) 2 o x) := by
    refine Fintype.sum_equiv (Equiv.arrowCongr (Equiv.swap (0 : Fin 2) 1) (Equiv.refl V))
      (fun x : Fin 2 → V => A (x 0) ^ p * treeSum (twoPoint pr ends) 2 o x)
      (fun x : Fin 2 → V => A (x 1) ^ p * treeSum (twoPoint pr ends) 2 o x) ?_
    intro x
    have hxs : (Equiv.arrowCongr (Equiv.swap (0 : Fin 2) 1) (Equiv.refl V)) x
        = fun i => x (Equiv.swap (0 : Fin 2) 1 i) := by
      funext i
      simp [Equiv.arrowCongr_apply]
    rw [hxs]
    have h2 : (fun i => x (Equiv.swap (0 : Fin 2) 1 i)) 1 = x 0 := by
      show x (Equiv.swap (0 : Fin 2) 1 1) = x 0
      rw [Equiv.swap_apply_right]
    rw [h2]
    have hts : treeSum (twoPoint pr ends) 2 o (fun i => x (Equiv.swap (0 : Fin 2) 1 i))
        = treeSum (twoPoint pr ends) 2 o x := by
      rw [treeSum_two, treeSum_two]
      simp only [Equiv.swap_apply_left, Equiv.swap_apply_right]
      exact Finset.sum_congr rfl fun w _ => by ring
    rw [hts]
  rcases Fin.eq_zero_or_eq_succ i₀ with h | ⟨j, rfl⟩
  · rw [h]
    rw [hswap]
    simpa [hSdef, hQdef, VolumeMoments.M, clusterVolume] using hmain
  · have hj : j = 0 := Subsingleton.elim j 0
    subst hj
    simpa [hSdef, hQdef, VolumeMoments.M, clusterVolume] using hmain

#print axioms PercLib.CriticalLRP.TreeExpansion.twoPoint_period
#print axioms PercLib.CriticalLRP.TreeExpansion.twoPoint_zero_eq
#print axioms PercLib.CriticalLRP.TreeExpansion.twoPoint_row_sum
#print axioms PercLib.CriticalLRP.TreeExpansion.clusterVolume_anchor_indep
#print axioms PercLib.CriticalLRP.TreeExpansion.weightedTreeSum_two_anchored
#print axioms PercLib.CriticalLRP.TreeExpansion.treeSumAt_two

/-! ## 5. The consumer: Lemma I.5.9 with arbitrary subadditive weights

The proof is the source's: weighted AM–GM pointwise in the tuple (already in the repository as
`prod_rpow_le_sum_div`), then the tree-graph inequality termwise, then the marked-leaf
tree-sum estimate — *once*, with the weight `A_i^P` — and finally the weight normalisation
`∑_i q_i / P = 1`.  Nothing but the tree estimate uses the particular shape of the weights. -/

theorem spatial_tree_graph_of_subadditive (pr : E → ℝ) (hp : ∀ e, 0 ≤ pr e) (hp1 : ∀ e, pr e ≤ 1)
    (ends : E → Sym2 V) (o : V) (hTG : TreeGraphBound pr ends (twoPoint pr ends))
    (hinv : ∀ a b : V, twoPoint pr ends a b = twoPoint pr ends o (b - a))
    {n : ℕ} (hn : 1 ≤ n) (hTree : TreeSumAt pr ends o n)
    (q : Fin n → ℝ) (A : Fin n → V → ℝ) (M : ℝ)
    (hq : ∀ i, 0 ≤ q i) (hP : 0 < ∑ i, q i)
    (hAn : ∀ (i : Fin n) (y : V), 0 ≤ A i y) (hA0 : ∀ i : Fin n, A i 0 = 0)
    (hsub : ∀ (i : Fin n) (a b : V), A i (a + b) ≤ A i a + A i b)
    (hM : ∀ i, ∑ y : V, A i y ^ (∑ j, q j) * twoPoint pr ends o y ≤ M) :
    expectReal pr (fun s => tupleSum (clusterF ends s o) n (fun x => ∏ i, A i (x i) ^ q i))
      ≤ (VolumeMoments.M (n - 1) : ℝ) * (n : ℝ) ^ (max (∑ i, q i) 1) *
          (clusterVolume pr ends o) ^ (2 * n - 2) * M := by
  classical
  set P : ℝ := ∑ j, q j with hPdef
  have hPpos : 0 < P := by rw [hPdef]; exact hP
  have hP0 : 0 ≤ P := hPpos.le
  have hS0 : 0 ≤ clusterVolume pr ends o :=
    Finset.sum_nonneg fun y _ => twoPoint_nonneg hp hp1 ends o y
  have hT0 : (0 : ℝ) ≤ (VolumeMoments.M (n - 1) : ℝ) * (n : ℝ) ^ (max P 1) *
      (clusterVolume pr ends o) ^ (2 * n - 2) :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg n) _))
      (pow_nonneg hS0 _)
  have hM' : ∀ i : Fin n, ∑ y : V, A i y ^ P * twoPoint pr ends o y ≤ M := by
    intro i
    rw [hPdef]
    exact hM i
  have hgm : ∀ x : Fin n → V,
      (∏ i, A i (x i) ^ q i) ≤ ∑ i, (q i / P) * A i (x i) ^ P := by
    intro x
    have h := prod_rpow_le_sum_div (fun i => A i (x i)) q (fun i => hAn i (x i)) hq hP
    rw [← hPdef] at h
    exact h
  have hPx0 : ∀ x : Fin n → V, 0 ≤ prob pr {s | ∀ i : Fin n, Conn ends s o (x i)} :=
    fun x => prob_nonneg hp hp1 _
  have hTGx : ∀ x : Fin n → V, prob pr {s | ∀ i : Fin n, Conn ends s o (x i)}
      ≤ treeSum (twoPoint pr ends) n o x := fun x => prob_conn_le_treeSum pr ends o hTG hn x
  have hstep1 : (∑ x : Fin n → V, (∏ i, A i (x i) ^ q i) *
        prob pr {s | ∀ i : Fin n, Conn ends s o (x i)})
      ≤ ∑ x : Fin n → V, (∑ i, (q i / P) * A i (x i) ^ P) *
        prob pr {s | ∀ i : Fin n, Conn ends s o (x i)} :=
    Finset.sum_le_sum fun x _ =>
      mul_le_mul_of_nonneg_right (hgm x) (hPx0 x)
  have hstep2 : (∑ x : Fin n → V, (∑ i, (q i / P) * A i (x i) ^ P) *
        prob pr {s | ∀ i : Fin n, Conn ends s o (x i)})
      = ∑ i : Fin n, (q i / P) *
        ∑ x : Fin n → V, A i (x i) ^ P *
          prob pr {s | ∀ i : Fin n, Conn ends s o (x i)} := by
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => by ring
  have hstep3 : (∑ i : Fin n, (q i / P) *
        ∑ x : Fin n → V, A i (x i) ^ P *
          prob pr {s | ∀ i : Fin n, Conn ends s o (x i)})
      ≤ ∑ i : Fin n, (q i / P) *
        ∑ x : Fin n → V, A i (x i) ^ P * treeSum (twoPoint pr ends) n o x :=
    Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum fun x _ =>
          mul_le_mul_of_nonneg_left (hTGx x) (Real.rpow_nonneg (hAn i (x i)) P))
        (div_nonneg (hq i) hP0)
  have hstep4 : (∑ i : Fin n, (q i / P) *
        ∑ x : Fin n → V, A i (x i) ^ P * treeSum (twoPoint pr ends) n o x)
      ≤ ∑ i : Fin n, (q i / P) * ((VolumeMoments.M (n - 1) : ℝ) * (n : ℝ) ^ (max P 1) *
          (clusterVolume pr ends o) ^ (2 * n - 2) *
          ∑ y : V, A i y ^ P * twoPoint pr ends o y) :=
    Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_left
        (hTree i (A i) P hP0 (hAn i) (hA0 i) (hsub i) hinv) (div_nonneg (hq i) hP0)
  have hstep5 : (∑ i : Fin n, (q i / P) * ((VolumeMoments.M (n - 1) : ℝ) * (n : ℝ) ^ (max P 1) *
        (clusterVolume pr ends o) ^ (2 * n - 2) *
        ∑ y : V, A i y ^ P * twoPoint pr ends o y))
      = ((VolumeMoments.M (n - 1) : ℝ) * (n : ℝ) ^ (max P 1) *
          (clusterVolume pr ends o) ^ (2 * n - 2)) *
        ∑ i : Fin n, (q i / P) * ∑ y : V, A i y ^ P * twoPoint pr ends o y := by
    conv_rhs => rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hstep6 : (∑ i : Fin n, (q i / P) * ∑ y : V, A i y ^ P * twoPoint pr ends o y) ≤ M := by
    have hw1 : ∑ i : Fin n, q i / P = 1 := by
      rw [← Finset.sum_div, ← hPdef]
      exact div_self hPpos.ne'
    calc ∑ i : Fin n, (q i / P) * ∑ y : V, A i y ^ P * twoPoint pr ends o y
        ≤ ∑ i : Fin n, (q i / P) * M :=
          Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hM' i) (div_nonneg (hq i) hP0)
      _ = (∑ i : Fin n, q i / P) * M := (Finset.sum_mul _ _ _).symm
      _ = M := by rw [hw1, one_mul]
  have hstep7 : ((VolumeMoments.M (n - 1) : ℝ) * (n : ℝ) ^ (max P 1) *
        (clusterVolume pr ends o) ^ (2 * n - 2)) *
        ∑ i : Fin n, (q i / P) * ∑ y : V, A i y ^ P * twoPoint pr ends o y
      ≤ ((VolumeMoments.M (n - 1) : ℝ) * (n : ℝ) ^ (max P 1) *
        (clusterVolume pr ends o) ^ (2 * n - 2)) * M :=
    mul_le_mul_of_nonneg_left hstep6 hT0
  rw [expectReal_tupleSum pr ends o n (fun x => ∏ i, A i (x i) ^ q i)]
  calc ∑ x : Fin n → V, (∏ i, A i (x i) ^ q i) *
        prob pr {s | ∀ i : Fin n, Conn ends s o (x i)}
      ≤ ∑ x : Fin n → V, (∑ i, (q i / P) * A i (x i) ^ P) *
          prob pr {s | ∀ i : Fin n, Conn ends s o (x i)} := hstep1
    _ = ∑ i : Fin n, (q i / P) *
          ∑ x : Fin n → V, A i (x i) ^ P *
            prob pr {s | ∀ i : Fin n, Conn ends s o (x i)} := hstep2
    _ ≤ ∑ i : Fin n, (q i / P) *
          ∑ x : Fin n → V, A i (x i) ^ P * treeSum (twoPoint pr ends) n o x := hstep3
    _ ≤ ∑ i : Fin n, (q i / P) * ((VolumeMoments.M (n - 1) : ℝ) * (n : ℝ) ^ (max P 1) *
          (clusterVolume pr ends o) ^ (2 * n - 2) *
          ∑ y : V, A i y ^ P * twoPoint pr ends o y) := hstep4
    _ = ((VolumeMoments.M (n - 1) : ℝ) * (n : ℝ) ^ (max P 1) *
          (clusterVolume pr ends o) ^ (2 * n - 2)) *
        ∑ i : Fin n, (q i / P) * ∑ y : V, A i y ^ P * twoPoint pr ends o y := hstep5
    _ ≤ ((VolumeMoments.M (n - 1) : ℝ) * (n : ℝ) ^ (max P 1) *
          (clusterVolume pr ends o) ^ (2 * n - 2)) * M := hstep7
    _ = (VolumeMoments.M (n - 1) : ℝ) * (n : ℝ) ^ (max (∑ i, q i) 1) *
          (clusterVolume pr ends o) ^ (2 * n - 2) * M := by rw [← hPdef]

/-- **Lemma I.5.9 in the source's printed shape**, with arbitrary subadditive weights: the
right-hand side carries `max_i E[|K|^{n-1} ∑_{y ∈ K} A_i y ^ p]` instead of the weighted
two-point sum. -/
theorem spatial_tree_graph_printed_of_subadditive (pr : E → ℝ) (hp : ∀ e, 0 ≤ pr e)
    (hp1 : ∀ e, pr e ≤ 1) (ends : E → Sym2 V) (o : V)
    (hTG : TreeGraphBound pr ends (twoPoint pr ends))
    (hinv : ∀ a b : V, twoPoint pr ends a b = twoPoint pr ends o (b - a))
    {n : ℕ} (hn : 1 ≤ n) (hTree : TreeSumAt pr ends o n)
    (q : Fin n → ℝ) (A : Fin n → V → ℝ) (M : ℝ)
    (hq : ∀ i, 0 ≤ q i) (hP : 0 < ∑ i, q i)
    (hAn : ∀ (i : Fin n) (y : V), 0 ≤ A i y) (hA0 : ∀ i : Fin n, A i 0 = 0)
    (hsub : ∀ (i : Fin n) (a b : V), A i (a + b) ≤ A i a + A i b)
    (hM : ∀ i, expectReal pr (fun s => ((clusterF ends s o).card : ℝ) ^ (n - 1) *
            ∑ y ∈ clusterF ends s o, A i y ^ (∑ j, q j)) ≤ M) :
    expectReal pr (fun s => tupleSum (clusterF ends s o) n (fun x => ∏ i, A i (x i) ^ q i))
      ≤ (VolumeMoments.M (n - 1) : ℝ) * (n : ℝ) ^ (max (∑ i, q i) 1) *
          (clusterVolume pr ends o) ^ (2 * n - 2) * M := by
  refine spatial_tree_graph_of_subadditive pr hp hp1 ends o hTG hinv hn hTree q A M hq hP
    hAn hA0 hsub ?_
  intro i
  have hw : ∀ y : V, 0 ≤ A i y ^ (∑ j, q j) :=
    fun y => Real.rpow_nonneg (hAn i y) _
  refine le_trans (le_of_eq ?_)
    (le_trans (expectReal_cluster_sum_le_pow_mul pr hp hp1 ends o hn _ hw) (hM i))
  exact (expectation_spatialMoment pr ends o (fun y => A i y ^ (∑ j, q j))).symm

/-- **The artificial signature is derived, not assumed**: the repository's printed form of
Lemma I.5.9 (additive `Φ_i`, hypothesis `WeightedTreeSum`) follows from the corrected input. -/
theorem spatial_tree_graph_printed_of_additiveTreeSum (pr : E → ℝ) (hp : ∀ e, 0 ≤ pr e)
    (hp1 : ∀ e, pr e ≤ 1) (ends : E → Sym2 V) (o : V)
    (hTG : TreeGraphBound pr ends (twoPoint pr ends))
    (h : SubadditiveTreeSum pr ends o)
    (hinv : ∀ a b : V, twoPoint pr ends a b = twoPoint pr ends o (b - a))
    {n : ℕ} (hn : 1 ≤ n) (q : Fin n → ℝ) (Φ : Fin n → V →+ ℝ) (M : ℝ)
    (hq : ∀ i, 0 ≤ q i) (hP : 0 < ∑ i, q i)
    (hM : ∀ i, expectReal pr (fun s => ((clusterF ends s o).card : ℝ) ^ (n - 1) *
            ∑ y ∈ clusterF ends s o, |Φ i y| ^ (∑ j, q j)) ≤ M) :
    expectReal pr (fun s => tupleSum (clusterF ends s o) n (fun x => ∏ i, |Φ i (x i)| ^ q i))
      ≤ (VolumeMoments.M (n - 1) : ℝ) * (n : ℝ) ^ (max (∑ i, q i) 1) *
          (clusterVolume pr ends o) ^ (2 * n - 2) * M :=
  spatial_tree_graph_printed pr hp hp1 ends o hTG (weightedTreeSum_of_subadditive pr ends o h)
    hinv hn q Φ M hq hP hM

/-- **Lemma I.5.9 for arbitrary subadditive weights with the tree-graph inequality discharged by
BK**: the only remaining input is the marked-leaf tree estimate at the given `n`. -/
theorem spatial_tree_graph_of_bk_subadditive (pr : E → ℝ) (hp : ∀ e, 0 ≤ pr e)
    (hp1 : ∀ e, pr e ≤ 1) (ends : E → Sym2 V) (o : V) (hBK : BKIncreasing pr)
    (hinv : ∀ a b : V, twoPoint pr ends a b = twoPoint pr ends o (b - a))
    {n : ℕ} (hn : 1 ≤ n) (hTree : TreeSumAt pr ends o n)
    (q : Fin n → ℝ) (A : Fin n → V → ℝ) (M : ℝ)
    (hq : ∀ i, 0 ≤ q i) (hP : 0 < ∑ i, q i)
    (hAn : ∀ (i : Fin n) (y : V), 0 ≤ A i y) (hA0 : ∀ i : Fin n, A i 0 = 0)
    (hsub : ∀ (i : Fin n) (a b : V), A i (a + b) ≤ A i a + A i b)
    (hM : ∀ i, ∑ y : V, A i y ^ (∑ j, q j) * twoPoint pr ends o y ≤ M) :
    expectReal pr (fun s => tupleSum (clusterF ends s o) n (fun x => ∏ i, A i (x i) ^ q i))
      ≤ (VolumeMoments.M (n - 1) : ℝ) * (n : ℝ) ^ (max (∑ i, q i) 1) *
          (clusterVolume pr ends o) ^ (2 * n - 2) * M :=
  spatial_tree_graph_of_subadditive pr hp hp1 ends o
    (PercLib.CriticalLRP.TreeGraph.treeGraphBound_of_bk' pr hp hp1 hBK) hinv hn hTree q A M
    hq hP hAn hA0 hsub hM

/-- The printed form of Lemma I.5.9 with both tree-graph inputs discharged by BK and the
proved all-`n` marked-leaf bound. No additive functional or vacuous finite-group weight is used. -/
theorem spatial_tree_graph_printed_of_bk_subadditive (pr : E → ℝ) (hp : ∀ e, 0 ≤ pr e)
    (hp1 : ∀ e, pr e ≤ 1) (ends : E → Sym2 V) (o : V) (hBK : BKIncreasing pr)
    (hinv : ∀ a b : V, twoPoint pr ends a b = twoPoint pr ends o (b - a))
    {n : ℕ} (hn : 1 ≤ n) (q : Fin n → ℝ) (A : Fin n → V → ℝ) (M : ℝ)
    (hq : ∀ i, 0 ≤ q i) (hP : 0 < ∑ i, q i)
    (hAn : ∀ (i : Fin n) (y : V), 0 ≤ A i y) (hA0 : ∀ i : Fin n, A i 0 = 0)
    (hsub : ∀ (i : Fin n) (a b : V), A i (a + b) ≤ A i a + A i b)
    (hM : ∀ i, expectReal pr (fun s => ((clusterF ends s o).card : ℝ) ^ (n - 1) *
            ∑ y ∈ clusterF ends s o, A i y ^ (∑ j, q j)) ≤ M) :
    expectReal pr (fun s => tupleSum (clusterF ends s o) n (fun x => ∏ i, A i (x i) ^ q i))
      ≤ (VolumeMoments.M (n - 1) : ℝ) * (n : ℝ) ^ (max (∑ i, q i) 1) *
          (clusterVolume pr ends o) ^ (2 * n - 2) * M :=
  spatial_tree_graph_printed_of_subadditive pr hp hp1 ends o
    (PercLib.CriticalLRP.TreeGraph.treeGraphBound_of_bk' pr hp hp1 hBK) hinv hn
    (subadditiveTreeSum pr hp hp1 ends o n hn) q A M hq hP hAn hA0 hsub hM


/-- **Lemma I.5.9 for `n = 1` with no tree-sum hypothesis at all**: the corrected input's `n = 1`
instance is the identity `subadditiveTreeSum_one`. -/
theorem spatial_tree_graph_one_of_subadditive (pr : E → ℝ) (hp : ∀ e, 0 ≤ pr e)
    (hp1 : ∀ e, pr e ≤ 1) (ends : E → Sym2 V) (o : V)
    (hTG : TreeGraphBound pr ends (twoPoint pr ends))
    (hinv : ∀ a b : V, twoPoint pr ends a b = twoPoint pr ends o (b - a))
    (q : Fin 1 → ℝ) (A : Fin 1 → V → ℝ) (M : ℝ)
    (hq : ∀ i, 0 ≤ q i) (hP : 0 < ∑ i, q i)
    (hAn : ∀ (i : Fin 1) (y : V), 0 ≤ A i y) (hA0 : ∀ i : Fin 1, A i 0 = 0)
    (hsub : ∀ (i : Fin 1) (a b : V), A i (a + b) ≤ A i a + A i b)
    (hM : ∀ i, ∑ y : V, A i y ^ (∑ j, q j) * twoPoint pr ends o y ≤ M) :
    expectReal pr (fun s => tupleSum (clusterF ends s o) 1 (fun x => ∏ i, A i (x i) ^ q i))
      ≤ (VolumeMoments.M 0 : ℝ) * (1 : ℝ) ^ (max (∑ i, q i) 1) *
          (clusterVolume pr ends o) ^ (2 * 1 - 2) * M :=
  by
  simpa using spatial_tree_graph_of_subadditive pr hp hp1 ends o hTG hinv le_rfl
    (treeSumAt_one pr ends o) q A M hq hP hAn hA0 hsub hM

/-- **Lemma I.5.9 for `n = 2` with no tree-sum hypothesis at all**: the corrected input's `n = 2`
instance is `treeSumAt_two`, proved at an arbitrary basepoint above. -/
theorem spatial_tree_graph_two_of_subadditive (pr : E → ℝ) (hp : ∀ e, 0 ≤ pr e)
    (hp1 : ∀ e, pr e ≤ 1) (ends : E → Sym2 V) (o : V)
    (hTG : TreeGraphBound pr ends (twoPoint pr ends))
    (hinv : ∀ a b : V, twoPoint pr ends a b = twoPoint pr ends o (b - a))
    (q : Fin 2 → ℝ) (A : Fin 2 → V → ℝ) (M : ℝ)
    (hq : ∀ i, 0 ≤ q i) (hP : 0 < ∑ i, q i)
    (hAn : ∀ (i : Fin 2) (y : V), 0 ≤ A i y) (hA0 : ∀ i : Fin 2, A i 0 = 0)
    (hsub : ∀ (i : Fin 2) (a b : V), A i (a + b) ≤ A i a + A i b)
    (hM : ∀ i, ∑ y : V, A i y ^ (∑ j, q j) * twoPoint pr ends o y ≤ M) :
    expectReal pr (fun s => tupleSum (clusterF ends s o) 2 (fun x => ∏ i, A i (x i) ^ q i))
      ≤ (VolumeMoments.M 1 : ℝ) * (2 : ℝ) ^ (max (∑ i, q i) 1) *
          (clusterVolume pr ends o) ^ (2 * 2 - 2) * M :=
  spatial_tree_graph_of_subadditive pr hp hp1 ends o hTG hinv (by norm_num) (treeSumAt_two pr hp hp1 ends o hinv)
    q A M hq hP hAn hA0 hsub hM

/-! ## 6. Non-vacuity of the corrected hypothesis

The class of admissible weights is nonempty and contains nonzero elements, unlike the class
`{|φ| : φ : V →+ ℝ}` which is `{0}` on a finite group.  The witness is the circular distance on
`ZMod 4`, `A y = min (y, 4 - y)`, i.e. the word metric of `ZMod 4`, which is subadditive. -/

/-- The circular distance on `ZMod 4`: `0, 1, 2, 1` on `0, 1, 2, 3`. -/
noncomputable def zmod4Dist : ZMod 4 → ℝ := fun v =>
  if v = 0 then 0 else if v = 2 then 2 else 1

theorem zmod4Dist_zero : zmod4Dist 0 = 0 := by
  unfold zmod4Dist
  rw [ite_eq_left rfl]

theorem zmod4Dist_nonneg (y : ZMod 4) : 0 ≤ zmod4Dist y := by
  unfold zmod4Dist
  split_ifs <;> norm_num

theorem zmod4Dist_ne_zero : zmod4Dist ≠ 0 := by
  intro h
  have h1 : zmod4Dist 1 = (0 : ZMod 4 → ℝ) 1 := by rw [h]
  unfold zmod4Dist at h1
  rw [ite_eq_right (by decide : (1 : ZMod 4) ≠ 0), ite_eq_right (by decide : (1 : ZMod 4) ≠ 2)] at h1
  norm_num at h1

/-- **The circular distance on `ZMod 4` is subadditive**: `A (a+b) ≤ A a + A b` on all `16`
pairs.  This is the `d (0, a+b) ≤ d (0,a) + d (a, a+b)` computation for the translation-invariant
metric `d` of `ZMod 4`. -/
theorem zmod4Dist_subadd : ∀ a b : ZMod 4, zmod4Dist (a + b) ≤ zmod4Dist a + zmod4Dist b := by
  intro a b
  rcases zmod_four_cases a with rfl | rfl | rfl | rfl <;>
    rcases zmod_four_cases b with rfl | rfl | rfl | rfl <;>
    (repeat (first | unfold zmod4Dist | rw [ite_eq_left (by decide)] | rw [ite_eq_right (by decide)])) <;>
    norm_num

/-- **Non-vacuity witness**: a nonnegative, subadditive, nontrivial weight vanishing at `0` on a
finite abelian group.  (For additive `φ : V →+ ℝ` on a finite `V`, `|φ| = 0` identically, so no
such witness exists in the artificial interface.) -/
theorem exists_nonvacuous_subadditive_weight :
    ∃ A : ZMod 4 → ℝ, (∀ y, 0 ≤ A y) ∧ A 0 = 0 ∧
      (∀ a b : ZMod 4, A (a + b) ≤ A a + A b) ∧ A ≠ 0 :=
  ⟨zmod4Dist, zmod4Dist_nonneg, zmod4Dist_zero, zmod4Dist_subadd, zmod4Dist_ne_zero⟩

/-- The artificial interface's weights are all zero on a finite group: every `|φ|` is `0`. -/
theorem abs_addHom_eq_zero (φ : V →+ ℝ) : (fun y => |φ y|) = fun _ => 0 := by
  funext y
  rw [addMonoidHom_eq_zero_of_finite φ]
  simp

end PercLib.CriticalLRP.TreeExpansion

/-! ## Axiom audit -/

#print axioms PercLib.CriticalLRP.TreeExpansion.subadditiveTreeSum_iff
#print axioms PercLib.CriticalLRP.TreeExpansion.subadditiveTreeSum
#print axioms PercLib.CriticalLRP.TreeExpansion.abs_addHom_subadditive
#print axioms PercLib.CriticalLRP.TreeExpansion.weightedTreeSum_of_subadditive
#print axioms PercLib.CriticalLRP.TreeExpansion.subadditiveTreeSum_one
#print axioms PercLib.CriticalLRP.TreeExpansion.treeSumAt_one
#print axioms PercLib.CriticalLRP.TreeExpansion.treeSumAt_zero_exponent
#print axioms PercLib.CriticalLRP.TreeExpansion.spatial_tree_graph_of_subadditive
#print axioms PercLib.CriticalLRP.TreeExpansion.spatial_tree_graph_printed_of_subadditive
#print axioms PercLib.CriticalLRP.TreeExpansion.spatial_tree_graph_printed_of_additiveTreeSum
#print axioms PercLib.CriticalLRP.TreeExpansion.spatial_tree_graph_of_bk_subadditive
#print axioms PercLib.CriticalLRP.TreeExpansion.spatial_tree_graph_printed_of_bk_subadditive
#print axioms PercLib.CriticalLRP.TreeExpansion.spatial_tree_graph_one_of_subadditive
#print axioms PercLib.CriticalLRP.TreeExpansion.spatial_tree_graph_two_of_subadditive
#print axioms PercLib.CriticalLRP.TreeExpansion.zmod4Dist_subadd
#print axioms PercLib.CriticalLRP.TreeExpansion.exists_nonvacuous_subadditive_weight
#print axioms PercLib.CriticalLRP.TreeExpansion.abs_addHom_eq_zero
