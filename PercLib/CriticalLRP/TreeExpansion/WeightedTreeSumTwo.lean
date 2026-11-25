/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

module

public import PercLib.CriticalLRP.TreeExpansion.SpatialTreeGraph
public import PercLib.CriticalLRP.TreeExpansion.ThreePointBridge

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

set_option autoImplicit true

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

/-!
# The honest (non-vacuous) spatial tree-sum input

`WeightedTreeSum` in `SpatialTreeGraph.lean` quantifies over `φ : V →+ ℝ` with `V` a *finite*
abelian group, so `φ ≡ 0` (`addMonoidHom_eq_zero_of_finite`) and the inequality is vacuous for
`p > 0`.  This file records the repair and proves its `n = 2` instance: the weight is an
arbitrary `A : V → ℝ` subject to the *path subadditivity* which the source obtains from
`(∑ a_m)^p ≤ ℓ^{max(p-1,0)} ∑ a_m^p` for `A = |⟨·,u⟩|^p`.  This hypothesis is non-vacuous on a
finite group (e.g. `A x = |φ x|^p` for additive `φ`, or the circular distance on `ZMod N`), and
for `n = 2` it gives exactly the source's constant `2^{max(p,1)} (E|K|)^2`.
-/

@[expose] public section

namespace PercLib.CriticalLRP.TreeExpansion

open Finset
open PercLib.CriticalLRP PercLib.CriticalLRP.TreeGraph

variable {V : Type*} [AddCommGroup V] [Fintype V] [DecidableEq V]

/-! ## Splitting a sum over `Fin 2 → V` into two coordinates -/

/-- `(Fin 2 → V) ≃ V × V`. -/
def finTwoArrowEquiv : (Fin 2 → V) ≃ V × V where
  toFun x := (x 0, x 1)
  invFun p := ![p.1, p.2]
  left_inv x := by
    funext i
    fin_cases i <;> simp
  right_inv p := by
    simp

theorem sum_finTwoArrow (F : (Fin 2 → V) → ℝ) :
    (∑ x : Fin 2 → V, F x) = ∑ a : V, ∑ b : V, F ![a, b] := by
  refine (Fintype.sum_equiv finTwoArrowEquiv F (fun p : V × V => F ![p.1, p.2]) ?_).trans ?_
  · intro x
    show F x = F ![x 0, x 1]
    congr 1
    funext i
    fin_cases i <;> simp
  · exact Fintype.sum_prod_type (f := fun p : V × V => F ![p.1, p.2])

/-! ## The elementary exponent identity -/

theorem two_rpow_max (p : ℝ) :
    (2 : ℝ) ^ (max p 1) = 2 * (2 : ℝ) ^ (max (p - 1) 0) := by
  rcases lt_or_ge p 1 with h | h
  · rw [max_eq_right h.le, max_eq_right (by linarith : p - 1 ≤ 0), Real.rpow_zero, mul_one,
      Real.rpow_one]
  · rw [max_eq_left h, max_eq_left (by linarith : (0 : ℝ) ≤ p - 1)]
    have hp : p = 1 + (p - 1) := by ring
    rw [hp, Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_one]
    ring

/-! ## The `n = 2` marked-leaf computation with a general weight -/

/-- **The `n = 2` marked-leaf tree-sum bound with a general weight.**  For a kernel with
translation invariance `k a b = k 0 (b - a)` and a weight `A ≥ 0` that is `p`-subadditive for
two terms, the tree sum with the weight on the second leaf is at most
`2^{max(p,1)} (∑_y k 0 y)^2 ∑_y A y ^ p k 0 y` — the `n = 2` instance of `WeightedTreeSum`
(`(2·2−3)!! = 1`, `2^{max(p,1)}`, exponent `2·2−2 = 2`) with an arbitrary leaf weight. -/
theorem weightedTreeSum_two_general (k : V → V → ℝ)
    (hinv : ∀ a b : V, k a b = k 0 (b - a)) (hk0 : ∀ a b : V, 0 ≤ k a b)
    (A : V → ℝ) (hA0 : ∀ y : V, 0 ≤ A y) {p : ℝ} (hp : 0 ≤ p)
    (hsub : ∀ a b : V, A (a + b) ^ p ≤ (2 : ℝ) ^ (max (p - 1) 0) * (A a ^ p + A b ^ p)) :
    (∑ x : Fin 2 → V, A (x 1) ^ p * treeSum k 2 0 x)
      ≤ (2 : ℝ) ^ (max p 1) * (∑ y : V, k 0 y) ^ 2 * ∑ y : V, A y ^ p * k 0 y := by
  classical
  set S : ℝ := ∑ y : V, k 0 y with hSdef
  set Q : ℝ := ∑ y : V, A y ^ p * k 0 y with hQdef
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun y _ => hk0 0 y
  have hQ0 : 0 ≤ Q :=
    Finset.sum_nonneg fun y _ => mul_nonneg (Real.rpow_nonneg (hA0 y) p) (hk0 0 y)
  -- row sums are constant
  have hrow : ∀ w : V, ∑ x : V, k w x = S := by
    intro w
    rw [hSdef, Finset.sum_congr rfl fun x _ => hinv w x]
    have hb : (∑ x : V, k 0 (x + -w)) = ∑ z : V, k 0 z := by
      refine (Fintype.sum_equiv (Equiv.addRight w) (fun z : V => k 0 z)
        (fun x : V => k 0 (x + -w)) ?_).symm
      intro z
      show k 0 z = k 0 (z + w + -w)
      rw [add_assoc, add_neg_cancel, add_zero]
    simpa [sub_eq_add_neg] using hb
  -- the inner (translated) sum
  have hinner : ∀ w : V, ∑ x : V, A x ^ p * k w x
      ≤ (2 : ℝ) ^ (max (p - 1) 0) * (Q + A w ^ p * S) := by
    intro w
    have h1 : (∑ x : V, A x ^ p * k w x) = ∑ x : V, A x ^ p * k 0 (x + -w) := by
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [hinv w x, sub_eq_add_neg]
    have h2 : (∑ x : V, A x ^ p * k 0 (x + -w)) = ∑ z : V, A (z + w) ^ p * k 0 z := by
      refine (Fintype.sum_equiv (Equiv.addRight w)
        (fun z : V => A (z + w) ^ p * k 0 z) (fun x : V => A x ^ p * k 0 (x + -w)) ?_).symm
      intro z
      show A (z + w) ^ p * k 0 z = A (z + w) ^ p * k 0 (z + w + -w)
      rw [add_assoc, add_neg_cancel, add_zero]
    rw [h1, h2]
    calc ∑ z : V, A (z + w) ^ p * k 0 z
        ≤ ∑ z : V, ((2 : ℝ) ^ (max (p - 1) 0) * (A z ^ p + A w ^ p)) * k 0 z :=
          Finset.sum_le_sum fun z _ => mul_le_mul_of_nonneg_right (hsub z w) (hk0 0 z)
      _ = (2 : ℝ) ^ (max (p - 1) 0) * (Q + A w ^ p * S) := by
          have hz : ∀ z : V, ((2 : ℝ) ^ (max (p - 1) 0) * (A z ^ p + A w ^ p)) * k 0 z
              = (2 : ℝ) ^ (max (p - 1) 0) * (A z ^ p * k 0 z)
                + (2 : ℝ) ^ (max (p - 1) 0) * (A w ^ p) * k 0 z := by
            intro z
            ring
          rw [Finset.sum_congr rfl fun z _ => hz z, Finset.sum_add_distrib, ← Finset.mul_sum,
            ← Finset.mul_sum, ← hQdef, ← hSdef]
          ring
  -- assemble the double sum
  have hmain : (∑ x : Fin 2 → V, A (x 1) ^ p * treeSum k 2 0 x)
      = ∑ w : V, k 0 w * ((∑ a : V, k w a) * ∑ b : V, A b ^ p * k w b) := by
    rw [sum_finTwoArrow]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    have hstep : ∀ a b : V, A b ^ p * treeSum k 2 0 ![a, b]
        = ∑ w : V, k 0 w * (k w a * (A b ^ p * k w b)) := by
      intro a b
      rw [treeSum_two, Finset.mul_sum]
      refine Finset.sum_congr rfl fun w _ => ?_
      show A b ^ p * (k 0 w * k w (![a, b] 0) * k w (![a, b] 1)) = _
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      ring
    rw [Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => hstep a b]
    calc ∑ a : V, ∑ b : V, ∑ w : V, k 0 w * (k w a * (A b ^ p * k w b))
        = ∑ a : V, ∑ w : V, ∑ b : V, k 0 w * (k w a * (A b ^ p * k w b)) := by
          refine Finset.sum_congr rfl fun a _ => ?_
          exact Finset.sum_comm
      _ = ∑ w : V, ∑ a : V, ∑ b : V, k 0 w * (k w a * (A b ^ p * k w b)) :=
          Finset.sum_comm
      _ = ∑ w : V, k 0 w * ((∑ a : V, k w a) * ∑ b : V, A b ^ p * k w b) := by
          refine Finset.sum_congr rfl fun w _ => ?_
          have e1 : (∑ a : V, ∑ b : V, k 0 w * (k w a * (A b ^ p * k w b)))
              = k 0 w * ∑ a : V, ∑ b : V, k w a * (A b ^ p * k w b) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun a _ => ?_
            rw [Finset.mul_sum]
          have e2 : (∑ a : V, ∑ b : V, k w a * (A b ^ p * k w b))
              = (∑ a : V, k w a) * ∑ b : V, A b ^ p * k w b := by
            rw [Fintype.sum_mul_sum]
          rw [e1, e2]
  -- the final three-factor estimate
  have hmain' : (∑ x : Fin 2 → V, A (x 1) ^ p * treeSum k 2 0 x)
      = ∑ w : V, k 0 w * (S * ∑ b : V, A b ^ p * k w b) := by
    rw [hmain]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [hrow w]
  rw [hmain']
  calc ∑ w : V, k 0 w * (S * ∑ b : V, A b ^ p * k w b)
      ≤ ∑ w : V, k 0 w * (S * ((2 : ℝ) ^ (max (p - 1) 0) * (Q + A w ^ p * S))) := by
        refine Finset.sum_le_sum fun w _ => ?_
        refine mul_le_mul_of_nonneg_left ?_ (hk0 0 w)
        exact mul_le_mul_of_nonneg_left (hinner w) hS0
    _ = (2 : ℝ) ^ (max (p - 1) 0) * S * (Q * S + S * Q) := by
        have hz : ∀ w : V,
            k 0 w * (S * ((2 : ℝ) ^ (max (p - 1) 0) * (Q + A w ^ p * S)))
              = (2 : ℝ) ^ (max (p - 1) 0) * S * (Q * k 0 w) +
                (2 : ℝ) ^ (max (p - 1) 0) * S * S * (A w ^ p * k 0 w) := by
          intro w
          ring_nf
        rw [Finset.sum_congr rfl fun w _ => hz w, Finset.sum_add_distrib]
        have hA : (∑ w : V, (2 : ℝ) ^ (max (p - 1) 0) * S * (Q * k 0 w))
            = (2 : ℝ) ^ (max (p - 1) 0) * S * (Q * S) := by
          rw [show (∑ w : V, (2 : ℝ) ^ (max (p - 1) 0) * S * (Q * k 0 w))
              = (2 : ℝ) ^ (max (p - 1) 0) * S * ∑ w : V, Q * k 0 w from
            (Finset.mul_sum _ _ _).symm]
          rw [show (∑ w : V, Q * k 0 w) = Q * S from by
            rw [show (∑ w : V, Q * k 0 w) = Q * ∑ w : V, k 0 w from
              (Finset.mul_sum _ _ _).symm, ← hSdef]]
        have hB : (∑ w : V, (2 : ℝ) ^ (max (p - 1) 0) * S * S * (A w ^ p * k 0 w))
            = (2 : ℝ) ^ (max (p - 1) 0) * S * S * Q := by
          rw [show (∑ w : V, (2 : ℝ) ^ (max (p - 1) 0) * S * S * (A w ^ p * k 0 w))
              = (2 : ℝ) ^ (max (p - 1) 0) * S * S * ∑ w : V, A w ^ p * k 0 w from
            (Finset.mul_sum _ _ _).symm, ← hQdef]
        rw [hA, hB]
        ring
    _ = (2 : ℝ) ^ (max p 1) * S ^ 2 * Q := by
        rw [two_rpow_max]
        ring_nf

end PercLib.CriticalLRP.TreeExpansion

namespace PercLib.CriticalLRP.TreeExpansion

open PercLib.CriticalLRP PercLib.CriticalLRP.TreeGraph

variable {V : Type*} [AddCommGroup V] [Fintype V] [DecidableEq V]
variable {E : Type*} [Fintype E] [DecidableEq E]

/-- The repository's translation invariance (read off at `o`) is the same as reading it off
at `0`: `P(a ↔ b) = T(b − a)`. -/
theorem twoPoint_hinv_zero (pr : E → ℝ) (ends : E → Sym2 V) (o : V)
    (hinv : ∀ a b : V, twoPoint pr ends a b = twoPoint pr ends o (b - a)) :
    ∀ a b : V, twoPoint pr ends a b = twoPoint pr ends (0 : V) (b - a) := by
  intro a b
  rw [hinv a b, hinv 0 (b - a)]
  simp

/-- **The `n = 2` marked-leaf bound in the repository's own terms**, with a general (not
necessarily additive) leaf weight `A` subject to the two-term `p`-subadditivity that the
source's telescoping produces. -/
theorem weightedTreeSum_two_of_prob (pr : E → ℝ) (hp : ∀ e, 0 ≤ pr e) (hp1 : ∀ e, pr e ≤ 1)
    (ends : E → Sym2 V) (o : V)
    (hinv : ∀ a b : V, twoPoint pr ends a b = twoPoint pr ends o (b - a))
    (A : V → ℝ) (hA0 : ∀ y : V, 0 ≤ A y) {p : ℝ} (hp0 : 0 ≤ p)
    (hsub : ∀ a b : V, A (a + b) ^ p ≤ (2 : ℝ) ^ (max (p - 1) 0) * (A a ^ p + A b ^ p)) :
    (∑ x : Fin 2 → V, A (x 1) ^ p * treeSum (twoPoint pr ends) 2 (0 : V) x)
      ≤ (VolumeMoments.M 1 : ℝ) * (2 : ℝ) ^ (max p 1) *
          (clusterVolume pr ends (0 : V)) ^ (2 * 2 - 2) *
          ∑ y : V, A y ^ p * twoPoint pr ends (0 : V) y := by
  have h := weightedTreeSum_two_general (k := twoPoint pr ends)
    (twoPoint_hinv_zero pr ends o hinv) (fun a b => twoPoint_nonneg hp hp1 ends a b)
    A hA0 (p := p) hp0 hsub
  simpa [VolumeMoments.M, clusterVolume, Finset.prod_range_succ] using h

#print axioms PercLib.CriticalLRP.TreeExpansion.weightedTreeSum_two_general
#print axioms PercLib.CriticalLRP.TreeExpansion.weightedTreeSum_two_of_prob

end PercLib.CriticalLRP.TreeExpansion
