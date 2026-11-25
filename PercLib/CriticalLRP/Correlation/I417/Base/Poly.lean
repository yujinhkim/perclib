/- Integrated from independently rebuilt Ultramath work.
Production base 38371c8354fd1b28220794b007003710ea155dea.
Scratch source: ../../.ultramath/smwvlmbqa/m6/Poly.lean; module paths rewritten.
-/

module

public import PercLib.CriticalLRP.Correlation.I417.Base.Defs
public import PercLib.CriticalLRP.Correlation.I417.Base.Marked

/-!
# Powers of a kernel: right recursion, symmetry, and the polygon composition

`iterPow k n` (`Defs.lean`) is the `n`-th power of the kernel `k`, defined by left
composition, `iterPow k (n+1) v w = ∑_u k v u · iterPow k n u w`.  For the two-point
function of the canonical model this is the matrix power `T^n(v,w)` of Lemma I.4.17 of
Hutchcroft, *Critical long-range percolation I* (arXiv:2508.18807v1, p. 45), and the source's
`∑_{ℓ=3}^{p+q+1} C_{p,q,ℓ} T^ℓ(x,y) (E|K|)^{2p+2q+1-ℓ}` is a sum of exactly these powers.

This file proves what the composition `∑_w T^ℓ(x,w) τ(y,w) = T^{ℓ+1}(y,x)` used in the
`∑_w` step of the source needs:

* `pathW_eq_iterPow` — the marked path weight of `Marked.lean` **is** the matrix power of
  order equal to the depth of the marked leaf (so a marked diagram of depth `ℓ` contributes
  `T^ℓ`);
* `iterPow_succ_right` — right recursion for powers;
* `iterPow_comm` — powers of a symmetric kernel are symmetric;
* `tsum_iterPow_mul` — the polygon composition `∑_w T^ℓ(x,w) τ(y,w) = T^{ℓ+1}(y,x)`;
* `tsum_finset_sum` — a `tsum` of a finite sum is the finite sum of the `tsum`s (the
  Tonelli step that turns the `∑_ℓ` of a diagram family into a `∑_ℓ` of matrix powers).

All unconditional: no probability, only `ℝ≥0∞` arithmetic.
-/

open scoped ENNReal NNReal

@[expose] public section

namespace PercLib.CriticalLRP.I417Base

open PercLib.CriticalLRP.TreeExpansion

variable {V : Type*} [DecidableEq V]

/-! ## Indicator sums -/

theorem tsum_indicator_left (f : V → ℝ≥0∞) (v : V) :
    (∑' u : V, (if v = u then 1 else 0) * f u) = f v := by
  rw [tsum_eq_single v]
  · simp
  · intro b hb
    simp [show ¬ (v = b) from fun h => hb h.symm]

theorem tsum_mul_indicator_right (f : V → ℝ≥0∞) (w : V) :
    (∑' u : V, f u * (if u = w then 1 else 0)) = f w := by
  rw [show (∑' u : V, f u * (if u = w then 1 else 0))
      = ∑' u : V, (if u = w then 1 else 0) * f u from tsum_congr fun u => mul_comm _ _,
    tsum_indicator_mul]

/-! ## The marked path weight is a matrix power -/

/-- **The marked path weight is the `depth`-th matrix power.**  The path weight of the tree
path from the root `v` to the marked leaf `q` is exactly `T^(depth t q)(v,w)`. -/
theorem pathW_eq_iterPow {α : Type*} (k : V → V → ℝ≥0∞) :
    ∀ (t : RTree α) (q : t.LeafPos) (v w : V),
      pathW k t q v w = iterPow k (RTree.depth t q) v w
  | .leaf a, q, v, w => by
      have hsub : Subsingleton (RTree.LeafPos (RTree.leaf a)) :=
        inferInstanceAs (Subsingleton PUnit)
      have hq : q = (⟨⟩ : RTree.LeafPos (RTree.leaf a)) := @Subsingleton.elim _ hsub q _
      rw [hq]
      change k v w = ∑' u : V, k v u * (if u = w then 1 else 0)
      rw [tsum_mul_indicator_right]
  | .node l r, Sum.inl q', v, w => by
      change (∑' u : V, k v u * pathW k l q' u w)
          = ∑' u : V, k v u * iterPow k (RTree.depth l q') u w
      exact tsum_congr fun u => by rw [pathW_eq_iterPow k l q' u w]
  | .node l r, Sum.inr q', v, w => by
      change (∑' u : V, k v u * pathW k r q' u w)
          = ∑' u : V, k v u * iterPow k (RTree.depth r q') u w
      exact tsum_congr fun u => by rw [pathW_eq_iterPow k r q' u w]

/-! ## Right recursion -/

/-- **Right recursion for powers**: composing on the right gives the next power. -/
theorem iterPow_succ_right (k : V → V → ℝ≥0∞) :
    ∀ (n : ℕ) (v w : V), iterPow k (n + 1) v w = ∑' u : V, iterPow k n v u * k u w
  | 0, v, w => by
      change (∑' u : V, k v u * (if u = w then 1 else 0))
          = ∑' u : V, (if v = u then 1 else 0) * k u w
      rw [tsum_mul_indicator_right, tsum_indicator_left]
  | n + 1, v, w => by
      change (∑' u : V, k v u * iterPow k (n + 1) u w)
          = ∑' u : V, iterPow k (n + 1) v u * k u w
      calc (∑' u : V, k v u * iterPow k (n + 1) u w)
          = ∑' u : V, k v u * ∑' t : V, iterPow k n u t * k t w :=
              tsum_congr fun u => by rw [iterPow_succ_right k n u w]
        _ = ∑' u : V, ∑' t : V, k v u * (iterPow k n u t * k t w) :=
              tsum_congr fun u => (ENNReal.tsum_mul_left).symm
        _ = ∑' t : V, ∑' u : V, k v u * (iterPow k n u t * k t w) := ENNReal.tsum_comm
        _ = ∑' t : V, (∑' u : V, k v u * iterPow k n u t) * k t w := by
              refine tsum_congr fun t => ?_
              rw [show (∑' u : V, k v u * (iterPow k n u t * k t w))
                  = ∑' u : V, (k v u * iterPow k n u t) * k t w from
                tsum_congr fun u => (mul_assoc _ _ _).symm,
                ENNReal.tsum_mul_right]
        _ = ∑' t : V, iterPow k (n + 1) v t * k t w :=
              tsum_congr fun t => rfl

/-! ## Symmetry -/

/-- **Powers of a symmetric kernel are symmetric.** -/
theorem iterPow_comm (k : V → V → ℝ≥0∞) (hk : ∀ a b, k a b = k b a) :
    ∀ (n : ℕ) (v w : V), iterPow k n v w = iterPow k n w v
  | 0, v, w => by
      change (if v = w then (1 : ℝ≥0∞) else 0) = (if w = v then 1 else 0)
      simp [eq_comm]
  | n + 1, v, w => by
      change (∑' u : V, k v u * iterPow k n u w) = ∑' u : V, k w u * iterPow k n u v
      calc (∑' u : V, k v u * iterPow k n u w)
          = ∑' u : V, k u v * iterPow k n w u :=
              tsum_congr fun u => by rw [hk v u, iterPow_comm k hk n u w]
        _ = ∑' u : V, iterPow k n w u * k u v := tsum_congr fun u => mul_comm _ _
        _ = iterPow k (n + 1) w v := (iterPow_succ_right k n w v).symm

/-! ## The polygon composition -/

/-- **`∑_w T^ℓ(x,w) τ(y,w) = T^{ℓ+1}(y,x)`**: appending one more edge to a path from `x` to
`w` gives a path from `y` to `x`.  This is the step that turns the `∑_w` of the source's
marked expansion into a higher matrix power (and hence raises `ℓ` by one, moving the sum from
`ℓ ∈ [2,p+1]` to `ℓ ∈ [3,p+2]`). -/
theorem tsum_iterPow_mul (k : V → V → ℝ≥0∞) (hk : ∀ a b, k a b = k b a)
    (n : ℕ) (y x : V) :
    (∑' w : V, iterPow k n x w * k y w) = iterPow k (n + 1) y x := by
  rw [show (∑' w : V, iterPow k n x w * k y w)
      = ∑' w : V, k y w * iterPow k n w x from
    tsum_congr fun w => by rw [iterPow_comm k hk n x w, mul_comm]]
  rfl

/-! ## A `tsum` of a finite sum -/

/-- **Tonelli for a finite index set**: a `tsum` of a finite sum is the finite sum of the
`tsum`s. -/
theorem tsum_finset_sum {ι α : Type*} (s : Finset ι) (f : ι → α → ℝ≥0∞) :
    (∑' a, ∑ i ∈ s, f i a) = ∑ i ∈ s, ∑' a, f i a := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert k s hk ih =>
      calc (∑' a, ∑ i ∈ insert k s, f i a)
          = ∑' a, (f k a + ∑ i ∈ s, f i a) := by
              refine tsum_congr fun a => ?_
              rw [Finset.sum_insert hk]
        _ = (∑' a, f k a) + ∑' a, ∑ i ∈ s, f i a := ENNReal.tsum_add
        _ = (∑' a, f k a) + ∑ i ∈ s, ∑' a, f i a := by rw [ih]
        _ = ∑ i ∈ insert k s, ∑' a, f i a := by
              rw [Finset.sum_insert hk]

end PercLib.CriticalLRP.I417Base
