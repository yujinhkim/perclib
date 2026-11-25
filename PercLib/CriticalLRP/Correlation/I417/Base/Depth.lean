/- Integrated from independently rebuilt Ultramath work.
Production base 38371c8354fd1b28220794b007003710ea155dea.
Scratch source: ../../.ultramath/smwvlmbqa/m6/Depth.lean; module paths rewritten.
-/

module

public import PercLib.CriticalLRP.Correlation.I417.Base.Marked
public import PercLib.CriticalLRP.Correlation.I417.Base.Poly

/-!
# The marked diagram family collapses to a finite polygon sum with integer coefficients

`Marked.tsum_wtE_marked` evaluates a *single* marked diagram: a rooted binary tree with one
leaf pinned at `w` and the other leaves and internal vertices summed over is worth
`χ^(2p+1-ℓ) T^ℓ(x,w)`, `ℓ` the depth of the marked leaf, whatever the shape of the tree.

This file sums a whole finite family `S` of marked diagrams (as supplied by the marked
tree-graph expansion of the base side of Lemma I.4.17) and groups it by the marked depth:
the family collapses to

  `∑_{ℓ=a}^{b} C_ℓ χ^(2p+1-ℓ) T^ℓ(x,w)`,

`C_ℓ = #{A ∈ S | depth A = ℓ}` the number of diagrams whose marked path has length `ℓ`.  This
is exactly the source's

> "`C_{p,q,ℓ}` counts the number of diagrams in the bound in which the path connecting `x`
> and `y` has length `ℓ`"

with the coefficients produced as explicit finite cardinalities (`Finset.card`), not assumed.

## Range convention

The bounds `a ≤ depth ≤ b` on the marked leaf are a **hypothesis** here, because they are a
statement about which diagrams the tree-graph expansion produces, not about their values.
At `q = 1`, composing once with `Poly.tsum_iterPow_mul` turns a base marked path of depth
`ℓ` into a path of length `ℓ + 1`. The source's range `3 ≤ ℓ ≤ p+q+1` then corresponds
to `2 ≤ ℓ ≤ p+1` before composition. A plain rooted-tree expansion can also produce
marked paths of depth `1`, so no lower bound is invented here. Consumers must supply the
depth restriction for the actual diagram family; the parameter `a` accommodates both the
printed range (`a = 2`) and any broader family (`a = 1`).

Everything unconditional: no probability, only the constant-row-sum hypothesis on the kernel.
-/

open scoped ENNReal NNReal

@[expose] public section

namespace PercLib.CriticalLRP.I417Base

open PercLib.CriticalLRP.TreeExpansion

variable {V : Type*} [DecidableEq V]

/-! ## Summing a finite family by the value of a `ℕ`-valued statistic -/

/-- **Grouping a finite sum by the fibres of a statistic**, `ℝ≥0∞` version.  If every `A ∈ S`
has `d A < m` then summing `g (d A)` over `S` is the same as summing, over `ℓ < m`, the number
of `A ∈ S` with `d A = ℓ` times `g ℓ`. -/
theorem finset_sum_by_fiber {ι : Type*} (S : Finset ι) (g : ℕ → ℝ≥0∞) (d : ι → ℕ) (m : ℕ)
    (hm : ∀ A ∈ S, d A < m) :
    (∑ A ∈ S, g (d A))
      = ∑ ℓ ∈ Finset.range m, ((S.filter (fun A => d A = ℓ)).card : ℝ≥0∞) * g ℓ := by
  classical
  have h1 : ∀ ℓ : ℕ, ((S.filter (fun A => d A = ℓ)).card : ℝ≥0∞) * g ℓ
      = ∑ A ∈ S, (if d A = ℓ then g ℓ else 0) := by
    intro ℓ
    rw [Finset.card_filter, Nat.cast_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun A _ => ?_
    split_ifs <;> simp
  rw [Finset.sum_congr rfl fun ℓ (_ : ℓ ∈ Finset.range m) => h1 ℓ, Finset.sum_comm]
  refine Finset.sum_congr rfl fun A hA => ?_
  rw [Finset.sum_ite_eq]
  simp [Finset.mem_range.mpr (hm A hA)]

/-! ## The marked family as a polygon sum -/

/-- **The marked diagram family is a polygon/two-point matrix sum.**  For a finite family `S`
of marked diagrams, all with `p+1` leaves and marked leaf of depth between `a` and `b`, the
total diagram value (leaf values summed, mark pinned at `w`) is

  `∑_{ℓ=a}^{b} C_ℓ χ^(2p+1-ℓ) T^ℓ(x,w)`,  `C_ℓ = #{A ∈ S | RTree.depth A = ℓ}`. -/
theorem marked_diagram_by_depth {α : Type*} (k : V → V → ℝ≥0∞) (χ : ℝ≥0∞)
    (hχ : ∀ v, ∑' y, k v y = χ) (p a b : ℕ) (S : Finset ((t : RTree α) × t.LeafPos))
    (hleaf : ∀ A ∈ S, A.1.numLeaves = p + 1)
    (hlo : ∀ A ∈ S, a ≤ RTree.depth A.1 A.2)
    (hhi : ∀ A ∈ S, RTree.depth A.1 A.2 ≤ b) (x w : V) :
    (∑ A ∈ S, ∑' y : A.1.LeafPos → V, (if y A.2 = w then 1 else 0) * wtE k A.1 y x)
      = ∑ ℓ ∈ Finset.Icc a b,
          ((S.filter (fun A => RTree.depth A.1 A.2 = ℓ)).card : ℝ≥0∞) *
            (χ ^ (2 * p + 1 - ℓ) * iterPow k ℓ x w) := by
  classical
  -- the value of a single marked diagram
  have hterm : ∀ A ∈ S,
      (∑' y : A.1.LeafPos → V, (if y A.2 = w then 1 else 0) * wtE k A.1 y x)
        = χ ^ (2 * p + 1 - RTree.depth A.1 A.2) * iterPow k (RTree.depth A.1 A.2) x w := by
    intro A hA
    rw [tsum_wtE_marked k χ hχ A.1 A.2 x w, pathW_eq_iterPow k A.1 A.2 x w, hleaf A hA]
    have h2p : 2 * (p + 1) - 1 = 2 * p + 1 := by omega
    rw [h2p]
  rw [Finset.sum_congr rfl hterm]
  -- every depth lies in `range (b+1)`
  have hbm : ∀ A ∈ S, RTree.depth A.1 A.2 < b + 1 := fun A hA => by
    have := hhi A hA; omega
  have hmain := finset_sum_by_fiber S
    (fun ℓ => χ ^ (2 * p + 1 - ℓ) * iterPow k ℓ x w)
    (fun A => RTree.depth A.1 A.2) (b + 1) hbm
  rw [hmain]
  -- the terms with `ℓ < a` vanish, so the range can be cut down to `Icc a b`
  refine (Finset.sum_subset ?hsub ?hzero).symm
  · intro ℓ hℓ
    simp only [Finset.mem_Icc] at hℓ
    exact Finset.mem_range.mpr (by omega)
  · intro ℓ hℓmem hℓ
    have hle : ℓ ≤ b := by simpa using hℓmem
    have hlt : ℓ < a := by
      by_contra hcon
      exact hℓ (Finset.mem_Icc.mpr ⟨by omega, hle⟩)
    have hemp : S.filter (fun A => RTree.depth A.1 A.2 = ℓ) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro A hA heq
      have := hlo A hA
      omega
    rw [hemp]
    simp

end PercLib.CriticalLRP.I417Base
