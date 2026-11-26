/-
Independently rebuilt and integrated from the accepted `smwx6p0op/m2` artifact
`.ultramath/smwx6p0op/m2/GQDepth`. Production integration revision:
`c83993396c566d21a0abe4051ed84dd6dab6093e`. The coordinator uses the production
namespace and fully qualified imports; this package is diagram infrastructure,
not an event-cover theorem.
-/
module

public import PercLib.CriticalLRP.Correlation.I417.Fresh.Subdivision.Range
public import PercLib.CriticalLRP.Correlation.I417.Base.Depth

/-!
Independently built for swarm `smwx6p0op`, member `m2`, direction DEPTH-RANGE-I417.

# The coefficient-weighted fresh diagram bound at arbitrary `q`

Source: T. Hutchcroft, *Critical long-range percolation I: High effective dimension*,
arXiv:2508.18807v1, Lemma I.4.17 (supplied PDF p. 45):

> "We obtain a bound in terms of tree diagrams [...]; in each case, `C_{p,q,ℓ}` counts the number
> of diagrams in the bound in which the path connecting `x` and `y` has length `ℓ`."

The **marked** (base) side of that sentence is production's `I417Base.marked_diagram_by_depth`: the
finite marked family collapses to `∑_{ℓ=a}^{b} C_ℓ χ^(2p+1-ℓ) T^ℓ(x,w)`, with the range `[a,b]` a
hypothesis there.  This file proves the analogous statement for the **fresh** side, with the range
`[1,q]` *derived* rather than assumed:

  `fresh_family_by_depth` — for any finite family of subdivided-edge fresh diagrams with `q` arms
  and mark depth in `[1, RTree.depth t q]`, the total diagram value is exactly

    `∑_{ℓ ∈ [1,q]} C_ℓ · χ^(2q-ℓ) T^ℓ(v,w)`,   `C_ℓ = #{i : dp i = ℓ}`,

  a cardinality, not an assumption.  `C ℓ` is exactly the `C_{p,q,ℓ}` of the source (at `p`-side
  coefficients 1), i.e. the number of fresh diagrams whose marked path has length `ℓ`.

So a consumer who has an event-level cover of the fresh event by this diagram family (the
`q`-dependent combinatorics; member `m1`'s direction) obtains the printed normalisation
`∑_{ℓ=1}^{q} C_ℓ χ^(2q-ℓ) T^ℓ` with no further hypothesis: in particular the `χ`- and
`T`-exponents always total `2q`, and the deepest possible `T`-power is `T^q`.

No probability, BK, moment or transitivity input: the only hypothesis is the constant row sum `χ`.
-/

open scoped ENNReal NNReal

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false

@[expose] public section

namespace PercLib.CriticalLRP.I417Fresh.Subdivision

open PercLib.CriticalLRP.TreeExpansion
open PercLib.CriticalLRP.I417Base

universe u

variable {V : Type*} [Countable V] [DecidableEq V]

/-- **The fresh diagram family is a coefficient-weighted polygon sum.**  For a finite family `S` of
subdivided-edge fresh diagrams (shape `T i`, marked arm `P i`, mark depth `dp i`) each with `q` arms
and mark depth in `[1, RTree.depth (T i) (P i)]`, the total value of the family is

  `∑_{ℓ ∈ [1,q]} C_ℓ · χ^(2q-ℓ) · T^ℓ(v,w)`,  `C_ℓ = #{i ∈ S | dp i = ℓ}`.

This is the fresh-side counterpart of `I417Base.marked_diagram_by_depth`, with the depth range
`[1,q]` proved (`subW_depth_le_numLeaves`, `RTree.depth_pos`) instead of assumed. -/
theorem fresh_family_by_depth {α : Type u} {ι : Type*} (k : V → V → ℝ≥0∞) (χ : ℝ≥0∞)
    (hχ : ∀ v, ∑' y, k v y = χ) (q : ℕ) (S : Finset ι)
    (T : ι → RTree α) (P : (i : ι) → (T i).LeafPos) (dp : ι → ℕ)
    (hleaves : ∀ i ∈ S, (T i).numLeaves = q)
    (hlo : ∀ i ∈ S, 1 ≤ dp i)
    (hhi : ∀ i ∈ S, dp i ≤ RTree.depth (T i) (P i)) (v w : V) :
    (∑ i ∈ S, subW k (T i) (P i) (dp i) v w) =
      freshPoly k χ q (fun ℓ => (S.filter (fun i => dp i = ℓ)).card) v w := by
  classical
  -- each diagram is worth the monomial determined by `(q, ℓ)`
  have hterm : ∀ i ∈ S, subW k (T i) (P i) (dp i) v w
      = χ ^ (2 * q - dp i) * iterPow k (dp i) v w := by
    intro i hi
    rw [subW_eq k χ hχ (T i) (P i) (dp i) v w (hlo i hi) (hhi i hi), hleaves i hi]
  rw [Finset.sum_congr rfl hterm]
  -- the depths lie below `q + 1`
  have hm : ∀ i ∈ S, dp i < q + 1 := by
    intro i hi
    have h1 : dp i ≤ RTree.depth (T i) (P i) := hhi i hi
    have h2 : RTree.depth (T i) (P i) ≤ (T i).numLeaves := RTree.depth_le_numLeaves _ _
    have h3 : (T i).numLeaves = q := hleaves i hi
    omega
  rw [finset_sum_by_fiber S (fun ℓ => χ ^ (2 * q - ℓ) * iterPow k ℓ v w) dp (q + 1) hm]
  rw [freshPoly]
  -- cut the range `[0,q]` down to `[1,q]`: the `ℓ = 0` fibre is empty
  refine (Finset.sum_subset ?hsub ?hzero).symm
  · intro ℓ hℓ
    simp only [Finset.mem_Icc] at hℓ
    exact Finset.mem_range.mpr (by omega)
  · intro ℓ hℓmem hℓ
    have hlt : ℓ < 1 := by
      simp only [Finset.mem_range] at hℓmem
      by_contra hcon
      exact hℓ (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
    have hemp : S.filter (fun i => dp i = ℓ) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro i hi heq
      have := hlo i hi
      omega
    rw [hemp]
    simp

end PercLib.CriticalLRP.I417Fresh.Subdivision
