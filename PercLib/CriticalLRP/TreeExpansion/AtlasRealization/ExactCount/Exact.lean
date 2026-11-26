/- Independently reviewed exact-count proof from smwwtnhaw/m1, with a
strict fresh rebuild and standard-axiom audit at the current integration bank. -/
/-
Independent UltraMath work, swarm `smwwtnhaw`, member `m1`.
Production base `4c53bb5a8e76a4358a426adf71169b916b90f51f` (read-only package
`.scratch/critical-lrp-orchestration`), Lean 4.35.0. Nothing outside this directory is modified.
-/
module

public import PercLib.CriticalLRP.TreeExpansion.AtlasRealization.ExactCount.Peel

/-!
# The exact plane-tree count and the exact child-swap orbit count

With `RTree.insertMap_injective` (`OrbitCount/Peel.lean`) and production's
`RTree.insertMap_surjective`, the insertion map is a bijection

`(Σ t : RTree.LT α, Pos t.val × Bool) ≃ RTree.LT (α ⊕ PUnit)`,

so the insertion inequality `RTree.card_LT_sum` becomes the equality `RTree.card_LT_sum_eq`,
and the counting recursion `RTree.card_LT_fin_succ_eq` becomes exact:

`#(LT (Fin (n+1))) = 2^n * (2n-1)!!`   (`RTree.card_LT_fin_eq`, `VolumeMoments.M`).

Feeding the exact plane count into the already proved equal-size orbit partition
(`RTree.card_swapOrbits_mul`, whose classes all have `2^(p-1)` plane representatives) gives the
exact number of child-swap orbits,

`#(RTree.swapOrbits (Fin p)) = VolumeMoments.M (p-1)`  for `p ≥ 1`
(`RTree.card_swapOrbits_fin_eq_dfactorial`), i.e. `(2p-3)!!` non-plane rooted binary trees with
`p` distinctly labelled leaves.

`p = 0` is genuinely excluded: `#(swapOrbits (Fin 0)) = 0` while `VolumeMoments.M 0 = 1`
(`RTree.card_swapOrbits_fin_zero`), because there is no fully labelled tree with no leaves.
-/

set_option autoImplicit false

@[expose] public section

namespace PercLib.CriticalLRP.TreeExpansion

namespace RTree

variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]

/-! ### The insertion map is a bijection -/

/-- **The insertion map is a bijection.**  The explicit equivalence is
`Equiv.ofBijective (insertMap (α := α)) RTree.insertMap_bijective`. -/
theorem insertMap_bijective : Function.Bijective (insertMap (α := α)) :=
  ⟨insertMap_injective, insertMap_surjective⟩

variable [Fintype (LT α)]

/-- **The exact counting recursion.**  Every fully labelled tree with `#α + 1` leaves arises from
exactly one fully labelled tree with `#α` leaves, one of its `2·#α − 1` vertices, and one of
the two sides: the insertion map is bijective, so the inequality `RTree.card_LT_sum` is an
equality. -/
theorem card_LT_sum_eq :
    Fintype.card (LT (α ⊕ PUnit)) = 2 * (2 * Fintype.card α - 1) * Fintype.card (LT α) := by
  have hcard : Fintype.card (LT (α ⊕ PUnit)) = Fintype.card (Σ t : LT α, Pos t.val × Bool) :=
    (Fintype.card_congr (Equiv.ofBijective (insertMap (α := α)) insertMap_bijective)).symm
  rw [hcard, Fintype.card_sigma]
  calc ∑ t : LT α, Fintype.card (Pos t.val × Bool)
      = ∑ _t : LT α, (2 * (2 * Fintype.card α - 1)) := by
        refine Finset.sum_congr rfl fun t _ => ?_
        have hle : (t : LT α).1.numLeaves = Fintype.card α := t.2.2
        rw [Fintype.card_prod, Fintype.card_bool, card_pos, hle]
        exact Nat.mul_comm _ 2
    _ = 2 * (2 * Fintype.card α - 1) * Fintype.card (LT α) := by
        rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_comm]

/-! ### The exact plane count for `Fin n` -/

/-- The exact counting recursion for `Fin n`. -/
theorem card_LT_fin_succ_eq (n : ℕ) :
    Fintype.card (LT (Fin (n + 2))) =
      2 * (2 * (n + 1) - 1) * Fintype.card (LT (Fin (n + 1))) := by
  have h := card_LT_sum_eq (α := Fin (n + 1))
  rw [← Fintype.card_congr (LTEquiv (finSuccEquivSum (n + 1)))] at h
  simpa using h

/-- **The exact number of plane trees**: `#(LT (Fin (n+1))) = 2^n * (2n-1)!!`.  Production's
`RTree.card_LT_fin_le` is the inequality `≤`; injectivity of the insertion map makes it an
equality. -/
theorem card_LT_fin_eq (m : ℕ) :
    Fintype.card (LT (Fin (m + 1))) = 2 ^ m * VolumeMoments.M m := by
  induction m with
  | zero => simpa using card_LT_fin_one
  | succ k ih =>
      have hrec := card_LT_fin_succ_eq k
      have hM : VolumeMoments.M (k + 1) = (2 * k + 1) * VolumeMoments.M k :=
        VolumeMoments.M_succ k
      have hexp : 2 * (2 * (k + 1) - 1) = 2 * (2 * k + 1) := by omega
      rw [hexp] at hrec
      rw [hrec, ih, hM]
      ring

/-! ### The exact child-swap orbit count -/

/-- The same count for `p = m + 1`, in the form used to derive it. -/
theorem card_swapOrbits_fin_succ_eq (m : ℕ) :
    (swapOrbits (Fin (m + 1))).card = VolumeMoments.M m := by
  have hidx : (Fintype.card (Fin (m + 1)) - 1) = m := by simp
  have hpos : 0 < 2 ^ m := pow_pos (by norm_num) m
  rw [card_swapOrbits_eq_div (α := Fin (m + 1)), card_LT_fin_eq m, hidx,
    mul_comm (2 ^ m) (VolumeMoments.M m), Nat.mul_div_left _ hpos]

/-- **The exact orbit count.**  Every child-swap orbit of `RTree.LT (Fin p)` has exactly
`2^(p-1)` plane representatives (`RTree.swapOrbits_card`), the orbits partition the family
(`RTree.card_swapOrbits_mul`), and the exact plane count is `2^(p-1) * (2p-3)!!`
(`RTree.card_LT_fin_eq`), so for `p ≥ 1` there are exactly `(2p-3)!!` orbits, i.e. non-plane
rooted binary trees with `p` distinctly labelled leaves. -/
theorem card_swapOrbits_fin_eq_dfactorial (p : ℕ) (hp : 1 ≤ p) :
    (swapOrbits (Fin p)).card = VolumeMoments.M (p - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, p = m + 1 := ⟨p - 1, by omega⟩
  simpa using card_swapOrbits_fin_succ_eq m

/-- The excluded case: with no labels there is no fully labelled tree, so there is no orbit at
all, while the double-factorial convention gives `VolumeMoments.M 0 = 1`. -/
theorem card_swapOrbits_fin_zero : (swapOrbits (Fin 0)).card = 0 := by
  have hempty : Fintype.card (LT (Fin 0)) = 0 := Fintype.card_eq_zero_iff.mpr instIsEmptyLTFinZero
  rw [card_swapOrbits_eq_div (α := Fin 0), hempty]
  simp

/-- The formula `#(swapOrbits (Fin p)) = VolumeMoments.M (p-1)` fails at `p = 0`; that is why
`RTree.card_swapOrbits_fin_eq_dfactorial` assumes `1 ≤ p`. -/
theorem card_swapOrbits_fin_zero_ne_M :
    (swapOrbits (Fin 0)).card ≠ VolumeMoments.M 0 := by
  rw [card_swapOrbits_fin_zero, VolumeMoments.M_zero]
  exact Nat.zero_ne_one

end RTree

end PercLib.CriticalLRP.TreeExpansion
