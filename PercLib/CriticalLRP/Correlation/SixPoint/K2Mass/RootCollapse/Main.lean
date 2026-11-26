/-
Swarm `smwxii2d9`, member `m3`, direction `d1` (`ROOT-CLASS-COLLAPSE`).

# The root-class collapse of the `p = 5`, `k = 2` shape masses

`K2Mass.shapeTotal π x k j` is the mass of the shape event of pattern `k` at split `j`, with the
five non-root terminals summed over all of `V`.  `SixPoint.pat_root_slot` shows that the root
`T 0` sits in comb slot `0` in twelve of the fifteen patterns and in comb slot `2` in the other
three.  The theorem proved here is that this is the *only* way `shapeTotal` depends on `k`:

  `shapeTotal π x k j = shapeTotal π x patSlot0 j`   if `pat k 0 = 0`,
  `shapeTotal π x k j = shapeTotal π x patSlot2 j`   if `pat k 2 = 0`,

with no hypothesis at all on `π` (no invariance, no independence, no finiteness); `x`, `V` and
`j` are arbitrary.  Hence the `105 = 15 * 7` shape masses collapse onto the `14 = 2 * 7` masses of
the two root classes, and the fifth-moment bound `fifth_moment_k2_le_of_rootClass_bounds` of
`K2Mass.Main` holds without its `hcollapse` hypothesis.

The proof is exactly the reindexing of the five free terminal sums.  `shapeTotal` is first
rewritten as the single sum over `u : Fin 5 → V` (`shapeTotal_eq_shapeTotal5`) over the five
terminals `u = ![y, z, w, q, t]`; the comb leaves of pattern `k` are then the vector
`fun i => slotVec x u (pat k i)`, and the mass `leafMass` only sees that vector.  Two patterns
that agree on the root slot differ by a permutation of the four free coordinates (with the sixth
terminal `t` fixed), which is a permutation `σ` of the five summation coordinates fixing `4`;
`SixPoint.TwoJointEval.tsum_fin5_perm` identifies the two total sums.  The fifteen `σ` are given
explicitly, and the leaf-tuple identity is checked slot by slot.

The four internal witnesses `c, u, v, w'` stay summed *inside* the measure throughout: nothing is
factored, no pointwise diagram is asserted, and no shape is identified with another except through
the coordinate reindexing of the five summed terminals.
-/
module

public import PercLib.CriticalLRP.Correlation.SixPoint.K2Mass.RootCollapse.Defs

/-! ## The shape mass is a function of the leaf tuple only -/

open Set MeasureTheory
open scoped ENNReal BigOperators
open PercLib.Percolation.Bond
open PercLib.CriticalLRP.TreeExpansion.FivePoint
open PercLib.CriticalLRP.TreeExpansion.SixPoint

@[expose] public section

namespace PercLib.CriticalLRP.TreeExpansion.SixPoint.K2Mass

variable {V : Type*}

/-- The `i`-th comb leaf of `SixShape` at the terminal vector `![x, u 0, u 1, u 2, u 3, r]`
(i.e. after the pattern `pat k` has been applied) is the `i`-th entry of `slotVec x u`.
This is the only place where `lift5` (the embedding of the first five terminals into the six
terminals) is used. -/
theorem shapeVec_lift5_eq_slotVec (x : V) (u : Fin 5 → V) (r : V) (i : Fin 5) :
    shapeVec x (u 0) (u 1) (u 2) (u 3) r (lift5 i) = slotVec x u i := by
  fin_cases i <;> rfl

/-- **The shape mass only depends on the comb-leaf tuple and the sixth terminal.**  The pattern
`k` enters through the leaf vector `fun i => slotVec x u (pat k i)`. -/
theorem shapeMass_eq_leafMass (π : Sym2 V → unitInterval) (x : V) (k : Fin 15) (j : Fin 7)
    (u : Fin 5 → V) (r : V) :
    shapeMass π x k j (u 0) (u 1) (u 2) (u 3) r =
      leafMass π j (fun i => slotVec x u (pat k i)) r := by
  rw [shapeMass, leafMass]
  simp only [SixShape, shapeVec_lift5_eq_slotVec, shapeVec_five]

/-- **`shapeTotal` as one sum over `Fin 5 → V`.**  The five nested terminal sums are bundled with
`SixPoint.TwoJointEval.tsum_fin5`; no hypothesis on `V` or `π` is used. -/
theorem shapeTotal_eq_shapeTotal5 (π : Sym2 V → unitInterval) (x : V) (k : Fin 15) (j : Fin 7) :
    shapeTotal π x k j = shapeTotal5 π x k j := by
  have key : (∑' u : Fin 5 → V, shapeMass π x k j (u 0) (u 1) (u 2) (u 3) (u 4))
      = ∑' y, ∑' z, ∑' w, ∑' q, ∑' r, shapeMass π x k j y z w q r := by
    rw [PercLib.CriticalLRP.SixPoint.TwoJointEval.tsum_fin5
      (G := fun u : Fin 5 → V => shapeMass π x k j (u 0) (u 1) (u 2) (u 3) (u 4))]
    rfl
  rw [shapeTotal, shapeTotal5, ← key]
  exact tsum_congr fun u => shapeMass_eq_leafMass π x k j u (u 4)

/-! ## Coordinate reindexing of the five summed terminals -/

/-- **The reindexing lemma.**  If a permutation `σ` of the five summation coordinates fixes the
sixth terminal coordinate `4` and carries the leaf tuple of pattern `k` to that of pattern `k'`,
then the two total masses are equal.  This is `TwoJointEval.tsum_fin5_perm` applied to the
summand `v ↦ leafMass π j (slotVec x v ∘ pat k') (v 4)`; the only other input is the pointwise
leaf-tuple identity. -/
theorem shapeTotal5_eq_of_coordPerm (π : Sym2 V → unitInterval) (x : V) (j : Fin 7)
    (k k' : Fin 15) (σ : Equiv.Perm (Fin 5)) (h4 : σ 4 = 4)
    (h : ∀ (u : Fin 5 → V) (i : Fin 5),
      slotVec x u (pat k i) = slotVec x (fun j => u (σ j)) (pat k' i)) :
    shapeTotal5 π x k j = shapeTotal5 π x k' j := by
  rw [shapeTotal5, shapeTotal5]
  have hpt : ∀ u : Fin 5 → V,
      leafMass π j (fun i => slotVec x u (pat k i)) (u 4)
        = (fun v : Fin 5 → V => leafMass π j (fun i => slotVec x v (pat k' i)) (v 4))
            (fun j => u (σ j)) := by
    intro u
    rw [funext (h u)]
    simp only [h4]
  rw [tsum_congr hpt]
  exact PercLib.CriticalLRP.SixPoint.TwoJointEval.tsum_fin5_perm σ
    (fun v : Fin 5 → V => leafMass π j (fun i => slotVec x v (pat k' i)) (v 4))

/-! ## The two root classes of the fifteen labelled patterns

Each pattern is compared with the canonical pattern of its root class: `patSlot0 = 6` (the
identity pattern, root in comb slot `0`) and `patSlot2 = 0` (root in comb slot `2`).  The
permutation of the four free coordinates is read off the pattern: the free coordinate sitting in
comb slot `i` moves to the coordinate of slot `(pat k i) - 1`, and the sixth terminal coordinate
`4` is fixed.  Each `σ` is a permutation, checked by `decide` on `Fin 5`; the leaf-tuple identity
is the five-slot check `pat k = ![…]`, `pat k' = ![…]` followed by `rfl`.
-/

theorem shapeTotal5_rootSlot0 (π : Sym2 V → unitInterval) (x : V) (j : Fin 7) (k : Fin 15)
    (hk : pat k 0 = 0) :
    shapeTotal5 π x k j = shapeTotal5 π x patSlot0 j := by
  fin_cases k
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · -- k = 3
    refine shapeTotal5_eq_of_coordPerm (π := π) (x := x) (j := j) (k := 3)
      (k' := patSlot0)
      (Equiv.ofBijective (fun i : Fin 5 => ![1, 0, 2, 3, 4] i)
        ⟨by decide, (Finite.injective_iff_surjective).1 (by decide)⟩) (by decide) ?_
    intro u i
    have e1 : pat (3 : Fin 15) = ![0, 2, 1, 3, 4] := by funext i; fin_cases i <;> rfl
    have e2 : pat patSlot0 = ![0, 1, 2, 3, 4] :=
      by funext i; fin_cases i <;> rfl
    rw [e1, e2]
    fin_cases i <;> rfl
  · -- k = 4
    refine shapeTotal5_eq_of_coordPerm (π := π) (x := x) (j := j) (k := 4)
      (k' := patSlot0)
      (Equiv.ofBijective (fun i : Fin 5 => ![2, 0, 1, 3, 4] i)
        ⟨by decide, (Finite.injective_iff_surjective).1 (by decide)⟩) (by decide) ?_
    intro u i
    have e1 : pat (4 : Fin 15) = ![0, 3, 1, 2, 4] := by funext i; fin_cases i <;> rfl
    have e2 : pat patSlot0 = ![0, 1, 2, 3, 4] :=
      by funext i; fin_cases i <;> rfl
    rw [e1, e2]
    fin_cases i <;> rfl
  · -- k = 5
    refine shapeTotal5_eq_of_coordPerm (π := π) (x := x) (j := j) (k := 5)
      (k' := patSlot0)
      (Equiv.ofBijective (fun i : Fin 5 => ![3, 0, 1, 2, 4] i)
        ⟨by decide, (Finite.injective_iff_surjective).1 (by decide)⟩) (by decide) ?_
    intro u i
    have e1 : pat (5 : Fin 15) = ![0, 4, 1, 2, 3] := by funext i; fin_cases i <;> rfl
    have e2 : pat patSlot0 = ![0, 1, 2, 3, 4] :=
      by funext i; fin_cases i <;> rfl
    rw [e1, e2]
    fin_cases i <;> rfl
  · -- k = 6
    refine shapeTotal5_eq_of_coordPerm (π := π) (x := x) (j := j) (k := 6)
      (k' := patSlot0)
      (Equiv.ofBijective (fun i : Fin 5 => ![0, 1, 2, 3, 4] i)
        ⟨by decide, (Finite.injective_iff_surjective).1 (by decide)⟩) (by decide) ?_
    intro u i
    have e1 : pat (6 : Fin 15) = ![0, 1, 2, 3, 4] := by funext i; fin_cases i <;> rfl
    have e2 : pat patSlot0 = ![0, 1, 2, 3, 4] :=
      by funext i; fin_cases i <;> rfl
    rw [e1, e2]
    fin_cases i <;> rfl
  · -- k = 7
    refine shapeTotal5_eq_of_coordPerm (π := π) (x := x) (j := j) (k := 7)
      (k' := patSlot0)
      (Equiv.ofBijective (fun i : Fin 5 => ![2, 1, 0, 3, 4] i)
        ⟨by decide, (Finite.injective_iff_surjective).1 (by decide)⟩) (by decide) ?_
    intro u i
    have e1 : pat (7 : Fin 15) = ![0, 3, 2, 1, 4] := by funext i; fin_cases i <;> rfl
    have e2 : pat patSlot0 = ![0, 1, 2, 3, 4] :=
      by funext i; fin_cases i <;> rfl
    rw [e1, e2]
    fin_cases i <;> rfl
  · -- k = 8
    refine shapeTotal5_eq_of_coordPerm (π := π) (x := x) (j := j) (k := 8)
      (k' := patSlot0)
      (Equiv.ofBijective (fun i : Fin 5 => ![3, 1, 0, 2, 4] i)
        ⟨by decide, (Finite.injective_iff_surjective).1 (by decide)⟩) (by decide) ?_
    intro u i
    have e1 : pat (8 : Fin 15) = ![0, 4, 2, 1, 3] := by funext i; fin_cases i <;> rfl
    have e2 : pat patSlot0 = ![0, 1, 2, 3, 4] :=
      by funext i; fin_cases i <;> rfl
    rw [e1, e2]
    fin_cases i <;> rfl
  · -- k = 9
    refine shapeTotal5_eq_of_coordPerm (π := π) (x := x) (j := j) (k := 9)
      (k' := patSlot0)
      (Equiv.ofBijective (fun i : Fin 5 => ![0, 2, 1, 3, 4] i)
        ⟨by decide, (Finite.injective_iff_surjective).1 (by decide)⟩) (by decide) ?_
    intro u i
    have e1 : pat (9 : Fin 15) = ![0, 1, 3, 2, 4] := by funext i; fin_cases i <;> rfl
    have e2 : pat patSlot0 = ![0, 1, 2, 3, 4] :=
      by funext i; fin_cases i <;> rfl
    rw [e1, e2]
    fin_cases i <;> rfl
  · -- k = 10
    refine shapeTotal5_eq_of_coordPerm (π := π) (x := x) (j := j) (k := 10)
      (k' := patSlot0)
      (Equiv.ofBijective (fun i : Fin 5 => ![1, 2, 0, 3, 4] i)
        ⟨by decide, (Finite.injective_iff_surjective).1 (by decide)⟩) (by decide) ?_
    intro u i
    have e1 : pat (10 : Fin 15) = ![0, 2, 3, 1, 4] := by funext i; fin_cases i <;> rfl
    have e2 : pat patSlot0 = ![0, 1, 2, 3, 4] :=
      by funext i; fin_cases i <;> rfl
    rw [e1, e2]
    fin_cases i <;> rfl
  · -- k = 11
    refine shapeTotal5_eq_of_coordPerm (π := π) (x := x) (j := j) (k := 11)
      (k' := patSlot0)
      (Equiv.ofBijective (fun i : Fin 5 => ![3, 2, 0, 1, 4] i)
        ⟨by decide, (Finite.injective_iff_surjective).1 (by decide)⟩) (by decide) ?_
    intro u i
    have e1 : pat (11 : Fin 15) = ![0, 4, 3, 1, 2] := by funext i; fin_cases i <;> rfl
    have e2 : pat patSlot0 = ![0, 1, 2, 3, 4] :=
      by funext i; fin_cases i <;> rfl
    rw [e1, e2]
    fin_cases i <;> rfl
  · -- k = 12
    refine shapeTotal5_eq_of_coordPerm (π := π) (x := x) (j := j) (k := 12)
      (k' := patSlot0)
      (Equiv.ofBijective (fun i : Fin 5 => ![0, 3, 1, 2, 4] i)
        ⟨by decide, (Finite.injective_iff_surjective).1 (by decide)⟩) (by decide) ?_
    intro u i
    have e1 : pat (12 : Fin 15) = ![0, 1, 4, 2, 3] := by funext i; fin_cases i <;> rfl
    have e2 : pat patSlot0 = ![0, 1, 2, 3, 4] :=
      by funext i; fin_cases i <;> rfl
    rw [e1, e2]
    fin_cases i <;> rfl
  · -- k = 13
    refine shapeTotal5_eq_of_coordPerm (π := π) (x := x) (j := j) (k := 13)
      (k' := patSlot0)
      (Equiv.ofBijective (fun i : Fin 5 => ![1, 3, 0, 2, 4] i)
        ⟨by decide, (Finite.injective_iff_surjective).1 (by decide)⟩) (by decide) ?_
    intro u i
    have e1 : pat (13 : Fin 15) = ![0, 2, 4, 1, 3] := by funext i; fin_cases i <;> rfl
    have e2 : pat patSlot0 = ![0, 1, 2, 3, 4] :=
      by funext i; fin_cases i <;> rfl
    rw [e1, e2]
    fin_cases i <;> rfl
  · -- k = 14
    refine shapeTotal5_eq_of_coordPerm (π := π) (x := x) (j := j) (k := 14)
      (k' := patSlot0)
      (Equiv.ofBijective (fun i : Fin 5 => ![2, 3, 0, 1, 4] i)
        ⟨by decide, (Finite.injective_iff_surjective).1 (by decide)⟩) (by decide) ?_
    intro u i
    have e1 : pat (14 : Fin 15) = ![0, 3, 4, 1, 2] := by funext i; fin_cases i <;> rfl
    have e2 : pat patSlot0 = ![0, 1, 2, 3, 4] :=
      by funext i; fin_cases i <;> rfl
    rw [e1, e2]
    fin_cases i <;> rfl

theorem shapeTotal5_rootSlot2 (π : Sym2 V → unitInterval) (x : V) (j : Fin 7) (k : Fin 15)
    (hk : pat k 2 = 0) :
    shapeTotal5 π x k j = shapeTotal5 π x patSlot2 j := by
  fin_cases k
  · -- k = 0
    refine shapeTotal5_eq_of_coordPerm (π := π) (x := x) (j := j) (k := 0)
      (k' := patSlot2)
      (Equiv.ofBijective (fun i : Fin 5 => ![0, 1, 2, 3, 4] i)
        ⟨by decide, (Finite.injective_iff_surjective).1 (by decide)⟩) (by decide) ?_
    intro u i
    have e1 : pat (0 : Fin 15) = ![1, 2, 0, 3, 4] := by funext i; fin_cases i <;> rfl
    have e2 : pat patSlot2 = ![1, 2, 0, 3, 4] :=
      by funext i; fin_cases i <;> rfl
    rw [e1, e2]
    fin_cases i <;> rfl
  · -- k = 1
    refine shapeTotal5_eq_of_coordPerm (π := π) (x := x) (j := j) (k := 1)
      (k' := patSlot2)
      (Equiv.ofBijective (fun i : Fin 5 => ![0, 2, 1, 3, 4] i)
        ⟨by decide, (Finite.injective_iff_surjective).1 (by decide)⟩) (by decide) ?_
    intro u i
    have e1 : pat (1 : Fin 15) = ![1, 3, 0, 2, 4] := by funext i; fin_cases i <;> rfl
    have e2 : pat patSlot2 = ![1, 2, 0, 3, 4] :=
      by funext i; fin_cases i <;> rfl
    rw [e1, e2]
    fin_cases i <;> rfl
  · -- k = 2
    refine shapeTotal5_eq_of_coordPerm (π := π) (x := x) (j := j) (k := 2)
      (k' := patSlot2)
      (Equiv.ofBijective (fun i : Fin 5 => ![0, 3, 1, 2, 4] i)
        ⟨by decide, (Finite.injective_iff_surjective).1 (by decide)⟩) (by decide) ?_
    intro u i
    have e1 : pat (2 : Fin 15) = ![1, 4, 0, 2, 3] := by funext i; fin_cases i <;> rfl
    have e2 : pat patSlot2 = ![1, 2, 0, 3, 4] :=
      by funext i; fin_cases i <;> rfl
    rw [e1, e2]
    fin_cases i <;> rfl
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)
  · exact absurd hk (by decide)

/-! ## The collapse, in the form of the `K2Mass` shape totals -/

/-- **The root-class dichotomy.**  Every one of the fifteen labelled patterns has the same total
mass as the canonical pattern of its root class.  No hypothesis on `π`. -/
theorem shapeTotal_eq_rootSlot (π : Sym2 V → unitInterval) (x : V) (k : Fin 15) (j : Fin 7) :
    shapeTotal π x k j = shapeTotal π x patSlot0 j ∨
      shapeTotal π x k j = shapeTotal π x patSlot2 j := by
  rcases pat_root_slot k with h0 | h2
  · exact Or.inl (by
      rw [shapeTotal_eq_shapeTotal5, shapeTotal5_rootSlot0 π x j k h0,
        ← shapeTotal_eq_shapeTotal5])
  · exact Or.inr (by
      rw [shapeTotal_eq_shapeTotal5, shapeTotal5_rootSlot2 π x j k h2,
        ← shapeTotal_eq_shapeTotal5])

/-- **The root-class collapse**, in the exact form in which `K2Mass.Main` used it as the
hypothesis `hcollapse`: every shape mass is at most the larger of the two root-class masses at
the same split. -/
theorem rootClass_collapse (π : Sym2 V → unitInterval) (x : V) (k : Fin 15) (j : Fin 7) :
    shapeTotal π x k j ≤
      max (shapeTotal π x patSlot0 j) (shapeTotal π x patSlot2 j) := by
  rcases shapeTotal_eq_rootSlot π x k j with h | h
  · rw [h]; exact le_max_left _ _
  · rw [h]; exact le_max_right _ _

/-! ## The `k = 2` fifth-moment bound, with `hcollapse` discharged -/

/-- **The `k = 2` fifth-moment bound from the twelve off-middle root-class masses.**  This is
`K2Mass.Main.fifth_moment_k2_le_of_rootClass_bounds` with its `hcollapse` hypothesis *removed*:
`rootClass_collapse` proves it, so the only inputs left are the profile invariance `hq` (used
only at the middle split `j = 2`, through `shapeTotal_mid_le`) and one mass bound for each of the
two root classes at each of the six off-middle splits — twelve bounds in total. -/
theorem fifth_moment_k2_le_of_rootSlot_bounds [Countable V] [AddCommGroup V]
    (π : Sym2 V → unitInterval)
    (hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y))
    (h0 : ∀ j : Fin 7, j ≠ 2 → shapeTotal π 0 patSlot0 j ≤ shapeCost π 0)
    (h2 : ∀ j : Fin 7, j ≠ 2 → shapeTotal π 0 patSlot2 j ≤ shapeCost π 0) :
    ∫⁻ ω, (PercLib.CriticalLRP.Percolation.cardFun
        (PercLib.CriticalLRP.cluster ω (0 : V))) ^ 5 ∂(law π) ≤
      105 * (∫⁻ ω, (PercLib.CriticalLRP.Percolation.cardFun
          (PercLib.CriticalLRP.cluster ω (0 : V))) ^ 2 ∂(law π)) ^ 2 *
        (∫⁻ ω, PercLib.CriticalLRP.Percolation.cardFun
          (PercLib.CriticalLRP.cluster ω (0 : V)) ∂(law π)) ^ 3 := by
  refine fifth_moment_k2_le_of_shapeTotal π fun k j => ?_
  by_cases hj : j = 2
  · subst hj
    exact shapeTotal_mid_le π hq k
  · rcases shapeTotal_eq_rootSlot π 0 k j with h | h
    · rw [h]; exact h0 j hj
    · rw [h]; exact h2 j hj

/-- **At the middle split both root-class masses are bounded by `shapeCost`.**  The production
evaluation `shapeTotal_mid_le` already covers all fifteen patterns at `j = 2`, so the collapse
adds nothing there.  Together with `fifth_moment_k2_le_of_rootSlot_bounds` this says that the
`14 = 2 * 7` root-class masses are bounded by `hq` (at `j = 2`) and the twelve off-middle
hypotheses (at `j ≠ 2`) — nothing else. -/
theorem shapeTotal_rootSlot_mid_le [Countable V] [AddCommGroup V]
    (π : Sym2 V → unitInterval)
    (hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y)) :
    shapeTotal π 0 patSlot0 2 ≤ shapeCost π 0 ∧
      shapeTotal π 0 patSlot2 2 ≤ shapeCost π 0 :=
  ⟨shapeTotal_mid_le π hq patSlot0, shapeTotal_mid_le π hq patSlot2⟩


/-! ## The collapse restated for `shapeTotal`, and the `105` multiplicity accounting -/

/-- The root-class dichotomy at the level of `shapeTotal`. -/
theorem shapeTotal_rootSlot0 (π : Sym2 V → unitInterval) (x : V) (k : Fin 15) (j : Fin 7)
    (hk : pat k 0 = 0) : shapeTotal π x k j = shapeTotal π x patSlot0 j := by
  rw [shapeTotal_eq_shapeTotal5, shapeTotal5_rootSlot0 π x j k hk, ← shapeTotal_eq_shapeTotal5]

theorem shapeTotal_rootSlot2 (π : Sym2 V → unitInterval) (x : V) (k : Fin 15) (j : Fin 7)
    (hk : pat k 2 = 0) : shapeTotal π x k j = shapeTotal π x patSlot2 j := by
  rw [shapeTotal_eq_shapeTotal5, shapeTotal5_rootSlot2 π x j k hk, ← shapeTotal_eq_shapeTotal5]

theorem tsum_shapeTotal_rootSlot0 (π : Sym2 V → unitInterval) (x : V) (k : Fin 15)
    (hk : pat k 0 = 0) :
    (∑' j : Fin 7, shapeTotal π x k j) = ∑' j : Fin 7, shapeTotal π x patSlot0 j :=
  tsum_congr fun j => shapeTotal_rootSlot0 π x k j hk

theorem tsum_shapeTotal_rootSlot2 (π : Sym2 V → unitInterval) (x : V) (k : Fin 15)
    (hk : pat k 2 = 0) :
    (∑' j : Fin 7, shapeTotal π x k j) = ∑' j : Fin 7, shapeTotal π x patSlot2 j :=
  tsum_congr fun j => shapeTotal_rootSlot2 π x k j hk

/-- **The `105`-shaped total is `12` copies of the slot-`0` class plus `3` of the slot-`2`
class.** -/
theorem tsum_shapeTotal_eq_rootClass (π : Sym2 V → unitInterval) (x : V) :
    (∑' k : Fin 15, ∑' j : Fin 7, shapeTotal π x k j)
      = 12 * (∑' j : Fin 7, shapeTotal π x patSlot0 j)
        + 3 * (∑' j : Fin 7, shapeTotal π x patSlot2 j) := by
  have hzero : ∀ k : Fin 15, ¬ (pat k 0 = 0 ∧ pat k 2 = 0) := by decide
  have hdisj : Disjoint (Finset.univ.filter (fun k : Fin 15 => pat k 0 = 0))
      (Finset.univ.filter (fun k : Fin 15 => pat k 2 = 0)) := by
    rw [Finset.disjoint_left]
    intro k hk1 hk2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk1 hk2
    exact hzero k ⟨hk1, hk2⟩
  have hunion : Finset.univ.filter (fun k : Fin 15 => pat k 0 = 0) ∪
      Finset.univ.filter (fun k : Fin 15 => pat k 2 = 0) = Finset.univ := by
    ext k
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun _ => trivial, fun _ => pat_root_slot k⟩
  have h1 : (∑ k ∈ Finset.univ.filter (fun k : Fin 15 => pat k 0 = 0),
        ∑' j : Fin 7, shapeTotal π x k j)
      = ∑ k ∈ Finset.univ.filter (fun k : Fin 15 => pat k 0 = 0),
        ∑' j : Fin 7, shapeTotal π x patSlot0 j :=
    Finset.sum_congr rfl fun k hk => by
      rw [Finset.mem_filter] at hk
      exact tsum_shapeTotal_rootSlot0 π x k hk.2
  have h2 : (∑ k ∈ Finset.univ.filter (fun k : Fin 15 => pat k 2 = 0),
        ∑' j : Fin 7, shapeTotal π x k j)
      = ∑ k ∈ Finset.univ.filter (fun k : Fin 15 => pat k 2 = 0),
        ∑' j : Fin 7, shapeTotal π x patSlot2 j :=
    Finset.sum_congr rfl fun k hk => by
      rw [Finset.mem_filter] at hk
      exact tsum_shapeTotal_rootSlot2 π x k hk.2
  rw [tsum_fintype, ← hunion, Finset.sum_union hdisj, h1, h2, Finset.sum_const,
    Finset.sum_const, card_pat_root_zero, card_pat_root_two, nsmul_eq_mul, nsmul_eq_mul]
  norm_num

/-- **The `k = 2` fifth-moment bound from the fourteen root-class masses.**  No profile
invariance is used at all: give the two root-class masses at each of the seven splits. -/
theorem fifth_moment_k2_le_of_rootSlot_all_bounds [Countable V] [AddCommGroup V]
    (π : Sym2 V → unitInterval)
    (h0 : ∀ j : Fin 7, shapeTotal π 0 patSlot0 j ≤ shapeCost π 0)
    (h2 : ∀ j : Fin 7, shapeTotal π 0 patSlot2 j ≤ shapeCost π 0) :
    ∫⁻ ω, (PercLib.CriticalLRP.Percolation.cardFun
        (PercLib.CriticalLRP.cluster ω (0 : V))) ^ 5 ∂(law π) ≤
      105 * (∫⁻ ω, (PercLib.CriticalLRP.Percolation.cardFun
          (PercLib.CriticalLRP.cluster ω (0 : V))) ^ 2 ∂(law π)) ^ 2 *
        (∫⁻ ω, PercLib.CriticalLRP.Percolation.cardFun
          (PercLib.CriticalLRP.cluster ω (0 : V)) ∂(law π)) ^ 3 := by
  refine fifth_moment_k2_le_of_shapeTotal π fun k j => ?_
  rcases shapeTotal_eq_rootSlot π 0 k j with h | h
  · rw [h]; exact h0 j
  · rw [h]; exact h2 j

/-- **The collapse as a single formula**: the mass of a labelled pattern is the mass of the
canonical pattern of its root class, selected by the root slot. -/
theorem shapeTotal_eq_rootSlot_if (π : Sym2 V → unitInterval) (x : V) (k : Fin 15)
    (j : Fin 7) :
    shapeTotal π x k j =
      if pat k 0 = 0 then shapeTotal π x patSlot0 j else shapeTotal π x patSlot2 j := by
  split_ifs with h
  · exact shapeTotal_rootSlot0 π x k j h
  · rcases pat_root_slot k with h0 | h2
    · exact absurd h0 h
    · exact shapeTotal_rootSlot2 π x k j h2

end PercLib.CriticalLRP.TreeExpansion.SixPoint.K2Mass
