/-
The three remaining `k = 2` two-joint/three-single split-position certificates of the
six-terminal arm system: `j = 1`, `j = 3` and `j = 4`.

Swarm `smwxfstjy`, member `m3`, direction `REMAINING-SPLIT-CERTIFICATES`.

Production proves this regrouping at `j = 2` (`SixPoint.combSystem_twoJointThree`, star set
`{u, w}`) and `SplitPattern/Regroup.lean` supplies `j = 0, 5, 6`.  This file closes the three
relabelled positions, each of which has the landing point `c` on an arm `b — u` or `b — w`:

* `j = 1`: `c` on the arm `b₁ — u` (`armTgt 1 = u`), so the second half of the split arm is
  `c — u` and the star at `u` has leaves `b₀, c, v`; the star at `w` has leaves `b₃, b₄, v`;
  singles `b₂ — v`, `b₁ — c`, `t — c`.
* `j = 3`: `c` on the arm `b₃ — w`, so the second half is `c — w` and the star at `w` has
  leaves `b₄, c, v`; the star at `u` has leaves `b₀, b₁, v`; singles `b₂ — v`, `b₃ — c`,
  `t — c`.
* `j = 4`: `c` on the arm `b₄ — w`; second star at `w` with leaves `b₃, c, v`; first star at
  `u` with leaves `b₀, b₁, v`; singles `b₂ — v`, `b₄ — c`, `t — c`.

Each proof consumes `combSystem_nine` (all nine pairwise edge-disjoint walks), the two halves
`A : armSrc j — c` and `B : c — armTgt j` of the split arm, and the sixth arm `Q : t — c`,
and keeps each shared spine (`u — v` resp. `v — w`) inside a single certificate set: no joint
pair is ever split.

Exact premises: `CombSystem (openGraph ω) b₀ … c j`, the deterministic six-terminal arm
system (seven pairwise edge-disjoint comb arms, the sixth arm `t — c`, and `c` on arm `j`).
Residual gap: this is an event-level inclusion feeding the fivefold BK bound, nothing more.
It does **not** evaluate the five groups; the `(∫|K|²)²(∫|K|)³` form needs the profile-`hq`
identifications of the joint free and anchored second moments, which are separate work
(and no factorisation of the joint groups is claimed).
-/

module

public import PercLib.CriticalLRP.Correlation.SixPoint.SplitEvents.Defs
public import PercLib.CriticalLRP.Correlation.SixPoint.TwoJointThree.Regroup

/-!
# All seven finite two-joint/three-single split certificates

No moment evaluation or terminal assembly is proved here.
-/


open Set MeasureTheory
open scoped ENNReal BigOperators
open PercLib.Percolation.Bond
open PercLib.CriticalLRP.TreeExpansion
open PercLib.CriticalLRP.TreeExpansion.SixPoint

@[expose] public section

namespace PercLib.CriticalLRP.TreeExpansion.SixPoint.SplitPattern

variable {V : Type*}

/-! ## Split position `j = 1`: the landing point lies on the arm `b₁ — u` -/

/-- **`k = 2` regrouping at split position `1`.**  The star at `u` has leaves `b₀, c, v`
(legs `b₀ — u` and the split half `c — u`, spine `u — v`), the star at `w` has leaves
`b₃, b₄, v` (spine `w — v`), and the three two-point factors are `b₂ — v`, `b₁ — c` and
`t — c`.

This is the `j = 0` pattern with `b₀` and `b₁` interchanged: at `j = 0` the star at `u` uses
`b₁ — u` and the split half is the single `b₀ — c`, at `j = 1` the roles of the two edges
`b₀ — u` and `b₁ — u` are swapped, and `armTgt 1 = u` makes the second split half `c — u`
again. -/
theorem combSystem_twoJointThree_one [Countable V] (b0 b1 b2 b3 b4 t u v w c : V) :
    {ω : Config V | CombSystem (openGraph ω) b0 b1 b2 b3 b4 t u v w c 1} ⊆
      TwoJointThreeCert (V := V) (conn b0 v ∩ conn c v) (conn b3 v ∩ conn b4 v)
        (conn b2 v) (conn b1 c) (conn t c) := by
  rintro ω h
  obtain ⟨p0, p1, p2, p3, p4, s1, s2, Q, A, B, _hsplit, _hnodup, hfamD, _hAn, _hBn, _hQn,
    hAB, hAi, hBi, hQi, hAQ, hBQ, _hc⟩ := combSystem_nine h
  refine fiveGroup_of_two_stars (ω := ω)
    ⟨u, b0, c, v, p0, B, s1⟩ ⟨w, b3, b4, v, p3, p4, s2.reverse⟩
    ![⟨(b2, v), p2⟩, ⟨(b1, c), A⟩, ⟨(t, c), Q⟩] ?_
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- the two stars are disjoint
    refine disjoint_union3_union3
      (disjoint_walkEdges p0 p3 (hfamD 0 3 (by decide)))
      (disjoint_walkEdges p0 p4 (hfamD 0 4 (by decide)))
      ?_ (disjoint_walkEdges B p3 (hBi 3 (by decide)))
      (disjoint_walkEdges B p4 (hBi 4 (by decide))) ?_
      (disjoint_walkEdges s1 p3 (hfamD 5 3 (by decide)))
      (disjoint_walkEdges s1 p4 (hfamD 5 4 (by decide))) ?_
    · rw [walkEdges_reverse]
      exact disjoint_walkEdges p0 s2 (hfamD 0 6 (by decide))
    · rw [walkEdges_reverse]
      exact disjoint_walkEdges B s2 (hBi 6 (by decide))
    · rw [walkEdges_reverse]
      exact disjoint_walkEdges s1 s2 (hfamD 5 6 (by decide))
  · -- the first star against the three single walks
    intro i
    fin_cases i
    · exact disjoint_union3_left (disjoint_walkEdges p0 p2 (hfamD 0 2 (by decide)))
        (disjoint_walkEdges B p2 (hBi 2 (by decide)))
        (disjoint_walkEdges s1 p2 (hfamD 5 2 (by decide)))
    · exact disjoint_union3_left (disjoint_walkEdges p0 A (hAi 0 (by decide)).symm)
        (disjoint_walkEdges B A hAB.symm)
        (disjoint_walkEdges s1 A (hAi 5 (by decide)).symm)
    · exact disjoint_union3_left (disjoint_walkEdges Q p0 (hQi 0)).symm
        (disjoint_walkEdges Q B hBQ.symm).symm
        (disjoint_walkEdges Q s1 (hQi 5)).symm
  · -- the second star against the three single walks
    intro i
    fin_cases i
    · exact disjoint_union3_left (disjoint_walkEdges p3 p2 (hfamD 3 2 (by decide)))
        (disjoint_walkEdges p4 p2 (hfamD 4 2 (by decide)))
        (by rw [walkEdges_reverse]
            exact disjoint_walkEdges s2 p2 (hfamD 6 2 (by decide)))
    · exact disjoint_union3_left (disjoint_walkEdges p3 A (hAi 3 (by decide)).symm)
        (disjoint_walkEdges p4 A (hAi 4 (by decide)).symm)
        (by rw [walkEdges_reverse]
            exact disjoint_walkEdges s2 A (hAi 6 (by decide)).symm)
    · exact disjoint_union3_left (disjoint_walkEdges Q p3 (hQi 3)).symm
        (disjoint_walkEdges Q p4 (hQi 4)).symm
        (by rw [walkEdges_reverse]
            exact (disjoint_walkEdges Q s2 (hQi 6)).symm)
  · -- the three single walks are pairwise disjoint
    intro i k hik
    fin_cases i <;> fin_cases k
    · exact absurd rfl hik
    · exact disjoint_walkEdges p2 A (hAi 2 (by decide)).symm
    · exact disjoint_walkEdges p2 Q (hQi 2).symm
    · exact disjoint_walkEdges A p2 (hAi 2 (by decide))
    · exact absurd rfl hik
    · exact disjoint_walkEdges A Q hAQ
    · exact disjoint_walkEdges Q p2 (hQi 2)
    · exact disjoint_walkEdges Q A hAQ.symm
    · exact absurd rfl hik

/-! ## Split position `j = 3`: the landing point lies on the arm `b₃ — w` -/

/-- **`k = 2` regrouping at split position `3`.**  The star at `u` has leaves `b₀, b₁, v`
(shared spine `u — v`), the star at `w` has leaves `b₄, c, v` (leg `b₄ — w`, split half
`c — w`, shared spine `w — v`), and the three two-point factors are `b₂ — v`, `b₃ — c` and
`t — c`. -/
theorem combSystem_twoJointThree_three [Countable V] (b0 b1 b2 b3 b4 t u v w c : V) :
    {ω : Config V | CombSystem (openGraph ω) b0 b1 b2 b3 b4 t u v w c 3} ⊆
      TwoJointThreeCert (V := V) (conn b0 v ∩ conn b1 v) (conn b4 v ∩ conn c v)
        (conn b2 v) (conn b3 c) (conn t c) := by
  rintro ω h
  obtain ⟨p0, p1, p2, p3, p4, s1, s2, Q, A, B, _hsplit, _hnodup, hfamD, _hAn, _hBn, _hQn,
    hAB, hAi, hBi, hQi, hAQ, hBQ, _hc⟩ := combSystem_nine h
  refine fiveGroup_of_two_stars (ω := ω)
    ⟨u, b0, b1, v, p0, p1, s1⟩ ⟨w, b4, c, v, p4, B, s2.reverse⟩
    ![⟨(b2, v), p2⟩, ⟨(b3, c), A⟩, ⟨(t, c), Q⟩] ?_
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- the two stars are disjoint
    refine disjoint_union3_union3
      (disjoint_walkEdges p0 p4 (hfamD 0 4 (by decide)))
      (disjoint_walkEdges p0 B (hBi 0 (by decide)).symm)
      ?_ (disjoint_walkEdges p1 p4 (hfamD 1 4 (by decide)))
      (disjoint_walkEdges p1 B (hBi 1 (by decide)).symm) ?_
      (disjoint_walkEdges s1 p4 (hfamD 5 4 (by decide)))
      (disjoint_walkEdges s1 B (hBi 5 (by decide)).symm) ?_
    · rw [walkEdges_reverse]
      exact disjoint_walkEdges p0 s2 (hfamD 0 6 (by decide))
    · rw [walkEdges_reverse]
      exact disjoint_walkEdges p1 s2 (hfamD 1 6 (by decide))
    · rw [walkEdges_reverse]
      exact disjoint_walkEdges s1 s2 (hfamD 5 6 (by decide))
  · -- the first star against the three single walks
    intro i
    fin_cases i
    · exact disjoint_union3_left (disjoint_walkEdges p0 p2 (hfamD 0 2 (by decide)))
        (disjoint_walkEdges p1 p2 (hfamD 1 2 (by decide)))
        (disjoint_walkEdges s1 p2 (hfamD 5 2 (by decide)))
    · exact disjoint_union3_left (disjoint_walkEdges p0 A (hAi 0 (by decide)).symm)
        (disjoint_walkEdges p1 A (hAi 1 (by decide)).symm)
        (disjoint_walkEdges s1 A (hAi 5 (by decide)).symm)
    · exact disjoint_union3_left (disjoint_walkEdges Q p0 (hQi 0)).symm
        (disjoint_walkEdges Q p1 (hQi 1)).symm
        (disjoint_walkEdges Q s1 (hQi 5)).symm
  · -- the second star against the three single walks
    intro i
    fin_cases i
    · exact disjoint_union3_left (disjoint_walkEdges p4 p2 (hfamD 4 2 (by decide)))
        (disjoint_walkEdges B p2 (hBi 2 (by decide)))
        (by rw [walkEdges_reverse]
            exact disjoint_walkEdges s2 p2 (hfamD 6 2 (by decide)))
    · exact disjoint_union3_left (disjoint_walkEdges p4 A (hAi 4 (by decide)).symm)
        (disjoint_walkEdges B A hAB.symm)
        (by rw [walkEdges_reverse]
            exact disjoint_walkEdges s2 A (hAi 6 (by decide)).symm)
    · exact disjoint_union3_left (disjoint_walkEdges Q p4 (hQi 4)).symm
        (disjoint_walkEdges Q B hBQ.symm).symm
        (by rw [walkEdges_reverse]
            exact (disjoint_walkEdges Q s2 (hQi 6)).symm)
  · -- the three single walks are pairwise disjoint
    intro i k hik
    fin_cases i <;> fin_cases k
    · exact absurd rfl hik
    · exact disjoint_walkEdges p2 A (hAi 2 (by decide)).symm
    · exact disjoint_walkEdges p2 Q (hQi 2).symm
    · exact disjoint_walkEdges A p2 (hAi 2 (by decide))
    · exact absurd rfl hik
    · exact disjoint_walkEdges A Q hAQ
    · exact disjoint_walkEdges Q p2 (hQi 2)
    · exact disjoint_walkEdges Q A hAQ.symm
    · exact absurd rfl hik

/-! ## Split position `j = 4`: the landing point lies on the arm `b₄ — w` -/

/-- **`k = 2` regrouping at split position `4`.**  The star at `u` has leaves `b₀, b₁, v`
(shared spine `u — v`), the star at `w` has leaves `b₃, c, v` (leg `b₃ — w`, split half
`c — w`, shared spine `w — v`), and the three two-point factors are `b₂ — v`, `b₄ — c` and
`t — c`. -/
theorem combSystem_twoJointThree_four [Countable V] (b0 b1 b2 b3 b4 t u v w c : V) :
    {ω : Config V | CombSystem (openGraph ω) b0 b1 b2 b3 b4 t u v w c 4} ⊆
      TwoJointThreeCert (V := V) (conn b0 v ∩ conn b1 v) (conn b3 v ∩ conn c v)
        (conn b2 v) (conn b4 c) (conn t c) := by
  rintro ω h
  obtain ⟨p0, p1, p2, p3, p4, s1, s2, Q, A, B, _hsplit, _hnodup, hfamD, _hAn, _hBn, _hQn,
    hAB, hAi, hBi, hQi, hAQ, hBQ, _hc⟩ := combSystem_nine h
  refine fiveGroup_of_two_stars (ω := ω)
    ⟨u, b0, b1, v, p0, p1, s1⟩ ⟨w, b3, c, v, p3, B, s2.reverse⟩
    ![⟨(b2, v), p2⟩, ⟨(b4, c), A⟩, ⟨(t, c), Q⟩] ?_
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- the two stars are disjoint
    refine disjoint_union3_union3
      (disjoint_walkEdges p0 p3 (hfamD 0 3 (by decide)))
      (disjoint_walkEdges p0 B (hBi 0 (by decide)).symm)
      ?_ (disjoint_walkEdges p1 p3 (hfamD 1 3 (by decide)))
      (disjoint_walkEdges p1 B (hBi 1 (by decide)).symm) ?_
      (disjoint_walkEdges s1 p3 (hfamD 5 3 (by decide)))
      (disjoint_walkEdges s1 B (hBi 5 (by decide)).symm) ?_
    · rw [walkEdges_reverse]
      exact disjoint_walkEdges p0 s2 (hfamD 0 6 (by decide))
    · rw [walkEdges_reverse]
      exact disjoint_walkEdges p1 s2 (hfamD 1 6 (by decide))
    · rw [walkEdges_reverse]
      exact disjoint_walkEdges s1 s2 (hfamD 5 6 (by decide))
  · -- the first star against the three single walks
    intro i
    fin_cases i
    · exact disjoint_union3_left (disjoint_walkEdges p0 p2 (hfamD 0 2 (by decide)))
        (disjoint_walkEdges p1 p2 (hfamD 1 2 (by decide)))
        (disjoint_walkEdges s1 p2 (hfamD 5 2 (by decide)))
    · exact disjoint_union3_left (disjoint_walkEdges p0 A (hAi 0 (by decide)).symm)
        (disjoint_walkEdges p1 A (hAi 1 (by decide)).symm)
        (disjoint_walkEdges s1 A (hAi 5 (by decide)).symm)
    · exact disjoint_union3_left (disjoint_walkEdges Q p0 (hQi 0)).symm
        (disjoint_walkEdges Q p1 (hQi 1)).symm
        (disjoint_walkEdges Q s1 (hQi 5)).symm
  · -- the second star against the three single walks
    intro i
    fin_cases i
    · exact disjoint_union3_left (disjoint_walkEdges p3 p2 (hfamD 3 2 (by decide)))
        (disjoint_walkEdges B p2 (hBi 2 (by decide)))
        (by rw [walkEdges_reverse]
            exact disjoint_walkEdges s2 p2 (hfamD 6 2 (by decide)))
    · exact disjoint_union3_left (disjoint_walkEdges p3 A (hAi 3 (by decide)).symm)
        (disjoint_walkEdges B A hAB.symm)
        (by rw [walkEdges_reverse]
            exact disjoint_walkEdges s2 A (hAi 6 (by decide)).symm)
    · exact disjoint_union3_left (disjoint_walkEdges Q p3 (hQi 3)).symm
        (disjoint_walkEdges Q B hBQ.symm).symm
        (by rw [walkEdges_reverse]
            exact (disjoint_walkEdges Q s2 (hQi 6)).symm)
  · -- the three single walks are pairwise disjoint
    intro i k hik
    fin_cases i <;> fin_cases k
    · exact absurd rfl hik
    · exact disjoint_walkEdges p2 A (hAi 2 (by decide)).symm
    · exact disjoint_walkEdges p2 Q (hQi 2).symm
    · exact disjoint_walkEdges A p2 (hAi 2 (by decide))
    · exact absurd rfl hik
    · exact disjoint_walkEdges A Q hAQ
    · exact disjoint_walkEdges Q p2 (hQi 2)
    · exact disjoint_walkEdges Q A hAQ.symm
    · exact absurd rfl hik

/-! ## All seven split positions -/

/-- **Every split position of the six-terminal arm system carries the `k = 2` certificate.**
For each `j : Fin 7` the arm system with the sixth terminal attached at `c` on arm `j` lies in
the two-joint/three-single certificate event given by the five groups `splitEvents … j`:
two joint pairs with shared spines (`u — v` or `v — w`) and three two-point factors.

The seven cases are the production middle split `j = 2`, the three arms into `u`/`w`
(`j = 0, 1, 3, 4`) and the two spine splits (`j = 5, 6`). -/
theorem combSystem_certified [Countable V] (b0 b1 b2 b3 b4 t u v w c : V) (j : Fin 7) :
    {ω : Config V | CombSystem (openGraph ω) b0 b1 b2 b3 b4 t u v w c j} ⊆
      (splitEvents b0 b1 b2 b3 b4 t u v w c j).cert := by
  fin_cases j
  · exact combSystem_twoJointThree_zero b0 b1 b2 b3 b4 t u v w c
  · exact combSystem_twoJointThree_one b0 b1 b2 b3 b4 t u v w c
  · exact combSystem_twoJointThree b0 b1 b2 b3 b4 t u v w c
  · exact combSystem_twoJointThree_three b0 b1 b2 b3 b4 t u v w c
  · exact combSystem_twoJointThree_four b0 b1 b2 b3 b4 t u v w c
  · exact combSystem_twoJointThree_five b0 b1 b2 b3 b4 t u v w c
  · exact combSystem_twoJointThree_six b0 b1 b2 b3 b4 t u v w c

/-- **Fivefold BK at every split position.**  The fivefold product bound of
`twoJointThree_le` applies to the certificate of `combSystem_certified` at every split
position: the joint groups are unsplit intersections of two connection events (upper sets by
`isUpperSet_inter_conn`) and the three factors are single connection events.

Premise: `CombSystem (openGraph ω) … j`.  Conclusion: the probability of the arm system at
position `j` is at most the product of the two joint probabilities and the three first
moments of the `splitEvents` groups.  This is a bound by *five* factors, not yet the
`(∫|K|²)²(∫|K|)³` form: that requires evaluating the two joint groups as second moments. -/
theorem law_combSystem_le [Countable V] (π : Sym2 V → unitInterval)
    (b0 b1 b2 b3 b4 t u v w c : V) (j : Fin 7) :
    law π {ω : Config V | CombSystem (openGraph ω) b0 b1 b2 b3 b4 t u v w c j} ≤
      (splitEvents b0 b1 b2 b3 b4 t u v w c j).lawProd π := by
  refine (measure_mono (combSystem_certified b0 b1 b2 b3 b4 t u v w c j)).trans ?_
  fin_cases j
  · exact twoJointThree_le (V := V) π (isUpperSet_inter_conn b1 c v)
      (isUpperSet_inter_conn b3 b4 v) (isIncreasing_connects b2 v)
      (isIncreasing_connects b0 c) (isIncreasing_connects t c)
  · exact twoJointThree_le (V := V) π (isUpperSet_inter_conn b0 c v)
      (isUpperSet_inter_conn b3 b4 v) (isIncreasing_connects b2 v)
      (isIncreasing_connects b1 c) (isIncreasing_connects t c)
  · exact twoJointThree_le (V := V) π (isUpperSet_inter_conn b0 b1 v)
      (isUpperSet_inter_conn b3 b4 v) (isIncreasing_connects b2 c)
      (isIncreasing_connects c v) (isIncreasing_connects t c)
  · exact twoJointThree_le (V := V) π (isUpperSet_inter_conn b0 b1 v)
      (isUpperSet_inter_conn b4 c v) (isIncreasing_connects b2 v)
      (isIncreasing_connects b3 c) (isIncreasing_connects t c)
  · exact twoJointThree_le (V := V) π (isUpperSet_inter_conn b0 b1 v)
      (isUpperSet_inter_conn b3 c v) (isIncreasing_connects b2 v)
      (isIncreasing_connects b4 c) (isIncreasing_connects t c)
  · exact twoJointThree_le (V := V) π (isUpperSet_inter_conn b0 b1 c)
      (isUpperSet_inter_conn b2 c w) (isIncreasing_connects b3 w)
      (isIncreasing_connects b4 w) (isIncreasing_connects t c)
  · exact twoJointThree_le (V := V) π (isUpperSet_inter_conn b0 b1 v)
      (isUpperSet_inter_conn v t w) (isIncreasing_connects b2 v)
      (isIncreasing_connects b3 w) (isIncreasing_connects b4 w)
/-- **The unrolled fivefold bound at split position `0`** (`c` on the arm `b₀ — u`):
two joint pairs `(b₁ v, c v)`, `(b₃ v, b₄ v)` and the three factors `b₂ v`, `b₀ c`, `t c`. -/
theorem law_combSystem_le_zero [Countable V] (π : Sym2 V → unitInterval)
    (b0 b1 b2 b3 b4 t u v w c : V) :
    law π {ω : Config V | CombSystem (openGraph ω) b0 b1 b2 b3 b4 t u v w c 0} ≤
      law π (conn b1 v ∩ conn c v) * (law π (conn b3 v ∩ conn b4 v) *
        (law π (conn b2 v) * (law π (conn b0 c) * law π (conn t c)))) :=
  law_combSystem_le π b0 b1 b2 b3 b4 t u v w c 0

/-- **The unrolled fivefold bound at split position `1`** (`c` on the arm `b₁ — u`). -/
theorem law_combSystem_le_one [Countable V] (π : Sym2 V → unitInterval)
    (b0 b1 b2 b3 b4 t u v w c : V) :
    law π {ω : Config V | CombSystem (openGraph ω) b0 b1 b2 b3 b4 t u v w c 1} ≤
      law π (conn b0 v ∩ conn c v) * (law π (conn b3 v ∩ conn b4 v) *
        (law π (conn b2 v) * (law π (conn b1 c) * law π (conn t c)))) :=
  law_combSystem_le π b0 b1 b2 b3 b4 t u v w c 1

/-- **The unrolled fivefold bound at split position `2`** (the production middle split, `c`
on the arm `b₂ — v`).  This is production's `SixPoint.combSystem_twoJointThree_le`, obtained
here as the `j = 2` instance of the uniform statement. -/
theorem law_combSystem_le_two [Countable V] (π : Sym2 V → unitInterval)
    (b0 b1 b2 b3 b4 t u v w c : V) :
    law π {ω : Config V | CombSystem (openGraph ω) b0 b1 b2 b3 b4 t u v w c 2} ≤
      law π (conn b0 v ∩ conn b1 v) * (law π (conn b3 v ∩ conn b4 v) *
        (law π (conn b2 c) * (law π (conn c v) * law π (conn t c)))) :=
  law_combSystem_le π b0 b1 b2 b3 b4 t u v w c 2

/-- **The unrolled fivefold bound at split position `3`** (`c` on the arm `b₃ — w`). -/
theorem law_combSystem_le_three [Countable V] (π : Sym2 V → unitInterval)
    (b0 b1 b2 b3 b4 t u v w c : V) :
    law π {ω : Config V | CombSystem (openGraph ω) b0 b1 b2 b3 b4 t u v w c 3} ≤
      law π (conn b0 v ∩ conn b1 v) * (law π (conn b4 v ∩ conn c v) *
        (law π (conn b2 v) * (law π (conn b3 c) * law π (conn t c)))) :=
  law_combSystem_le π b0 b1 b2 b3 b4 t u v w c 3

/-- **The unrolled fivefold bound at split position `4`** (`c` on the arm `b₄ — w`). -/
theorem law_combSystem_le_four [Countable V] (π : Sym2 V → unitInterval)
    (b0 b1 b2 b3 b4 t u v w c : V) :
    law π {ω : Config V | CombSystem (openGraph ω) b0 b1 b2 b3 b4 t u v w c 4} ≤
      law π (conn b0 v ∩ conn b1 v) * (law π (conn b3 v ∩ conn c v) *
        (law π (conn b2 v) * (law π (conn b4 c) * law π (conn t c)))) :=
  law_combSystem_le π b0 b1 b2 b3 b4 t u v w c 4

/-- **The unrolled fivefold bound at split position `5`** (the landing point on the spine
`u — v`). -/
theorem law_combSystem_le_five [Countable V] (π : Sym2 V → unitInterval)
    (b0 b1 b2 b3 b4 t u v w c : V) :
    law π {ω : Config V | CombSystem (openGraph ω) b0 b1 b2 b3 b4 t u v w c 5} ≤
      law π (conn b0 c ∩ conn b1 c) * (law π (conn b2 w ∩ conn c w) *
        (law π (conn b3 w) * (law π (conn b4 w) * law π (conn t c)))) :=
  law_combSystem_le π b0 b1 b2 b3 b4 t u v w c 5

/-- **The unrolled fivefold bound at split position `6`** (the landing point on the spine
`v — w`). -/
theorem law_combSystem_le_six [Countable V] (π : Sym2 V → unitInterval)
    (b0 b1 b2 b3 b4 t u v w c : V) :
    law π {ω : Config V | CombSystem (openGraph ω) b0 b1 b2 b3 b4 t u v w c 6} ≤
      law π (conn b0 v ∩ conn b1 v) * (law π (conn v w ∩ conn t w) *
        (law π (conn b2 v) * (law π (conn b3 w) * law π (conn b4 w)))) :=
  law_combSystem_le π b0 b1 b2 b3 b4 t u v w c 6

end PercLib.CriticalLRP.TreeExpansion.SixPoint.SplitPattern
