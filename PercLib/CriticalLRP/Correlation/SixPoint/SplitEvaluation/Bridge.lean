/-
Event-level bridges for the split positions `j = 0, 5, 6`: from the arm system to the evaluated
slot.

Swarm `smwxfstjy`, member `m2`, direction d3 (`REMAINING-SPLIT-EVALUATIONS`).

The production certificates `combSystem_twoJointThree_zero`, `..._five`, `..._six` are statements
about the arm system at *fixed* witnesses `c, u, v, w`.  The slot evaluation of `Peel.lean` is
about the probability with the witnesses that no longer occur in the five-factor product summed.
The order of operations matters and is the one in the direction: the two witnesses that the
product does not mention are **eliminated by containment inside the event, before any union
bound**.  Doing it after the union bound would introduce the extended sums `∑' u, 1` and
`∑' w, 1`, i.e. an infinite constant; here nothing is lost.

The witnesses absorbed by containment are

* `j = 0`: `u` and `w` (the two star centres); the surviving free vertices are `v, c`;
* `j = 5`: `u` and `v` (the star centres); the surviving free vertices are `c, w`;
* `j = 6`: `u` and `c` (the star centres); the surviving free vertices are `v, w`.

The three terminal sums are then taken in the assembly order, and the root is pinned in the slot
evaluation: `b₁` at `j = 0`, `b₂` at `j = 5`, `t` at `j = 6`.
-/
module

public import PercLib.CriticalLRP.Correlation.SixPoint.SplitEvaluation.Peel
public import PercLib.CriticalLRP.Correlation.SixPoint.SplitPattern.Regroup

/-!
# Split evaluation and event bridges (`j = 0,5,6`)

The specified root placement is part of each evaluation. Other splits and the final moment assembly
remain open.-/


/-!
# Union bounds and terminal sums at split positions `0`, `5`, `6`
-/

open Set MeasureTheory
open scoped ENNReal BigOperators
open PercLib.Percolation.Bond
open PercLib.Probability
open PercLib.CriticalLRP.TreeExpansion
open PercLib.CriticalLRP.TreeExpansion.FivePoint
open PercLib.CriticalLRP.TreeExpansion.SixPoint
open PercLib.CriticalLRP.TreeExpansion.SixPoint.SplitPattern

@[expose] public section

namespace PercLib.CriticalLRP.SixPoint.SplitEval

variable {V : Type*}

/-! ## Split position `j = 0` -/

/-- **The `j = 0` slot bound, free vertices included.**  The probability that the six-terminal arm
system can be split at comb arm `0` somewhere is at most the two-joint slot diagram: the two star
centres `u, w` are absorbed into the joint connection events by containment, and only the landing
point `c` and the spine vertex `v` are summed, in that order. -/
theorem combSystem_zero_union_le [Countable V] (π : Sym2 V → unitInterval)
    (b0 b1 b2 b3 b4 t : V) :
    law π (⋃ c : V, ⋃ u : V, ⋃ v : V, ⋃ w : V,
        {ω : PercLib.CriticalLRP.Config V |
          CombSystem (openGraph ω) b0 b1 b2 b3 b4 t u v w c 0}) ≤
      slotZero π b0 b1 b2 b3 b4 t := by
  classical
  have hsub : (⋃ c : V, ⋃ u : V, ⋃ v : V, ⋃ w : V,
      {ω : PercLib.CriticalLRP.Config V |
        CombSystem (openGraph ω) b0 b1 b2 b3 b4 t u v w c 0}) ⊆
      (⋃ c : V, ⋃ v : V, TwoJointThreeCert (conn b1 v ∩ conn c v)
        (conn b3 v ∩ conn b4 v) (conn b2 v) (conn b0 c) (conn t c)) := by
    intro ω hω
    simp only [Set.mem_iUnion] at hω ⊢
    obtain ⟨c, u, v, w, hw⟩ := hω
    exact ⟨c, v, combSystem_twoJointThree_zero (V := V) b0 b1 b2 b3 b4 t u v w c hw⟩
  calc law π (⋃ c : V, ⋃ u : V, ⋃ v : V, ⋃ w : V,
        {ω : PercLib.CriticalLRP.Config V |
          CombSystem (openGraph ω) b0 b1 b2 b3 b4 t u v w c 0})
      ≤ law π (⋃ c : V, ⋃ v : V, TwoJointThreeCert (conn b1 v ∩ conn c v)
          (conn b3 v ∩ conn b4 v) (conn b2 v) (conn b0 c) (conn t c)) :=
        measure_mono hsub
    _ ≤ ∑' c : V, ∑' v : V, law π (TwoJointThreeCert (conn b1 v ∩ conn c v)
          (conn b3 v ∩ conn b4 v) (conn b2 v) (conn b0 c) (conn t c)) := by
        refine (measure_iUnion_le (μ := law π) (s := fun c : V => ⋃ v : V,
          TwoJointThreeCert (conn b1 v ∩ conn c v) (conn b3 v ∩ conn b4 v)
            (conn b2 v) (conn b0 c) (conn t c))).trans ?_
        exact ENNReal.tsum_le_tsum fun c =>
          measure_iUnion_le (μ := law π) (s := fun v : V =>
            TwoJointThreeCert (conn b1 v ∩ conn c v) (conn b3 v ∩ conn b4 v)
              (conn b2 v) (conn b0 c) (conn t c))
    _ ≤ ∑' c : V, ∑' v : V, prodZero π b0 b1 b2 b3 b4 t v c :=
        ENNReal.tsum_le_tsum fun c => ENNReal.tsum_le_tsum fun v => by
          simpa only [prodZero, jointP, tau] using
            twoJointThree_le (V := V) π
              ((isUpperSet_conn b1 v).inter (isUpperSet_conn c v))
              ((isUpperSet_conn b3 v).inter (isUpperSet_conn b4 v))
              (isUpperSet_conn b2 v) (isUpperSet_conn b0 c) (isUpperSet_conn t c)
    _ = slotZero π b0 b1 b2 b3 b4 t := rfl

/-! ## Split position `j = 5` -/

/-- **The `j = 5` slot bound, free vertices included.**  The two star centres `u, v` are absorbed
by containment; the landing point `c` and the spine vertex `w` remain free, summed in that
order. -/
theorem combSystem_five_union_le [Countable V] (π : Sym2 V → unitInterval)
    (b0 b1 b2 b3 b4 t : V) :
    law π (⋃ c : V, ⋃ u : V, ⋃ v : V, ⋃ w : V,
        {ω : PercLib.CriticalLRP.Config V |
          CombSystem (openGraph ω) b0 b1 b2 b3 b4 t u v w c 5}) ≤
      slotFive π b0 b1 b2 b3 b4 t := by
  classical
  have hsub : (⋃ c : V, ⋃ u : V, ⋃ v : V, ⋃ w : V,
      {ω : PercLib.CriticalLRP.Config V |
        CombSystem (openGraph ω) b0 b1 b2 b3 b4 t u v w c 5}) ⊆
      (⋃ c : V, ⋃ w : V, TwoJointThreeCert (conn b0 c ∩ conn b1 c)
        (conn b2 w ∩ conn c w) (conn b3 w) (conn b4 w) (conn t c)) := by
    intro ω hω
    simp only [Set.mem_iUnion] at hω ⊢
    obtain ⟨c, u, v, w, hw⟩ := hω
    exact ⟨c, w, combSystem_twoJointThree_five (V := V) b0 b1 b2 b3 b4 t u v w c hw⟩
  calc law π (⋃ c : V, ⋃ u : V, ⋃ v : V, ⋃ w : V,
        {ω : PercLib.CriticalLRP.Config V |
          CombSystem (openGraph ω) b0 b1 b2 b3 b4 t u v w c 5})
      ≤ law π (⋃ c : V, ⋃ w : V, TwoJointThreeCert (conn b0 c ∩ conn b1 c)
          (conn b2 w ∩ conn c w) (conn b3 w) (conn b4 w) (conn t c)) :=
        measure_mono hsub
    _ ≤ ∑' c : V, ∑' w : V, law π (TwoJointThreeCert (conn b0 c ∩ conn b1 c)
          (conn b2 w ∩ conn c w) (conn b3 w) (conn b4 w) (conn t c)) := by
        refine (measure_iUnion_le (μ := law π) (s := fun c : V => ⋃ w : V,
          TwoJointThreeCert (conn b0 c ∩ conn b1 c) (conn b2 w ∩ conn c w)
            (conn b3 w) (conn b4 w) (conn t c))).trans ?_
        exact ENNReal.tsum_le_tsum fun c =>
          measure_iUnion_le (μ := law π) (s := fun w : V =>
            TwoJointThreeCert (conn b0 c ∩ conn b1 c) (conn b2 w ∩ conn c w)
              (conn b3 w) (conn b4 w) (conn t c))
    _ ≤ ∑' c : V, ∑' w : V, prodFive π b0 b1 b2 b3 b4 t c w :=
        ENNReal.tsum_le_tsum fun c => ENNReal.tsum_le_tsum fun w => by
          simpa only [prodFive, jointP, tau] using
            twoJointThree_le (V := V) π
              ((isUpperSet_conn b0 c).inter (isUpperSet_conn b1 c))
              ((isUpperSet_conn b2 w).inter (isUpperSet_conn c w))
              (isUpperSet_conn b3 w) (isUpperSet_conn b4 w) (isUpperSet_conn t c)
    _ = slotFive π b0 b1 b2 b3 b4 t := rfl

/-! ## Split position `j = 6` -/

/-- **The `j = 6` slot bound, free vertices included.**  The two star centres `u, c` are absorbed
by containment; the spine vertices `v, w` remain free, summed in that order. -/
theorem combSystem_six_union_le [Countable V] (π : Sym2 V → unitInterval)
    (b0 b1 b2 b3 b4 t : V) :
    law π (⋃ c : V, ⋃ u : V, ⋃ v : V, ⋃ w : V,
        {ω : PercLib.CriticalLRP.Config V |
          CombSystem (openGraph ω) b0 b1 b2 b3 b4 t u v w c 6}) ≤
      slotSix π b0 b1 b2 b3 b4 t := by
  classical
  have hsub : (⋃ c : V, ⋃ u : V, ⋃ v : V, ⋃ w : V,
      {ω : PercLib.CriticalLRP.Config V |
        CombSystem (openGraph ω) b0 b1 b2 b3 b4 t u v w c 6}) ⊆
      (⋃ v : V, ⋃ w : V, TwoJointThreeCert (conn b0 v ∩ conn b1 v)
        (conn v w ∩ conn t w) (conn b2 v) (conn b3 w) (conn b4 w)) := by
    intro ω hω
    simp only [Set.mem_iUnion] at hω ⊢
    obtain ⟨c, u, v, w, hw⟩ := hω
    exact ⟨v, w, combSystem_twoJointThree_six (V := V) b0 b1 b2 b3 b4 t u v w c hw⟩
  calc law π (⋃ c : V, ⋃ u : V, ⋃ v : V, ⋃ w : V,
        {ω : PercLib.CriticalLRP.Config V |
          CombSystem (openGraph ω) b0 b1 b2 b3 b4 t u v w c 6})
      ≤ law π (⋃ v : V, ⋃ w : V, TwoJointThreeCert (conn b0 v ∩ conn b1 v)
          (conn v w ∩ conn t w) (conn b2 v) (conn b3 w) (conn b4 w)) :=
        measure_mono hsub
    _ ≤ ∑' v : V, ∑' w : V, law π (TwoJointThreeCert (conn b0 v ∩ conn b1 v)
          (conn v w ∩ conn t w) (conn b2 v) (conn b3 w) (conn b4 w)) := by
        refine (measure_iUnion_le (μ := law π) (s := fun v : V => ⋃ w : V,
          TwoJointThreeCert (conn b0 v ∩ conn b1 v) (conn v w ∩ conn t w)
            (conn b2 v) (conn b3 w) (conn b4 w))).trans ?_
        exact ENNReal.tsum_le_tsum fun v =>
          measure_iUnion_le (μ := law π) (s := fun w : V =>
            TwoJointThreeCert (conn b0 v ∩ conn b1 v) (conn v w ∩ conn t w)
              (conn b2 v) (conn b3 w) (conn b4 w))
    _ ≤ ∑' v : V, ∑' w : V, prodSix π b0 b1 b2 b3 b4 t v w :=
        ENNReal.tsum_le_tsum fun v => ENNReal.tsum_le_tsum fun w => by
          simpa only [prodSix, jointP, tau] using
            twoJointThree_le (V := V) π
              ((isUpperSet_conn b0 v).inter (isUpperSet_conn b1 v))
              ((isUpperSet_conn v w).inter (isUpperSet_conn t w))
              (isUpperSet_conn b2 v) (isUpperSet_conn b3 w) (isUpperSet_conn b4 w)
    _ = slotSix π b0 b1 b2 b3 b4 t := rfl

/-! ## The five terminal sums: the three evaluated slots -/

/-- **The `j = 0` split, all five non-root terminals summed, costs `(E|K|²)²(E|K|)³`.**  The root
is `b₁`; there is no constant, no moment finiteness and no independence assumption. -/
theorem zero_tsum_le [Countable V] [AddCommGroup V] (π : Sym2 V → unitInterval)
    (hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y)) (b1 : V) :
    (∑' b0, ∑' b2, ∑' b3, ∑' b4, ∑' t, law π (⋃ c : V, ⋃ u : V, ⋃ v : V, ⋃ w : V,
        {ω : PercLib.CriticalLRP.Config V |
          CombSystem (openGraph ω) b0 b1 b2 b3 b4 t u v w c 0})) ≤
      (secondMoment π 0) ^ 2 * (∑' x, tau π 0 x) ^ 3 :=
  (ENNReal.tsum_le_tsum fun b0 => ENNReal.tsum_le_tsum fun b2 =>
    ENNReal.tsum_le_tsum fun b3 => ENNReal.tsum_le_tsum fun b4 =>
      ENNReal.tsum_le_tsum fun t =>
        combSystem_zero_union_le (V := V) π b0 b1 b2 b3 b4 t).trans_eq (slotZero_tsum π hq b1)

/-- **The `j = 5` split, all five non-root terminals summed, costs `(E|K|²)²(E|K|)³`.**  The root
is `b₂`. -/
theorem five_tsum_le [Countable V] [AddCommGroup V] (π : Sym2 V → unitInterval)
    (hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y)) (b2 : V) :
    (∑' b0, ∑' b1, ∑' b3, ∑' b4, ∑' t, law π (⋃ c : V, ⋃ u : V, ⋃ v : V, ⋃ w : V,
        {ω : PercLib.CriticalLRP.Config V |
          CombSystem (openGraph ω) b0 b1 b2 b3 b4 t u v w c 5})) ≤
      (secondMoment π 0) ^ 2 * (∑' x, tau π 0 x) ^ 3 :=
  (ENNReal.tsum_le_tsum fun b0 => ENNReal.tsum_le_tsum fun b1 =>
    ENNReal.tsum_le_tsum fun b3 => ENNReal.tsum_le_tsum fun b4 =>
      ENNReal.tsum_le_tsum fun t =>
        combSystem_five_union_le (V := V) π b0 b1 b2 b3 b4 t).trans_eq (slotFive_tsum π hq b2)

/-- **The `j = 6` split, all five comb terminals summed, costs `(E|K|²)²(E|K|)³`.**  Here the
pinned terminal is `t`, the end of the *sixth* arm: the pinning step of `peelSix` consumes the
centre `w` and the ear `v` of the joint pair `v, t`.  The root placement is forced — see
`NOTES.md` for the finite check over the three admissible star sets at this split. -/
theorem six_tsum_le [Countable V] [AddCommGroup V] (π : Sym2 V → unitInterval)
    (hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y)) (t : V) :
    (∑' b0, ∑' b1, ∑' b2, ∑' b3, ∑' b4, law π (⋃ c : V, ⋃ u : V, ⋃ v : V, ⋃ w : V,
        {ω : PercLib.CriticalLRP.Config V |
          CombSystem (openGraph ω) b0 b1 b2 b3 b4 t u v w c 6})) ≤
      (secondMoment π 0) ^ 2 * (∑' x, tau π 0 x) ^ 3 :=
  (ENNReal.tsum_le_tsum fun b0 => ENNReal.tsum_le_tsum fun b1 =>
    ENNReal.tsum_le_tsum fun b2 => ENNReal.tsum_le_tsum fun b3 =>
      ENNReal.tsum_le_tsum fun b4 =>
        combSystem_six_union_le (V := V) π b0 b1 b2 b3 b4 t).trans_eq (slotSix_tsum π hq t)

/-! ## Transport of the `j = 0` evaluation to split `j = 1`

The arm system is equivariant under exchanging the two `u`-arms: `b₀ — u` becomes `b₁ — u` and at
the same time split arm `0` becomes split arm `1`.  This turns the `j = 0` evaluation (whose pinning
step forces the root `b₁`, i.e. comb slot `1`) into an evaluation of split `j = 1` with the root
`b₀`, i.e. **comb slot `0`**, which is one of the two slots the labelled patterns
`SixPoint.SixShape` actually use.  The proof is a genuine list-permutation argument on the eight
edge blocks of the certificate, not an `rfl`. -/

/-- Swapping two adjacent blocks of a concatenation is a permutation. -/
theorem perm_swap_first_two {α : Type*} (a b r : List α) :
    (a ++ (b ++ r)).Perm (b ++ (a ++ r)) := by
  rw [← List.append_assoc a b r, ← List.append_assoc b a r]
  exact List.perm_append_comm.append_right r

/-- **Swapping the first two blocks of an eight-block nodup concatenation preserves nodup.**  This
is the list content of the arm-system symmetry `b₀ ↔ b₁`. -/
theorem nodup_swap_first_two {α : Type*} {a b c d e f g q : List α}
    (h : (a ++ b ++ c ++ d ++ e ++ f ++ g ++ q).Nodup) :
    (b ++ a ++ c ++ d ++ e ++ f ++ g ++ q).Nodup := by
  have h' : (a ++ (b ++ (c ++ (d ++ (e ++ (f ++ (g ++ q))))))).Nodup := by
    simpa only [List.append_assoc] using h
  have hp := perm_swap_first_two a b (c ++ (d ++ (e ++ (f ++ (g ++ q)))))
  have hnew := hp.nodup_iff.mp h'
  simpa only [List.append_assoc] using hnew

/-- **The arm-system symmetry `b₀ ↔ b₁`.**  Splitting at arm `0` with the two `u`-arms exchanged
is the same event as splitting at arm `1`. -/
theorem combSystem_swap01 {G : SimpleGraph V} (b0 b1 b2 b3 b4 t u v w c : V) :
    CombSystem G b1 b0 b2 b3 b4 t u v w c 0 ↔
      CombSystem G b0 b1 b2 b3 b4 t u v w c 1 := by
  constructor
  · rintro ⟨p0, p1, p2, p3, p4, s1, s2, Q, hnd, hc⟩
    exact ⟨p1, p0, p2, p3, p4, s1, s2, Q, nodup_swap_first_two hnd, hc⟩
  · rintro ⟨p0, p1, p2, p3, p4, s1, s2, Q, hnd, hc⟩
    exact ⟨p1, p0, p2, p3, p4, s1, s2, Q, nodup_swap_first_two hnd, hc⟩

/-- **The `j = 1` split, all five non-root terminals summed, costs `(E|K|²)²(E|K|)³`.**  The root
is `b₀`, i.e. comb slot `0`.  This is the `b₀ ↔ b₁` transport of `zero_tsum_le`. -/
theorem one_tsum_le [Countable V] [AddCommGroup V] (π : Sym2 V → unitInterval)
    (hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y)) (b0 : V) :
    (∑' b1, ∑' b2, ∑' b3, ∑' b4, ∑' t, law π (⋃ c : V, ⋃ u : V, ⋃ v : V, ⋃ w : V,
        {ω : PercLib.CriticalLRP.Config V |
          CombSystem (openGraph ω) b0 b1 b2 b3 b4 t u v w c 1})) ≤
      (secondMoment π 0) ^ 2 * (∑' x, tau π 0 x) ^ 3 := by
  have hset : ∀ (b1 b2 b3 b4 t : V),
      law π (⋃ c : V, ⋃ u : V, ⋃ v : V, ⋃ w : V,
        {ω : PercLib.CriticalLRP.Config V |
          CombSystem (openGraph ω) b0 b1 b2 b3 b4 t u v w c 1}) =
      law π (⋃ c : V, ⋃ u : V, ⋃ v : V, ⋃ w : V,
        {ω : PercLib.CriticalLRP.Config V |
          CombSystem (openGraph ω) b1 b0 b2 b3 b4 t u v w c 0}) := by
    intro b1 b2 b3 b4 t
    congr 1
    ext ω
    simp only [Set.mem_iUnion]
    exact ⟨fun ⟨c, u, v, w, h⟩ =>
        ⟨c, u, v, w, (combSystem_swap01 (V := V) b0 b1 b2 b3 b4 t u v w c).mpr h⟩,
      fun ⟨c, u, v, w, h⟩ =>
        ⟨c, u, v, w, (combSystem_swap01 (V := V) b0 b1 b2 b3 b4 t u v w c).mp h⟩⟩
  rw [show (∑' b1, ∑' b2, ∑' b3, ∑' b4, ∑' t, law π (⋃ c : V, ⋃ u : V, ⋃ v : V, ⋃ w : V,
      {ω : PercLib.CriticalLRP.Config V |
        CombSystem (openGraph ω) b0 b1 b2 b3 b4 t u v w c 1})) =
      ∑' b1, ∑' b2, ∑' b3, ∑' b4, ∑' t, law π (⋃ c : V, ⋃ u : V, ⋃ v : V, ⋃ w : V,
      {ω : PercLib.CriticalLRP.Config V |
        CombSystem (openGraph ω) b1 b0 b2 b3 b4 t u v w c 0}) from
    tsum_congr fun b1 => tsum_congr fun b2 => tsum_congr fun b3 => tsum_congr fun b4 =>
      tsum_congr fun t => hset b1 b2 b3 b4 t]
  exact zero_tsum_le π hq b0

end PercLib.CriticalLRP.SixPoint.SplitEval
