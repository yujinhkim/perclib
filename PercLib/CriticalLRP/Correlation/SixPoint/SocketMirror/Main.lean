/-
Swarm `smwxk27m7`, member `m3`, direction `d3` (`SOCKET-MIRROR`).

# Mirror pairs of split positions for the `p = 5`, `k = 2` root-socket shape masses

`SixPoint.CombSystem G b0 b1 b2 b3 b4 t u v w c j` is the deterministic certificate of the
six-terminal split shape at split position `j`: seven pairwise edge-disjoint comb arms
(`bᵢ — u/v/w` and the spine `u — v — w`), the sixth arm `t — c`, and `c` lying on arm `j`.
The nine edges of the split tree are the seven arms split at `c`.

The only dependence of `CombSystem` on `j` is *which* arm carries `c`.  Hence a leaf permutation
that maps arm `j` to arm `j'` carries the certificate at `j` onto the certificate at `j'`, with
nothing changed but the order of the eight walk edge-lists (and, for the `u ↔ w` automorphism, a
reversal of the two spine walks).  Summed over the four internal witnesses and the five free
terminals, and reindexed over the five free terminal coordinates, this gives unconditional
identities between the shape totals of *different split positions*:

* `shapeTotal π x k 3 = shapeTotal π x k 4` for **every** labelled pattern `k` (leaf swap
  `b₃ ↔ b₄`; no pattern of the family has its root at leaf `3` or `4`, so the root slot is
  never moved);
* `shapeTotal π x patSlot2 0 = · 1 = · 3 = · 4` and `shapeTotal π x patSlot2 5 = · 6`
  (the tree automorphism `u ↔ w`, `b₀ ↔ b₃`, `b₁ ↔ b₄`, which fixes the root leaf `2` of the
  `patSlot2` class).

Consequently the twelve off-middle root-class bounds of Lemma I.4.16 (`p = 5`, `k = 2`) reduce to
seven: five for `patSlot0` (`j = 0, 1, 3, 5, 6`) and two for `patSlot2` (`j = 0, 5`).  This is a
reduction of the *statements*, not of the analysis: no mass bound is proved here, and the middle
split `j = 2` is untouched.  In particular, whoever closes the split `j = 3` mass bound closes the
`j = 4` column for both sockets at once.

Everything is unconditional: no profile invariance, no independence, no finiteness, and no
measure-theoretic input beyond `law π` applied to the *same* configuration set (the unions over the
internal witnesses are equal as sets, not merely bounded).
-/
module

public import PercLib.CriticalLRP.Correlation.SixPoint.SocketMirror.Defs

/-! Transport of split certificates, leaf masses, and total masses by leaf permutations. -/

open Set MeasureTheory
open scoped ENNReal BigOperators
open PercLib.Percolation.Bond
open PercLib.CriticalLRP.TreeExpansion.FivePoint
open PercLib.CriticalLRP.TreeExpansion.SixPoint
open PercLib.CriticalLRP.TreeExpansion.SixPoint.K2Mass

@[expose] public section

namespace SocketMirror

variable {V : Type*}

/-! ## Permuting two adjacent blocks of the nine-edge certificate -/

/-- `List.Nodup` is invariant under swapping two adjacent blocks of a concatenation (here the
third and fourth block of an eight-block concatenation). -/
theorem nodup_swap_mid34 {α : Type*} (l0 l1 l2 a b l5 l6 l7 : List α) :
    (l0 ++ (l1 ++ (l2 ++ (a ++ (b ++ (l5 ++ (l6 ++ l7))))))).Nodup →
      (l0 ++ (l1 ++ (l2 ++ (b ++ (a ++ (l5 ++ (l6 ++ l7))))))).Nodup := by
  intro h
  have t1 : (a ++ (b ++ (l5 ++ (l6 ++ l7)))).Perm (b ++ (a ++ (l5 ++ (l6 ++ l7)))) := by
    have s1 : (a ++ (b ++ (l5 ++ (l6 ++ l7)))).Perm
        ((b ++ a) ++ (l5 ++ (l6 ++ l7))) := by
      rw [← List.append_assoc a b (l5 ++ (l6 ++ l7))]
      exact List.perm_append_comm.append_right (l5 ++ (l6 ++ l7))
    have s2 : ((b ++ a) ++ (l5 ++ (l6 ++ l7))).Perm
        (b ++ (a ++ (l5 ++ (l6 ++ l7)))) := by rw [List.append_assoc]
    exact s1.trans s2
  have hperm := (((t1.append_left l2).append_left l1).append_left l0)
  exact List.Perm.nodup_iff hperm |>.mp h

/-- `List.Nodup` is invariant under swapping the first two blocks of a concatenation. -/
theorem nodup_swap_front {α : Type*} (a b B : List α) :
    (a ++ (b ++ B)).Nodup → (b ++ (a ++ B)).Nodup := by
  intro h
  have t1 : (a ++ (b ++ B)).Perm (b ++ (a ++ B)) := by
    have s1 : (a ++ (b ++ B)).Perm ((b ++ a) ++ B) := by
      rw [← List.append_assoc a b B]
      exact List.perm_append_comm.append_right B
    have s2 : ((b ++ a) ++ B).Perm (b ++ (a ++ B)) := by rw [List.append_assoc]
    exact s1.trans s2
  exact List.Perm.nodup_iff t1 |>.mp h

/-! ## The split trees at `j = 3` and `j = 4`, and at `j = 0` and `j = 1` -/

/-- **The `3 ↔ 4` certificate transport.**  Interchanging the two leaf arguments `b₃, b₄`
(both attached to `w`) turns the split certificate at position `3` into the one at position `4`.
No hypothesis on `G`. -/
theorem combSystem_three_iff_four (G : SimpleGraph V) (b0 b1 b2 b3 b4 t u v w c : V) :
    CombSystem G b0 b1 b2 b3 b4 t u v w c 3 ↔
      CombSystem G b0 b1 b2 b4 b3 t u v w c 4 := by
  constructor
  · rintro ⟨p0, p1, p2, p3, p4, s1, s2, Q, hn, hc⟩
    refine ⟨p0, p1, p2, p4, p3, s1, s2, Q, ?_, hc⟩
    simp only [List.append_assoc] at hn ⊢
    exact nodup_swap_mid34 _ _ _ _ _ _ _ _ hn
  · rintro ⟨p0, p1, p2, p3, p4, s1, s2, Q, hn, hc⟩
    refine ⟨p0, p1, p2, p4, p3, s1, s2, Q, ?_, hc⟩
    simp only [List.append_assoc] at hn ⊢
    exact nodup_swap_mid34 _ _ _ _ _ _ _ _ hn

/-- **The `0 ↔ 1` certificate transport.**  Interchanging the two leaf arguments `b₀, b₁`
(both attached to `u`) turns the split certificate at position `0` into the one at position `1`. -/
theorem combSystem_zero_iff_one (G : SimpleGraph V) (b0 b1 b2 b3 b4 t u v w c : V) :
    CombSystem G b0 b1 b2 b3 b4 t u v w c 0 ↔
      CombSystem G b1 b0 b2 b3 b4 t u v w c 1 := by
  constructor
  · rintro ⟨p0, p1, p2, p3, p4, s1, s2, Q, hn, hc⟩
    refine ⟨p1, p0, p2, p3, p4, s1, s2, Q, ?_, hc⟩
    simp only [List.append_assoc] at hn ⊢
    exact nodup_swap_front _ _ _ hn
  · rintro ⟨p0, p1, p2, p3, p4, s1, s2, Q, hn, hc⟩
    refine ⟨p1, p0, p2, p3, p4, s1, s2, Q, ?_, hc⟩
    simp only [List.append_assoc] at hn ⊢
    exact nodup_swap_front _ _ _ hn

/-! ## The leaf masses of the two split positions -/

/-- **The `3 ↔ 4` leaf-mass transport**: the mass of the shape with leaf tuple `L` and sixth
terminal `t` at split `3` is the mass at split `4` of the leaf tuple `L ∘ swap34`.  This is
`combSystem_three_iff_four` under the union of the four internal witnesses; the measure and the
witnesses are untouched. -/
theorem leafMass_three_eq_four (π : Sym2 V → unitInterval) (L : Fin 5 → V) (t : V) :
    leafMass π 3 L t = leafMass π 4 (fun i => L (swap34 i)) t := by
  simp only [leafMass, swap34_three, swap34_four, swap34_zero, swap34_one, swap34_two]
  congr 1
  ext ω
  simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
  refine exists_congr fun c => exists_congr fun u => exists_congr fun v =>
    exists_congr fun w' => ?_
  exact combSystem_three_iff_four (openGraph ω) (L 0) (L 1) (L 2) (L 3) (L 4) t u v w' c

/-- **The `0 ↔ 1` leaf-mass transport**: the mass at split `0` of `L` is the mass at split `1` of
`L ∘ swap01`. -/
theorem leafMass_zero_eq_one (π : Sym2 V → unitInterval) (L : Fin 5 → V) (t : V) :
    leafMass π 0 L t = leafMass π 1 (fun i => L (swap01 i)) t := by
  simp only [leafMass, swap01_zero, swap01_one, swap01_two, swap01_three, swap01_four]
  congr 1
  ext ω
  simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
  refine exists_congr fun c => exists_congr fun u => exists_congr fun v =>
    exists_congr fun w' => ?_
  exact combSystem_zero_iff_one (openGraph ω) (L 0) (L 1) (L 2) (L 3) (L 4) t u v w' c


/-! ## Reindexing the five free terminal sums against the slot permutation -/

/-- **The `3 → 4` reindexing step.**  A slot permutation `σ` of the five free coordinates which
fixes the sixth-terminal coordinate `4` and commutes with the leaf swap `swap34` through the
pattern `p` turns the `j = 3` sum over all free terminals into the `j = 4` sum of the same
pattern.  This is `TwoJointEval.tsum_fin5_perm` applied to the summand of `patTotal`. -/
theorem patTotal_three_eq_four_of_slots (π : Sym2 V → unitInterval) (x : V) (p : Fin 5 → Fin 5)
    (σ : Equiv.Perm (Fin 5)) (hσ : σ 4 = 4)
    (h : ∀ (u : Fin 5 → V) (i : Fin 5),
      slotVec x u (p (swap34 i)) = slotVec x (fun j => u (σ j)) (p i)) :
    patTotal π x p 3 = patTotal π x p 4 := by
  have step1 : patTotal π x p 3 =
      ∑' u : Fin 5 → V, leafMass π 4 (fun i => slotVec x u (p (swap34 i))) (u 4) :=
    tsum_congr fun u => leafMass_three_eq_four π (fun i => slotVec x u (p i)) (u 4)
  have step2 : (∑' u : Fin 5 → V, leafMass π 4 (fun i => slotVec x u (p (swap34 i))) (u 4))
      = ∑' u : Fin 5 → V, (fun v : Fin 5 → V =>
          leafMass π 4 (fun i => slotVec x v (p i)) (v 4)) (fun j => u (σ j)) := by
    refine tsum_congr fun u => ?_
    rw [funext (h u)]
    simp only [hσ]
  have step3 : (∑' u : Fin 5 → V, (fun v : Fin 5 → V =>
        leafMass π 4 (fun i => slotVec x v (p i)) (v 4)) (fun j => u (σ j)))
      = ∑' v : Fin 5 → V, leafMass π 4 (fun i => slotVec x v (p i)) (v 4) :=
    PercLib.CriticalLRP.SixPoint.TwoJointEval.tsum_fin5_perm σ
      (fun v : Fin 5 → V => leafMass π 4 (fun i => slotVec x v (p i)) (v 4))
  rw [patTotal, patTotal]
  exact step1.trans (step2.trans step3)

/-- **The `0 → 1` reindexing step**, the mirror of `patTotal_three_eq_four_of_slots`. -/
theorem patTotal_zero_eq_one_of_slots (π : Sym2 V → unitInterval) (x : V) (p : Fin 5 → Fin 5)
    (σ : Equiv.Perm (Fin 5)) (hσ : σ 4 = 4)
    (h : ∀ (u : Fin 5 → V) (i : Fin 5),
      slotVec x u (p (swap01 i)) = slotVec x (fun j => u (σ j)) (p i)) :
    patTotal π x p 0 = patTotal π x p 1 := by
  have step1 : patTotal π x p 0 =
      ∑' u : Fin 5 → V, leafMass π 1 (fun i => slotVec x u (p (swap01 i))) (u 4) :=
    tsum_congr fun u => leafMass_zero_eq_one π (fun i => slotVec x u (p i)) (u 4)
  have step2 : (∑' u : Fin 5 → V, leafMass π 1 (fun i => slotVec x u (p (swap01 i))) (u 4))
      = ∑' u : Fin 5 → V, (fun v : Fin 5 → V =>
          leafMass π 1 (fun i => slotVec x v (p i)) (v 4)) (fun j => u (σ j)) := by
    refine tsum_congr fun u => ?_
    rw [funext (h u)]
    simp only [hσ]
  have step3 : (∑' u : Fin 5 → V, (fun v : Fin 5 → V =>
        leafMass π 1 (fun i => slotVec x v (p i)) (v 4)) (fun j => u (σ j)))
      = ∑' v : Fin 5 → V, leafMass π 1 (fun i => slotVec x v (p i)) (v 4) :=
    PercLib.CriticalLRP.SixPoint.TwoJointEval.tsum_fin5_perm σ
      (fun v : Fin 5 → V => leafMass π 1 (fun i => slotVec x v (p i)) (v 4))
  rw [patTotal, patTotal]
  exact step1.trans (step2.trans step3)

/-! ## The fifteen labelled patterns at `j = 3` and `j = 4`

Each pattern is a permutation of the five slot coordinates in which the root `0` sits in slot `0`
(twelve patterns) or slot `2` (three patterns); in no pattern does the root sit in comb slot `3`
or `4`, so the leaf swap `swap34` always acts on two *free* leaf positions and induces a
transposition of two free summation coordinates, never touching the root coordinate or the sixth
terminal coordinate `4`.  Every `σ` below is that transposition, `decide` proves `σ 4 = 4`, and
the five slot identities are `rfl`. -/

/-- **`j = 3` and `j = 4` have the same mass for every labelled pattern.** -/
theorem patTotal_pat_three_eq_four (π : Sym2 V → unitInterval) (x : V) (k : Fin 15) :
    patTotal π x (pat k) 3 = patTotal π x (pat k) 4 := by
  fin_cases k
  · exact patTotal_three_eq_four_of_slots π x _ (Equiv.swap (2 : Fin 5) (3 : Fin 5))
      (by decide) (by intro u i; fin_cases i <;> rfl)
  · exact patTotal_three_eq_four_of_slots π x _ (Equiv.swap (1 : Fin 5) (3 : Fin 5))
      (by decide) (by intro u i; fin_cases i <;> rfl)
  · exact patTotal_three_eq_four_of_slots π x _ (Equiv.swap (1 : Fin 5) (2 : Fin 5))
      (by decide) (by intro u i; fin_cases i <;> rfl)
  · exact patTotal_three_eq_four_of_slots π x _ (Equiv.swap (2 : Fin 5) (3 : Fin 5))
      (by decide) (by intro u i; fin_cases i <;> rfl)
  · exact patTotal_three_eq_four_of_slots π x _ (Equiv.swap (1 : Fin 5) (3 : Fin 5))
      (by decide) (by intro u i; fin_cases i <;> rfl)
  · exact patTotal_three_eq_four_of_slots π x _ (Equiv.swap (1 : Fin 5) (2 : Fin 5))
      (by decide) (by intro u i; fin_cases i <;> rfl)
  · exact patTotal_three_eq_four_of_slots π x _ (Equiv.swap (2 : Fin 5) (3 : Fin 5))
      (by decide) (by intro u i; fin_cases i <;> rfl)
  · exact patTotal_three_eq_four_of_slots π x _ (Equiv.swap (0 : Fin 5) (3 : Fin 5))
      (by decide) (by intro u i; fin_cases i <;> rfl)
  · exact patTotal_three_eq_four_of_slots π x _ (Equiv.swap (0 : Fin 5) (2 : Fin 5))
      (by decide) (by intro u i; fin_cases i <;> rfl)
  · exact patTotal_three_eq_four_of_slots π x _ (Equiv.swap (1 : Fin 5) (3 : Fin 5))
      (by decide) (by intro u i; fin_cases i <;> rfl)
  · exact patTotal_three_eq_four_of_slots π x _ (Equiv.swap (0 : Fin 5) (3 : Fin 5))
      (by decide) (by intro u i; fin_cases i <;> rfl)
  · exact patTotal_three_eq_four_of_slots π x _ (Equiv.swap (0 : Fin 5) (1 : Fin 5))
      (by decide) (by intro u i; fin_cases i <;> rfl)
  · exact patTotal_three_eq_four_of_slots π x _ (Equiv.swap (1 : Fin 5) (2 : Fin 5))
      (by decide) (by intro u i; fin_cases i <;> rfl)
  · exact patTotal_three_eq_four_of_slots π x _ (Equiv.swap (0 : Fin 5) (2 : Fin 5))
      (by decide) (by intro u i; fin_cases i <;> rfl)
  · exact patTotal_three_eq_four_of_slots π x _ (Equiv.swap (0 : Fin 5) (1 : Fin 5))
      (by decide) (by intro u i; fin_cases i <;> rfl)

/-- **The shape totals at `j = 3` and `j = 4` agree for every labelled pattern.** -/
theorem shapeTotal5_three_eq_four (π : Sym2 V → unitInterval) (x : V) (k : Fin 15) :
    shapeTotal5 π x k 3 = shapeTotal5 π x k 4 := by
  rw [← patTotal_pat (j := 3), ← patTotal_pat (j := 4)]
  exact patTotal_pat_three_eq_four π x k

/-! ## The `patSlot2` root class at `j = 0` and `j = 1` -/

/-- **`j = 0` and `j = 1` have the same mass for the three patterns of the `patSlot2` root class**
(the patterns whose root leaf is `2`, which the leaf swap `swap01` fixes). -/
theorem patTotal_pat_zero_eq_one (π : Sym2 V → unitInterval) (x : V) (k : Fin 15)
    (hk : pat k 2 = 0) : patTotal π x (pat k) 0 = patTotal π x (pat k) 1 := by
  fin_cases k
  · exact patTotal_zero_eq_one_of_slots π x _ (Equiv.swap (0 : Fin 5) (1 : Fin 5))
      (by decide) (by intro u i; fin_cases i <;> rfl)
  · exact patTotal_zero_eq_one_of_slots π x _ (Equiv.swap (0 : Fin 5) (2 : Fin 5))
      (by decide) (by intro u i; fin_cases i <;> rfl)
  · exact patTotal_zero_eq_one_of_slots π x _ (Equiv.swap (0 : Fin 5) (3 : Fin 5))
      (by decide) (by intro u i; fin_cases i <;> rfl)
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

/-- **The `patSlot2` shape total at `j = 1` is the one at `j = 0`.** -/
theorem shapeTotal5_patSlot2_zero_eq_one (π : Sym2 V → unitInterval) (x : V) :
    shapeTotal5 π x patSlot2 0 = shapeTotal5 π x patSlot2 1 := by
  rw [← patTotal_pat (j := 0), ← patTotal_pat (j := 1)]
  exact patTotal_pat_zero_eq_one π x patSlot2 (by decide)


/-! ## The root-class shape totals and the reduction of the off-middle bounds -/

/-- **The shape total at `j = 3` and `j = 4` agree for every labelled pattern.**  This is the
`K2Mass.shapeTotal` form of `shapeTotal5_three_eq_four`; no hypothesis on `π`, `x` or `V`. -/
theorem shapeTotal_three_eq_four (π : Sym2 V → unitInterval) (x : V) (k : Fin 15) :
    shapeTotal π x k 3 = shapeTotal π x k 4 := by
  rw [shapeTotal_eq_shapeTotal5, shapeTotal_eq_shapeTotal5, shapeTotal5_three_eq_four]

/-- The canonical root class with the root in comb slot `0`. -/
theorem shapeTotal_patSlot0_three_eq_four (π : Sym2 V → unitInterval) (x : V) :
    shapeTotal π x patSlot0 3 = shapeTotal π x patSlot0 4 :=
  shapeTotal_three_eq_four π x patSlot0

/-- The canonical root class with the root in comb slot `2`. -/
theorem shapeTotal_patSlot2_three_eq_four (π : Sym2 V → unitInterval) (x : V) :
    shapeTotal π x patSlot2 3 = shapeTotal π x patSlot2 4 :=
  shapeTotal_three_eq_four π x patSlot2

/-- The `patSlot2` root class at `j = 0` and `j = 1`. -/
theorem shapeTotal_patSlot2_zero_eq_one (π : Sym2 V → unitInterval) (x : V) :
    shapeTotal π x patSlot2 0 = shapeTotal π x patSlot2 1 := by
  rw [shapeTotal_eq_shapeTotal5, shapeTotal_eq_shapeTotal5, shapeTotal5_patSlot2_zero_eq_one]

/-- **The `j = 4` bound of the `patSlot0` root class follows from the `j = 3` bound.** -/
theorem shapeTotal_patSlot0_four_le_of_three (π : Sym2 V → unitInterval) (x : V)
    (h : shapeTotal π x patSlot0 3 ≤ shapeCost π x) :
    shapeTotal π x patSlot0 4 ≤ shapeCost π x := by
  rwa [← shapeTotal_patSlot0_three_eq_four]

/-- **The `j = 4` bound of the `patSlot2` root class follows from the `j = 3` bound.** -/
theorem shapeTotal_patSlot2_four_le_of_three (π : Sym2 V → unitInterval) (x : V)
    (h : shapeTotal π x patSlot2 3 ≤ shapeCost π x) :
    shapeTotal π x patSlot2 4 ≤ shapeCost π x := by
  rwa [← shapeTotal_patSlot2_three_eq_four]

/-- **The `j = 1` bound of the `patSlot2` root class follows from the `j = 0` bound.** -/
theorem shapeTotal_patSlot2_one_le_of_zero (π : Sym2 V → unitInterval) (x : V)
    (h : shapeTotal π x patSlot2 0 ≤ shapeCost π x) :
    shapeTotal π x patSlot2 1 ≤ shapeCost π x := by
  rwa [← shapeTotal_patSlot2_zero_eq_one]

/-! ## The `k = 2` fifth-moment bound from nine off-middle root-class bounds -/

/-- **The `k = 2` fifth-moment bound from nine off-middle root-class bounds.**

`K2Mass.RootCollapse.fifth_moment_k2_le_of_rootSlot_bounds` needs the twelve off-middle
root-class bounds (`two sockets × six splits`).  The mirror identities proved here remove three
of them: the `j = 4` bound of each socket follows from its `j = 3` bound, and the `j = 1` bound of
`patSlot2` follows from its `j = 0` bound.  What remains — and is *not* proved here — is five
bounds for `patSlot0` (`j = 0, 1, 3, 5, 6`) and four for `patSlot2` (`j = 0, 3, 5, 6`), in
addition to `hq` which covers the middle split `j = 2`.  Neither the middle split nor the
`j = 0, 1, 5, 6` bounds are re-proved here. -/
theorem fifth_moment_k2_le_of_rootSlot_nine_bounds [Countable V] [AddCommGroup V]
    (π : Sym2 V → unitInterval)
    (hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y))
    (h0 : ∀ j ∈ ({0, 1, 3, 5, 6} : Finset (Fin 7)), shapeTotal π 0 patSlot0 j ≤ shapeCost π 0)
    (h2 : ∀ j ∈ ({0, 3, 5, 6} : Finset (Fin 7)), shapeTotal π 0 patSlot2 j ≤ shapeCost π 0) :
    ∫⁻ ω, (PercLib.CriticalLRP.Percolation.cardFun
        (PercLib.CriticalLRP.cluster ω (0 : V))) ^ 5 ∂(law π) ≤
      105 * (∫⁻ ω, (PercLib.CriticalLRP.Percolation.cardFun
          (PercLib.CriticalLRP.cluster ω (0 : V))) ^ 2 ∂(law π)) ^ 2 *
        (∫⁻ ω, PercLib.CriticalLRP.Percolation.cardFun
          (PercLib.CriticalLRP.cluster ω (0 : V)) ∂(law π)) ^ 3 := by
  refine PercLib.CriticalLRP.TreeExpansion.SixPoint.K2Mass.fifth_moment_k2_le_of_rootSlot_bounds
    π hq (fun j hj => ?_) (fun j hj => ?_)
  · fin_cases j
    · exact h0 0 (by decide)
    · exact h0 1 (by decide)
    · exact absurd rfl hj
    · exact h0 3 (by decide)
    · exact shapeTotal_patSlot0_four_le_of_three π 0 (h0 3 (by decide))
    · exact h0 5 (by decide)
    · exact h0 6 (by decide)
  · fin_cases j
    · exact h2 0 (by decide)
    · exact shapeTotal_patSlot2_one_le_of_zero π 0 (h2 0 (by decide))
    · exact absurd rfl hj
    · exact h2 3 (by decide)
    · exact shapeTotal_patSlot2_four_le_of_three π 0 (h2 3 (by decide))
    · exact h2 5 (by decide)
    · exact h2 6 (by decide)

end SocketMirror
