/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Star-pair shape regrouping and native moment evaluation. The pointwise first factor
keeps its joint three-point event rather than a product of separate two-point factors.
-/
module

public import PercLib.CriticalLRP.Correlation.CubicMixed.Defs

open Set MeasureTheory
open scoped ENNReal BigOperators
open PercLib.Percolation.Bond
open PercLib.Probability

@[expose] public section

namespace PercLib.CriticalLRP.TreeExpansion

variable {V : Type*}


/-! ### Bookkeeping -/

/-- The edge set of an appended walk is the union of the edge sets. -/
theorem walkEdges_append [Countable V] {ω : Config V} {a b c : V}
    (p : (openGraph ω).Walk a b) (q : (openGraph ω).Walk b c) :
    walkEdges (p.append q) = walkEdges p ∪ walkEdges q := by
  ext e
  simp [walkEdges, SimpleGraph.Walk.edges_append, List.mem_append]

/-- An intersection of two connection events is an increasing event. -/
theorem isUpperSet_inter_conn [Countable V] (a b c : V) :
    IsUpperSet ((conn a c ∩ conn b c : Set (Config V))) :=
  fun _ _ h hin =>
    ⟨isIncreasing_connects a c h hin.1, isIncreasing_connects b c h hin.2⟩

/-! ### Star-pair certificate bounds -/

/-- A star-pair certificate is a nested disjoint occurrence of three increasing events. -/
theorem starPairEvent_subset [Countable V] (root x y z w : V) :
    StarPairEvent (V := V) root x y z w ⊆
      disjointOccurrence (disjointOccurrence (conn root w ∩ conn x w) (conn w y))
        (conn w z) := by
  rintro ω ⟨U, W₁, W₂, hfU, hf1, hf2, hU, h1, h2, hmU, hm1, hm2, hdU1, hdU2, hd12⟩
  exact (mem_disjointOccurrence_three_iff (isUpperSet_inter_conn root x w)
      (isIncreasing_connects w y) (isIncreasing_connects w z) ω).mpr
    ⟨U, W₁, W₂, hfU, hf1, hf2, hdU1, hdU2, hd12, hU, h1, h2, hmU, hm1, hm2⟩

/-- **The regrouping.**  The five pairwise edge-disjoint walks of a `ShapeWitness` with branch
vertices `u` (carrying `root` and `a`) and `v` (carrying `b` and `c`) regroup into a star-pair
certificate centred at the middle vertex `v`: the joint pair `root <-> v, a <-> v` is certified by
the concatenations through `u`, and the two remaining arms `v <-> b`, `v <-> c` are untouched.
All five walk edge lists remain pairwise disjoint. -/
theorem shapeWitness_starPair [Countable V] {ω : Config V} {root a b c u v : V}
    (h : ShapeWitness (openGraph ω) root a b c u v) :
    ω ∈ StarPairEvent (V := V) root a b c v := by
  obtain ⟨p, q, s, t, r, hpq, hps, hpt, hpr, hqs, hqt, hqr, hst, hsr, htr⟩ := h
  have hpr_sub : walkEdges (p.append r) = walkEdges p ∪ walkEdges r := walkEdges_append p r
  have hqr_sub : walkEdges (q.append r) = walkEdges q ∪ walkEdges r := walkEdges_append q r
  have dps : Disjoint (walkEdges p) (walkEdges s) := disjoint_walkEdges p s hps
  have dpr : Disjoint (walkEdges p) (walkEdges t) := disjoint_walkEdges p t hpt
  have drs : Disjoint (walkEdges r) (walkEdges s) := (disjoint_walkEdges s r hsr).symm
  have drt : Disjoint (walkEdges r) (walkEdges t) := (disjoint_walkEdges t r htr).symm
  have dqs : Disjoint (walkEdges q) (walkEdges s) := disjoint_walkEdges q s hqs
  have dqt : Disjoint (walkEdges q) (walkEdges t) := disjoint_walkEdges q t hqt
  have dUs : Disjoint (walkEdges (p.append r) ∪ walkEdges (q.append r)) (walkEdges s) := by
    rw [hpr_sub, hqr_sub]
    exact disjoint_union_left.mpr
      ⟨disjoint_union_left.mpr ⟨dps, drs⟩, disjoint_union_left.mpr ⟨dqs, drs⟩⟩
  have dUt : Disjoint (walkEdges (p.append r) ∪ walkEdges (q.append r)) (walkEdges t) := by
    rw [hpr_sub, hqr_sub]
    exact disjoint_union_left.mpr
      ⟨disjoint_union_left.mpr ⟨dpr, drt⟩, disjoint_union_left.mpr ⟨dqt, drt⟩⟩
  have dst : Disjoint (walkEdges s) (walkEdges t) := disjoint_walkEdges s t hst
  have hmU : (walkEdges (p.append r) ∪ walkEdges (q.append r)) ∈ (conn root v ∩ conn a v) := by
    refine ⟨?_, ?_⟩
    · exact conn_mono subset_union_left (mem_conn_walkEdges (p.append r))
    · exact conn_mono subset_union_right (mem_conn_walkEdges (q.append r))
  have hm1 : walkEdges s ∈ conn v b := by
    have h' := mem_conn_walkEdges s
    rwa [conn_symm b v] at h'
  have hm2 : walkEdges t ∈ conn v c := by
    have h' := mem_conn_walkEdges t
    rwa [conn_symm c v] at h'
  refine ⟨walkEdges (p.append r) ∪ walkEdges (q.append r), walkEdges s, walkEdges t,
    (walkEdges_finite (p.append r)).union (walkEdges_finite (q.append r)),
    walkEdges_finite s, walkEdges_finite t, ?_, walkEdges_subset s, walkEdges_subset t,
    hmU, hm1, hm2, dUs, dUt, dst⟩
  exact union_subset (walkEdges_subset (p.append r)) (walkEdges_subset (q.append r))

/-! ### Threefold BK at the star-pair event -/

/-- **The per-centre star-pair bound.**  Threefold BK: the joint pair costs the joint probability
`P(root <-> w, x <-> w)` and the two single arms cost `tau w y` and `tau w z`. -/
theorem starPairEvent_le [Countable V] (π : Sym2 V → unitInterval) (root x y z w : V) :
    law π (StarPairEvent (V := V) root x y z w)
      ≤ law π (conn root w ∩ conn x w) * (tau π w y * tau π w z) := by
  refine (measure_mono (starPairEvent_subset root x y z w)).trans ?_
  have hbk := countable_profile_bk_foldl (p := π) [conn w y, conn w z] ?_
    (A := conn root w ∩ conn x w) ?_
  · simpa [law, List.foldl, tau] using hbk
  · intro B hB
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hB
    rcases hB with rfl | rfl
    exacts [isIncreasing_connects w y, isIncreasing_connects w z]
  · exact isUpperSet_inter_conn root x w

/-! ### The exact native second moment -/

/-- A product of two indicator functions is the indicator of the intersection. -/
theorem indicator_mul_two {α : Type*} (s t : Set α) :
    ((s.indicator (fun _ => (1 : ℝ≥0∞))) * (t.indicator (fun _ => (1 : ℝ≥0∞))))
      = (s ∩ t).indicator (fun _ => (1 : ℝ≥0∞)) := by
  funext a
  simp only [Pi.mul_apply]
  by_cases h1 : a ∈ s <;> by_cases h2 : a ∈ t <;>
    simp [Set.indicator_of_mem, Set.indicator_of_notMem, h1, h2]

/-- **The exact second moment of the cluster size at the native law.**  `|K_x|^2` expands into
pairs, so by Tonelli `E|K_x|^2` is the double sum of two-point connection probabilities. -/
theorem lintegral_cardFun_sq_eq [Countable V] (π : Sym2 V → unitInterval) (x : V) :
    ∫⁻ ω, (PercLib.CriticalLRP.Percolation.cardFun (PercLib.CriticalLRP.cluster ω x)) ^ 2
        ∂(law π)
      = ∑' y, ∑' z, law π (conn x y ∩ conn x z) := by
  classical
  obtain ⟨f, hf⟩ : ∃ f : V → Config V → ℝ≥0∞,
      ∀ (y : V) (ω : Config V),
        f y ω = (conn x y).indicator (fun _ => (1 : ℝ≥0∞)) ω :=
    ⟨fun y ω => (conn x y).indicator (fun _ => (1 : ℝ≥0∞)) ω, fun _ _ => rfl⟩
  have hfm : ∀ y, Measurable (f y) := by
    intro y
    rw [show f y = fun ω => (conn x y).indicator (fun _ => (1 : ℝ≥0∞)) ω from funext (hf y)]
    exact measurable_const.indicator (measurableSet_conn x y)
  have hcard : ∀ ω, PercLib.CriticalLRP.Percolation.cardFun
      (PercLib.CriticalLRP.cluster ω x) = ∑' y, f y ω := by
    intro ω
    rw [PercLib.CriticalLRP.Percolation.cardFun_eq_encard, encard_cluster_eq_tsum]
    exact tsum_congr fun y => (hf y ω).symm
  have hsq : ∀ ω, (∑' y, f y ω) ^ 2 = ∑' y, ∑' z, f y ω * f z ω := by
    intro ω
    rw [sq]
    exact (tsum_two_mul (fun y => f y ω) (fun z => f z ω)).symm
  have hjoint : ∀ y z : V,
      ∫⁻ ω, f y ω * f z ω ∂(law π) = law π (conn x y ∩ conn x z) := by
    intro y z
    have hfun : (fun ω => f y ω * f z ω)
        = ((conn x y).indicator (fun _ => (1 : ℝ≥0∞))
            * (conn x z).indicator (fun _ => (1 : ℝ≥0∞))) := by
      funext ω
      simp only [Pi.mul_apply]
      rw [hf y ω, hf z ω]
    rw [hfun, indicator_mul_two]
    exact lintegral_indicator_one ((measurableSet_conn x y).inter (measurableSet_conn x z))
  calc ∫⁻ ω, (PercLib.CriticalLRP.Percolation.cardFun
        (PercLib.CriticalLRP.cluster ω x)) ^ 2 ∂(law π)
      = ∫⁻ ω, ∑' y, ∑' z, f y ω * f z ω ∂(law π) := by
        refine lintegral_congr fun ω => ?_
        rw [hcard ω, hsq ω]
    _ = ∑' y, ∫⁻ ω, ∑' z, f y ω * f z ω ∂(law π) := by
        refine lintegral_tsum fun y => ?_
        exact (Measurable.tsum fun z => (hfm y).mul (hfm z)).aemeasurable
    _ = ∑' y, ∑' z, ∫⁻ ω, f y ω * f z ω ∂(law π) := by
        refine tsum_congr fun y => lintegral_tsum fun z => ?_
        exact ((hfm y).mul (hfm z)).aemeasurable
    _ = ∑' y, ∑' z, law π (conn x y ∩ conn x z) :=
        tsum_congr fun y => tsum_congr fun z => hjoint y z

/-- **The native second moment is a joint-pair sum, and it is at most the star sum.**
`{o <-> x, o <-> w}` forces `{o <-> w, x <-> w}`; the latter is the joint pair that the star-pair
regrouping produces.  Hence `E|K_o|^2 <= Z_o` for `Z_o = sum_{x,w} P(o <-> w, x <-> w)`. -/
theorem lintegral_cardFun_sq_le_joinSum [Countable V] (π : Sym2 V → unitInterval) (o : V) :
    ∫⁻ ω, (PercLib.CriticalLRP.Percolation.cardFun (PercLib.CriticalLRP.cluster ω o)) ^ 2
        ∂(law π)
      ≤ ∑' x, ∑' w, law π (conn o w ∩ conn x w) := by
  rw [lintegral_cardFun_sq_eq π o]
  refine ENNReal.tsum_le_tsum fun y => ENNReal.tsum_le_tsum fun z => ?_
  refine measure_mono ?_
  rintro ω ⟨h1, h2⟩
  have h1' : ω ∈ conn y o := by rw [conn_symm o y] at h1; exact h1
  exact ⟨h2, conn_trans h1' h2⟩

/-! ### The mixed cubic bound -/

variable [Countable V] [AddCommGroup V]

set_option linter.unusedSectionVars false

/-- The three-point connection event is covered by the star-pair events over the three labellings
of the labelled binary tree on four leaves, all centres `w` included. -/
theorem triple_cover (a b c : V) :
    (conn 0 a ∩ conn 0 b ∩ conn 0 c) ⊆
      ((⋃ w, StarPairEvent (V := V) 0 a b c w)
        ∪ (⋃ w, StarPairEvent (V := V) 0 b a c w))
        ∪ (⋃ w, StarPairEvent (V := V) 0 c a b w) := by
  rintro ω ⟨⟨h0a, h0b⟩, h0c⟩
  rcases Native.arm_decomposition_native 0 a b c ω h0a h0b h0c with ⟨u, v, hw⟩ | ⟨u, v, hw⟩ | ⟨u, v, hw⟩
  · exact Or.inl (Or.inl (mem_iUnion.mpr ⟨v, shapeWitness_starPair hw⟩))
  · exact Or.inl (Or.inr (mem_iUnion.mpr ⟨v, shapeWitness_starPair hw⟩))
  · exact Or.inr (mem_iUnion.mpr ⟨v, shapeWitness_starPair hw⟩)

/-- **The per-triple bound.**  For fixed `a, b, c` the probability that all three lie in the
cluster of `0` is at most the sum over centres `w` of the three star-pair products. -/
theorem triple_le_starSum (π : Sym2 V → unitInterval) (a b c : V) :
    law π (conn 0 a ∩ conn 0 b ∩ conn 0 c)
      ≤ ∑' w,
          (law π (conn 0 w ∩ conn a w) * (tau π w b * tau π w c)
            + law π (conn 0 w ∩ conn b w) * (tau π w a * tau π w c)
            + law π (conn 0 w ∩ conn c w) * (tau π w a * tau π w b)) := by
  have h1 := starPairEvent_le (V := V) π 0 a b c
  have h2 := starPairEvent_le (V := V) π 0 b a c
  have h3 := starPairEvent_le (V := V) π 0 c a b
  have hU1 := measure_iUnion_le (μ := law π) (s := fun w => StarPairEvent (V := V) 0 a b c w)
  have hU2 := measure_iUnion_le (μ := law π) (s := fun w => StarPairEvent (V := V) 0 b a c w)
  have hU3 := measure_iUnion_le (μ := law π) (s := fun w => StarPairEvent (V := V) 0 c a b w)
  calc law π (conn 0 a ∩ conn 0 b ∩ conn 0 c)
      ≤ law π (((⋃ w, StarPairEvent (V := V) 0 a b c w)
          ∪ (⋃ w, StarPairEvent (V := V) 0 b a c w))
          ∪ (⋃ w, StarPairEvent (V := V) 0 c a b w)) :=
        measure_mono (μ := law π) (triple_cover (V := V) a b c)
    _ ≤ law π ((⋃ w, StarPairEvent (V := V) 0 a b c w)
          ∪ (⋃ w, StarPairEvent (V := V) 0 b a c w))
          + law π (⋃ w, StarPairEvent (V := V) 0 c a b w) := measure_union_le _ _
    _ ≤ (law π (⋃ w, StarPairEvent (V := V) 0 a b c w)
          + law π (⋃ w, StarPairEvent (V := V) 0 b a c w))
          + law π (⋃ w, StarPairEvent (V := V) 0 c a b w) :=
        add_le_add (measure_union_le _ _) le_rfl
    _ ≤ (∑' w, law π (StarPairEvent (V := V) 0 a b c w))
          + (∑' w, law π (StarPairEvent (V := V) 0 b a c w))
          + (∑' w, law π (StarPairEvent (V := V) 0 c a b w)) :=
        add_le_add (add_le_add hU1 hU2) hU3
    _ ≤ (∑' w, law π (conn 0 w ∩ conn a w) * (tau π w b * tau π w c))
          + (∑' w, law π (conn 0 w ∩ conn b w) * (tau π w a * tau π w c))
          + (∑' w, law π (conn 0 w ∩ conn c w) * (tau π w a * tau π w b)) :=
        add_le_add (add_le_add (ENNReal.tsum_le_tsum h1) (ENNReal.tsum_le_tsum h2))
          (ENNReal.tsum_le_tsum h3)
    _ = ∑' w,
          (law π (conn 0 w ∩ conn a w) * (tau π w b * tau π w c)
            + law π (conn 0 w ∩ conn b w) * (tau π w a * tau π w c)
            + law π (conn 0 w ∩ conn c w) * (tau π w a * tau π w b)) := by
        rw [ENNReal.tsum_add, ENNReal.tsum_add]

/-- Moving the first index of a triple sum to the back. -/
theorem tsum_swap_fst_third (G : V → V → V → V → ℝ≥0∞) :
    (∑' a, ∑' b, ∑' c, ∑' w, G a b c w) = ∑' c, ∑' a, ∑' b, ∑' w, G a b c w := by
  calc (∑' a, ∑' b, ∑' c, ∑' w, G a b c w)
      = ∑' b, ∑' a, ∑' c, ∑' w, G a b c w := ENNReal.tsum_comm
    _ = ∑' b, ∑' c, ∑' a, ∑' w, G a b c w := tsum_congr fun b => ENNReal.tsum_comm
    _ = ∑' c, ∑' b, ∑' a, ∑' w, G a b c w := ENNReal.tsum_comm
    _ = ∑' c, ∑' a, ∑' b, ∑' w, G a b c w := tsum_congr fun c => ENNReal.tsum_comm

/-- One star-pair group: pull the centre sum to the front and factorise the two free leaf sums
into `chi^2`, leaving the joint star sum `Z` untouched. -/
theorem tsum_starTerm_factor (π : Sym2 V → unitInterval)
    (hinv : ∀ a b : V, tau π a b = tau π 0 (b - a)) :
    (∑' a, ∑' b, ∑' c, ∑' w,
        law π (conn 0 w ∩ conn a w) * (tau π w b * tau π w c))
      = (∑' x, tau π 0 x) ^ 2 * (∑' x, ∑' w, law π (conn 0 w ∩ conn x w)) := by
  have hrowX : ∀ a : V, (∑' b, tau π a b) = ∑' x, tau π 0 x :=
    fun a => tsum_row_eq (tau π) 0 hinv a
  rw [tsum_move_last_four]
  have hbc : ∀ (w a : V), (∑' b, ∑' c,
      law π (conn 0 w ∩ conn a w) * (tau π w b * tau π w c))
      = (law π (conn 0 w ∩ conn a w) * (∑' x, tau π 0 x)) * (∑' x, tau π 0 x) := by
    intro w a
    rw [show (∑' b, ∑' c, law π (conn 0 w ∩ conn a w) * (tau π w b * tau π w c))
        = ∑' b, ∑' c, (law π (conn 0 w ∩ conn a w) * tau π w b) * tau π w c from
      tsum_congr fun b => tsum_congr fun c => by ring_nf]
    rw [tsum_two_mul, ENNReal.tsum_mul_left, hrowX w]
  rw [show (∑' w, ∑' a, ∑' b, ∑' c,
        law π (conn 0 w ∩ conn a w) * (tau π w b * tau π w c))
      = ∑' w, ∑' a, (law π (conn 0 w ∩ conn a w) * (∑' x, tau π 0 x)) * (∑' x, tau π 0 x) from
    tsum_congr fun w => tsum_congr fun a => hbc w a]
  have hinner : ∀ w : V, (∑' a,
        (law π (conn 0 w ∩ conn a w) * (∑' x, tau π 0 x)) * (∑' x, tau π 0 x))
      = (∑' a, law π (conn 0 w ∩ conn a w)) * ((∑' x, tau π 0 x) * (∑' x, tau π 0 x)) := by
    intro w
    rw [ENNReal.tsum_mul_right, ENNReal.tsum_mul_right, mul_assoc]
  rw [tsum_congr hinner]
  conv_lhs => rw [ENNReal.tsum_mul_right, ENNReal.tsum_comm]
  rw [pow_two]
  exact mul_comm _ _

/-- Distributing an addition of three four-fold sums. -/
theorem tsum_add_three_four (F G H : V → V → V → V → ℝ≥0∞) :
    (∑' a, ∑' b, ∑' c, ∑' w, (F a b c w + G a b c w + H a b c w))
      = (∑' a, ∑' b, ∑' c, ∑' w, F a b c w)
        + (∑' a, ∑' b, ∑' c, ∑' w, G a b c w)
        + (∑' a, ∑' b, ∑' c, ∑' w, H a b c w) := by
  simp only [ENNReal.tsum_add]

/-- **The mixed cubic bound at the native translation-invariant law.**
`E|K_0|^3 <= 3 (E|K_0|)^2 Z`, where `Z = sum_{x,w} P(0 <-> w, x <-> w)` is the star three-point
function: the second-moment slot of Lemma I.4.16, kept joint instead of being split into two
two-point factors.  No moment finiteness is assumed (`ℝ≥0∞` throughout). -/
theorem cubic_le_chi_sq_mul_joinSum (π : Sym2 V → unitInterval)
    (hinv : ∀ a b : V, tau π a b = tau π 0 (b - a)) :
    ∫⁻ ω, (PercLib.CriticalLRP.Percolation.cardFun (PercLib.CriticalLRP.cluster ω 0)) ^ 3
        ∂(law π)
      ≤ 3 * (∫⁻ ω, PercLib.CriticalLRP.Percolation.cardFun
            (PercLib.CriticalLRP.cluster ω 0) ∂(law π)) ^ 2
          * (∑' x, ∑' w, law π (conn 0 w ∩ conn x w)) := by
  have hmean : (∫⁻ ω, PercLib.CriticalLRP.Percolation.cardFun
      (PercLib.CriticalLRP.cluster ω 0) ∂(law π)) = ∑' x, tau π 0 x := by
    rw [show (∫⁻ ω, PercLib.CriticalLRP.Percolation.cardFun
        (PercLib.CriticalLRP.cluster ω 0) ∂(law π))
        = ∫⁻ ω, ((PercLib.CriticalLRP.cluster ω 0).encard : ℝ≥0∞) ∂(law π) from by
      refine lintegral_congr fun ω => ?_
      exact PercLib.CriticalLRP.Percolation.cardFun_eq_encard _]
    exact chi_eq_tsum_tau π 0
  rw [lintegral_cardFun_cube_eq π 0, hmean]
  have hstep : (∑' a, ∑' b, ∑' c, law π (conn 0 a ∩ conn 0 b ∩ conn 0 c))
      ≤ ∑' a, ∑' b, ∑' c, ∑' w,
          (law π (conn 0 w ∩ conn a w) * (tau π w b * tau π w c)
            + law π (conn 0 w ∩ conn b w) * (tau π w a * tau π w c)
            + law π (conn 0 w ∩ conn c w) * (tau π w a * tau π w b)) :=
    ENNReal.tsum_le_tsum fun a => ENNReal.tsum_le_tsum fun b =>
      ENNReal.tsum_le_tsum fun c => triple_le_starSum π a b c
  refine hstep.trans (le_of_eq ?_)
  have hsplit := tsum_add_three_four (V := V)
    (fun a b c w => law π (conn 0 w ∩ conn a w) * (tau π w b * tau π w c))
    (fun a b c w => law π (conn 0 w ∩ conn b w) * (tau π w a * tau π w c))
    (fun a b c w => law π (conn 0 w ∩ conn c w) * (tau π w a * tau π w b))
  rw [hsplit, tsum_starTerm_factor π hinv]
  have h2 : (∑' a, ∑' b, ∑' c, ∑' w,
      law π (conn 0 w ∩ conn b w) * (tau π w a * tau π w c))
      = (∑' x, tau π 0 x) ^ 2 * (∑' x, ∑' w, law π (conn 0 w ∩ conn x w)) := by
    rw [ENNReal.tsum_comm (f := fun a b => ∑' c, ∑' w,
      law π (conn 0 w ∩ conn b w) * (tau π w a * tau π w c))]
    exact tsum_starTerm_factor π hinv
  have h3 : (∑' a, ∑' b, ∑' c, ∑' w,
      law π (conn 0 w ∩ conn c w) * (tau π w a * tau π w b))
      = (∑' x, tau π 0 x) ^ 2 * (∑' x, ∑' w, law π (conn 0 w ∩ conn x w)) := by
    rw [tsum_swap_fst_third (G := fun a b c w =>
      law π (conn 0 w ∩ conn c w) * (tau π w a * tau π w b))]
    exact tsum_starTerm_factor π hinv
  rw [h2, h3]
  ring

end PercLib.CriticalLRP.TreeExpansion
