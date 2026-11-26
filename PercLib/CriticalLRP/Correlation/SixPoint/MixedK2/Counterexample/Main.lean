/-
Coordinator-integrated from the independently rebuilt `smwxb4a1l/m3` Line6 artifact
at production base `8d1c9eb3738a26cc63afc07f525ba4af357bd905`.
-/
/-
The two-hub `hpoint` premise fails on the six-vertex line.

Ultramath swarm `smwxb4a1l`, member `m3`, direction `HUB-LINK-COUNTEREXAMPLE`.

The production premise `hpoint` of
`PercLib.CriticalLRP.TreeExpansion.HubK2.fifth_moment_mixed_k2_le_of_hubBound` asks, for a
profile `π`, all five-point tuples and a family of `105` slot labellings,
`law π (⋂ conn 0 ·) ≤ ∑' s, slotK2 π (pat s) 0 (five leaves)`.

This file refutes that premise for the profile `lineProfile theta` on `Fin 6` that opens only
the five consecutive pairs `0—1—2—3—4—5`, each with probability `1/64`, and for the tuple
`(1,2,3,4,5)`: the left side is `eps ^ 5`, while the right side is at most
`105 * (36 * eps ^ 7) < eps ^ 5`.
-/
module

public import PercLib.CriticalLRP.Correlation.SixPoint.MixedK2.Counterexample.Arith

/-!
# Failure of the two-hub pointwise bound
-/

@[expose] public section

namespace PercLib.CriticalLRP.Counterexample.Line6

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators
open PercLib.Percolation.Bond
open PercLib.Probability
open PercLib.CriticalLRP.TreeExpansion.FivePoint
open PercLib.CriticalLRP.TreeExpansion.HubK2

/-! ## Elementary facts about `eps` -/

theorem eps_eq : eps = ((1 / 64 : ℝ≥0) : ℝ≥0∞) := rfl

theorem eps_pos : 0 < eps := by
  rw [eps_eq, ← ENNReal.coe_zero, ENNReal.coe_lt_coe]
  norm_num

theorem eps_le_one : eps ≤ 1 := by
  rw [eps_eq, ← ENNReal.coe_one, ENNReal.coe_le_coe]
  exact NNReal.coe_le_coe.mp (by push_cast; norm_num)

theorem eps_pow_le_eps_pow {m n : ℕ} (h : m ≤ n) : eps ^ n ≤ eps ^ m := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [pow_add]
  calc eps ^ m * eps ^ k ≤ eps ^ m * 1 := by
        gcongr
        exact pow_le_one₀ eps_pos.le eps_le_one
    _ = eps ^ m := mul_one _

theorem le_eps_pow_max {x : ℝ≥0∞} {A B : ℕ} (hA : x ≤ eps ^ A) (hB : x ≤ eps ^ B) :
    x ≤ eps ^ max A B := by
  rcases le_total A B with h | h
  · rw [max_eq_right h]; exact hB
  · rw [max_eq_left h]; exact hA

/-! ## Two-point functions -/

/-- On the line support, a connection is exactly the set of spanned line edges being open. -/
theorem seg_subset_iff (x y : Fin 6) (ω : Set (Sym2 (Fin 6))) :
    ((seg x y : Set (Sym2 (Fin 6))) ⊆ ω) ↔
      ∀ (i : ℕ) (hi : i < 5), min x.val y.val ≤ i → i < max x.val y.val → peAt i hi ∈ ω := by
  constructor
  · intro h i hi h1 h2
    exact h (mem_seg hi |>.mpr ⟨h1, h2⟩)
  · intro h e he
    obtain ⟨i, hi, rfl⟩ := mem_lineEdges.mp (seg_subset_lineEdges x y he)
    obtain ⟨h1, h2⟩ := (mem_seg hi).mp he
    exact h i hi h1 h2

/-- **Exact two-point function on the line.** -/
theorem tau_line (θ : unitInterval) (x y : Fin 6) :
    tau (lineProfile θ) x y = (unitInterval.toNNReal θ : ℝ≥0∞) ^ pdist x y := by
  have hcongr : law (lineProfile θ) (conn x y)
      = law (lineProfile θ) {ω : Config (Fin 6) | (seg x y : Set (Sym2 (Fin 6))) ⊆ ω} :=
    law_congr_of_lineSupport fun ω hω => by
      change (openGraph ω).Reachable x y ↔ ((seg x y : Set (Sym2 (Fin 6))) ⊆ ω)
      exact (reach_iff_seg hω x y).trans (seg_subset_iff x y ω).symm
  rw [tau, hcongr, law_subset_lineEdges θ (seg x y) (seg_subset_lineEdges x y), seg_card]

/-- The two-point function at `θ = 1/64`. -/
theorem tau_line_theta (x y : Fin 6) :
    tau (lineProfile theta) x y = eps ^ pdist x y := tau_line theta x y

/-- A joint connection is at most the two-point function to either leaf. -/
theorem jointP_le_eps (a b c : Fin 6) :
    jointP (lineProfile theta) a b c ≤ eps ^ pdist a c := by
  have hmono : law (lineProfile theta) (conn a c ∩ conn b c)
      ≤ law (lineProfile theta) (conn a c) := measure_mono Set.inter_subset_left
  rw [jointP]
  exact hmono.trans_eq (tau_line_theta a c)

/-- The joint connection is symmetric in its two leaves. -/
theorem jointP_comm (a b c : Fin 6) :
    jointP (lineProfile theta) a b c = jointP (lineProfile theta) b a c := by
  rw [jointP, jointP, Set.inter_comm]

/-- The joint connection is also at most the two-point function to the second leaf. -/
theorem jointP_le_eps' (a b c : Fin 6) :
    jointP (lineProfile theta) a b c ≤ eps ^ pdist b c := by
  rw [jointP_comm]
  exact jointP_le_eps b a c

/-! ## The slot diagram -/

/-- The number of line edges. -/
theorem lineEdges_card : lineEdges.card = 5 := by
  rw [lineEdges, Finset.card_image_of_injOn]
  · rw [Finset.card_attach, Finset.card_range]
  · intro p _ q _ hpq
    have hp5 : p.val < 5 := by have := p.prop; simp only [Finset.mem_range] at this; omega
    have hq5 : q.val < 5 := by have := q.prop; simp only [Finset.mem_range] at this; omega
    exact Subtype.ext (peAt_inj hp5 hq5 hpq)

/-- Every leaf of the tuple `1,2,3,4,5` is connected to the root when all line edges are
open. -/
theorem reachable_of_line_open {ω : Set (Sym2 (Fin 6))}
    (h : (lineEdges : Set (Sym2 (Fin 6))) ⊆ ω) (x : Fin 6) :
    (openGraph ω).Reachable 0 x := by
  refine reach_of_seg ?_
  intro i hi h1 h2
  exact h (seg_subset_lineEdges 0 x (mem_seg hi |>.mpr ⟨h1, h2⟩))

/-- If `0` is connected to every leaf, then every line edge is open. -/
theorem lineEdges_subset_of_five_reachable {ω : Set (Sym2 (Fin 6))}
    (hω : ω ⊆ (lineEdges : Set (Sym2 (Fin 6))))
    (h : (openGraph ω).Reachable 0 (leaves 0) ∧ (openGraph ω).Reachable 0 (leaves 1) ∧
      (openGraph ω).Reachable 0 (leaves 2) ∧ (openGraph ω).Reachable 0 (leaves 3) ∧
      (openGraph ω).Reachable 0 (leaves 4)) :
    (lineEdges : Set (Sym2 (Fin 6))) ⊆ ω := by
  intro e he
  obtain ⟨i, hi, rfl⟩ := mem_lineEdges.mp he
  have key : ∀ (k : Fin 5) (i : ℕ) (hi : i < 5), (leaves k).val = i + 1 →
      peAt i hi ∈ ω := by
    intro k i hi hk
    have := reach_forward hω (show (openGraph ω).Reachable 0 (leaves k) from by
      rcases k with ⟨n, hn⟩
      interval_cases n
      · exact h.1
      · exact h.2.1
      · exact h.2.2.1
      · exact h.2.2.2.1
      · exact h.2.2.2.2) i hi (by omega) (by omega)
    exact this
  have hrange : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
  rcases hrange with rfl | rfl | rfl | rfl | rfl
  · exact key 0 0 hi (by decide)
  · exact key 1 1 hi (by decide)
  · exact key 2 2 hi (by decide)
  · exact key 3 3 hi (by decide)
  · exact key 4 4 hi (by decide)

/-- **The left side of the premise at the tuple `(1,2,3,4,5)`.** -/
theorem law_five :
    law (lineProfile theta) (conn 0 (leaves 0) ∩ conn 0 (leaves 1) ∩ conn 0 (leaves 2) ∩
      conn 0 (leaves 3) ∩ conn 0 (leaves 4)) = eps ^ 5 := by
  have hcongr : law (lineProfile theta) (conn 0 (leaves 0) ∩ conn 0 (leaves 1) ∩
        conn 0 (leaves 2) ∩ conn 0 (leaves 3) ∩ conn 0 (leaves 4))
      = law (lineProfile theta) {ω : Config (Fin 6) |
          (lineEdges : Set (Sym2 (Fin 6))) ⊆ ω} :=
    law_congr_of_lineSupport fun ω hω => by
      constructor
      · intro h
        exact lineEdges_subset_of_five_reachable hω ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2,
          h.2⟩
      · intro h
        exact ⟨⟨⟨⟨reachable_of_line_open h (leaves 0), reachable_of_line_open h (leaves 1)⟩,
          reachable_of_line_open h (leaves 2)⟩, reachable_of_line_open h (leaves 3)⟩,
          reachable_of_line_open h (leaves 4)⟩
  rw [hcongr, law_subset_lineEdges theta lineEdges (subset_refl _), lineEdges_card]
  rfl

/-- **Every slot term is at most `eps ^ 7`.** -/
theorem hubStar_bound (σ : Equiv.Perm (Fin 5)) (c1 c2 : Fin 6) :
    hubStar (lineProfile theta) 0 (leaves (σ 0)) (leaves (σ 1)) (leaves (σ 2))
      (leaves (σ 3)) (leaves (σ 4)) c1 c2 ≤ eps ^ 7 := by
  have h1 : jointP (lineProfile theta) (leaves (σ 0)) (leaves (σ 1)) c1
      ≤ eps ^ max (pdist (leaves (σ 0)) c1) (pdist (leaves (σ 1)) c1) :=
    le_eps_pow_max (A := pdist (leaves (σ 0)) c1) (B := pdist (leaves (σ 1)) c1)
      (jointP_le_eps (leaves (σ 0)) (leaves (σ 1)) c1)
      (jointP_le_eps' (leaves (σ 0)) (leaves (σ 1)) c1)
  have h2 : tau (lineProfile theta) 0 c1 = eps ^ c1.val := by
    rw [tau_line_theta]; rfl
  have h3 : jointP (lineProfile theta) (leaves (σ 2)) (leaves (σ 3)) c2
      ≤ eps ^ max (pdist (leaves (σ 2)) c2) (pdist (leaves (σ 3)) c2) :=
    le_eps_pow_max (A := pdist (leaves (σ 2)) c2) (B := pdist (leaves (σ 3)) c2)
      (jointP_le_eps (leaves (σ 2)) (leaves (σ 3)) c2)
      (jointP_le_eps' (leaves (σ 2)) (leaves (σ 3)) c2)
  have h4 : tau (lineProfile theta) 0 c2 = eps ^ c2.val := by
    rw [tau_line_theta]; rfl
  have h5 : tau (lineProfile theta) (leaves (σ 4)) c1 = eps ^ pdist (leaves (σ 4)) c1 :=
    tau_line_theta _ _
  rw [hubStar, h2, h4, h5]
  calc (jointP (lineProfile theta) (leaves (σ 0)) (leaves (σ 1)) c1 * eps ^ c1.val) *
        (jointP (lineProfile theta) (leaves (σ 2)) (leaves (σ 3)) c2 * eps ^ c2.val) *
        eps ^ pdist (leaves (σ 4)) c1
      ≤ (eps ^ max (pdist (leaves (σ 0)) c1) (pdist (leaves (σ 1)) c1) * eps ^ c1.val) *
        (eps ^ max (pdist (leaves (σ 2)) c2) (pdist (leaves (σ 3)) c2) * eps ^ c2.val) *
        eps ^ pdist (leaves (σ 4)) c1 := by gcongr
    _ = eps ^ (max (pdist (leaves (σ 0)) c1) (pdist (leaves (σ 1)) c1) + c1.val
        + max (pdist (leaves (σ 2)) c2) (pdist (leaves (σ 3)) c2) + c2.val
        + pdist (leaves (σ 4)) c1) := by
        rw [← pow_add, ← pow_add, ← pow_add, ← pow_add]
        congr 1
        omega
    _ ≤ eps ^ 7 := by
        apply eps_pow_le_eps_pow
        have := exp_eight σ c1 c2
        omega

/-- **The slot diagram is at most `36 eps ^ 7`.** -/
theorem slotK2_bound (σ : Equiv.Perm (Fin 5)) :
    slotK2 (lineProfile theta) σ 0 leaves ≤ 36 * eps ^ 7 := by
  simp only [slotK2, tsum_fintype]
  have hinner : ∀ c1 : Fin 6,
      (∑ c2 : Fin 6, hubStar (lineProfile theta) 0 (leaves (σ 0)) (leaves (σ 1))
        (leaves (σ 2)) (leaves (σ 3)) (leaves (σ 4)) c1 c2) ≤ 6 * eps ^ 7 := by
    intro c1
    calc (∑ c2 : Fin 6, hubStar (lineProfile theta) 0 (leaves (σ 0)) (leaves (σ 1))
          (leaves (σ 2)) (leaves (σ 3)) (leaves (σ 4)) c1 c2)
        ≤ ∑ _c2 : Fin 6, eps ^ 7 :=
          Finset.sum_le_sum fun c2 _ => hubStar_bound σ c1 c2
      _ = 6 * eps ^ 7 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          norm_num
  calc (∑ c1 : Fin 6, ∑ c2 : Fin 6, hubStar (lineProfile theta) 0 (leaves (σ 0))
        (leaves (σ 1)) (leaves (σ 2)) (leaves (σ 3)) (leaves (σ 4)) c1 c2)
      ≤ ∑ _c1 : Fin 6, 6 * eps ^ 7 := Finset.sum_le_sum fun c1 _ => hinner c1
    _ = 36 * eps ^ 7 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

/-- **The right side of the premise at the tuple `(1,2,3,4,5)`.** -/
theorem tsum_slotK2_bound (pat : Fin 105 → Equiv.Perm (Fin 5)) :
    (∑' s : Fin 105, slotK2 (lineProfile theta) (pat s) 0 leaves) ≤ 105 * (36 * eps ^ 7) := by
  rw [tsum_fintype]
  calc (∑ s : Fin 105, slotK2 (lineProfile theta) (pat s) 0 leaves)
      ≤ ∑ _s : Fin 105, 36 * eps ^ 7 :=
        Finset.sum_le_sum fun s _ => slotK2_bound (pat s)
    _ = 105 * (36 * eps ^ 7) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        norm_num

/-- The numerical comparison. -/
theorem numeric : 105 * (36 * eps ^ 7) < eps ^ 5 := by
  have hlt : ((105 : ℝ≥0) * (36 * (1 / 64 : ℝ≥0) ^ 7)) < (1 / 64 : ℝ≥0) ^ 5 := by norm_num
  have hcast := ENNReal.coe_lt_coe.mpr hlt
  have e1 : (((105 : ℝ≥0) * (36 * (1 / 64 : ℝ≥0) ^ 7) : ℝ≥0) : ℝ≥0∞)
      = 105 * (36 * eps ^ 7) := by
    rw [eps_eq]
    push_cast
    ring
  have e2 : (((1 / 64 : ℝ≥0) ^ 5 : ℝ≥0) : ℝ≥0∞) = eps ^ 5 := by
    rw [eps_eq, ENNReal.coe_pow]
  rwa [e1, e2] at hcast

/-- **The two-hub pointwise bound fails on the six-vertex line.**  For every family of `105`
slot labellings, the premise of the `p = 5`, `k = 2` two-hub consumer is false at the tuple
`(1,2,3,4,5)`. -/
theorem hpoint_false (pat : Fin 105 → Equiv.Perm (Fin 5)) :
    ¬ (∀ y z w q r : Fin 6,
      law (lineProfile theta) (conn 0 y ∩ conn 0 z ∩ conn 0 w ∩ conn 0 q ∩ conn 0 r) ≤
        ∑' s : Fin 105, slotK2 (lineProfile theta) (pat s) 0 ![y, z, w, q, r]) := by
  intro hpoint
  have h := hpoint (leaves 0) (leaves 1) (leaves 2) (leaves 3) (leaves 4)
  rw [law_five] at h
  have hle := tsum_slotK2_bound pat
  have hnum := numeric
  have hchain : eps ^ 5 ≤ 105 * (36 * eps ^ 7) := le_trans h hle
  exact absurd hnum (not_lt.mpr hchain)

end PercLib.CriticalLRP.Counterexample.Line6
