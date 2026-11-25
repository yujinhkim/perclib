/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.
New proofs, written for package Q-71 (issue 378), on the D-2 interface and the rooted-tree
conventions of `PercLib.Models.Tree`. Source of the model: G. Grimmett, *Percolation*
(2nd ed., 1999), the rooted tree example. No source text or code is copied.
-/
module

public import PercLib.Models.TreeRecursion
public import PercLib.Percolation.Bond.Susceptibility
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Data.Fintype.BigOperators

/-!
# Bond percolation on the rooted binary tree: exact formulas

Vertices are words `List (Fin k)`, the root is `[]`, the tree is
`SimpleGraph.fromRel fun u w => ∃ b, w = b :: u`, and the profile is `p` on tree edges and
`0` on other pairs (any value on the diagonal).

* `tau_nil_eq` (any `k`): `τ([], w) = p^|w|`.
* `chi_nil_eq` (any `k`): `χ([]) = (1 - k p)⁻¹` in `ℝ≥0∞`; in particular for the binary
  tree `χ = (1 - 2p)⁻¹` when `p < 1/2` (`binaryTree_chi_of_lt`) and `χ = ⊤` when
  `p ≥ 1/2` (`binaryTree_chi_of_le`).
* `binaryTree_theta_of_le` and `binaryTree_theta_of_lt`: `θ = 0` for `p ≤ 1/2` and
  `θ = 1 - ((1 - p)/p)^2` for `1/2 < p ≤ 1`, from the depth recursion
  `r_{n+1} = 1 - (1 - p r_n)^2` and its largest fixed point.
* `binaryTree_theta_pos_iff` and `binaryTree_chi_lt_top_iff`: the root critical probability
  is `1/2` for both `θ` and `χ`.

This file adds no definition.
-/

@[expose] public section
noncomputable section

open MeasureTheory Set Filter PercLib.Probability PercLib.Percolation.Bond
open scoped ENNReal

namespace PercLib.Models

variable {k : ℕ}

private theorem coe_toNNReal_eq_ofReal (p : unitInterval) :
    (unitInterval.toNNReal p : ℝ≥0∞) = ENNReal.ofReal (p : ℝ) := by
  rw [ENNReal.ofReal_eq_coe_nnreal p.2.1]; rfl

/-! ### Two-point function and susceptibility -/

/-- **The two-point function of the root.** `τ([], w) = p^|w|`. -/
theorem tau_nil_eq (p : unitInterval) (q : Sym2 (List (Fin k)) → unitInterval)
    (hq : ∀ e, ¬ e.IsDiag → q e =
      if e ∈ (SimpleGraph.fromRel fun u w : List (Fin k) => ∃ b, w = b :: u).edgeSet then p
        else 0)
    (w : List (Fin k)) :
    tau q [] w = (unitInterval.toNNReal p : ℝ≥0∞) ^ w.length := by
  classical
  set G := SimpleGraph.fromRel fun u w : List (Fin k) => ∃ b, w = b :: u
  set q₀ : Sym2 (List (Fin k)) → unitInterval := fun e => if e ∈ G.edgeSet then p else 0
  have hdiag : law q (conn [] w) = law q₀ (conn [] w) := by
    refine law_event_eq_of_offDiagonal q q₀ (fun e he => hq e he) (measurableSet_conn _ _)
      fun ω ω' h => ?_
    show (openGraph ω).Reachable [] w ↔ (openGraph ω').Reachable [] w
    rw [← openGraph_sdiff_diagSet ω, h, openGraph_sdiff_diagSet]
  change law q (conn [] w) = _
  rw [hdiag]
  have hsupp : ∀ᵐ ω ∂law q₀, ω ⊆ G.edgeSet :=
    ae_config_subset_host G q₀ fun e he => by simp [q₀, he]
  set F : Finset (Sym2 (List (Fin k))) :=
    (Finset.range w.length).image fun m => s(w.drop (m + 1), w.drop m)
  have hev : law q₀ (conn [] w) = law q₀ {ω : Config (List (Fin k)) | (F : Set _) ⊆ ω} := by
    refine measure_congr ?_
    filter_upwards [hsupp] with ω hω
    refine propext ?_
    show (openGraph ω).Reachable [] w ↔ (F : Set _) ⊆ ω
    rw [reachable_nil_iff_of_subset hω]
    constructor
    · intro h e he
      obtain ⟨m, hm, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 he)
      exact h m (Finset.mem_range.1 hm)
    · intro h m hm
      exact h (Finset.mem_coe.2 (Finset.mem_image.2 ⟨m, Finset.mem_range.2 hm, rfl⟩))
  rw [hev]
  change prodBernoulli q₀ _ = _
  rw [prodBernoulli_subset]
  have hinj : Set.InjOn (fun m => s(w.drop (m + 1), w.drop m))
      (Finset.range w.length : Set ℕ) := by
    intro a ha b hb hab
    rcases Sym2.eq_iff.1 hab with ⟨h1, -⟩ | ⟨h1, h2⟩
    · have := congrArg List.length h1
      simp only [List.length_drop] at this
      simp only [Finset.coe_range, mem_Iio] at ha hb
      omega
    · have e1 := congrArg List.length h1
      have e2 := congrArg List.length h2
      simp only [List.length_drop] at e1 e2
      simp only [Finset.coe_range, mem_Iio] at ha hb
      omega
  rw [Finset.prod_image hinj]
  have hval : ∀ m ∈ Finset.range w.length,
      (unitInterval.toNNReal (q₀ s(w.drop (m + 1), w.drop m)) : ℝ≥0∞) =
        (unitInterval.toNNReal p : ℝ≥0∞) := by
    intro m hm
    have hlen : m < w.length := Finset.mem_range.1 hm
    have hcons : w.drop m = (w.get ⟨m, hlen⟩) :: w.drop (m + 1) :=
      List.drop_eq_getElem_cons hlen
    have hedge : s(w.drop (m + 1), w.drop m) ∈ G.edgeSet := by
      rw [SimpleGraph.mem_edgeSet, kTree_adj_iff]
      exact Or.inl ⟨_, hcons⟩
    simp only [q₀, hedge, ite_true]
  rw [Finset.prod_congr rfl hval, Finset.prod_const, Finset.card_range]

/-- Summing a function of the length over all words. -/
theorem tsum_pow_length (r : ℝ≥0∞) :
    ∑' w : List (Fin k), r ^ w.length = ∑' n : ℕ, ((k : ℝ≥0∞) * r) ^ n := by
  rw [← (Equiv.sigmaFiberEquiv (List.length : List (Fin k) → ℕ)).tsum_eq,
    ENNReal.tsum_sigma']
  refine tsum_congr fun n => ?_
  have h1 : ∀ b : {w : List (Fin k) // w.length = n},
      r ^ ((Equiv.sigmaFiberEquiv (List.length : List (Fin k) → ℕ)) ⟨n, b⟩).length =
        r ^ n := fun b => by
    simp [Equiv.sigmaFiberEquiv, b.2]
  rw [tsum_congr h1, ENNReal.tsum_const, mul_pow]
  have hcard : ENat.card {w : List (Fin k) // w.length = n} = ((k ^ n : ℕ) : ℕ∞) := by
    change ENat.card (List.Vector (Fin k) n) = _
    rw [ENat.card_eq_coe_fintype_card, card_vector, Fintype.card_fin]
  rw [hcard]
  simp

/-- **The susceptibility of the root of the `k`-ary tree.** `χ([]) = (1 - k p)⁻¹` in
`ℝ≥0∞`; this is `⊤` when `k p ≥ 1`. -/
theorem chi_nil_eq (p : unitInterval) (q : Sym2 (List (Fin k)) → unitInterval)
    (hq : ∀ e, ¬ e.IsDiag → q e =
      if e ∈ (SimpleGraph.fromRel fun u w : List (Fin k) => ∃ b, w = b :: u).edgeSet then p
        else 0) :
    chi q [] = (1 - (k : ℝ≥0∞) * (unitInterval.toNNReal p : ℝ≥0∞))⁻¹ := by
  rw [chi_eq_tsum_tau]
  simp_rw [tau_nil_eq p q hq]
  rw [tsum_pow_length, ENNReal.tsum_geometric]

/-- **Binary tree, subcritical susceptibility.** `χ = (1 - 2p)⁻¹` for `p < 1/2`. -/
theorem binaryTree_chi_of_lt (p : unitInterval) (q : Sym2 (List (Fin 2)) → unitInterval)
    (hq : ∀ e, ¬ e.IsDiag → q e =
      if e ∈ (SimpleGraph.fromRel fun u w : List (Fin 2) => ∃ b, w = b :: u).edgeSet then p
        else 0)
    (hp : (p : ℝ) < 1 / 2) :
    chi q [] = ENNReal.ofReal (1 - 2 * (p : ℝ))⁻¹ := by
  rw [chi_nil_eq p q hq, coe_toNNReal_eq_ofReal]
  have h2 : ((2 : ℕ) : ℝ≥0∞) = ENNReal.ofReal 2 := by simp
  rw [h2, ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_one,
    ← ENNReal.ofReal_sub _ (by have := p.2.1; positivity),
    ENNReal.ofReal_inv_of_pos (by linarith)]

/-- **Binary tree, susceptibility at and above one half.** `χ = ⊤` for `p ≥ 1/2`. -/
theorem binaryTree_chi_of_le (p : unitInterval) (q : Sym2 (List (Fin 2)) → unitInterval)
    (hq : ∀ e, ¬ e.IsDiag → q e =
      if e ∈ (SimpleGraph.fromRel fun u w : List (Fin 2) => ∃ b, w = b :: u).edgeSet then p
        else 0)
    (hp : 1 / 2 ≤ (p : ℝ)) :
    chi q [] = ⊤ := by
  rw [chi_nil_eq p q hq, coe_toNNReal_eq_ofReal, ENNReal.inv_eq_top]
  refine tsub_eq_zero_of_le ?_
  have h2 : ((2 : ℕ) : ℝ≥0∞) = ENNReal.ofReal 2 := by simp
  rw [h2, ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_one]
  exact ENNReal.ofReal_le_ofReal (by linarith)

/-! ### The percolation probability -/

/-- **Binary tree, no percolation at or below one half.** `θ = 0` for `p ≤ 1/2`. -/
theorem binaryTree_theta_of_le (p : unitInterval) (q : Sym2 (List (Fin 2)) → unitInterval)
    (hq : ∀ e, ¬ e.IsDiag → q e =
      if e ∈ (SimpleGraph.fromRel fun u w : List (Fin 2) => ∃ b, w = b :: u).edgeSet then p
        else 0)
    (hp : (p : ℝ) ≤ 1 / 2) :
    law q {ω | (cluster ω []).Infinite} = 0 := by
  by_contra h
  rcases (law_cluster_nil_infinite_pos_iff (k := 2) (by norm_num) p q hq).1
    (pos_iff_ne_zero.2 h) with h1 | h1
  · push_cast at h1; linarith
  · have := congrArg Subtype.val h1
    change (p : ℝ) = 1 at this
    linarith

/-- **Binary tree, supercritical percolation probability.**
`θ = 1 - ((1 - p)/p)^2` for `1/2 < p ≤ 1`: the limit of the depth recursion
`r_{n+1} = 1 - (1 - p r_n)^2`, `r_0 = 1`, is its largest fixed point `(2p - 1)/p^2`. -/
theorem binaryTree_theta_of_lt (p : unitInterval) (q : Sym2 (List (Fin 2)) → unitInterval)
    (hq : ∀ e, ¬ e.IsDiag → q e =
      if e ∈ (SimpleGraph.fromRel fun u w : List (Fin 2) => ∃ b, w = b :: u).edgeSet then p
        else 0)
    (hp : 1 / 2 < (p : ℝ)) :
    law q {ω | (cluster ω []).Infinite} = ENNReal.ofReal (1 - ((1 - (p : ℝ)) / p) ^ 2) := by
  classical
  set G := SimpleGraph.fromRel fun u w : List (Fin 2) => ∃ b, w = b :: u
  set q₀ : Sym2 (List (Fin 2)) → unitInterval := fun e => if e ∈ G.edgeSet then p else 0
  set B : ℕ → Set (Config (List (Fin 2))) := fun n =>
    {ω | ∃ w : List (Fin 2), w.length = n ∧ ∀ m < n, s(w.drop (m + 1), w.drop m) ∈ ω}
  have hdiag : law q {ω | (cluster ω []).Infinite} = law q₀ {ω | (cluster ω []).Infinite} := by
    refine law_event_eq_of_offDiagonal q q₀ (fun e he => hq e he)
      (measurableSet_cluster_infinite _) fun ω ω' h => ?_
    simp only [mem_ofPred_eq, cluster]
    rw [← openGraph_sdiff_diagSet ω, h, openGraph_sdiff_diagSet]
  have hsupp : ∀ᵐ ω ∂law q₀, ω ⊆ G.edgeSet :=
    ae_config_subset_host G q₀ fun e he => by simp [q₀, he]
  have hinf : law q₀ {ω | (cluster ω []).Infinite} = law q₀ (⋂ n, B n) := by
    refine measure_congr ?_
    filter_upwards [hsupp] with ω hω
    refine propext ?_
    rw [mem_iInter]
    exact cluster_nil_infinite_iff hω
  have hanti : Antitone B := by
    refine antitone_nat_of_succ_le fun n ω hω => ?_
    obtain ⟨w, hw, h⟩ := hω
    refine ⟨w.drop 1, by simp [hw], fun m hm => ?_⟩
    have := h (m + 1) (by omega)
    simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm] using this
  have hB0 : B 0 = univ :=
    eq_univ_of_forall fun ω => ⟨[], rfl, fun m hm => absurd hm (by omega)⟩
  have hθ : law q₀ (⋂ n, B n) = ⨅ n, law q₀ (B n) :=
    hanti.measure_iInter (fun n => (measurableSet_depth_open n).nullMeasurableSet)
      ⟨0, measure_ne_top _ _⟩
  set f : ℕ → ℝ := fun n => (law q₀ (B n)).toReal
  have hfx : ∀ n, law q₀ (B n) = ENNReal.ofReal (f n) := fun n =>
    (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
  have hf0 : ∀ n, 0 ≤ f n := fun n => ENNReal.toReal_nonneg
  have hf1 : ∀ n, f n ≤ 1 := fun n => by
    have := ENNReal.toReal_mono ENNReal.one_ne_top (prob_le_one (μ := law q₀) (s := B n))
    simpa using this
  have hpr : ((unitInterval.toNNReal p : ℝ≥0∞)).toReal = (p : ℝ) := rfl
  have hp0 : (0 : ℝ) ≤ p := p.2.1
  have hp1 : (p : ℝ) ≤ 1 := p.2.2
  have hfrec : ∀ n, f (n + 1) = 1 - (1 - p * f n) ^ 2 := by
    intro n
    have h := law_depth_succ (k := 2) p n
    change law q₀ (B (n + 1)) = 1 - (1 - _ * law q₀ (B n)) ^ 2 at h
    have hx : (unitInterval.toNNReal p : ℝ≥0∞) * law q₀ (B n) ≤ 1 :=
      mul_le_one' (by exact_mod_cast unitInterval.le_one p) prob_le_one
    have hy : (1 - (unitInterval.toNNReal p : ℝ≥0∞) * law q₀ (B n)) ^ 2 ≤ 1 :=
      pow_le_one₀ zero_le tsub_le_self
    change (law q₀ (B (n + 1))).toReal = _
    rw [h, ENNReal.toReal_sub_of_le hy ENNReal.one_ne_top, ENNReal.toReal_pow,
      ENNReal.toReal_sub_of_le hx ENNReal.one_ne_top, ENNReal.toReal_mul, hpr]
    simp [f]
  -- the limit
  have hfanti : Antitone f := fun m n hmn =>
    ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (hanti hmn))
  have hbdd : BddBelow (Set.range f) := ⟨0, fun _ ⟨n, hn⟩ => hn ▸ hf0 n⟩
  have htend : Tendsto f atTop (nhds (⨅ n, f n)) := tendsto_atTop_ciInf hfanti hbdd
  set L := ⨅ n, f n with hLdef
  have hgc : Continuous fun s : ℝ => 1 - (1 - p * s) ^ 2 := by fun_prop
  have h1 : Tendsto (fun n => f (n + 1)) atTop (nhds (1 - (1 - p * L) ^ 2)) := by
    simp_rw [hfrec]
    exact (hgc.tendsto L).comp htend
  have h2 : Tendsto (fun n => f (n + 1)) atTop (nhds L) :=
    (tendsto_add_atTop_iff_nat 1).2 htend
  have hfix : 1 - (1 - p * L) ^ 2 = L := tendsto_nhds_unique h1 h2
  -- the largest fixed point `c = (2p - 1)/p^2` is below every `f n`
  have hppos : (0 : ℝ) < p := by linarith
  set c : ℝ := (2 * p - 1) / p ^ 2 with hc
  have hc0 : 0 < c := div_pos (by linarith) (by positivity)
  have hc1 : c ≤ 1 := by
    rw [hc, div_le_one (by positivity)]
    nlinarith [sq_nonneg ((p : ℝ) - 1)]
  have hcfix : 1 - (1 - p * c) ^ 2 = c := by
    rw [hc]; field_simp; ring
  have hfc : ∀ n, c ≤ f n := by
    intro n
    induction n with
    | zero =>
      have : f 0 = 1 := by simp [f, hB0]
      rw [this]; exact hc1
    | succ n ih =>
      rw [hfrec]
      calc c = 1 - (1 - p * c) ^ 2 := hcfix.symm
        _ ≤ 1 - (1 - p * f n) ^ 2 := recursion_mono hp0 hp1 2 (hf1 n) ih
  have hcL : c ≤ L := le_ciInf hfc
  -- the fixed points are `0` and `c`
  have hLc : L = c := by
    have hquad : L * (p ^ 2 * L - (2 * p - 1)) = 0 := by nlinarith [hfix]
    rcases mul_eq_zero.1 hquad with h | h
    · linarith
    · rw [hc]; field_simp; linarith
  -- assemble
  have hlim : (⨅ n, law q₀ (B n)) = ENNReal.ofReal L := by
    have ht1 : Tendsto (fun n => law q₀ (B n)) atTop (nhds (⨅ n, law q₀ (B n))) :=
      tendsto_atTop_iInf fun m n hmn => measure_mono (hanti hmn)
    have ht2 : Tendsto (fun n => law q₀ (B n)) atTop (nhds (ENNReal.ofReal L)) := by
      simp_rw [hfx]; exact ENNReal.tendsto_ofReal htend
    exact tendsto_nhds_unique ht1 ht2
  rw [hdiag, hinf, hθ, hlim, hLc, hc]
  congr 1
  field_simp
  ring

/-! ### The root critical probability is one half -/

/-- **The root critical probability of the binary tree is `1/2`** for the percolation
probability: `θ(p) > 0` exactly when `p > 1/2`. -/
theorem binaryTree_theta_pos_iff (p : unitInterval) (q : Sym2 (List (Fin 2)) → unitInterval)
    (hq : ∀ e, ¬ e.IsDiag → q e =
      if e ∈ (SimpleGraph.fromRel fun u w : List (Fin 2) => ∃ b, w = b :: u).edgeSet then p
        else 0) :
    0 < law q {ω | (cluster ω []).Infinite} ↔ 1 / 2 < (p : ℝ) := by
  rw [law_cluster_nil_infinite_pos_iff (k := 2) (by norm_num) p q hq]
  have hp1 : (p : ℝ) ≤ 1 := p.2.2
  constructor
  · rintro (h | h)
    · push_cast at h; linarith
    · have := congrArg Subtype.val h
      change (p : ℝ) = 1 at this
      linarith
  · intro h
    left; push_cast; linarith

/-- **The root critical probability of the binary tree is `1/2`** for the susceptibility:
`χ(p) < ∞` exactly when `p < 1/2`. -/
theorem binaryTree_chi_lt_top_iff (p : unitInterval) (q : Sym2 (List (Fin 2)) → unitInterval)
    (hq : ∀ e, ¬ e.IsDiag → q e =
      if e ∈ (SimpleGraph.fromRel fun u w : List (Fin 2) => ∃ b, w = b :: u).edgeSet then p
        else 0) :
    chi q [] < ⊤ ↔ (p : ℝ) < 1 / 2 := by
  constructor
  · intro h
    by_contra hp
    rw [binaryTree_chi_of_le p q hq (not_lt.1 hp)] at h
    exact lt_irrefl _ h
  · intro hp
    rw [binaryTree_chi_of_lt p q hq hp]
    exact ENNReal.ofReal_lt_top

/-! ### Non-vacuity (D-5): `p = 0`, `p = 1/2`, `p = 1` -/

example : chi (fun e : Sym2 (List (Fin 2)) =>
      if e ∈ (SimpleGraph.fromRel fun u w : List (Fin 2) => ∃ b, w = b :: u).edgeSet then
        (0 : unitInterval) else 0) [] = 1 ∧
    law (fun e : Sym2 (List (Fin 2)) =>
      if e ∈ (SimpleGraph.fromRel fun u w : List (Fin 2) => ∃ b, w = b :: u).edgeSet then
        (0 : unitInterval) else 0) {ω | (cluster ω []).Infinite} = 0 := by
  refine ⟨?_, binaryTree_theta_of_le 0 _ (fun _ _ => rfl) (by norm_num)⟩
  rw [binaryTree_chi_of_lt 0 _ (fun _ _ => rfl) (by norm_num)]
  norm_num

example : chi (fun e : Sym2 (List (Fin 2)) =>
      if e ∈ (SimpleGraph.fromRel fun u w : List (Fin 2) => ∃ b, w = b :: u).edgeSet then
        (⟨1 / 2, by norm_num, by norm_num⟩ : unitInterval) else 0) [] = ⊤ ∧
    law (fun e : Sym2 (List (Fin 2)) =>
      if e ∈ (SimpleGraph.fromRel fun u w : List (Fin 2) => ∃ b, w = b :: u).edgeSet then
        (⟨1 / 2, by norm_num, by norm_num⟩ : unitInterval) else 0)
      {ω | (cluster ω []).Infinite} = 0 :=
  ⟨binaryTree_chi_of_le _ _ (fun _ _ => rfl) le_rfl,
    binaryTree_theta_of_le _ _ (fun _ _ => rfl) le_rfl⟩

example : chi (fun e : Sym2 (List (Fin 2)) =>
      if e ∈ (SimpleGraph.fromRel fun u w : List (Fin 2) => ∃ b, w = b :: u).edgeSet then
        (1 : unitInterval) else 0) [] = ⊤ ∧
    law (fun e : Sym2 (List (Fin 2)) =>
      if e ∈ (SimpleGraph.fromRel fun u w : List (Fin 2) => ∃ b, w = b :: u).edgeSet then
        (1 : unitInterval) else 0) {ω | (cluster ω []).Infinite} = 1 := by
  refine ⟨binaryTree_chi_of_le _ _ (fun _ _ => rfl) (by norm_num), ?_⟩
  rw [binaryTree_theta_of_lt 1 _ (fun _ _ => rfl) (by norm_num)]
  norm_num

end PercLib.Models
