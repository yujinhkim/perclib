/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.
Q-86: intrinsic balls. New for this project; no upstream proof is copied, and no new
definition is introduced: the intrinsic distance is mathlib's `(openGraph ω).edist`, and
balls and spheres are written out as sets.
-/
module

public import PercLib.Percolation.Bond.Susceptibility
public import PercLib.Percolation.Bond.PathLowerBounds
public import PercLib.Percolation.Bond.Intensity.Defs
public import PercLib.Probability.Superposition
public import Mathlib.Combinatorics.SimpleGraph.Metric
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# Intrinsic balls

The intrinsic ball is `B_ω(o,r) = {y | (openGraph ω).edist o y ≤ r}` and the sphere is
`S_ω(o,r) = {y | (openGraph ω).edist o y = r}`.

* `law_edist_le_le` (PI11): for `q_t = intensityProfile J t` and `0 < α ≤ β`,
  `P_β(x ∈ B_ω(o,r)) ≤ (β/α)^r P_α(o ↔ x)`; `lintegral_ball_le` sums this to
  `E_β|B_ω(o,r)| ≤ (β/α)^r χ_o(α)`; `eventually_lintegral_ball_le` gives the linear bound
  `E_b|B_ω(o,r)| ≤ (eC/b)(r+1)` for large `r` from `χ_o(b-ε) ≤ C/ε`.
* `measure_encard_cluster_ge_le` (J1V5): under any measure on configurations, sphere and
  ball bounds `Q_r ≤ A/r`, `E|B_ω(o,r)| ≤ B r` give `P(|K_o| ≥ n) ≤ (A + 2B)/√n`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set PercLib.Probability
open scoped ENNReal NNReal

namespace PercLib.Percolation.Bond

variable {V : Type*}

/-! ### Graph distance recursion -/

/-- One-step recursion for graph distance balls. -/
theorem edist_le_succ_iff {W : Type*} (G : SimpleGraph W) (o y : W) (r : ℕ) :
    G.edist o y ≤ (r + 1 : ℕ) ↔ y = o ∨ ∃ z, G.Adj z y ∧ G.edist o z ≤ r := by
  constructor
  · intro h
    by_cases hy : y = o
    · exact Or.inl hy
    right
    have hne : G.edist y o ≠ ⊤ := by
      rw [SimpleGraph.edist_comm]
      exact ne_top_of_le_ne_top (by simp) h
    obtain ⟨p, hp⟩ := (SimpleGraph.reachable_of_edist_ne_top hne).exists_walk_length_eq_edist
    cases p with
    | nil => exact absurd rfl hy
    | @cons _ z _ hadj p' =>
      refine ⟨z, hadj.symm, ?_⟩
      rw [SimpleGraph.edist_comm]
      have h1 : G.edist z o ≤ p'.length := SimpleGraph.edist_le p'
      have h2 : ((p'.length + 1 : ℕ) : ℕ∞) ≤ (r + 1 : ℕ) := by
        rw [← SimpleGraph.Walk.length_cons hadj p', hp, SimpleGraph.edist_comm]
        exact h
      have h3' : p'.length + 1 ≤ r + 1 := by exact_mod_cast h2
      have h3 : p'.length ≤ r := by omega
      exact h1.trans (by exact_mod_cast h3)
  · rintro (rfl | ⟨z, hadj, hz⟩)
    · simp
    · calc G.edist o y ≤ G.edist o z + G.edist z y := SimpleGraph.edist_triangle
        _ ≤ r + 1 := by
          rw [SimpleGraph.edist_eq_one_iff_adj.mpr hadj]
          exact add_le_add hz le_rfl
        _ = (r + 1 : ℕ) := by push_cast; rfl

/-- Intrinsic balls are measurable events when there are countably many vertices. -/
theorem measurableSet_edist_le [Countable V] (o y : V) (r : ℕ) :
    MeasurableSet {ω : Config V | (openGraph ω).edist o y ≤ r} := by
  induction r generalizing y with
  | zero =>
    have : {ω : Config V | (openGraph ω).edist o y ≤ (0 : ℕ)} = {_ω | o = y} := by
      ext ω
      simp [SimpleGraph.edist_eq_zero_iff]
    rw [this]
    exact MeasurableSet.const _
  | succ r ih =>
    have : {ω : Config V | (openGraph ω).edist o y ≤ (r + 1 : ℕ)} =
        {_ω | y = o} ∪ ⋃ z : V, ({ω : Config V | s(z, y) ∈ ω} ∩ {_ω | z ≠ y}) ∩
          {ω | (openGraph ω).edist o z ≤ r} := by
      ext ω
      simp only [mem_ofPred_eq, edist_le_succ_iff, mem_union, mem_iUnion, mem_inter_iff,
        openGraph_adj_iff]
    rw [this]
    exact (MeasurableSet.const _).union (MeasurableSet.iUnion fun z =>
      ((measurableSet_mem _).inter (MeasurableSet.const _)).inter (ih z))

/-- The intrinsic ball volume as a sum of indicators. -/
theorem encard_ball_eq_tsum (ω : Config V) (o : V) (r : ℕ) :
    (({y | (openGraph ω).edist o y ≤ r} : Set V).encard : ℝ≥0∞) =
      ∑' y, {ω' : Config V | (openGraph ω').edist o y ≤ r}.indicator (fun _ => (1 : ℝ≥0∞)) ω := by
  classical
  rw [← ENNReal.tsum_set_one, tsum_subtype ({y | (openGraph ω).edist o y ≤ r} : Set V)
    (fun _ => (1 : ℝ≥0∞))]
  congr 1

theorem measurable_encard_ball [Countable V] (o : V) (r : ℕ) :
    Measurable fun ω : Config V =>
      (({y | (openGraph ω).edist o y ≤ r} : Set V).encard : ℝ≥0∞) := by
  have hset : Measurable fun ω : Config V => ({y | (openGraph ω).edist o y ≤ r} : Set V) :=
    Measurable.of_mem fun y => (measurableSet_edist_le o y r).mem
  exact (measurable_of_countable (fun n : ℕ∞ => (n : ℝ≥0∞))).comp
    (measurable_encard.comp hset)

/-- The expected ball volume is the sum of the ball probabilities. -/
theorem lintegral_encard_ball [Countable V] (μ : Measure (Config V)) (o : V) (r : ℕ) :
    ∫⁻ ω, (({y | (openGraph ω).edist o y ≤ r} : Set V).encard : ℝ≥0∞) ∂μ =
      ∑' y, μ {ω | (openGraph ω).edist o y ≤ r} := by
  simp_rw [encard_ball_eq_tsum]
  rw [lintegral_tsum fun y =>
    (measurable_const.indicator (measurableSet_edist_le o y r)).aemeasurable]
  exact tsum_congr fun y => lintegral_indicator_one (measurableSet_edist_le o y r)

/-- If no vertex is at distance exactly `r`, no vertex is at distance at least `r`. -/
theorem exists_edist_eq_of_le {W : Type*} (G : SimpleGraph W) (o : W) (r : ℕ) :
    ∀ m : ℕ, ∀ y, G.edist o y = m → r ≤ m → ∃ w, G.edist o w = r := by
  intro m
  induction m with
  | zero =>
    intro y hy hr
    have : r = 0 := by omega
    exact ⟨y, by rw [hy, this]⟩
  | succ m ih =>
    intro y hy hr
    rcases Nat.lt_or_ge m r with hm | hm
    · have : r = m + 1 := by omega
      exact ⟨y, by rw [hy, this]⟩
    · have hy' : G.edist o y ≤ (m + 1 : ℕ) := hy.le
      rcases (edist_le_succ_iff G o y m).mp hy' with rfl | ⟨z, hadj, hz⟩
      · rw [SimpleGraph.edist_self] at hy
        exact absurd hy.symm (by exact_mod_cast Nat.succ_ne_zero m)
      · have hlow : ((m + 1 : ℕ) : ℕ∞) ≤ G.edist o z + 1 := by
          rw [← hy]
          calc G.edist o y ≤ G.edist o z + G.edist z y := SimpleGraph.edist_triangle
            _ = G.edist o z + 1 := by rw [SimpleGraph.edist_eq_one_iff_adj.mpr hadj]
        have hzm : G.edist o z = m := by
          apply le_antisymm hz
          have hfin : G.edist o z ≠ ⊤ := ne_top_of_le_ne_top (by simp) hz
          obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp hfin
          rw [← hk] at hlow ⊢
          have : m + 1 ≤ k + 1 := by exact_mod_cast hlow
          exact_mod_cast (by omega : m ≤ k)
        exact ih z hzm hm

/-- If the sphere of radius `r` is empty, the cluster lies in the ball of radius `r`. -/
theorem cluster_subset_ball_of_sphere_empty (ω : Config V) (o : V) (r : ℕ)
    (h : ¬ ∃ y, (openGraph ω).edist o y = r) :
    cluster ω o ⊆ {y | (openGraph ω).edist o y ≤ r} := by
  intro y hy
  have hfin : (openGraph ω).edist o y ≠ ⊤ :=
    SimpleGraph.edist_ne_top_iff_reachable.mpr hy
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp hfin
  show (openGraph ω).edist o y ≤ r
  rw [← hm]
  by_contra hlt
  have hrm : r ≤ m := by
    have : ¬ (m ≤ r) := fun h' => hlt (by exact_mod_cast h')
    omega
  exact h (exists_edist_eq_of_le (openGraph ω) o r m y hm.symm hrm)

/-! ### J1V5: the square-root tail -/

private theorem sqrt_bounds (n : ℕ) (hn : 1 ≤ n) :
    ENNReal.ofReal (Real.sqrt n) ≤ ((Nat.sqrt n + 1 : ℕ) : ℝ≥0∞) ∧
      ((Nat.sqrt n + 1 : ℕ) : ℝ≥0∞) / n ≤ 2 / ENNReal.ofReal (Real.sqrt n) := by
  have hs1 : (1 : ℝ) ≤ Real.sqrt n := by
    rw [Real.one_le_sqrt]; exact_mod_cast hn
  have hspos : 0 < Real.sqrt n := by linarith
  have hr : (Nat.sqrt n : ℝ) + 1 ≤ 2 * Real.sqrt n := by
    linarith [Real.nat_sqrt_le_real_sqrt (a := n)]
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  constructor
  · rw [← ENNReal.ofReal_natCast]
    apply ENNReal.ofReal_le_ofReal
    push_cast
    exact Real.real_sqrt_le_nat_sqrt_succ
  · rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_natCast n, ← ENNReal.ofReal_ofNat 2,
      ← ENNReal.ofReal_div_of_pos hnpos, ← ENNReal.ofReal_div_of_pos hspos]
    apply ENNReal.ofReal_le_ofReal
    push_cast
    rw [div_le_div_iff₀ hnpos hspos]
    have hsq : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt hnpos.le
    nlinarith

/-- **J1V5.** Under any measure on configurations of a countable vertex type, if the
sphere probabilities satisfy `Q_r = μ(S_ω(o,r) ≠ ∅) ≤ A/r` and the ball volumes satisfy
`E|B_ω(o,r)| ≤ B r` for `r ≥ 1`, then `μ(|K_o| ≥ n) ≤ (A + 2B)/√n` for every `n ≥ 1`. -/
theorem measure_encard_cluster_ge_le [Countable V] (μ : Measure (Config V)) (o : V)
    (A B : ℝ≥0∞)
    (hQ : ∀ r : ℕ, 1 ≤ r → μ {ω | ∃ y, (openGraph ω).edist o y = r} ≤ A / r)
    (hB : ∀ r : ℕ, 1 ≤ r →
      ∫⁻ ω, (({y | (openGraph ω).edist o y ≤ r} : Set V).encard : ℝ≥0∞) ∂μ ≤ B * r)
    (n : ℕ) (hn : 1 ≤ n) :
    μ {ω | (n : ℕ∞) ≤ (cluster ω o).encard} ≤ (A + 2 * B) / ENNReal.ofReal (Real.sqrt n) := by
  set r : ℕ := Nat.sqrt n + 1 with hr
  have hr1 : 1 ≤ r := by omega
  obtain ⟨hsr, hrn⟩ := sqrt_bounds n hn
  have hsub : {ω : Config V | (n : ℕ∞) ≤ (cluster ω o).encard} ⊆
      {ω | ∃ y, (openGraph ω).edist o y = r} ∪
        {ω | (n : ℝ≥0∞) ≤ (({y | (openGraph ω).edist o y ≤ r} : Set V).encard : ℝ≥0∞)} := by
    intro ω hω
    by_cases hS : ∃ y, (openGraph ω).edist o y = r
    · exact Or.inl hS
    · right
      have := (hω.trans (Set.encard_le_encard
        (cluster_subset_ball_of_sphere_empty ω o r hS)))
      show (n : ℝ≥0∞) ≤ _
      exact_mod_cast this
  have hn0 : (n : ℝ≥0∞) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hmarkov := meas_ge_le_lintegral_div (μ := μ)
    (measurable_encard_ball o r).aemeasurable hn0 (ENNReal.natCast_ne_top n)
  calc μ {ω | (n : ℕ∞) ≤ (cluster ω o).encard}
      ≤ μ {ω | ∃ y, (openGraph ω).edist o y = r} +
        μ {ω | (n : ℝ≥0∞) ≤ (({y | (openGraph ω).edist o y ≤ r} : Set V).encard : ℝ≥0∞)} :=
        (measure_mono hsub).trans (measure_union_le _ _)
    _ ≤ A / r + B * r / n := add_le_add (hQ r hr1)
        (hmarkov.trans (ENNReal.div_le_div_right (hB r hr1) _))
    _ ≤ A / ENNReal.ofReal (Real.sqrt n) + 2 * B / ENNReal.ofReal (Real.sqrt n) := by
        apply add_le_add
        · exact ENNReal.div_le_div_left hsr A
        · rw [mul_div_assoc, mul_comm (2 : ℝ≥0∞), mul_div_assoc]
          exact mul_le_mul' le_rfl hrn
    _ = (A + 2 * B) / ENNReal.ofReal (Real.sqrt n) := (ENNReal.add_div).symm

/-! ### PI11: thinning comparison -/

/-- Concavity of `t ↦ 1 - e^{-tJ}`: `(α/β)(1 - e^{-βJ}) ≤ 1 - e^{-αJ} ≤ 1 - e^{-βJ}`. -/
theorem intensity_ratio_bounds {J α β : ℝ} (hJ : 0 ≤ J) (hα : 0 < α) (hαβ : α ≤ β) :
    α / β * (1 - Real.exp (-β * J)) ≤ 1 - Real.exp (-α * J) ∧
      1 - Real.exp (-α * J) ≤ 1 - Real.exp (-β * J) := by
  have hβ : 0 < β := hα.trans_le hαβ
  have hl0 : 0 ≤ α / β := (div_pos hα hβ).le
  have hl1 : α / β ≤ 1 := (div_le_one hβ).mpr hαβ
  refine ⟨?_, ?_⟩
  · have h := convexOn_exp.2 (Set.mem_univ (-β * J)) (Set.mem_univ 0) hl0 (by linarith : 0 ≤ 1 - α / β)
      (by ring)
    simp only [smul_eq_mul, mul_zero, add_zero, Real.exp_zero, mul_one] at h
    have he : α / β * (-β * J) = -α * J := by field_simp
    rw [he] at h
    nlinarith
  · have : Real.exp (-β * J) ≤ Real.exp (-α * J) := Real.exp_le_exp.mpr (by nlinarith)
    linarith

/-- A thinning profile: retaining each `β`-open pair with probability `s e` gives the
`α`-profile, and every retention probability is at least `α/β`. -/
theorem exists_thinning_profile (J : Sym2 V → ℝ≥0) {α β : ℝ≥0} (hα : 0 < α) (hαβ : α ≤ β) :
    ∃ s : Sym2 V → unitInterval, (∀ e, intensityProfile J β e * s e = intensityProfile J α e) ∧
      ∀ e, (α / β : ℝ) ≤ s e := by
  classical
  have hα' : (0 : ℝ) < α := hα
  have hαβ' : (α : ℝ) ≤ β := hαβ
  have hβ' : (0 : ℝ) < β := hα'.trans_le hαβ'
  have hpα : ∀ e, (intensityProfile J α e : ℝ) = 1 - Real.exp (-(α : ℝ) * J e) := fun e => rfl
  have hpβ : ∀ e, (intensityProfile J β e : ℝ) = 1 - Real.exp (-(β : ℝ) * J e) := fun e => rfl
  have hb := fun e => intensity_ratio_bounds (J := (J e : ℝ)) (J e).coe_nonneg hα' hαβ'
  let s : Sym2 V → unitInterval := fun e =>
    if h : (intensityProfile J β e : ℝ) = 0 then 1 else
      ⟨(intensityProfile J α e : ℝ) / intensityProfile J β e, by
        have h0 : 0 < (intensityProfile J β e : ℝ) :=
          lt_of_le_of_ne (unitInterval.nonneg _) (Ne.symm h)
        refine ⟨div_nonneg (unitInterval.nonneg _) h0.le, (div_le_one h0).mpr ?_⟩
        rw [hpα, hpβ]
        exact (hb e).2⟩
  refine ⟨s, fun e => ?_, fun e => ?_⟩
  · apply Subtype.ext
    change (intensityProfile J β e : ℝ) * (s e : ℝ) = intensityProfile J α e
    by_cases h : (intensityProfile J β e : ℝ) = 0
    · have hle : (intensityProfile J α e : ℝ) ≤ intensityProfile J β e := by
        rw [hpα, hpβ]; exact (hb e).2
      have h0 := unitInterval.nonneg (intensityProfile J α e)
      rw [h, zero_mul]
      linarith
    · have hse : (s e : ℝ) = (intensityProfile J α e : ℝ) / intensityProfile J β e := by
        simp only [s]
        split_ifs
        rfl
      rw [hse]
      field_simp
  · simp only [s]
    split_ifs with h
    · simpa using (div_le_one hβ').mpr hαβ'
    · have h0 : 0 < (intensityProfile J β e : ℝ) :=
        lt_of_le_of_ne (unitInterval.nonneg _) (Ne.symm h)
      simp only
      rw [le_div_iff₀ h0, hpα, hpβ]
      exact (hb e).1

private theorem coe_toNNReal_eq_ofReal (u : unitInterval) :
    (unitInterval.toNNReal u : ℝ≥0∞) = ENNReal.ofReal u := by
  rw [ENNReal.ofReal, Real.toNNReal_of_nonneg (unitInterval.nonneg u)]
  rfl

/-- **PI11**, pointwise. For `q_t = intensityProfile J t` and `0 < α ≤ β`,
`P_β(x ∈ B_ω(o,r)) ≤ (β/α)^r · P_α(o ↔ x)`. -/
theorem law_edist_le_le [Countable V] (J : Sym2 V → ℝ≥0) {α β : ℝ≥0} (hα : 0 < α)
    (hαβ : α ≤ β) (o x : V) (r : ℕ) :
    law (intensityProfile J β) {ω | (openGraph ω).edist o x ≤ r} ≤
      ((β : ℝ≥0∞) / α) ^ r * tau (intensityProfile J α) o x := by
  classical
  obtain ⟨s, hs, hsl⟩ := exists_thinning_profile J hα hαβ
  have hα' : (0 : ℝ) < α := hα
  have hβ' : (0 : ℝ) < β := hα'.trans_le hαβ
  set lam : ℝ≥0∞ := ENNReal.ofReal ((α : ℝ) / β) with hlam
  have hlam_eq : lam = ((β : ℝ≥0∞) / α)⁻¹ := by
    rw [hlam, ENNReal.ofReal_div_of_pos hβ', ENNReal.ofReal_coe_nnreal,
      ENNReal.ofReal_coe_nnreal, ENNReal.inv_div (Or.inl ENNReal.coe_ne_top)
        (Or.inl (by exact_mod_cast hα.ne'))]
  have hlam1 : lam ≤ 1 := by
    rw [hlam, ← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal ((div_le_one hβ').mpr hαβ)
  have hm : Measurable fun ω : Config V × Config V => ω.1 ∩ ω.2 :=
    measurable_fst.inter measurable_snd
  have hlaw : law (intensityProfile J α) =
      ((law (intensityProfile J β)).prod (law s)).map (fun ω => ω.1 ∩ ω.2) := by
    rw [law, law, law, prodBernoulli_prod_map_inter]
    congr 1
    funext e
    exact (hs e).symm
  set B : Set (Config V) := {ω | (openGraph ω).edist o x ≤ r}
  have hBm : MeasurableSet B := measurableSet_edist_le o x r
  have hconn := measurableSet_conn (V := V) o x
  have hlow : ∀ ω, B.indicator (fun _ => lam ^ r) ω ≤
      law s (Prod.mk ω ⁻¹' ((fun ω : Config V × Config V => ω.1 ∩ ω.2) ⁻¹' conn o x)) := by
    intro ω
    by_cases hω : ω ∈ B
    · rw [Set.indicator_of_mem hω]
      have hne : (openGraph ω).edist o x ≠ ⊤ := ne_top_of_le_ne_top (by simp) hω
      obtain ⟨p, hp⟩ :=
        (SimpleGraph.reachable_of_edist_ne_top hne).exists_walk_length_eq_edist
      have hplen : p.length ≤ r := by
        have : (p.length : ℕ∞) ≤ r := hp ▸ hω
        exact_mod_cast this
      set F : Finset (Sym2 V) := p.edges.toFinset
      have hsub : {ω' : Config V | (F : Set (Sym2 V)) ⊆ ω'} ⊆
          Prod.mk ω ⁻¹' ((fun ω : Config V × Config V => ω.1 ∩ ω.2) ⁻¹' conn o x) := by
        intro ω' hω'
        refine ⟨p.transfer (openGraph (ω ∩ ω')) fun e he => ?_⟩
        have he' := p.edges_subset_edgeSet he
        rw [openGraph, SimpleGraph.edgeSet_fromEdgeSet] at he' ⊢
        exact ⟨⟨he'.1, hω' (by simpa [F] using he)⟩, he'.2⟩
      calc lam ^ r ≤ lam ^ F.card := pow_le_pow_right_of_le_one' hlam1
            ((List.toFinset_card_le _).trans (by rw [SimpleGraph.Walk.length_edges]; exact hplen))
        _ = ∏ _e ∈ F, lam := (Finset.prod_const lam).symm
        _ ≤ ∏ e ∈ F, (unitInterval.toNNReal (s e) : ℝ≥0∞) :=
            Finset.prod_le_prod fun e _ => by
              rw [coe_toNNReal_eq_ofReal]
              exact ENNReal.ofReal_le_ofReal (hsl e)
        _ = law s {ω' | (F : Set (Sym2 V)) ⊆ ω'} := (prodBernoulli_subset s F).symm
        _ ≤ _ := measure_mono hsub
    · rw [Set.indicator_of_notMem hω]
      exact zero_le
  have htau : lam ^ r * law (intensityProfile J β) B ≤ tau (intensityProfile J α) o x := by
    rw [tau, hlaw, Measure.map_apply hm hconn, Measure.prod_apply (hm hconn),
      ← lintegral_indicator_const hBm]
    exact lintegral_mono hlow
  have hone : ((β : ℝ≥0∞) / α) ^ r * lam ^ r = 1 := by
    rw [← mul_pow, hlam_eq, ENNReal.mul_inv_cancel, one_pow]
    · exact ENNReal.div_pos_iff.mpr ⟨by exact_mod_cast hβ'.ne', ENNReal.coe_ne_top⟩ |>.ne'
    · exact ENNReal.div_ne_top ENNReal.coe_ne_top (by exact_mod_cast hα.ne')
  calc law (intensityProfile J β) B = ((β : ℝ≥0∞) / α) ^ r * lam ^ r *
        law (intensityProfile J β) B := by rw [hone, one_mul]
    _ = ((β : ℝ≥0∞) / α) ^ r * (lam ^ r * law (intensityProfile J β) B) := by ring
    _ ≤ _ := mul_le_mul' le_rfl htau

/-- **PI11**, volume form: `E_β|B_ω(o,r)| ≤ (β/α)^r χ_o(α)`. -/
theorem lintegral_ball_le [Countable V] (J : Sym2 V → ℝ≥0) {α β : ℝ≥0} (hα : 0 < α)
    (hαβ : α ≤ β) (o : V) (r : ℕ) :
    ∫⁻ ω, (({y | (openGraph ω).edist o y ≤ r} : Set V).encard : ℝ≥0∞)
        ∂law (intensityProfile J β) ≤
      ((β : ℝ≥0∞) / α) ^ r * chi (intensityProfile J α) o := by
  rw [lintegral_encard_ball, chi_eq_tsum_tau, ← ENNReal.tsum_mul_left]
  exact ENNReal.tsum_le_tsum fun x => law_edist_le_le J hα hαβ o x r

private theorem one_add_inv_pow_le_exp (r : ℕ) (hr : r ≠ 0) :
    ((r + 1 : ℝ) / r) ^ r ≤ Real.exp 1 := by
  have hr' : (0 : ℝ) < r := by exact_mod_cast Nat.pos_of_ne_zero hr
  have h1 : (r + 1 : ℝ) / r = 1 / r + 1 := by field_simp; ring
  rw [h1]
  calc (1 / (r : ℝ) + 1) ^ r ≤ Real.exp (1 / r) ^ r :=
        pow_le_pow_left₀ (by positivity) (Real.add_one_le_exp _) r
    _ = Real.exp 1 := by
        rw [← Real.exp_nat_mul]
        congr 1
        field_simp

/-- **PI11**, linear growth. If `b > 0` and `χ_o(b - ε) ≤ C/ε` for all `0 < ε < ε₀`, then
`E_b|B_ω(o,r)| ≤ (eC/b)(r+1)` for all large `r`. -/
theorem eventually_lintegral_ball_le [Countable V] (J : Sym2 V → ℝ≥0) (o : V) {b : ℝ≥0}
    (hb : 0 < b) (C : ℝ≥0∞) {ε₀ : ℝ≥0} (hε₀ : 0 < ε₀)
    (hχ : ∀ ε : ℝ≥0, 0 < ε → ε < ε₀ → chi (intensityProfile J (b - ε)) o ≤ C / ε) :
    ∃ R : ℕ, ∀ r : ℕ, R ≤ r →
      ∫⁻ ω, (({y | (openGraph ω).edist o y ≤ r} : Set V).encard : ℝ≥0∞)
          ∂law (intensityProfile J b) ≤
        ENNReal.ofReal (Real.exp 1) * C / b * (r + 1) := by
  obtain ⟨R₀, hR₀⟩ := exists_nat_gt ((b : ℝ) / ε₀)
  refine ⟨max R₀ 1, fun r hr => ?_⟩
  have hr1 : 1 ≤ r := le_of_max_le_right hr
  have hrR : R₀ ≤ r := le_of_max_le_left hr
  have hb' : (0 : ℝ) < b := hb
  have hε₀' : (0 : ℝ) < ε₀ := hε₀
  have hrpos : (0 : ℝ) < r := by exact_mod_cast hr1
  set ε : ℝ≥0 := b / (r + 1) with hεeq
  have hεr : (ε : ℝ) = b / (r + 1) := by simp [hεeq]
  have hε0 : 0 < ε := by
    have : (0 : ℝ) < ε := by rw [hεr]; positivity
    exact_mod_cast this
  have hεε₀ : ε < ε₀ := by
    have : (ε : ℝ) < ε₀ := by
      rw [hεr, div_lt_iff₀ (by positivity)]
      have h1 : (b : ℝ) / ε₀ < r + 1 := by
        have : (R₀ : ℝ) ≤ r := by exact_mod_cast hrR
        linarith
      rw [div_lt_iff₀ hε₀'] at h1
      linarith
    exact_mod_cast this
  have hεb : ε < b := by
    have : (ε : ℝ) < b := by
      rw [hεr, div_lt_iff₀ (by positivity)]
      nlinarith
    exact_mod_cast this
  set α : ℝ≥0 := b - ε with hαeq
  have hα : 0 < α := tsub_pos_of_lt hεb
  have hαb : α ≤ b := tsub_le_self
  have hαr : (α : ℝ) = b - b / (r + 1) := by
    rw [hαeq, NNReal.coe_sub hεb.le, hεr]
  have hαpos : (0 : ℝ) < α := hα
  have hratio : ((b : ℝ≥0∞) / α) ^ r ≤ ENNReal.ofReal (Real.exp 1) := by
    rw [← ENNReal.ofReal_coe_nnreal (p := b), ← ENNReal.ofReal_coe_nnreal (p := α),
      ← ENNReal.ofReal_div_of_pos hαpos, ← ENNReal.ofReal_pow (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have hq : (b : ℝ) / α = (r + 1) / r := by
      rw [hαr]
      have hr0 : (r : ℝ) ≠ 0 := hrpos.ne'
      field_simp
      ring_nf
      field_simp
    rw [hq]
    exact one_add_inv_pow_le_exp r (by omega)
  have hCε : C / ε = C * ((r + 1) / b) := by
    have hcoe : (ε : ℝ≥0∞) = b / (r + 1) := by
      rw [hεeq, ENNReal.coe_div (by positivity)]
      push_cast
      rfl
    rw [hcoe, div_eq_mul_inv, ENNReal.inv_div (Or.inl (by simp)) (Or.inl (by simp))]
  calc ∫⁻ ω, (({y | (openGraph ω).edist o y ≤ r} : Set V).encard : ℝ≥0∞)
          ∂law (intensityProfile J b)
      ≤ ((b : ℝ≥0∞) / α) ^ r * chi (intensityProfile J α) o := lintegral_ball_le J hα hαb o r
    _ ≤ ENNReal.ofReal (Real.exp 1) * (C * ((r + 1) / b)) :=
        mul_le_mul' hratio (hCε ▸ hχ ε hε0 hεε₀)
    _ = ENNReal.ofReal (Real.exp 1) * C / b * (r + 1) := by
        simp only [div_eq_mul_inv]
        ring

/-! ### Non-vacuity witnesses (D-5) -/

/-- PI11 on the two-vertex model at `r = 0` and `r = 1`. -/
example (α β : ℝ≥0) (hα : 0 < α) (hαβ : α ≤ β) :
    law (intensityProfile (fun _ : Sym2 Bool => (1 : ℝ≥0)) β)
        {ω | (openGraph ω).edist false true ≤ (0 : ℕ)} ≤
      ((β : ℝ≥0∞) / α) ^ 0 * tau (intensityProfile (fun _ : Sym2 Bool => (1 : ℝ≥0)) α) false true ∧
    law (intensityProfile (fun _ : Sym2 Bool => (1 : ℝ≥0)) β)
        {ω | (openGraph ω).edist false true ≤ (1 : ℕ)} ≤
      ((β : ℝ≥0∞) / α) ^ 1 * tau (intensityProfile (fun _ : Sym2 Bool => (1 : ℝ≥0)) α) false true :=
  ⟨law_edist_le_le _ hα hαβ false true 0, law_edist_le_le _ hα hαβ false true 1⟩

/-- J1V5 for the deterministic singleton cluster: on `Unit` under the point mass at the
empty configuration, `Q_r = 0` and `|B_ω(o,r)| = 1`, so the hypotheses hold with `A = 0`,
`B = 1`. -/
example (n : ℕ) (hn : 1 ≤ n) :
    Measure.dirac (∅ : Config Unit) {ω | (n : ℕ∞) ≤ (cluster ω ()).encard} ≤
      (0 + 2 * 1) / ENNReal.ofReal (Real.sqrt n) := by
  refine measure_encard_cluster_ge_le _ () 0 1 (fun r hr => ?_) (fun r hr => ?_) n hn
  · have : {ω : Config Unit | ∃ y, (openGraph ω).edist () y = r} = ∅ := by
      ext ω
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_exists]
      intro y h
      rw [Subsingleton.elim y (), SimpleGraph.edist_self] at h
      exact absurd h.symm (by exact_mod_cast (by omega : r ≠ 0))
    rw [this, measure_empty]
    exact zero_le
  · have hball : ∀ ω : Config Unit,
        (({y | (openGraph ω).edist () y ≤ r} : Set Unit).encard : ℝ≥0∞) = 1 := by
      intro ω
      have : ({y | (openGraph ω).edist () y ≤ r} : Set Unit) = Set.univ := by
        ext y
        rw [Subsingleton.elim y ()]
        simp [SimpleGraph.edist_self]
      rw [this, Set.encard_univ]
      simp
    simp only [hball, lintegral_const, measure_univ, mul_one, one_mul]
    exact_mod_cast hr

end PercLib.Percolation.Bond
