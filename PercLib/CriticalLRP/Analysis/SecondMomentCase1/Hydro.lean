/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Case 1 of Corollary I.4.14: the single-cluster tail gives the median bound
`M_r ⪯ (E_{β_c,r}|K|)² log r`, and hence the hydrodynamic condition when `d > 3α`.
-/
module
public import PercLib.CriticalLRP.Analysis.Case3Hydro
public import PercLib.CriticalLRP.Analysis.SecondMomentCase2.Source.Defs

/-!
# Case 1 of Corollary I.4.14: from the single-cluster tail to (Hydro)

Hutchcroft, *Critical long-range percolation I: High effective dimension*,
arXiv:2508.18807v1, proof of Corollary I.4.14 (p. 42):

> It follows from Proposition I.4.2 and the tree-graph inequality applied as in [55, Eq. 6.99]
> that
>     P_{β_c,r}(|K| ≥ n) ≤ sqrt(2 E_{β_c,r}|K| / n) exp(−n / (4 (E_{β_c,r}|K|)²))
> for every n ≥ 1. This implies by a union bound that
>     M_r ⪯ (E_{β_c,r}|K|)² log r
> for every r ≥ 2, which is sufficient to establish the hydrodynamic condition when d > 3α by
> Proposition I.4.2 (since 2α < (d + α)/2 when d > 3α).

This file discharges the *second* sentence exactly: the union bound over the window and the
elementary calculus step. The displayed single-cluster tail — the tree-graph input of
Proposition I.4.2 — is carried as the explicit predicate `SingleClusterTail`, whose statement is
copied verbatim from the display above with `m = E_{β_c,r}|K|`.

The main results are

* `tail_maxCluster_le`: `P(|K_max(B_r)| ≥ n) ≤ |B_r| P(|K| ≥ n)`, the union bound over the
  finite window, from the block display plus translation invariance of the cutoff law;
* `mr_le_singleClusterTail`: `∃ C > 0, ∀ r ≥ 2, M_r ≤ C (E|K|)² log r` at an abstract scale
  `m` with `m r ≥ 1`;
* `hydro_of_singleClusterTail`: `Hydro M` when `3α < d` and `m r ⪯ r^α`;
* `exists_ball_ncard_bound`: the cardinality bound `|B_r| ⪯ r^d` for every `r ≥ 2`, from
  production's `ball_ncard_eventually_le` and monotonicity of the source-norm balls;
* `mr_le_cutMoment_one`, `mr_isBigO_cutMoment_one`, `hydro_of_cutMoment_one`,
  `hydro_of_cutMoment_one'`: the same statements at the model's own first moment
  `m r = (M.cutMoment 1 r).toReal`, the last one with no ball-cardinality hypothesis.

No `sorry`, no custom axioms. The only remaining analytic input is `SingleClusterTail`, the
displayed tree-graph tail bound of Proposition I.4.2, and `hydro_of_cutMoment_one'` also uses the
first-moment upper bound `E_{β_c,r}|K| ⪯ r^α` of Proposition I.4.2, Case 1.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false
set_option linter.hashCommand false

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal Topology BigOperators

namespace PercLib.CriticalLRP

namespace CaseOne

open PercLib.CriticalLRP.Percolation
open PercLib.CriticalLRP.Orchestration

variable (M : SourceModelData)

/-! ## The single-cluster tail input of Corollary I.4.14 -/

/-- **The displayed tail bound of Corollary I.4.14** at the cutoff law, with the single-cluster
scale `m = E_{β_c,r}|K|` passed explicitly:

`P_{β_c,r}(|K| ≥ n) ≤ sqrt(2 m / n) exp(−n / (4 m²))` for every `n ≥ 1`.

This is the consequence of Proposition I.4.2 and the tree-graph inequality used in the paper; it
is the only analytic input of the Case-1 argument and is *not* proved here. -/
def SingleClusterTail (r m : ℝ) : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    (M.cutLaw r) {ω : Config M.V | (n : ℝ≥0∞) ≤ clusterVol ω (0 : M.V)} ≤
      ENNReal.ofReal (Real.sqrt (2 * m / n) * Real.exp (-((n : ℝ) / (4 * m ^ 2))))

/-! ## The truncated cluster volume is monotone in the window -/

/-- `|K_v ∩ W| ≤ |K_v ∩ W'|` for `W ⊆ W'`. -/
theorem clusterVolIn_mono {V : Type*} [Countable V] {ω : Config V} {v : V} {W W' : Set V}
    (h : W ⊆ W') : clusterVolIn ω v W ≤ clusterVolIn ω v W' := by
  simp only [clusterVolIn]
  exact_mod_cast Set.encard_mono (Set.inter_subset_inter le_rfl h)

/-! ## The union bound over the window -/

/-- **The union bound of Corollary I.4.14**: the tail of the largest cluster in `B_r` is at most
`|B_r|` times the tail of the cluster of the origin.

Every cluster meeting `B_r` is the cluster of a point of `B_r`, and a point `w ∈ B_r` sees the
whole window inside its own doubled window `B_{2r}(w)`; the cutoff law is translation invariant,
so all `|B_r|` summands are equal. -/
theorem tail_maxCluster_le (r : ℝ) (hr : 0 ≤ r) (n : ℕ) :
    (M.cutLaw r) {ω : Config M.V |
        (n : ℝ≥0∞) ≤ clusterMaxVol ω (E1Sign.ballF M r)} ≤
      ((E1Sign.ballF M r).card : ℝ≥0∞) *
        (M.cutLaw r) {ω : Config M.V | (n : ℝ≥0∞) ≤ clusterVol ω (0 : M.V)} := by
  classical
  set W := E1Sign.ballF M r with hWdef
  have hWne : W.Nonempty := ⟨0, (E1Sign.mem_ballF M).mpr (CaseTwo.zero_mem_ball M hr)⟩
  have hWcoe : (W : Set M.V) = M.ball r := CaseTwo.coe_ballF M r
  -- Step 1: the maximum-cluster event is covered by the `w`-indexed doubled-window events.
  have hcover : {ω : Config M.V | (n : ℝ≥0∞) ≤ clusterMaxVol ω W} ⊆
      ⋃ w ∈ W, {ω : Config M.V |
        (n : ℝ≥0∞) ≤ clusterVolIn ω w (M5.ballAt M w (2 * r))} := by
    intro ω hω
    obtain ⟨w, hw, hsup⟩ :=
      Finset.exists_mem_eq_sup W hWne (fun w => clusterVolIn ω w (W : Set M.V))
    refine Set.mem_biUnion hw ?_
    have h1 : (n : ℝ≥0∞) ≤ clusterVolIn ω w ((W : Set M.V)) := by
      simp only [clusterMaxVol] at hω
      exact le_trans hω (le_of_eq hsup)
    refine le_trans h1 (clusterVolIn_mono ?_)
    rw [hWcoe]
    exact M5.ball_subset_ballAt_two_mul M ((E1Sign.mem_ballF M).mp hw)
  -- Step 2: union bound, translation invariance, and domination by the untruncated cluster.
  calc (M.cutLaw r) {ω : Config M.V | (n : ℝ≥0∞) ≤ clusterMaxVol ω W}
      ≤ (M.cutLaw r) (⋃ w ∈ W, {ω : Config M.V |
          (n : ℝ≥0∞) ≤ clusterVolIn ω w (M5.ballAt M w (2 * r))}) :=
        measure_mono hcover
    _ ≤ ∑ w ∈ W, (M.cutLaw r) {ω : Config M.V |
          (n : ℝ≥0∞) ≤ clusterVolIn ω w (M5.ballAt M w (2 * r))} :=
        measure_biUnion_finset_le W _
    _ = ∑ _w ∈ W, (M.cutLaw r) {ω : Config M.V |
          (n : ℝ≥0∞) ≤ clusterVolIn ω (0 : M.V) (M.ball (2 * r))} := by
        refine Finset.sum_congr rfl fun w _ => ?_
        exact M5.measure_clusterVolIn_ballAt_eq M n r w
    _ = (W.card : ℝ≥0∞) * (M.cutLaw r) {ω : Config M.V |
          (n : ℝ≥0∞) ≤ clusterVolIn ω (0 : M.V) (M.ball (2 * r))} := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (W.card : ℝ≥0∞) * (M.cutLaw r) {ω : Config M.V |
          (n : ℝ≥0∞) ≤ clusterVol ω (0 : M.V)} := by
        exact mul_le_mul_right (measure_mono fun ω hω =>
          le_trans hω (clusterVolIn_le_clusterVol ω 0 (M.ball (2 * r)))) _

end CaseOne

end PercLib.CriticalLRP

namespace PercLib.CriticalLRP

namespace CaseOne

open PercLib.CriticalLRP.Percolation
open PercLib.CriticalLRP.Orchestration

variable (M : SourceModelData)

/-- **Case 1 of Corollary I.4.14, median bound**: if the first moment `m r = E_{β_c,r}|K|` is at
least `1` and satisfies the displayed single-cluster tail bound, and `|B_r| ≤ Bc · r^d`, then
there is a constant `C`, depending only on `d`, `Bc` and `α`, with

`M_r ≤ C (E_{β_c,r}|K|)² log r` for every `r ≥ 2`.

The proof is the union bound `tail_maxCluster_le` at the scale `n = ⌈A m² log r⌉`: the tail
factor `exp(−n/(4m²))` becomes `r^{−A/4}`, the prefactor `sqrt(2m/n)` is bounded using
`m ≥ 1`, and `A` is chosen so that `|B_r| r^{−A/4}` beats the exponential gain. -/
theorem mr_le_singleClusterTail (Bc : ℝ) (hBc : 0 < Bc)
    (hball : ∀ r : ℝ, 2 ≤ r → ((M.ball r).ncard : ℝ) ≤ Bc * r ^ (M.d : ℝ))
    (m : ℝ → ℝ) (hm1 : ∀ r : ℝ, 2 ≤ r → 1 ≤ m r)
    (htail : ∀ r : ℝ, 2 ≤ r → SingleClusterTail M r (m r)) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 2 ≤ r →
      (M.Mr r : ℝ) ≤ C * (m r) ^ 2 * Real.log r := by
  classical
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  -- The scale constant `A`: large enough that `|B_r| ≤ Bc r^d` loses against `r^{-A/4}`.
  set A : ℝ := max (max 1 (4 * ((M.d : ℝ) + 1))) (2 * Bc ^ 2 * Real.exp 2 / Real.log 2 + 1)
    with hAdef
  have hA1 : 1 ≤ A := (le_max_left _ _).trans (le_max_left _ _)
  have hAd : 4 * ((M.d : ℝ) + 1) ≤ A := (le_max_right _ _).trans (le_max_left _ _)
  have hAe : 2 * Bc ^ 2 * Real.exp 2 / Real.log 2 + 1 ≤ A := le_max_right _ _
  refine ⟨A + 1 / Real.log 2, by positivity, fun r hr => ?_⟩
  have hr2 : (0 : ℝ) < r := by linarith
  have hr1 : (1 : ℝ) ≤ r := by linarith
  have hlogr : 0 < Real.log r := Real.log_pos (by linarith)
  have hlog2r : Real.log 2 ≤ Real.log r := Real.log_le_log (by norm_num) hr
  set mr : ℝ := m r with hmrdef
  have hmr1 : 1 ≤ mr := hm1 r hr
  have hmrpos : 0 < mr := lt_of_lt_of_le zero_lt_one hmr1
  set nr : ℕ := Nat.ceil (A * mr ^ 2 * Real.log r) with hnrdef
  have hxpos : 0 < A * mr ^ 2 * Real.log r := by
    have : (0 : ℝ) < A := lt_of_lt_of_le zero_lt_one hA1
    positivity
  have hnr_ge : A * mr ^ 2 * Real.log r ≤ (nr : ℝ) := Nat.le_ceil _
  have hnr_lt : (nr : ℝ) < A * mr ^ 2 * Real.log r + 1 := Nat.ceil_lt_add_one hxpos.le
  have hnr1 : 1 ≤ nr := Nat.ceil_pos.mpr hxpos
  have hnrpos : (0 : ℝ) < (nr : ℝ) := by exact_mod_cast hnr1
  -- The tail at the chosen scale is already below `e^{-1}`.
  have hApos : (0 : ℝ) < A := lt_of_lt_of_le zero_lt_one hA1
  have hlog2A : (0 : ℝ) < A * Real.log 2 := mul_pos hApos hlog2
  have hsqrt_step : Real.sqrt (2 * mr / nr) ≤ Real.sqrt (2 / (A * Real.log 2)) := by
    refine Real.sqrt_le_sqrt ?_
    rw [div_le_div_iff₀ hnrpos hlog2A]
    have hstep1 : mr * (A * Real.log 2) ≤ mr * (A * Real.log r) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlog2r hApos.le) hmrpos.le
    have hstep2 : mr * (A * Real.log r) ≤ mr ^ 2 * (A * Real.log r) := by
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      nlinarith [hmr1]
    have hstep3 : mr ^ 2 * (A * Real.log r) = A * mr ^ 2 * Real.log r := by ring
    nlinarith [hstep1, hstep2, hnr_ge, hstep3]
  have hexp_step :
      Real.exp (-((nr : ℝ) / (4 * mr ^ 2))) ≤ r ^ (-(A / 4)) := by
    rw [Real.rpow_def_of_pos hr2, Real.exp_le_exp]
    have h4 : (0 : ℝ) < 4 * mr ^ 2 := by positivity
    have hkey : A * Real.log r / 4 ≤ (nr : ℝ) / (4 * mr ^ 2) := by
      rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 4) h4]
      nlinarith [hnr_ge, hmrpos]
    have hrew : Real.log r * -(A / 4) = -(A * Real.log r / 4) := by ring
    rw [hrew]
    linarith
  have hA4 : (M.d : ℝ) ≤ A / 4 := by linarith
  have hpow_step : r ^ (M.d : ℝ) * r ^ (-(A / 4)) ≤ 1 := by
    have hmono : r ^ (M.d : ℝ) ≤ r ^ (A / 4) := Real.rpow_le_rpow_of_exponent_le hr1 hA4
    have hone : r ^ (A / 4) * r ^ (-(A / 4)) = 1 := by
      rw [← Real.rpow_add hr2]
      norm_num
    calc r ^ (M.d : ℝ) * r ^ (-(A / 4)) ≤ r ^ (A / 4) * r ^ (-(A / 4)) :=
          mul_le_mul_of_nonneg_right hmono (by positivity)
      _ = 1 := hone
  have hBcsqrt : Bc * Real.sqrt (2 / (A * Real.log 2)) ≤ Real.exp (-1) := by
    have hnums : 2 * Bc ^ 2 * Real.exp 2 ≤ A * Real.log 2 := by
      have hAe' : 2 * Bc ^ 2 * Real.exp 2 / Real.log 2 ≤ A := by linarith
      rw [div_le_iff₀ hlog2] at hAe'
      linarith
    have hkey : Bc ^ 2 * (2 / (A * Real.log 2)) ≤ Real.exp (-2) := by
      have hR : Real.exp (-2) = (Real.exp 2)⁻¹ := Real.exp_neg 2
      rw [hR, ← one_div, ← mul_div_assoc,
        div_le_div_iff₀ (by positivity) (Real.exp_pos 2)]
      nlinarith [hnums]
    have hsq : (Bc * Real.sqrt (2 / (A * Real.log 2))) ^ 2 ≤ (Real.exp (-1)) ^ 2 := by
      have hexp_sq : (Real.exp (-1)) ^ 2 = Real.exp (-2) := by
        rw [pow_two, ← Real.exp_add]
        norm_num
      rw [mul_pow, Real.sq_sqrt (by positivity), hexp_sq]
      exact hkey
    have hnonneg : (0 : ℝ) ≤ Bc * Real.sqrt (2 / (A * Real.log 2)) := by positivity
    calc Bc * Real.sqrt (2 / (A * Real.log 2))
        = Real.sqrt ((Bc * Real.sqrt (2 / (A * Real.log 2))) ^ 2) :=
          (Real.sqrt_sq hnonneg).symm
      _ ≤ Real.sqrt ((Real.exp (-1)) ^ 2) := Real.sqrt_le_sqrt hsq
      _ = Real.exp (-1) := Real.sqrt_sq (Real.exp_pos (-1)).le
  have hbound : (M.cutLaw r) {ω : Config M.V |
        (nr : ℝ≥0∞) ≤ clusterMaxVol ω (E1Sign.ballF M r)} ≤
      ENNReal.ofReal (Real.exp (-1)) := by
    have hcard : ((E1Sign.ballF M r).card : ℝ≥0∞) ≤
        ENNReal.ofReal (Bc * r ^ (M.d : ℝ)) := by
      rw [E1Sign.card_ballF]
      have hcast : ((M.ball r).ncard : ℝ≥0∞) = ENNReal.ofReal (((M.ball r).ncard : ℝ)) := by
        simp
      rw [hcast]
      exact ENNReal.ofReal_le_ofReal (hball r hr)
    have htail' : (M.cutLaw r) {ω : Config M.V | (nr : ℝ≥0∞) ≤ clusterVol ω (0 : M.V)} ≤
        ENNReal.ofReal (Real.sqrt (2 * mr / nr) *
          Real.exp (-((nr : ℝ) / (4 * mr ^ 2)))) := htail r hr nr hnr1
    refine (tail_maxCluster_le M r (by linarith) nr).trans ?_
    refine (mul_le_mul hcard htail' (by positivity) (by positivity)).trans ?_
    rw [← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    refine le_trans (mul_le_mul_of_nonneg_left
      (mul_le_mul hsqrt_step hexp_step (Real.exp_pos _).le (Real.sqrt_nonneg _))
      (by positivity)) ?_
    have hsplit : Bc * r ^ (M.d : ℝ) *
        (Real.sqrt (2 / (A * Real.log 2)) * r ^ (-(A / 4)))
        = (Bc * Real.sqrt (2 / (A * Real.log 2))) *
            (r ^ (M.d : ℝ) * r ^ (-(A / 4))) := by ring
    rw [hsplit]
    calc (Bc * Real.sqrt (2 / (A * Real.log 2))) *
          (r ^ (M.d : ℝ) * r ^ (-(A / 4)))
        ≤ Real.exp (-1) * 1 :=
          mul_le_mul hBcsqrt hpow_step (by positivity) (Real.exp_pos _).le
      _ = Real.exp (-1) := mul_one _
  have hMr : M.Mr r ≤ nr := by
    rw [CaseTwo.Mr_eq_edianMaxVol M r]
    exact Nat.find_min' (Percolation.exists_edianMaxVol (E1Sign.ballF M r)) hbound
  have hmrge : (1 : ℝ) ≤ mr ^ 2 := by nlinarith
  have hlog2le : Real.log 2 ≤ mr ^ 2 * Real.log r := by
    nlinarith [hmrge, hlogr, hlog2r, hlog2]
  have hconst : (1 : ℝ) ≤ (1 / Real.log 2) * (mr ^ 2 * Real.log r) := by
    rw [div_mul_eq_mul_div, one_le_div hlog2]
    linarith
  calc (M.Mr r : ℝ) ≤ (nr : ℝ) := by exact_mod_cast hMr
    _ ≤ A * mr ^ 2 * Real.log r + 1 := le_of_lt hnr_lt
    _ ≤ (A + 1 / Real.log 2) * (mr ^ 2 * Real.log r) := by nlinarith [hconst]
    _ = (A + 1 / Real.log 2) * mr ^ 2 * Real.log r := by ring

end CaseOne

end PercLib.CriticalLRP

namespace PercLib.CriticalLRP

namespace CaseOne

open PercLib.CriticalLRP.Percolation
open PercLib.CriticalLRP.Orchestration

variable (M : SourceModelData)

/-- **Case 1 of Corollary I.4.14, the hydrodynamic condition**: if `3α < d`, the cutoff first
moment satisfies `E_{β_c,r}|K| ≤ C₁ r^α`, and the single-cluster tail `SingleClusterTail`
holds at that scale, then `M_r = o(r^{(d+α)/2})`.

The exponent gain is the paper's `2α < (d + α)/2`: the median bound contributes `r^{2α} log r`
and `log r / r^{(d-3α)/2} → 0`. The hypothesis `0 < α` is carried for fidelity with the paper's
Case 1 but is not needed for this implication. -/
theorem hydro_of_singleClusterTail (_hα : 0 < M.α) (hd : 3 * M.α < (M.d : ℝ))
    (Bc : ℝ) (hBc : 0 < Bc)
    (hball : ∀ r : ℝ, 2 ≤ r → ((M.ball r).ncard : ℝ) ≤ Bc * r ^ (M.d : ℝ))
    (m : ℝ → ℝ) (hm1 : ∀ r : ℝ, 2 ≤ r → 1 ≤ m r)
    (htail : ∀ r : ℝ, 2 ≤ r → SingleClusterTail M r (m r))
    (C₁ : ℝ) (hC₁ : 0 < C₁)
    (hm : ∀ᶠ r : ℝ in atTop, m r ≤ C₁ * r ^ M.α) :
    Hydro M := by
  obtain ⟨C, hC0, hC⟩ := mr_le_singleClusterTail M Bc hBc hball m hm1 htail
  have hs : 0 < ((M.d : ℝ) - 3 * M.α) / 2 := by linarith
  have htend : Tendsto (fun r : ℝ => Real.log r / r ^ (((M.d : ℝ) - 3 * M.α) / 2))
      atTop (𝓝 0) := (isLittleO_log_rpow_atTop hs).tendsto_div_nhds_zero
  have htend' : Tendsto (fun r : ℝ =>
      C * C₁ ^ 2 * (Real.log r / r ^ (((M.d : ℝ) - 3 * M.α) / 2))) atTop (𝓝 0) := by
    simpa using htend.const_mul (C * C₁ ^ 2)
  refine squeeze_zero' ?_ ?_ htend'
  · filter_upwards [eventually_ge_atTop (2 : ℝ)] with r hr
    have hr2 : (0 : ℝ) < r := by linarith
    have hEpos : (0 : ℝ) < r ^ (((M.d : ℝ) + M.α) / 2) := Real.rpow_pos_of_pos hr2 _
    exact div_nonneg (by positivity) hEpos.le
  · filter_upwards [eventually_ge_atTop (2 : ℝ), hm] with r hr hmr
    have hr2 : (0 : ℝ) < r := by linarith
    have hr1 : (1 : ℝ) ≤ r := by linarith
    have hmr1 : (0 : ℝ) ≤ m r := le_trans zero_le_one (hm1 r hr)
    have hlogr : 0 ≤ Real.log r := Real.log_nonneg hr1
    have hC₁pos : (0 : ℝ) ≤ C₁ * r ^ M.α := by positivity
    have hsq : (m r) ^ 2 ≤ (C₁ * r ^ M.α) ^ 2 := by nlinarith [hmr, hmr1, hC₁pos]
    have hbound : (M.Mr r : ℝ) ≤ C * (C₁ * r ^ M.α) ^ 2 * Real.log r := by
      refine (hC r hr).trans ?_
      have hstep : C * (m r) ^ 2 * Real.log r ≤ C * (C₁ * r ^ M.α) ^ 2 * Real.log r := by
        refine mul_le_mul_of_nonneg_right ?_ hlogr
        exact mul_le_mul_of_nonneg_left hsq hC0.le
      exact hstep
    have hEpos : (0 : ℝ) < r ^ (((M.d : ℝ) + M.α) / 2) := Real.rpow_pos_of_pos hr2 _
    refine (div_le_div_of_nonneg_right hbound hEpos.le).trans (le_of_eq ?_)
    have hpowsq : (r ^ M.α) ^ 2 = r ^ (2 * M.α) := by
      rw [pow_two, ← Real.rpow_add hr2]
      ring_nf
    have hsub : 2 * M.α - ((M.d : ℝ) + M.α) / 2 = -(((M.d : ℝ) - 3 * M.α) / 2) := by ring
    have hpowdiv : r ^ (2 * M.α) / r ^ (((M.d : ℝ) + M.α) / 2)
        = (r ^ (((M.d : ℝ) - 3 * M.α) / 2))⁻¹ := by
      rw [← Real.rpow_sub hr2, hsub, Real.rpow_neg hr2.le]
    have hkey : (C₁ * r ^ M.α) ^ 2 * Real.log r / r ^ (((M.d : ℝ) + M.α) / 2)
        = C₁ ^ 2 * (Real.log r / r ^ (((M.d : ℝ) - 3 * M.α) / 2)) := by
      rw [mul_pow, hpowsq]
      calc C₁ ^ 2 * r ^ (2 * M.α) * Real.log r / r ^ (((M.d : ℝ) + M.α) / 2)
          = C₁ ^ 2 * (r ^ (2 * M.α) / r ^ (((M.d : ℝ) + M.α) / 2)) * Real.log r := by
            field_simp
        _ = C₁ ^ 2 * (r ^ (((M.d : ℝ) - 3 * M.α) / 2))⁻¹ * Real.log r := by rw [hpowdiv]
        _ = C₁ ^ 2 * (Real.log r / r ^ (((M.d : ℝ) - 3 * M.α) / 2)) := by
            rw [div_eq_mul_inv]
            ring
    calc C * (C₁ * r ^ M.α) ^ 2 * Real.log r / r ^ (((M.d : ℝ) + M.α) / 2)
        = C * ((C₁ * r ^ M.α) ^ 2 * Real.log r / r ^ (((M.d : ℝ) + M.α) / 2)) := by
          field_simp
      _ = C * (C₁ ^ 2 * (Real.log r / r ^ (((M.d : ℝ) - 3 * M.α) / 2))) := by rw [hkey]
      _ = C * C₁ ^ 2 * (Real.log r / r ^ (((M.d : ℝ) - 3 * M.α) / 2)) := by ring

end CaseOne

end PercLib.CriticalLRP

namespace PercLib.CriticalLRP

namespace CaseOne

open PercLib.CriticalLRP.Percolation
open PercLib.CriticalLRP.Orchestration

variable (M : SourceModelData)

/-! ## Discharging the ball-cardinality bound -/

/-- **`|B_r| ⪯ r^d` at every `r ≥ 2`**, with one constant: production's
`ball_ncard_eventually_le` (`|B_r| ≤ 2 r^d` eventually) extended to all `r ≥ 2` by monotonicity
of the source-norm balls and the trivial bound `|B_r| ≤ |B_R|` below the threshold `R`. -/
theorem exists_ball_ncard_bound :
    ∃ Bc : ℝ, 0 < Bc ∧ ∀ r : ℝ, 2 ≤ r →
      ((M.ball r).ncard : ℝ) ≤ Bc * r ^ (M.d : ℝ) := by
  obtain ⟨R, hR⟩ := eventually_atTop.mp (M5.ball_ncard_eventually_le M)
  set R' : ℝ := max R 2 with hR'def
  have hRR' : R ≤ R' := le_max_left _ _
  set q : ℝ := ((M.ball R').ncard : ℝ) / 2 ^ M.d with hqdef
  have hq0 : 0 ≤ q := by positivity
  refine ⟨max 2 q, by positivity, fun r hr => ?_⟩
  have hr0 : (0 : ℝ) < r := by linarith
  have hrpow : (0 : ℝ) < r ^ (M.d : ℝ) := Real.rpow_pos_of_pos hr0 _
  have hBc2 : (2 : ℝ) ≤ max 2 q := le_max_left _ _
  have hBcq : q ≤ max 2 q := le_max_right _ _
  rcases le_or_gt R' r with h | h
  · have h1 : ((M.ball r).ncard : ℝ) ≤ 2 * r ^ M.d := hR r (le_trans hRR' h)
    have h1' : ((M.ball r).ncard : ℝ) ≤ 2 * r ^ (M.d : ℝ) := by
      rwa [Real.rpow_natCast]
    calc ((M.ball r).ncard : ℝ) ≤ 2 * r ^ (M.d : ℝ) := h1'
      _ ≤ max 2 q * r ^ (M.d : ℝ) := mul_le_mul_of_nonneg_right hBc2 hrpow.le
  · have hsub : M.ball r ⊆ M.ball R' := fun y hy => le_trans hy h.le
    have hmono : ((M.ball r).ncard : ℝ) ≤ ((M.ball R').ncard : ℝ) := by
      exact_mod_cast Set.ncard_le_ncard hsub (M.finite_ball R')
    have h2d : (0 : ℝ) < 2 ^ (M.d : ℝ) := by positivity
    have hrd : (2 : ℝ) ^ (M.d : ℝ) ≤ r ^ (M.d : ℝ) := by
      rw [Real.rpow_natCast, Real.rpow_natCast]
      exact pow_le_pow_left₀ (by norm_num) hr M.d
    have hqeq : q = ((M.ball R').ncard : ℝ) / 2 ^ (M.d : ℝ) := by
      simp only [hqdef, Real.rpow_natCast]
    have hfac : 1 ≤ r ^ (M.d : ℝ) / 2 ^ (M.d : ℝ) := by
      rw [le_div_iff₀ h2d, one_mul]
      exact hrd
    have hnn : (0 : ℝ) ≤ ((M.ball R').ncard : ℝ) := by positivity
    have hkey : ((M.ball R').ncard : ℝ) ≤ q * r ^ (M.d : ℝ) := by
      calc ((M.ball R').ncard : ℝ) = ((M.ball R').ncard : ℝ) * 1 := by ring
        _ ≤ ((M.ball R').ncard : ℝ) * (r ^ (M.d : ℝ) / 2 ^ (M.d : ℝ)) :=
            mul_le_mul_of_nonneg_left hfac hnn
        _ = q * r ^ (M.d : ℝ) := by
            rw [hqeq]
            field_simp
    calc ((M.ball r).ncard : ℝ) ≤ ((M.ball R').ncard : ℝ) := hmono
      _ ≤ q * r ^ (M.d : ℝ) := hkey
      _ ≤ max 2 q * r ^ (M.d : ℝ) := mul_le_mul_of_nonneg_right hBcq hrpow.le

/-! ## At the actual cutoff first moment -/

/-- **Case 1 of Corollary I.4.14 at the model's own first moment**: with `m r = E_{β_c,r}|K|`
realised as `(M.cutMoment 1 r).toReal`, the displayed single-cluster tail bound, and `m r ≥ 1`,
one has `M_r ≤ C (E_{β_c,r}|K|)² log r` for every `r ≥ 2`. -/
theorem mr_le_cutMoment_one (Bc : ℝ) (hBc : 0 < Bc)
    (hball : ∀ r : ℝ, 2 ≤ r → ((M.ball r).ncard : ℝ) ≤ Bc * r ^ (M.d : ℝ))
    (hm1 : ∀ r : ℝ, 2 ≤ r → 1 ≤ (M.cutMoment 1 r).toReal)
    (htail : ∀ r : ℝ, 2 ≤ r → SingleClusterTail M r (M.cutMoment 1 r).toReal) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 2 ≤ r →
      (M.Mr r : ℝ) ≤ C * ((M.cutMoment 1 r).toReal) ^ 2 * Real.log r :=
  mr_le_singleClusterTail M Bc hBc hball (fun r => (M.cutMoment 1 r).toReal) hm1 htail

/-- **Case 1 of Corollary I.4.14, capstone**: `3α < d`, `E_{β_c,r}|K| ≤ C₁ r^α`, and the
displayed single-cluster tail at the model's own first moment imply the hydrodynamic condition.
The ball-cardinality bound is passed as `hball` (discharge it with `exists_ball_ncard_bound`). -/
theorem hydro_of_cutMoment_one (_hα : 0 < M.α) (hd : 3 * M.α < (M.d : ℝ))
    (Bc : ℝ) (hBc : 0 < Bc)
    (hball : ∀ r : ℝ, 2 ≤ r → ((M.ball r).ncard : ℝ) ≤ Bc * r ^ (M.d : ℝ))
    (hm1 : ∀ r : ℝ, 2 ≤ r → 1 ≤ (M.cutMoment 1 r).toReal)
    (htail : ∀ r : ℝ, 2 ≤ r → SingleClusterTail M r (M.cutMoment 1 r).toReal)
    (C₁ : ℝ) (hC₁ : 0 < C₁)
    (hm : ∀ᶠ r : ℝ in atTop, (M.cutMoment 1 r).toReal ≤ C₁ * r ^ M.α) :
    Hydro M :=
  hydro_of_singleClusterTail M _hα hd Bc hBc hball (fun r => (M.cutMoment 1 r).toReal)
    hm1 htail C₁ hC₁ hm

end CaseOne

end PercLib.CriticalLRP

/-! ## Axiom audit -/

#print axioms PercLib.CriticalLRP.CaseOne.clusterVolIn_mono
#print axioms PercLib.CriticalLRP.CaseOne.tail_maxCluster_le
#print axioms PercLib.CriticalLRP.CaseOne.mr_le_singleClusterTail
#print axioms PercLib.CriticalLRP.CaseOne.hydro_of_singleClusterTail
#print axioms PercLib.CriticalLRP.CaseOne.exists_ball_ncard_bound
#print axioms PercLib.CriticalLRP.CaseOne.mr_le_cutMoment_one
#print axioms PercLib.CriticalLRP.CaseOne.hydro_of_cutMoment_one

namespace PercLib.CriticalLRP

namespace CaseOne

open PercLib.CriticalLRP.Percolation
open PercLib.CriticalLRP.Orchestration

variable (M : SourceModelData)

/-- **`M_r ⪯ (E_{β_c,r}|K|)² log r` in the paper's `O`-notation**, at the model's own first
moment. -/
theorem mr_isBigO_cutMoment_one (Bc : ℝ) (hBc : 0 < Bc)
    (hball : ∀ r : ℝ, 2 ≤ r → ((M.ball r).ncard : ℝ) ≤ Bc * r ^ (M.d : ℝ))
    (hm1 : ∀ r : ℝ, 2 ≤ r → 1 ≤ (M.cutMoment 1 r).toReal)
    (htail : ∀ r : ℝ, 2 ≤ r → SingleClusterTail M r (M.cutMoment 1 r).toReal) :
    (fun r : ℝ => (M.Mr r : ℝ)) =O[atTop]
      (fun r : ℝ => ((M.cutMoment 1 r).toReal) ^ 2 * Real.log r) := by
  obtain ⟨C, hC0, hC⟩ := mr_le_cutMoment_one M Bc hBc hball hm1 htail
  refine Asymptotics.IsBigO.of_bound C ?_
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with r hr
  have hm0 : (0 : ℝ) ≤ (M.cutMoment 1 r).toReal := le_trans zero_le_one (hm1 r hr)
  have hlog0 : (0 : ℝ) ≤ Real.log r := Real.log_nonneg (by linarith)
  have hg : (0 : ℝ) ≤ ((M.cutMoment 1 r).toReal) ^ 2 * Real.log r := by positivity
  calc ‖(M.Mr r : ℝ)‖ = (M.Mr r : ℝ) := by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    _ ≤ C * ((M.cutMoment 1 r).toReal) ^ 2 * Real.log r := hC r hr
    _ = C * ‖((M.cutMoment 1 r).toReal) ^ 2 * Real.log r‖ := by
        rw [Real.norm_eq_abs, abs_of_nonneg hg]
        ring

/-- **Case 1 of Corollary I.4.14, capstone with no ball hypothesis**: `3α < d`, the first-moment
bound `E_{β_c,r}|K| ≤ C₁ r^α` and the displayed single-cluster tail imply `Hydro M`. -/
theorem hydro_of_cutMoment_one' (_hα : 0 < M.α) (hd : 3 * M.α < (M.d : ℝ))
    (hm1 : ∀ r : ℝ, 2 ≤ r → 1 ≤ (M.cutMoment 1 r).toReal)
    (htail : ∀ r : ℝ, 2 ≤ r → SingleClusterTail M r (M.cutMoment 1 r).toReal)
    (C₁ : ℝ) (hC₁ : 0 < C₁)
    (hm : ∀ᶠ r : ℝ in atTop, (M.cutMoment 1 r).toReal ≤ C₁ * r ^ M.α) :
    Hydro M := by
  obtain ⟨Bc, hBc, hball⟩ := exists_ball_ncard_bound M
  exact hydro_of_cutMoment_one M _hα hd Bc hBc hball hm1 htail C₁ hC₁ hm

end CaseOne

end PercLib.CriticalLRP

#print axioms PercLib.CriticalLRP.CaseOne.mr_isBigO_cutMoment_one
#print axioms PercLib.CriticalLRP.CaseOne.hydro_of_cutMoment_one'
