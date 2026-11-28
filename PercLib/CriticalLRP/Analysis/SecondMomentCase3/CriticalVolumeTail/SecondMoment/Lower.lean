/-
Second-moment lower bounds for the critical cluster-volume tail.

Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Ultramath swarm `smwzt36y2`, member `m3`, direction `d7`.
Production review base `175f10881a6efbf55f4e6e67ec6c508ba91ef5e0`.

Source: Hutchcroft, *Critical long-range percolation I*, arXiv:2508.18807v1.

* Theorem I.1.6, (I.1.7), p. 10: the critical cluster-volume tail satisfies
  `P_{β_c}(|K| ≥ n) ∼ (α/β_c) √(2/(π A)) · n^{-1/2}`.
* Remark I.3.4, p. 31: `P_{β_c}(|K| ≥ Ê_{β_c,r}|K|) ≍ r^α / Ê_{β_c,r}|K|`, where
  `Ê_{β_c,r}|K| = E_{β_c,r}|K|² / E_{β_c,r}|K|`.

The production packets `CriticalVolumeTail` and `CriticalVolumeTail.SecondMoment` record the
*upper* half of the second-moment method: Markov at the second moment gives the per-radius
envelope `P_{β_c,r}(|K| ≥ n) ≤ (E_{β_c,r}|K|²)^{1/4} / √n`, and the cited leaf
`SourceModelData.CriticalVolumeTail` is not derived from it.

This file supplies the complementary *lower* half, and nothing else.

## §1 The Paley--Zygmund truncation inequality

For a probability measure `μ`, a measurable `X : Ω → ℝ≥0∞` and a threshold `t`,
`(∫⁻ X - t)² ≤ μ{X ≥ t} · ∫⁻ X²` (`sq_tsub_ofReal_le_meas_mul_lintegral_sq`).  When `X` is
additionally `ℕ`-valued and `n ≥ 1`, the sharper event `{X ≥ n}` may be used
(`sq_tsub_one_le_meas_mul_lintegral_sq`): on `{X < n}` one has `X ≤ n - 1`, not merely `X ≤ n`.
Both are consequences of Cauchy--Schwarz (`sq_lintegral_mul_le`).

## §2 The model statement

Applied to `M.cutLaw r` and `clusterVol · 0` this gives, for finite cutoff moments,
`P_{β_c,r}(|K_0| ≥ n) ≥ (E_{β_c,r}|K| - (n-1))² / E_{β_c,r}|K|²`
(`cutLaw_tail_ge_secondMoment`), the explicit `n^{-1}` consequence
`2n ≤ E|K|` and `E|K|² ≤ C n³` imply `P ≥ 1/(C n)` (`cutLaw_tail_ge_inv`), the mean-scale form
`P_{β_c,r}(|K_0| ≥ E|K|/2) ≥ (E|K|)² / (4 E|K|²)` (`cutLaw_tail_ge_half_mean`), and the same
bounds for the *uncut* critical law, using the already-proved cutoff-to-uncut domination
(`criticalLaw_tail_ge_inv`, `criticalLaw_tail_ge_half_mean`).

## §3 From the moment asymptotics to a critical-tail lower bound

`exists_tailProb_ge_inv_of_moment_asymptotics` takes as hypothesis exactly the two asymptotic
relations `E_{β_c,r}|K| ∼ κ r^α` and `E_{β_c,r}|K|² ∼ κ' r^{3α}` with positive `κ, κ'` -- the
`p = 1, 2` cases of (I.1.6), with `κ = α/β_c` and `κ' = A (α/β_c)` in the `I16rhs`
normalization -- and produces
`∃ C > 0, ∀ᶠ n, 1/(C n) ≤ P_{β_c}(|K_0| ≥ n)`, with the explicit constant `C = 128 κ'/κ³`.
No inverse of `r ↦ E_{β_c,r}|K|` is needed: the radius is chosen explicitly as
`r_n = (4n/κ)^{1/α}`, so that `κ r_n^α = 4n` *identically*.  The corollary
`exists_tailProb_ge_inv_of_I16` restates this directly in the frozen `I16rhs` normalization
with the paper's constant `A` (`Audit.I16rhs_one`, `Audit.I16rhs_two`), giving
`C = 128 A (β_c/α)²`.

## §4 Sharpness

`twoAtom_sharpness` records that the truncation inequality is attained up to the factor `8` by the
two-point law `P(X = M) = p`, `P(X = 1) = 1 - p`, for which `P(X ≥ n) = p`.  Hence no inequality
`P(X ≥ n) ≥ c ((E X - (n-1))²/E X²)` with `c > 8` holds for all `ℕ`-valued `X ≥ 1`: the
`n^{-1}` rate of `cutLaw_tail_ge_inv` is the best that two moments can give.

## What this does and does not establish

The moment asymptotics (I.1.6) at `p = 1, 2` give `E_{β_c,r}|K| ≍ r^α` and
`E_{β_c,r}|K|² ≍ r^{3α}`, i.e. `E|K|² ≍ (E|K|)³` with `n`-independent constants.  At the mean
scale `n ≍ E_{β_c,r}|K|` the inequalities above therefore yield a genuine, `r`-independent
`n^{-1}` lower bound for the critical tail.  This is *one power of `n` weaker* than the
`n^{-1/2}` of (I.1.7), and no choice of threshold in these two lemmas can close the gap: at any
scale above the mean the truncation step is vacuous.  The `n^{-1/2}` rate needs the full moment
sequence and a Tauberian argument (Section I.3.2), not second moments alone.  In particular this
file proves neither direction of `SourceModelData.CriticalVolumeTail`.
-/
module

public import PercLib.CriticalLRP.Analysis.SecondMomentCase3.CriticalVolumeTail.SecondMoment.Defs
public import PercLib.CriticalLRP.MomentMonotonicity.SourceModelMoments
public import PercLib.CriticalLRP.Orchestration.SourceFidelity.Defs
public import Mathlib.MeasureTheory.Integral.MeanInequalities

/-!
# Second-moment lower bounds for the critical cluster-volume tail

Paley--Zygmund truncation inequalities (`sq_lintegral_mul_le`,
`sq_tsub_one_le_meas_mul_lintegral_sq`, `sq_tsub_ofReal_le_meas_mul_lintegral_sq`) and their
cluster-volume consequences: the per-radius lower bound
`P_{β_c,r}(|K_0| ≥ n) ≥ (E_{β_c,r}|K| - (n-1))² / E_{β_c,r}|K|²`, its `n^{-1}` corollary, the
mean-scale form, the extension to the uncut critical law, and a conditional application of the
`p = 1, 2` moment asymptotics (Theorem I.1.6) yielding `P_{β_c}(|K_0| ≥ n) ≥ 1/(C n)` eventually.
The header comment above records the source passages and the precise scope.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.hashCommand false

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace PercLib.CriticalLRP.Analysis.Route3

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : Ω → ℝ≥0∞}

/-! ## §1 The Paley--Zygmund truncation inequality -/

/-- **Cauchy--Schwarz for `lintegral`, in squared form.** -/
theorem sq_lintegral_mul_le (f g : Ω → ℝ≥0∞) (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    (∫⁻ ω, (f * g) ω ∂μ) ^ 2
      ≤ (∫⁻ ω, f ω ^ 2 ∂μ) * (∫⁻ ω, g ω ^ 2 ∂μ) := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ (p := 2) (q := 2)
    (Real.HolderConjugate.two_two) hf hg
  simp only [Pi.mul_apply] at h
  calc (∫⁻ ω, f ω * g ω ∂μ) ^ 2
      ≤ ((∫⁻ ω, f ω ^ 2 ∂μ) ^ ((1 : ℝ) / 2)
          * (∫⁻ ω, g ω ^ 2 ∂μ) ^ ((1 : ℝ) / 2)) ^ 2 :=
        pow_le_pow_left' h 2
    _ = (∫⁻ ω, f ω ^ 2 ∂μ) * (∫⁻ ω, g ω ^ 2 ∂μ) := by
        rw [mul_pow]
        congr 1
        · rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
          norm_num
        · rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
          norm_num

/-- **Paley--Zygmund truncation at an integer threshold.**  For a probability measure and an
`ℕ`-valued `X` (`X = ⊤` allowed), `(∫⁻ X - (n-1))² ≤ μ{X ≥ n} · ∫⁻ X²` for `n ≥ 1`.
The integer-valued hypothesis is what upgrades `X < n` to `X ≤ n - 1` off the event. -/
theorem sq_tsub_one_le_meas_mul_lintegral_sq [IsProbabilityMeasure μ]
    (hX : Measurable X)
    (hint : ∀ ω, X ω = ⊤ ∨ ∃ m : ℕ, X ω = (m : ℝ≥0∞)) {n : ℕ} (hn : 1 ≤ n) :
    (∫⁻ ω, X ω ∂μ - ((n : ℝ≥0∞) - 1)) ^ 2
      ≤ μ {ω | (n : ℝ≥0∞) ≤ X ω} * ∫⁻ ω, X ω ^ 2 ∂μ := by
  classical
  set A : Set Ω := {ω | (n : ℝ≥0∞) ≤ X ω} with hAdef
  have hAm : MeasurableSet A := hX measurableSet_Ici
  have hbound : ∀ ω ∈ Aᶜ, X ω ≤ (n : ℝ≥0∞) - 1 := by
    intro ω hω
    have hnot : ¬ ((n : ℝ≥0∞) ≤ X ω) := by simpa [hAdef] using hω
    have hlt : X ω < (n : ℝ≥0∞) := not_le.1 hnot
    rcases hint ω with htop | ⟨m, hm⟩
    · rw [htop] at hlt
      exact absurd hlt (not_lt.2 le_top)
    · rw [hm] at hlt ⊢
      have hmn : m < n := by exact_mod_cast hlt
      have hcast : ((n - 1 : ℕ) : ℝ≥0∞) = (n : ℝ≥0∞) - 1 := by
        cases n with
        | zero => omega
        | succ k => simp
      rw [← hcast]
      exact_mod_cast Nat.le_sub_one_of_lt hmn
  have hcompl : ∫⁻ ω in Aᶜ, X ω ∂μ ≤ (n : ℝ≥0∞) - 1 := by
    calc ∫⁻ ω in Aᶜ, X ω ∂μ = ∫⁻ ω, Aᶜ.indicator X ω ∂μ :=
          (lintegral_indicator hAm.compl X).symm
      _ ≤ ∫⁻ _ω, ((n : ℝ≥0∞) - 1) ∂μ := by
          refine lintegral_mono fun ω => ?_
          by_cases hω : ω ∈ Aᶜ
          · rw [Set.indicator_of_mem hω]; exact hbound ω hω
          · rw [Set.indicator_of_notMem hω]; exact zero_le
      _ = (n : ℝ≥0∞) - 1 := by
          rw [lintegral_const, measure_univ, mul_one]
  have hstep : ∫⁻ ω, X ω ∂μ ≤ (∫⁻ ω in A, X ω ∂μ) + ((n : ℝ≥0∞) - 1) := by
    rw [← lintegral_add_compl (μ := μ) (fun ω => X ω) hAm]
    exact add_le_add (le_refl _) hcompl
  have hCS : (∫⁻ ω in A, X ω ∂μ) ^ 2 ≤ μ A * ∫⁻ ω, X ω ^ 2 ∂μ := by
    have hind : ∫⁻ ω in A, X ω ∂μ
        = ∫⁻ ω, X ω * A.indicator (fun _ => (1 : ℝ≥0∞)) ω ∂μ := by
      rw [← lintegral_indicator hAm X]
      refine lintegral_congr fun ω => ?_
      by_cases hω : ω ∈ A <;> simp [Set.indicator_of_mem, hω]
    rw [hind]
    have hg : AEMeasurable (A.indicator (fun _ => (1 : ℝ≥0∞))) μ :=
      aemeasurable_const.indicator hAm
    have h := sq_lintegral_mul_le (μ := μ) X (A.indicator fun _ => (1 : ℝ≥0∞))
      hX.aemeasurable hg
    have hsq : ∫⁻ ω, A.indicator (fun _ => (1 : ℝ≥0∞)) ω ^ 2 ∂μ = μ A := by
      have hfun : (fun ω => A.indicator (fun _ => (1 : ℝ≥0∞)) ω ^ 2)
          = A.indicator (fun _ => (1 : ℝ≥0∞)) := by
        funext ω
        by_cases hω : ω ∈ A <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, hω]
      rw [hfun]
      exact lintegral_indicator_one hAm
    rw [hsq] at h
    calc (∫⁻ ω, X ω * A.indicator (fun _ => (1 : ℝ≥0∞)) ω ∂μ) ^ 2
        ≤ (∫⁻ ω, X ω ^ 2 ∂μ) * μ A := h
      _ = μ A * ∫⁻ ω, X ω ^ 2 ∂μ := mul_comm _ _
  calc (∫⁻ ω, X ω ∂μ - ((n : ℝ≥0∞) - 1)) ^ 2
      ≤ (∫⁻ ω in A, X ω ∂μ) ^ 2 := by
        refine pow_le_pow_left' ?_ 2
        rw [tsub_le_iff_right]
        exact hstep
    _ ≤ μ A * ∫⁻ ω, X ω ^ 2 ∂μ := hCS

/-- **Paley--Zygmund truncation at a real threshold.**  For a probability measure and any real
`t`, `(∫⁻ X - t)² ≤ μ{X ≥ t} · ∫⁻ X²`.  No integrality of `X` is needed: off the event
`{X ≥ t}` one has `X ≤ t` pointwise. -/
theorem sq_tsub_ofReal_le_meas_mul_lintegral_sq [IsProbabilityMeasure μ]
    (hX : Measurable X) (t : ℝ) :
    (∫⁻ ω, X ω ∂μ - ENNReal.ofReal t) ^ 2
      ≤ μ {ω | ENNReal.ofReal t ≤ X ω} * ∫⁻ ω, X ω ^ 2 ∂μ := by
  classical
  set A : Set Ω := {ω | ENNReal.ofReal t ≤ X ω} with hAdef
  have hAm : MeasurableSet A := hX measurableSet_Ici
  have hbound : ∀ ω ∈ Aᶜ, X ω ≤ ENNReal.ofReal t := by
    intro ω hω
    have hnot : ¬ (ENNReal.ofReal t ≤ X ω) := by simpa [hAdef] using hω
    exact le_of_lt (not_le.1 hnot)
  have hcompl : ∫⁻ ω in Aᶜ, X ω ∂μ ≤ ENNReal.ofReal t := by
    calc ∫⁻ ω in Aᶜ, X ω ∂μ = ∫⁻ ω, Aᶜ.indicator X ω ∂μ :=
          (lintegral_indicator hAm.compl X).symm
      _ ≤ ∫⁻ _ω, ENNReal.ofReal t ∂μ := by
          refine lintegral_mono fun ω => ?_
          by_cases hω : ω ∈ Aᶜ
          · rw [Set.indicator_of_mem hω]; exact hbound ω hω
          · rw [Set.indicator_of_notMem hω]; exact zero_le
      _ = ENNReal.ofReal t := by
          rw [lintegral_const, measure_univ, mul_one]
  have hstep : ∫⁻ ω, X ω ∂μ ≤ (∫⁻ ω in A, X ω ∂μ) + ENNReal.ofReal t := by
    rw [← lintegral_add_compl (μ := μ) (fun ω => X ω) hAm]
    exact add_le_add (le_refl _) hcompl
  have hCS : (∫⁻ ω in A, X ω ∂μ) ^ 2 ≤ μ A * ∫⁻ ω, X ω ^ 2 ∂μ := by
    have hind : ∫⁻ ω in A, X ω ∂μ
        = ∫⁻ ω, X ω * A.indicator (fun _ => (1 : ℝ≥0∞)) ω ∂μ := by
      rw [← lintegral_indicator hAm X]
      refine lintegral_congr fun ω => ?_
      by_cases hω : ω ∈ A <;> simp [Set.indicator_of_mem, hω]
    rw [hind]
    have hg : AEMeasurable (A.indicator (fun _ => (1 : ℝ≥0∞))) μ :=
      aemeasurable_const.indicator hAm
    have h := sq_lintegral_mul_le (μ := μ) X (A.indicator fun _ => (1 : ℝ≥0∞))
      hX.aemeasurable hg
    have hsq : ∫⁻ ω, A.indicator (fun _ => (1 : ℝ≥0∞)) ω ^ 2 ∂μ = μ A := by
      have hfun : (fun ω => A.indicator (fun _ => (1 : ℝ≥0∞)) ω ^ 2)
          = A.indicator (fun _ => (1 : ℝ≥0∞)) := by
        funext ω
        by_cases hω : ω ∈ A <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, hω]
      rw [hfun]
      exact lintegral_indicator_one hAm
    rw [hsq] at h
    calc (∫⁻ ω, X ω * A.indicator (fun _ => (1 : ℝ≥0∞)) ω ∂μ) ^ 2
        ≤ (∫⁻ ω, X ω ^ 2 ∂μ) * μ A := h
      _ = μ A * ∫⁻ ω, X ω ^ 2 ∂μ := mul_comm _ _
  calc (∫⁻ ω, X ω ∂μ - ENNReal.ofReal t) ^ 2
      ≤ (∫⁻ ω in A, X ω ∂μ) ^ 2 := by
        refine pow_le_pow_left' ?_ 2
        rw [tsub_le_iff_right]
        exact hstep
    _ ≤ μ A * ∫⁻ ω, X ω ^ 2 ∂μ := hCS

end PercLib.CriticalLRP.Analysis.Route3

namespace PercLib.CriticalLRP.Orchestration.SourceModelData

variable (M : SourceModelData)

/-! ## §2 The model statements -/

/-- **The truncation inequality at the cutoff law.** -/
theorem sq_cutMoment_sub_le (r : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    (M.cutMoment 1 r - ((n : ℝ≥0∞) - 1)) ^ 2
      ≤ M.cutLaw r {ω : Config M.V | (n : ℝ≥0∞) ≤ clusterVol ω (0 : M.V)}
        * M.cutMoment 2 r := by
  have h := PercLib.CriticalLRP.Analysis.Route3.sq_tsub_one_le_meas_mul_lintegral_sq
    (μ := M.cutLaw r) (X := fun ω => clusterVol ω (0 : M.V))
    (measurable_clusterVol 0) (fun ω => clusterVol_eq_top_or_nat ω 0) hn
  simpa [SourceModelData.cutMoment, pow_one] using h

/-- `ofReal (n - 1) = (n : ℝ≥0∞) - 1` for natural `n` (valid at `n = 0` too). -/
theorem ofReal_natCast_sub_one {n : ℕ} :
    ENNReal.ofReal ((n : ℝ) - 1) = (n : ℝ≥0∞) - 1 := by
  rw [ENNReal.ofReal_sub _ (by norm_num : (0 : ℝ) ≤ 1), ENNReal.ofReal_natCast]
  norm_num

/-- **The second-moment lower bound on the cutoff tail.**  For `n ≥ 1`, finite first and second
cutoff moments, and `n - 1 ≤ E_{β_c,r}|K|`,
`P_{β_c,r}(|K_0| ≥ n) ≥ (E_{β_c,r}|K| - (n-1))² / E_{β_c,r}|K|²`, in square-root form. -/
theorem cutLaw_tail_ge_secondMoment (r : ℝ) {n : ℕ} (hn : 1 ≤ n)
    (h1 : M.cutMoment 1 r ≠ ⊤) (h2 : M.cutMoment 2 r ≠ ⊤)
    (hge : ((n : ℝ) - 1) ≤ (M.cutMoment 1 r).toReal) :
    (M.cutMoment 1 r).toReal - ((n : ℝ) - 1)
      ≤ Real.sqrt
          ((M.cutLaw r {ω : Config M.V | (n : ℝ≥0∞) ≤ clusterVol ω (0 : M.V)}).toReal
            * (M.cutMoment 2 r).toReal) := by
  set P : ℝ≥0∞ := M.cutLaw r {ω : Config M.V | (n : ℝ≥0∞) ≤ clusterVol ω (0 : M.V)}
    with hPdef
  have hb : ((n : ℝ≥0∞) - 1) ≤ M.cutMoment 1 r := by
    rw [← ofReal_natCast_sub_one, ENNReal.ofReal_le_iff_le_toReal h1]
    exact hge
  have h := M.sq_cutMoment_sub_le r hn
  have hPtop : P ≠ ⊤ := by
    refine ne_top_of_le_ne_top ENNReal.one_ne_top ?_
    rw [hPdef]
    calc M.cutLaw r {ω : Config M.V | (n : ℝ≥0∞) ≤ clusterVol ω (0 : M.V)}
        ≤ M.cutLaw r Set.univ := measure_mono (Set.subset_univ _)
      _ = 1 := measure_univ
  have htop : P * M.cutMoment 2 r ≠ ⊤ := ENNReal.mul_ne_top hPtop h2
  have hle := ENNReal.toReal_mono htop h
  rw [ENNReal.toReal_pow, ENNReal.toReal_mul, ENNReal.toReal_sub_of_le hb h1] at hle
  have hbtr : (((n : ℝ≥0∞) - 1)).toReal = (n : ℝ) - 1 := by
    rw [← ofReal_natCast_sub_one, ENNReal.toReal_ofReal (by
      have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      linarith)]
  rw [hbtr] at hle
  have hx0 : 0 ≤ (M.cutMoment 1 r).toReal - ((n : ℝ) - 1) := by linarith
  have hy0 : 0 ≤ P.toReal * (M.cutMoment 2 r).toReal := by positivity
  exact (Real.le_sqrt hx0 hy0).2 hle

/-- **The cutoff second moment is at least one** (finiteness assumed). -/
theorem one_le_cutMoment_two (r : ℝ) (h2 : M.cutMoment 2 r ≠ ⊤) :
    1 ≤ (M.cutMoment 2 r).toReal := by
  have h : (1 : ℝ≥0∞) ≤ M.cutMoment 2 r := by
    calc (1 : ℝ≥0∞) = ∫⁻ _ω : Config M.V, (1 : ℝ≥0∞) ∂(M.cutLaw r) := by simp
      _ ≤ ∫⁻ ω, clusterVol ω (0 : M.V) ^ 2 ∂(M.cutLaw r) := by
          refine lintegral_mono fun ω => ?_
          have h1 := one_le_clusterVol ω (0 : M.V)
          simpa using pow_le_pow_left' h1 2
  calc (1 : ℝ) = ((1 : ℝ≥0∞)).toReal := by simp
    _ ≤ (M.cutMoment 2 r).toReal := ENNReal.toReal_mono h2 h

/-- **The `n^{-1}` lower bound on the cutoff tail** from two moment bounds at one radius: if
`E_{β_c,r}|K| ≥ 2n` and `E_{β_c,r}|K|² ≤ C n³` then `P_{β_c,r}(|K_0| ≥ n) ≥ 1/(C n)`. -/
theorem cutLaw_tail_ge_inv {r : ℝ} {n : ℕ} (hn : 1 ≤ n) {C : ℝ} (hC : 0 < C)
    (h1 : M.cutMoment 1 r ≠ ⊤) (h2 : M.cutMoment 2 r ≠ ⊤)
    (hm1 : 2 * (n : ℝ) ≤ (M.cutMoment 1 r).toReal)
    (hm2 : (M.cutMoment 2 r).toReal ≤ C * (n : ℝ) ^ 3) :
    1 / (C * (n : ℝ))
      ≤ (M.cutLaw r {ω : Config M.V | (n : ℝ≥0∞) ≤ clusterVol ω (0 : M.V)}).toReal := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hmain := M.cutLaw_tail_ge_secondMoment r hn h1 h2 (by linarith)
  set P : ℝ := (M.cutLaw r {ω : Config M.V | (n : ℝ≥0∞) ≤ clusterVol ω (0 : M.V)}).toReal
    with hPdef
  have hy0 : 0 ≤ P * (M.cutMoment 2 r).toReal := by positivity
  have hx0 : 0 ≤ (n : ℝ) + 1 := by positivity
  have hle : (n : ℝ) + 1 ≤ Real.sqrt (P * (M.cutMoment 2 r).toReal) := by
    refine le_trans ?_ hmain
    linarith
  have hsq : ((n : ℝ) + 1) ^ 2 ≤ P * (M.cutMoment 2 r).toReal :=
    (Real.le_sqrt hx0 hy0).1 hle
  have hm2pos : 0 < (M.cutMoment 2 r).toReal := by
    have := M.one_le_cutMoment_two r h2
    linarith
  have hP : ((n : ℝ) + 1) ^ 2 / (M.cutMoment 2 r).toReal ≤ P := by
    rw [div_le_iff₀ hm2pos]
    linarith [hsq]
  have hstep1 : 1 / (C * (n : ℝ)) ≤ ((n : ℝ) + 1) ^ 2 / (C * (n : ℝ) ^ 3) := by
    have hd : (0 : ℝ) < C * (n : ℝ) ^ 3 := by positivity
    have h1 : (1 : ℝ) / (C * (n : ℝ)) = (n : ℝ) ^ 2 / (C * (n : ℝ) ^ 3) := by
      field_simp
    rw [h1]
    exact div_le_div_of_nonneg_right (by nlinarith : (n : ℝ) ^ 2 ≤ ((n : ℝ) + 1) ^ 2) hd.le
  have hstep2 : ((n : ℝ) + 1) ^ 2 / (C * (n : ℝ) ^ 3)
      ≤ ((n : ℝ) + 1) ^ 2 / (M.cutMoment 2 r).toReal :=
    div_le_div_of_nonneg_left (by positivity) hm2pos hm2
  rw [hPdef]
  linarith

/-! ### From the cutoff law to the uncut critical law -/

/-- The cluster-volume tail event is increasing in the edge configuration. -/
theorem isIncreasing_clusterVol_ge_nat (n : ℕ) :
    IsIncreasing {ω : Config M.V | (n : ℝ≥0∞) ≤ clusterVol ω (0 : M.V)} := by
  intro ω ω' h hω
  exact le_trans hω (clusterVol_mono (fun e he => h he) (0 : M.V))

/-- The real-threshold cluster-volume tail event is increasing as well. -/
theorem isIncreasing_clusterVol_ge_ofReal (t : ℝ) :
    IsIncreasing {ω : Config M.V | ENNReal.ofReal t ≤ clusterVol ω (0 : M.V)} := by
  intro ω ω' h hω
  exact le_trans hω (clusterVol_mono (fun e he => h he) (0 : M.V))

/-- **Cutoff-to-uncut domination at a real threshold.** -/
theorem cutLaw_tail_le_criticalLaw_ofReal (r : ℝ) (hr : 0 ≤ r) (t : ℝ) :
    M.cutLaw r {ω : Config M.V | ENNReal.ofReal t ≤ clusterVol ω (0 : M.V)}
      ≤ M.criticalLaw {ω : Config M.V | ENNReal.ofReal t ≤ clusterVol ω (0 : M.V)} := by
  have h := (M.cutoff_mono_beta_and_le_uncut (β := M.betaCrit) (γ := M.betaCrit)
    le_rfl hr).1 {ω : Config M.V | ENNReal.ofReal t ≤ clusterVol ω (0 : M.V)}
    ((measurable_clusterVol (0 : M.V)) measurableSet_Ici)
    (M.isIncreasing_clusterVol_ge_ofReal t)
  simpa [SourceModelData.cutLaw, SourceModelData.criticalLaw] using h.2

/-- **The cutoff law is dominated by the uncut critical law** on the cluster-volume tail. -/
theorem cutLaw_tail_le_criticalLaw_of_nonneg (r : ℝ) (hr : 0 ≤ r) (n : ℕ) :
    M.cutLaw r {ω : Config M.V | (n : ℝ≥0∞) ≤ clusterVol ω (0 : M.V)}
      ≤ M.criticalLaw {ω : Config M.V | (n : ℝ≥0∞) ≤ clusterVol ω (0 : M.V)} := by
  have h := (M.cutoff_mono_beta_and_le_uncut (β := M.betaCrit) (γ := M.betaCrit)
    le_rfl hr).1 {ω : Config M.V | (n : ℝ≥0∞) ≤ clusterVol ω (0 : M.V)}
    ((measurable_clusterVol (0 : M.V)) measurableSet_Ici) (M.isIncreasing_clusterVol_ge_nat n)
  simpa [SourceModelData.cutLaw, SourceModelData.criticalLaw] using h.2

/-- **The `n^{-1}` lower bound for the uncut critical cluster-volume tail.** -/
theorem criticalLaw_tail_ge_inv {r : ℝ} (hr : 0 < r) {n : ℕ} (hn : 1 ≤ n) {C : ℝ}
    (hC : 0 < C) (h1 : M.cutMoment 1 r ≠ ⊤) (h2 : M.cutMoment 2 r ≠ ⊤)
    (hm1 : 2 * (n : ℝ) ≤ (M.cutMoment 1 r).toReal)
    (hm2 : (M.cutMoment 2 r).toReal ≤ C * (n : ℝ) ^ 3) :
    1 / (C * (n : ℝ))
      ≤ (M.criticalLaw {ω : Config M.V | (n : ℝ≥0∞) ≤ clusterVol ω (0 : M.V)}).toReal := by
  refine le_trans (M.cutLaw_tail_ge_inv hn hC h1 h2 hm1 hm2) ?_
  haveI : IsProbabilityMeasure M.criticalLaw :=
    inferInstanceAs (IsProbabilityMeasure (M.law M.betaCrit))
  have htop : M.criticalLaw {ω : Config M.V | (n : ℝ≥0∞) ≤ clusterVol ω (0 : M.V)} ≠ ⊤ := by
    refine ne_top_of_le_ne_top ENNReal.one_ne_top ?_
    calc M.criticalLaw {ω : Config M.V | (n : ℝ≥0∞) ≤ clusterVol ω (0 : M.V)}
        ≤ M.criticalLaw Set.univ := measure_mono (Set.subset_univ _)
      _ = 1 := measure_univ
  exact ENNReal.toReal_mono htop (M.cutLaw_tail_le_criticalLaw_of_nonneg r hr.le n)

/-- **Real-threshold truncation bound.**  For finite first and second cutoff moments and any
`t ≤ E_{β_c,r}|K|`, `P_{β_c,r}(|K_0| ≥ t) ≥ (E_{β_c,r}|K| - t)² / E_{β_c,r}|K|²`. -/
theorem cutLaw_tail_ge_ofReal (r : ℝ) {t : ℝ} (ht : 0 ≤ t) (h1 : M.cutMoment 1 r ≠ ⊤)
    (h2 : M.cutMoment 2 r ≠ ⊤) (hle : t ≤ (M.cutMoment 1 r).toReal) :
    (M.cutMoment 1 r).toReal - t
      ≤ Real.sqrt
          ((M.cutLaw r {ω : Config M.V | ENNReal.ofReal t ≤ clusterVol ω (0 : M.V)}).toReal
            * (M.cutMoment 2 r).toReal) := by
  set P : ℝ≥0∞ := M.cutLaw r {ω : Config M.V | ENNReal.ofReal t ≤ clusterVol ω (0 : M.V)}
    with hPdef
  have hb : ENNReal.ofReal t ≤ M.cutMoment 1 r := by
    rw [ENNReal.ofReal_le_iff_le_toReal h1]
    exact hle
  have h := PercLib.CriticalLRP.Analysis.Route3.sq_tsub_ofReal_le_meas_mul_lintegral_sq
    (μ := M.cutLaw r) (X := fun ω => clusterVol ω (0 : M.V)) (measurable_clusterVol 0) t
  have h' : (M.cutMoment 1 r - ENNReal.ofReal t) ^ 2
      ≤ M.cutLaw r {ω : Config M.V | ENNReal.ofReal t ≤ clusterVol ω (0 : M.V)}
        * M.cutMoment 2 r := by
    simpa [SourceModelData.cutMoment, pow_one] using h
  have hPtop : P ≠ ⊤ := by
    refine ne_top_of_le_ne_top ENNReal.one_ne_top ?_
    rw [hPdef]
    calc M.cutLaw r {ω : Config M.V | ENNReal.ofReal t ≤ clusterVol ω (0 : M.V)}
        ≤ M.cutLaw r Set.univ := measure_mono (Set.subset_univ _)
      _ = 1 := measure_univ
  have htop : P * M.cutMoment 2 r ≠ ⊤ := ENNReal.mul_ne_top hPtop h2
  have hle' := ENNReal.toReal_mono htop h'
  rw [ENNReal.toReal_pow, ENNReal.toReal_mul, ENNReal.toReal_sub_of_le hb h1,
    ENNReal.toReal_ofReal ht] at hle'
  have hx0 : 0 ≤ (M.cutMoment 1 r).toReal - t := by linarith
  have hy0 : 0 ≤ P.toReal * (M.cutMoment 2 r).toReal := by positivity
  exact (Real.le_sqrt hx0 hy0).2 hle'

/-- **The mean-scale lower bound.**  At half the mean cutoff cluster volume,
`P_{β_c,r}(|K_0| ≥ E|K|/2) ≥ E|K|² / (4 E|K|²)`; equivalently, writing
`Ê|K| = E|K|²/E|K|`, the tail is at least `E|K| / (4 Ê|K|)`.
This is the same shape as the source's size-biased estimate of Remark I.3.4, but at the mean
scale `E|K|/2` rather than at `Ê|K|`; it is a consequence of the first two moments alone. -/
theorem cutLaw_tail_ge_half_mean (r : ℝ) (h1 : M.cutMoment 1 r ≠ ⊤)
    (h2 : M.cutMoment 2 r ≠ ⊤) (h1pos : 0 < (M.cutMoment 1 r).toReal) :
    (M.cutMoment 1 r).toReal ^ 2 / (4 * (M.cutMoment 2 r).toReal)
      ≤ (M.cutLaw r {ω : Config M.V |
          ENNReal.ofReal ((M.cutMoment 1 r).toReal / 2) ≤ clusterVol ω (0 : M.V)}).toReal := by
  set m1 := (M.cutMoment 1 r).toReal with hm1
  set m2 := (M.cutMoment 2 r).toReal with hm2
  have hm1pos : 0 < m1 := h1pos
  have hm2pos : 0 < m2 := by
    have := M.one_le_cutMoment_two r h2
    rw [hm2]
    linarith
  have ht : 0 ≤ m1 / 2 := by positivity
  have hle : m1 / 2 ≤ m1 := by linarith
  have hmain := M.cutLaw_tail_ge_ofReal r ht h1 h2 hle
  set P : ℝ := (M.cutLaw r
    {ω : Config M.V | ENNReal.ofReal (m1 / 2) ≤ clusterVol ω (0 : M.V)}).toReal with hPdef
  have hy0 : 0 ≤ P * m2 := by positivity
  have hx0 : 0 ≤ m1 - m1 / 2 := by linarith
  have hsq : (m1 - m1 / 2) ^ 2 ≤ P * m2 := (Real.le_sqrt hx0 hy0).1 hmain
  have hkey : (m1 - m1 / 2) ^ 2 = m1 ^ 2 / 4 := by ring
  rw [hkey] at hsq
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < 4 * m2)]
  nlinarith [hsq]

/-- **The same mean-scale bound for the uncut critical law.** -/
theorem criticalLaw_tail_ge_half_mean {r : ℝ} (hr : 0 < r) (h1 : M.cutMoment 1 r ≠ ⊤)
    (h2 : M.cutMoment 2 r ≠ ⊤) (h1pos : 0 < (M.cutMoment 1 r).toReal) :
    (M.cutMoment 1 r).toReal ^ 2 / (4 * (M.cutMoment 2 r).toReal)
      ≤ (M.criticalLaw {ω : Config M.V |
          ENNReal.ofReal ((M.cutMoment 1 r).toReal / 2) ≤ clusterVol ω (0 : M.V)}).toReal := by
  refine le_trans (M.cutLaw_tail_ge_half_mean r h1 h2 h1pos) ?_
  haveI : IsProbabilityMeasure M.criticalLaw :=
    inferInstanceAs (IsProbabilityMeasure (M.law M.betaCrit))
  have htop : M.criticalLaw {ω : Config M.V |
      ENNReal.ofReal ((M.cutMoment 1 r).toReal / 2) ≤ clusterVol ω (0 : M.V)} ≠ ⊤ := by
    refine ne_top_of_le_ne_top ENNReal.one_ne_top ?_
    calc M.criticalLaw {ω : Config M.V |
          ENNReal.ofReal ((M.cutMoment 1 r).toReal / 2) ≤ clusterVol ω (0 : M.V)}
        ≤ M.criticalLaw Set.univ := measure_mono (Set.subset_univ _)
      _ = 1 := measure_univ
  refine ENNReal.toReal_mono htop ?_
  exact M.cutLaw_tail_le_criticalLaw_ofReal r hr.le ((M.cutMoment 1 r).toReal / 2)

/-- **Conditional `n^{-1}` lower bound from the two lowest moment asymptotics.**  Suppose that
the cutoff first and second moments satisfy the two asymptotic relations with positive constants
`κ` and `κ'`:
`E_{β_c,r}|K| ∼ κ r^α` and `E_{β_c,r}|K|² ∼ κ' r^{3α}`.
Then there is an explicit constant `C = 128 κ' / κ³` with
`P_{β_c}(|K_0| ≥ n) ≥ 1/(C n)` for all sufficiently large `n`.

In the normalization of Theorem I.1.6 one has `κ = α/β_c` and `κ' = A (α/β_c)`
(`I16rhs M A 1 r` and `I16rhs M A 2 r`), so this is a rigorous, one-power-weaker consequence of
the `p = 1, 2` cases of the source's moment asymptotics for the critical volume tail. -/
theorem exists_tailProb_ge_inv_of_moment_asymptotics (κ κ' : ℝ) (hκ : 0 < κ) (hκ' : 0 < κ')
    (h1 : Tendsto (fun r : ℝ => (M.cutMoment 1 r).toReal / (κ * r ^ M.α)) atTop (𝓝 1))
    (h2 : Tendsto (fun r : ℝ => (M.cutMoment 2 r).toReal / (κ' * r ^ (3 * M.α)))
      atTop (𝓝 1)) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop, 1 / (C * (n : ℝ)) ≤ M.tailProb n := by
  have hα : 0 < M.α := M.hα
  set C : ℝ := 128 * κ' / κ ^ 3 with hCdef
  have hC : 0 < C := by positivity
  refine ⟨C, hC, ?_⟩
  set rr : ℕ → ℝ := fun n => (4 * (n : ℝ) / κ) ^ (1 / M.α) with hrdef
  have hr : Tendsto rr atTop atTop := by
    have h2' : Tendsto (fun n : ℕ => 4 * (n : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num)
    have h3 : Tendsto (fun n : ℕ => 4 * (n : ℝ) / κ) atTop atTop := h2'.atTop_div_const hκ
    exact (tendsto_rpow_atTop (by positivity : (0 : ℝ) < 1 / M.α)).comp h3
  have h1c := h1.comp hr
  have h2c := h2.comp hr
  have hrpow1 : ∀ n : ℕ, (rr n) ^ M.α = 4 * (n : ℝ) / κ := by
    intro n
    rw [hrdef]
    rw [← Real.rpow_mul (by positivity)]
    have h : (1 / M.α) * M.α = 1 := by field_simp
    rw [h, Real.rpow_one]
  have hrpow3 : ∀ n : ℕ, (rr n) ^ (3 * M.α) = (4 * (n : ℝ) / κ) ^ 3 := by
    intro n
    rw [hrdef]
    rw [← Real.rpow_mul (by positivity)]
    have h : (1 / M.α) * (3 * M.α) = 3 := by field_simp
    rw [h]
    exact Real.rpow_natCast _ 3
  have hev1 : ∀ᶠ n : ℕ in atTop,
      (1 / 2 : ℝ) < (M.cutMoment 1 (rr n)).toReal / (κ * (rr n) ^ M.α) :=
    h1c.eventually (eventually_gt_nhds (by norm_num))
  have hev2a : ∀ᶠ n : ℕ in atTop,
      (1 / 2 : ℝ) < (M.cutMoment 2 (rr n)).toReal / (κ' * (rr n) ^ (3 * M.α)) :=
    h2c.eventually (eventually_gt_nhds (by norm_num))
  have hev2b : ∀ᶠ n : ℕ in atTop,
      (M.cutMoment 2 (rr n)).toReal / (κ' * (rr n) ^ (3 * M.α)) < 2 :=
    h2c.eventually (eventually_lt_nhds (by norm_num))
  filter_upwards [hev1, hev2a, hev2b, eventually_ge_atTop 1] with n hn1 hn2a hn2b hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hrpos : 0 < rr n := Real.rpow_pos_of_pos (by positivity) _
  have hm1 : 2 * (n : ℝ) ≤ (M.cutMoment 1 (rr n)).toReal := by
    rw [hrpow1 n] at hn1
    have h4 : κ * (4 * (n : ℝ) / κ) = 4 * (n : ℝ) := by field_simp
    rw [h4, lt_div_iff₀ (by positivity)] at hn1
    linarith
  have hm2 : (M.cutMoment 2 (rr n)).toReal ≤ C * (n : ℝ) ^ 3 := by
    rw [hrpow3 n] at hn2a hn2b
    have hden : (0 : ℝ) < κ' * (4 * (n : ℝ) / κ) ^ 3 := by positivity
    rw [div_lt_iff₀ hden] at hn2b
    have heq : 2 * (κ' * (4 * (n : ℝ) / κ) ^ 3) = C * (n : ℝ) ^ 3 := by
      rw [hCdef]
      field_simp
      ring
    rw [heq] at hn2b
    linarith
  have hfin1 : M.cutMoment 1 (rr n) ≠ ⊤ := by
    intro htop
    rw [htop] at hn1
    simp at hn1
    linarith
  have hfin2 : M.cutMoment 2 (rr n) ≠ ⊤ := by
    intro htop
    rw [htop] at hn2a
    simp at hn2a
    linarith
  have htail := M.criticalLaw_tail_ge_inv (r := rr n) hrpos hn hC hfin1 hfin2 hm1 hm2
  simpa [SourceModelData.tailProb, Measure.real] using htail

/-- **The same consequence, stated directly in the frozen `I16rhs` normalization of Theorem
I.1.6.**  With `κ = α/β_c` and `κ' = A (α/β_c)` one has `I16rhs M A 1 r = κ r^α` and
`I16rhs M A 2 r = κ' r^{3α}` (`I16rhs_one`, `I16rhs_two`), so the `p = 1, 2` cases of (I.1.6)
give `P_{β_c}(|K_0| ≥ n) ≥ 1/(C n)` eventually, with `C = 128 A (β_c/α)²`. -/
theorem exists_tailProb_ge_inv_of_I16 (A : ℝ) (hA : 0 < A)
    (hκ : 0 < M.α / (M.betaCrit : ℝ))
    (h1 : Tendsto (fun r : ℝ => (M.cutMoment 1 r).toReal / I16rhs M A 1 r) atTop (𝓝 1))
    (h2 : Tendsto (fun r : ℝ => (M.cutMoment 2 r).toReal / I16rhs M A 2 r) atTop (𝓝 1)) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop, 1 / (C * (n : ℝ)) ≤ M.tailProb n := by
  have h1' : Tendsto (fun r : ℝ =>
      (M.cutMoment 1 r).toReal / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) atTop (𝓝 1) := by
    refine h1.congr' ?_
    filter_upwards with r
    rw [Audit.I16rhs_one]
    norm_num
  have h2' : Tendsto (fun r : ℝ =>
      (M.cutMoment 2 r).toReal
        / ((A * (M.α / (M.betaCrit : ℝ))) * r ^ (3 * M.α))) atTop (𝓝 1) := by
    refine h2.congr' ?_
    filter_upwards with r
    rw [Audit.I16rhs_two]
    norm_num
  exact M.exists_tailProb_ge_inv_of_moment_asymptotics
    (M.α / (M.betaCrit : ℝ)) (A * (M.α / (M.betaCrit : ℝ))) hκ (by positivity) h1' h2'

/-- `I16rhs M A 1` is nonnegative when `A ≥ 0` and `α/β_c ≥ 0`. -/
theorem I16rhs_one_nonneg {A : ℝ} (_hA : 0 ≤ A) (hκ : 0 ≤ M.α / (M.betaCrit : ℝ)) {r : ℝ}
    (hr : 0 ≤ r) : 0 ≤ I16rhs M A 1 r := by
  rw [Audit.I16rhs_one]
  exact mul_nonneg hκ (Real.rpow_nonneg hr _)

/-- `I16rhs M A 2` is nonnegative when `A ≥ 0` and `α/β_c ≥ 0`. -/
theorem I16rhs_two_nonneg {A : ℝ} (hA : 0 ≤ A) (hκ : 0 ≤ M.α / (M.betaCrit : ℝ)) {r : ℝ}
    (hr : 0 ≤ r) : 0 ≤ I16rhs M A 2 r := by
  rw [Audit.I16rhs_two]
  exact mul_nonneg (mul_nonneg hA hκ) (Real.rpow_nonneg hr _)

/-- **The `I16rhs` consequence from the literal `ℝ≥0∞`-valued ratio form of (I.1.6).**  The frozen
anchor of Theorem I.1.6 states its moment asymptotics as
`Tendsto (fun r => M.cutMoment p r / ENNReal.ofReal (I16rhs M A p r)) atTop (𝓝 1)`; this version
takes exactly that shape at `p = 1, 2` and returns the `n^{-1}` critical-tail lower bound. -/
theorem exists_tailProb_ge_inv_of_I16_ennreal (A : ℝ) (hA : 0 < A)
    (hκ : 0 < M.α / (M.betaCrit : ℝ))
    (h1 : Tendsto (fun r : ℝ => M.cutMoment 1 r / ENNReal.ofReal (I16rhs M A 1 r))
      atTop (𝓝 1))
    (h2 : Tendsto (fun r : ℝ => M.cutMoment 2 r / ENNReal.ofReal (I16rhs M A 2 r))
      atTop (𝓝 1)) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop, 1 / (C * (n : ℝ)) ≤ M.tailProb n := by
  have h1r : Tendsto (fun r : ℝ => (M.cutMoment 1 r).toReal / I16rhs M A 1 r) atTop (𝓝 1) := by
    have h := (ENNReal.tendsto_toReal (a := 1) (by norm_num)).comp h1
    simp only [ENNReal.toReal_one] at h
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with r hr
    change (M.cutMoment 1 r / ENNReal.ofReal (I16rhs M A 1 r)).toReal
      = (M.cutMoment 1 r).toReal / I16rhs M A 1 r
    rw [ENNReal.toReal_div, ENNReal.toReal_ofReal (M.I16rhs_one_nonneg hA.le hκ.le hr)]
  have h2r : Tendsto (fun r : ℝ => (M.cutMoment 2 r).toReal / I16rhs M A 2 r) atTop (𝓝 1) := by
    have h := (ENNReal.tendsto_toReal (a := 1) (by norm_num)).comp h2
    simp only [ENNReal.toReal_one] at h
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with r hr
    change (M.cutMoment 2 r / ENNReal.ofReal (I16rhs M A 2 r)).toReal
      = (M.cutMoment 2 r).toReal / I16rhs M A 2 r
    rw [ENNReal.toReal_div, ENNReal.toReal_ofReal (M.I16rhs_two_nonneg hA.le hκ.le hr)]
  exact M.exists_tailProb_ge_inv_of_I16 A hA hκ h1r h2r

/-! ### Sharpness of the truncation inequality -/

/-- **The truncation inequality is sharp at the two-point law.**  Let `X` take the value `M > 0`
with probability `p` and the value `1` with probability `1 - p`; then `E X = 1 + p (M - 1)` and
`E X² = 1 + p (M² - 1)`, while `P(X ≥ n) = p` whenever `1 < n ≤ M`.  If `2n ≤ p M` (so the mean
is at least of order `n`) and `p M² ≥ 1`, then the truncation lower bound is at least `p/8`.
Consequently no inequality of the form
`P(X ≥ n) ≥ c ((E X - (n-1))² / E X²)` can hold for all `ℕ`-valued `X ≥ 1` with `c > 8`, and the
`n^{-1}` rate extracted in `cutLaw_tail_ge_inv` is the best that first and second moments give. -/
theorem twoAtom_sharpness {p M : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) {n : ℕ} (hn : 1 ≤ n)
    (hlo : 2 * (n : ℝ) ≤ p * M) (hM2 : 1 ≤ p * M ^ 2) :
    p / 8 ≤ (1 + p * (M - 1) - ((n : ℝ) - 1)) ^ 2 / (1 + p * (M ^ 2 - 1)) := by
  set A : ℝ := 1 + p * (M - 1) - ((n : ℝ) - 1) with hAdef
  set B : ℝ := 1 + p * (M ^ 2 - 1) with hBdef
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hA : p * M / 2 ≤ A := by
    rw [hAdef]
    nlinarith [hlo, hp1, hn1]
  have hpM : 0 ≤ p * M := by linarith
  have hA0 : 0 ≤ A := le_trans (by linarith) hA
  have hBpos : 0 < B := by
    rw [hBdef]
    nlinarith [hM2, hp1, hp]
  have hA2 : (p * M / 2) ^ 2 ≤ A ^ 2 := by
    have h0 : 0 ≤ p * M / 2 := by linarith
    exact pow_le_pow_left₀ h0 hA 2
  have hB : B ≤ 2 * (p * M ^ 2) := by
    rw [hBdef]
    nlinarith [hM2]
  rw [le_div_iff₀ hBpos]
  have hkey : p / 8 * (2 * (p * M ^ 2)) = (p * M / 2) ^ 2 := by ring
  nlinarith [hA2, hB, hBpos, hA0, hpM]

end PercLib.CriticalLRP.Orchestration.SourceModelData

#print axioms PercLib.CriticalLRP.Analysis.Route3.sq_lintegral_mul_le
#print axioms PercLib.CriticalLRP.Analysis.Route3.sq_tsub_one_le_meas_mul_lintegral_sq
#print axioms PercLib.CriticalLRP.Analysis.Route3.sq_tsub_ofReal_le_meas_mul_lintegral_sq
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.sq_cutMoment_sub_le
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.cutLaw_tail_ge_secondMoment
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.one_le_cutMoment_two
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.cutLaw_tail_ge_inv
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.cutLaw_tail_le_criticalLaw_of_nonneg
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.criticalLaw_tail_ge_inv
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.cutLaw_tail_ge_ofReal
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.cutLaw_tail_ge_half_mean
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.criticalLaw_tail_ge_half_mean
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.cutLaw_tail_le_criticalLaw_ofReal
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.exists_tailProb_ge_inv_of_I16
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.isIncreasing_clusterVol_ge_ofReal
#print axioms
  PercLib.CriticalLRP.Orchestration.SourceModelData.exists_tailProb_ge_inv_of_moment_asymptotics
#print axioms
  PercLib.CriticalLRP.Orchestration.SourceModelData.exists_tailProb_ge_inv_of_I16_ennreal
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.twoAtom_sharpness
