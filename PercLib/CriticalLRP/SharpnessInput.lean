/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
-/

/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
New proofs. Candidate file for swarm smwj6kwzx, member m1, direction d4.

# Two inputs of the sharpness chain of Lemma I.4.9

Source: T. Hutchcroft, *Critical long-range percolation I: High effective
dimension*, arXiv:2508.18807v1, Lemma I.4.9 (pp. 37-38) and the passage to
`β ↑ β_c` inside Proposition I.4.2.

`VolumeMoments.FirstMoment.first_moment_bound_all_beta` takes three model inputs
that are not proved in the library:

* `hmeet` -- left continuity in `β` of the cut-off first moment at each fixed `r`;
* `hbdd` / `hmin` -- the a priori ("sharpness") bound
  `E_{β,r}|K| ≤ (2α/β) r^α` for `r ≥ r₀(β)`.

This file proves two statements that remove or reduce those inputs.

* `tendsto_lintegral_clusterVol_nat`: for any monotone sequence of edge
  probabilities increasing to `q`, the expected cluster volume increases to
  that of `q` (the `ℕ`-indexed form, obtained from the library's
  `iSup_lintegral_clusterVol`).
* `tendsto_lintegral_clusterVol_Iio`: the same for a real parameter `β ↑ βc`,
  which is `hmeet`, and then `tendsto_lintegral_clusterVol_longRangeMeasure`
  for Bernoulli edge probabilities `1 - exp(-(β * J e))`, i.e. for every
  `longRangeMeasure J hJ β`.  No mean finiteness, no sharpness and no kernel
  regularity is assumed: the value `⊤` is allowed.
* `exists_eventual_rpow_bound_of_le`: a uniform bound `F r ≤ χ`, `χ ≠ ⊤`,
  gives the a priori bound `(F r).toReal ≤ (2α/β) r^α` for `r ≥ r₀`, with the
  explicit threshold `r₀ = max 1 ((χ * β / (2α)) ^ (1/α))`.  Applied to the
  cut-off first moment `F r = E_{β,r}|K_o|` and the uncut mean `χ = E_β|K_o|`
  this is exactly `hbdd`; `hmin` follows by taking the minimal such `r₀`.
  The remaining premise is the finiteness of the uncut mean itself, which this
  file does *not* prove.

No `sorry`, no `admit`, no `native_decide`, no custom axioms.
-/
module

public import PercLib.CriticalLRP.CutoffLimit
public import PercLib.CriticalLRP.CountableProduct.Marks

set_option autoImplicit true

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

@[expose] public section

open MeasureTheory Measure Filter Topology
open scoped ENNReal Topology

namespace PercLib.CriticalLRP

open PercLib.CriticalLRP.FiniteVolume CutoffKernel TreeExpansion PercLib.CriticalLRP.CutoffLimit

variable {V : Type*} [Countable V]

/-! ## `ℕ`-indexed monotone convergence of the expected cluster volume -/

/-- For a monotone sequence of edge laws `p n ↑ q`, the expected cluster volume
of the root `o` increases to the expected cluster volume under `q`.  This is the
`Tendsto` form of `iSup_lintegral_clusterVol`, with no finiteness hypothesis. -/
theorem tendsto_lintegral_clusterVol_nat {p : ℕ → Sym2 V → unitInterval}
    {q : Sym2 V → unitInterval}
    (hmono : ∀ (n : ℕ) (e : Sym2 V), p n e ≤ p (n + 1) e)
    (hlim : ∀ e : Sym2 V,
      Tendsto (fun n : ℕ => ((p n e : unitInterval) : ℝ)) atTop (𝓝 ((q e : unitInterval) : ℝ)))
    (o : V) :
    Tendsto (fun n : ℕ => ∫⁻ ω, clusterVol ω o ∂(edgeMeasure (p n))) atTop
      (𝓝 (∫⁻ ω, clusterVol ω o ∂(edgeMeasure q))) := by
  have hmonoF : Monotone fun n : ℕ => ∫⁻ ω, clusterVol ω o ∂(edgeMeasure (p n)) :=
    monotone_nat_of_le_succ fun n => lintegral_clusterVol_mono (fun e => hmono n e) o
  have h : Tendsto (fun n : ℕ => ∫⁻ ω, clusterVol ω o ∂(edgeMeasure (p n))) atTop
      (𝓝 (⨆ n, ∫⁻ ω, clusterVol ω o ∂(edgeMeasure (p n)))) := tendsto_atTop_iSup hmonoF
  rwa [iSup_lintegral_clusterVol hmono hlim o] at h

/-! ## Left continuity in the parameter `β` -/

/-- **Left continuity in the parameter of the expected cluster volume.**

Let `P β` be a family of edge laws, nondecreasing in `β` up to `βc`, with
`1 - exp`-type pointwise convergence at `βc` from below (only the values of the
probabilities are used).  Then the expected cluster volume of the root `o` is
left continuous at `βc`:

`E_{β,r}|K_o| → E_{βc,r}|K_o|` as `β ↑ βc`.

No finiteness, sharpness or kernel regularity hypothesis is used, and the value
`⊤` is allowed on both sides.  This is the `hmeet` input of
`VolumeMoments.FirstMoment.first_moment_bound_all_beta` in general form. -/
theorem tendsto_lintegral_clusterVol_Iio {P : ℝ → Sym2 V → unitInterval} {βc : ℝ}
    (hmono : ∀ ⦃β β' : ℝ⦄, β ≤ β' → β' ≤ βc → ∀ e : Sym2 V, P β e ≤ P β' e)
    (hcont : ∀ e : Sym2 V,
      Tendsto (fun β : ℝ => ((P β e : unitInterval) : ℝ)) (𝓝[<] βc)
        (𝓝 ((P βc e : unitInterval) : ℝ)))
    (o : V) :
    Tendsto (fun β : ℝ => ∫⁻ ω, clusterVol ω o ∂(edgeMeasure (P β))) (𝓝[<] βc)
      (𝓝 (∫⁻ ω, clusterVol ω o ∂(edgeMeasure (P βc)))) := by
  set G : ℝ → ℝ≥0∞ := fun β => ∫⁻ ω, clusterVol ω o ∂(edgeMeasure (P β)) with hG
  -- monotonicity of `G` up to `βc`
  have hGmono : ∀ ⦃β β' : ℝ⦄, β ≤ β' → β' ≤ βc → G β ≤ G β' :=
    fun β β' h1 h2 => lintegral_clusterVol_mono (fun e => hmono h1 h2 e) o
  have hGle : ∀ β, β ≤ βc → G β ≤ G βc := fun β hβ => hGmono hβ le_rfl
  -- the approximating sequence `βc - 1/(n+1)`
  set a : ℕ → ℝ := fun n => βc - 1 / ((n : ℝ) + 1) with ha
  have ha_lt : ∀ n, a n < βc := by
    intro n
    have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    simp only [ha]
    linarith
  have ha_mono : Monotone a := by
    refine monotone_nat_of_le_succ fun n => ?_
    have hle : 1 / ((n : ℝ) + 1 + 1) ≤ 1 / ((n : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by linarith)
    have hn : (((n + 1 : ℕ)) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
    simp only [ha, hn]
    linarith
  have ha_tendsto : Tendsto a atTop (𝓝[<] βc) := by
    have h1 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have h2 : Tendsto a atTop (𝓝 βc) := by
      have h : Tendsto (fun n : ℕ => βc - 1 / ((n : ℝ) + 1)) atTop (𝓝 (βc - 0)) :=
        tendsto_const_nhds.sub h1
      simpa [ha] using h
    exact tendsto_nhdsWithin_iff.mpr ⟨h2, Eventually.of_forall ha_lt⟩
  -- `ℕ`-indexed convergence along the sequence
  have hnat : Tendsto (fun n : ℕ => G (a n)) atTop (𝓝 (G βc)) := by
    have hm : ∀ (n : ℕ) (e : Sym2 V), P (a n) e ≤ P (a (n + 1)) e :=
      fun n e => hmono (ha_mono (Nat.le_succ n)) (le_of_lt (ha_lt _)) e
    have hl : ∀ e : Sym2 V,
        Tendsto (fun n : ℕ => ((P (a n) e : unitInterval) : ℝ)) atTop
          (𝓝 ((P βc e : unitInterval) : ℝ)) :=
      fun e => (hcont e).comp ha_tendsto
    simpa only [hG] using tendsto_lintegral_clusterVol_nat hm hl o
  -- hence `G βc` is the supremum over the sequence
  have hsup : G βc = ⨆ n : ℕ, G (a n) := by
    refine le_antisymm ?_ ?_
    · exact le_of_tendsto hnat (Eventually.of_forall fun n => le_iSup (fun n => G (a n)) n)
    · exact iSup_le fun n => hGle (a n) (le_of_lt (ha_lt n))
  refine tendsto_order.mpr ⟨?_, ?_⟩
  · intro b hb
    change b < G βc at hb
    rw [hsup] at hb
    obtain ⟨n, hn⟩ := lt_iSup_iff.mp hb
    have hmem : Set.Ici (a n) ∈ 𝓝[<] βc :=
      nhdsWithin_le_nhds (Ici_mem_nhds (ha_lt n))
    filter_upwards [hmem, self_mem_nhdsWithin] with β hβ hβlt
    exact lt_of_lt_of_le hn (hGmono hβ (le_of_lt hβlt))
  · intro b hb
    filter_upwards [self_mem_nhdsWithin] with β hβ
    exact lt_of_le_of_lt (hGle β (le_of_lt hβ)) hb

/-! ## The a priori ("sharpness") bound from a uniform first-moment bound -/

/-- **The a priori bound of Lemma I.4.9 from a uniform bound on the first moment.**

If `F r ≤ χ` for every `r` with `χ ≠ ⊤`, then for `r ≥ r₀ := max 1 ((χ β / (2α)) ^ (1/α))`
one has `(F r).toReal ≤ (2α/β) r^α`.  No monotonicity of `F` is needed: the bound is
compared with the constant `χ` and then with the increasing function `r ↦ (2α/β) r^α`.

Applied to the cut-off first moment `F r = E_{β,r}|K_o|` and the uncut mean
`χ = E_β|K_o|`, this is the source's a priori (sharpness) input `hbdd`: everything
reduces to `χ ≠ ⊤`. -/
theorem eventual_rpow_bound_of_le {F : ℝ → ℝ≥0∞} {χ : ℝ≥0∞} {α β : ℝ}
    (hα : 0 < α) (hβ : 0 < β) (hχ : χ ≠ ⊤) (hF : ∀ r : ℝ, F r ≤ χ) :
    ∀ r : ℝ, max 1 ((χ.toReal / (2 * α / β)) ^ (1 / α)) ≤ r →
      (F r).toReal ≤ (2 * α / β) * r ^ α := by
  have hc : 0 < 2 * α / β := by positivity
  set r₀ : ℝ := max 1 ((χ.toReal / (2 * α / β)) ^ (1 / α)) with hr₀
  have hr₀1 : (1 : ℝ) ≤ r₀ := le_max_left _ _
  have hr₀0 : (0 : ℝ) ≤ r₀ := le_trans zero_le_one hr₀1
  have hx0 : 0 ≤ χ.toReal / (2 * α / β) := by positivity
  have hkey : ((χ.toReal / (2 * α / β)) ^ (1 / α)) ^ α = χ.toReal / (2 * α / β) := by
    rw [← Real.rpow_mul hx0, show (1 / α) * α = 1 by field_simp, Real.rpow_one]
  have hmono : ((χ.toReal / (2 * α / β)) ^ (1 / α)) ^ α ≤ r₀ ^ α :=
    Real.rpow_le_rpow (by positivity) (le_max_right _ _) hα.le
  have hχle : χ.toReal ≤ (2 * α / β) * r₀ ^ α := by
    have h1 : (2 * α / β) * (((χ.toReal / (2 * α / β)) ^ (1 / α)) ^ α)
        = χ.toReal := by
      rw [hkey]
      field_simp
    rw [← h1]
    exact mul_le_mul_of_nonneg_left hmono hc.le
  intro r hr
  calc (F r).toReal ≤ χ.toReal := ENNReal.toReal_mono hχ (hF r)
    _ ≤ (2 * α / β) * r₀ ^ α := hχle
    _ ≤ (2 * α / β) * r ^ α :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hr₀0 hr hα.le) hc.le

/-- The existential form of `eventual_rpow_bound_of_le`. -/
theorem exists_eventual_rpow_bound_of_le {F : ℝ → ℝ≥0∞} {χ : ℝ≥0∞} {α β : ℝ}
    (hα : 0 < α) (hβ : 0 < β) (hχ : χ ≠ ⊤) (hF : ∀ r : ℝ, F r ≤ χ) :
    ∃ r₀ : ℝ, 1 ≤ r₀ ∧ ∀ r : ℝ, r₀ ≤ r → (F r).toReal ≤ (2 * α / β) * r ^ α :=
  ⟨_, le_max_left _ _, eventual_rpow_bound_of_le hα hβ hχ hF⟩

/-- **The source's minimal sharpness threshold is controlled by the mean.**

If `r₀` is admissible (`F r ≤ (2α/β) r^α` for all `r ≥ r₀`, `1 ≤ r₀`) and minimal
among the admissible thresholds, and `F r ≤ χ` with `χ ≠ ⊤`, then
`r₀ ≤ max 1 ((χ β / (2α)) ^ (1/α))`.  In particular `r₀(β)` in Lemma I.4.9 is
bounded by `(β E_β|K| / (2α)) ^ (1/α)` whenever the uncut mean is finite. -/
theorem le_of_forall_le_rpow {F : ℝ → ℝ≥0∞} {χ : ℝ≥0∞} {α β r₀ : ℝ}
    (hα : 0 < α) (hβ : 0 < β) (hχ : χ ≠ ⊤) (hF : ∀ r : ℝ, F r ≤ χ)
    (hr₀ : 1 ≤ r₀) (hbdd : ∀ r : ℝ, r₀ ≤ r → (F r).toReal ≤ (2 * α / β) * r ^ α)
    (hmin : ∀ b : ℝ, 1 ≤ b → (∀ r : ℝ, b ≤ r → (F r).toReal ≤ (2 * α / β) * r ^ α) →
      r₀ ≤ b) :
    r₀ ≤ max 1 ((χ.toReal / (2 * α / β)) ^ (1 / α)) := by
  exact hmin _ (le_max_left _ _) (eventual_rpow_bound_of_le (F := F) hα hβ hχ hF)

/-! ## The model-level form of the two inputs -/

/-- **`hmeet`: left continuity in `β` of the Bernoulli / `longRangeMeasure` first moment.**

For any nonnegative symmetric intensity `J` on the edges of `V` (in particular for the
uncut kernel `kernelJ K` or for any cut-off kernel `cutoffSymKernel K d r`), the expected
cluster volume of a root is left continuous in the parameter `β`:

`E_β|K_o| → E_{βc}|K_o|` as `β ↑ βc`, with `⊤` allowed. This is the `ℝ≥0∞`
counterpart of the `hmeet` premise of
`VolumeMoments.FirstMoment.first_moment_bound_all_beta`. Its `toReal` version below requires
finiteness of the endpoint mean, because `toReal ∞ = 0`. -/
theorem tendsto_lintegral_clusterVol_longRangeMeasure {J : Sym2 V → ℝ}
    (hJ : ∀ e : Sym2 V, 0 ≤ J e) {βc : ℝ} (hβc : 0 < βc) (o : V) :
    Tendsto (fun β : ℝ => ∫⁻ ω, clusterVol ω o ∂(longRangeMeasure J hJ
        (NNReal.mk (max β 0) (le_max_right β 0))))
      (𝓝[<] βc)
      (𝓝 (∫⁻ ω, clusterVol ω o ∂(longRangeMeasure J hJ
        (NNReal.mk (max βc 0) (le_max_right βc 0))))) := by
  have hbase := tendsto_lintegral_clusterVol_Iio (βc := βc)
    (P := fun β : ℝ => bernoulliEdgeProb J hJ (NNReal.mk (max β 0) (le_max_right β 0))) ?_ ?_ o
  · simpa only [longRangeMeasure, max_eq_left hβc.le] using hbase
  · intro β β' h1 h2 e
    refine bernoulliEdgeProb_mono J hJ ?_ e
    exact max_le_iff.mpr ⟨le_trans h1 (le_max_left β' 0), le_max_right β' 0⟩
  · intro e
    have hmax : Tendsto (fun β : ℝ => max β 0) (𝓝[<] βc) (𝓝 (max βc 0)) := by
      have hcont : Continuous fun β : ℝ => max β 0 := by fun_prop
      exact hcont.continuousAt.mono_left nhdsWithin_le_nhds
    have hcont : Continuous fun t : ℝ => (1 : ℝ) - Real.exp (-(t * J e)) := by fun_prop
    have h1 : Tendsto (fun β : ℝ => (1 : ℝ) - Real.exp (-(max β 0 * J e))) (𝓝[<] βc)
        (𝓝 ((1 : ℝ) - Real.exp (-(max βc 0 * J e)))) := (hcont.tendsto _).comp hmax
    simpa only [bernoulliEdgeProb_coe, NNReal.coe_mk] using h1

/-- **The a priori bound `hbdd` of Lemma I.4.9 from finiteness of the uncut mean.**

For an antitone nonnegative profile `K` with `K 0 = 0` and `K → 0` at infinity, and any
`α > 0`, `β > 0`: if the uncut expected cluster volume at `β` is finite, then there is an
explicit threshold `r₀` with

`E_{β,r}|K_o| ≤ (2α/β) r^α`  for every `r ≥ r₀`.

This is exactly the a priori ("sharpness") input of `first_moment_bound_all_beta`, and its
only remaining premise is the finiteness of the uncut mean at `β`, i.e. the source input
`P_{(1-ε)β_c}`; the threshold is `r₀ = max 1 ((β E_β|K_o| / (2α)) ^ (1/α))`. -/
theorem cutoff_eventual_rpow_bound_of_uncut_ne_top {d : ℕ} {K : ℝ → ℝ}
    (hK : AntitoneOn K (Set.Ioi 0)) (hKtop : Tendsto K atTop (𝓝 0))
    (hK0 : K 0 = 0) (hKnn : ∀ t, 0 < t → 0 ≤ K t)
    {α : ℝ} (hα : 0 < α) {β : NNReal} (hβ : 0 < (β : ℝ)) (o : Fin d → ℤ)
    (hfin : (∫⁻ ω, clusterVol ω o ∂(longRangeMeasure
        (kernelJ (fun y : Fin d → ℤ => K ((linfNorm y : ℕ) : ℝ)) (profile_even K))
        (uncutKernel_nonneg hKnn hK0 d) β)) ≠ ⊤) :
    ∃ r₀ : ℝ, 1 ≤ r₀ ∧ ∀ r : ℝ, r₀ ≤ r →
      (∫⁻ ω, clusterVol ω o ∂(longRangeMeasure (cutoffSymKernel K d r)
        (fun e => cutoffSymKernel_nonneg' hK d r e) β)).toReal
        ≤ (2 * α / (β : ℝ)) * r ^ α :=
  exists_eventual_rpow_bound_of_le
    (F := fun r : ℝ => ∫⁻ ω, clusterVol ω o ∂(longRangeMeasure (cutoffSymKernel K d r)
      (fun e => cutoffSymKernel_nonneg' hK d r e) β))
    hα hβ hfin
    (fun r => lintegral_clusterVol_cutoff_le hK hKtop hK0 hKnn d β o r)

/-- **The source's minimal sharpness threshold exists and is controlled by the mean.**

Assume `F` is monotone and uniformly bounded by `χ ≠ ⊤`.  Then there is a *least*
admissible threshold `r₀`: `1 ≤ r₀`, `(F r).toReal ≤ (2α/β) r^α` for every `r ≥ r₀`, and
`r₀ ≤ b` for every admissible `b`.  Moreover `r₀ ≤ max 1 ((χ β / (2α)) ^ (1/α))`.

This is the pair `(hbdd, hmin)` of `VolumeMoments.FirstMoment.first_moment_bound_all_beta`
for `F r = E_{β,r}|K_o|`: the source's a priori sharpness threshold exists as soon as the
first moment is *uniformly bounded*, and its size is controlled by that bound.  The proof
is the monotonicity of `F` together with continuity of `r ↦ r^α` at `r₀ ≥ 1`. -/
theorem exists_minimal_eventual_rpow_bound {F : ℝ → ℝ≥0∞} {χ : ℝ≥0∞} {α β : ℝ}
    (hα : 0 < α) (hβ : 0 < β) (hχ : χ ≠ ⊤) (hF : ∀ r : ℝ, F r ≤ χ) (hmono : Monotone F) :
    ∃ r₀ : ℝ, 1 ≤ r₀ ∧ (∀ r : ℝ, r₀ ≤ r → (F r).toReal ≤ (2 * α / β) * r ^ α) ∧
      (∀ b : ℝ, 1 ≤ b → (∀ r : ℝ, b ≤ r → (F r).toReal ≤ (2 * α / β) * r ^ α) → r₀ ≤ b) := by
  set G : ℝ → ℝ := fun r => (F r).toReal with hGdef
  have hGmono : Monotone G := by
    intro r r' h
    exact ENNReal.toReal_mono (ne_top_of_le_ne_top hχ (hF r')) (hmono h)
  set S : Set ℝ := {b | 1 ≤ b ∧ ∀ r : ℝ, b ≤ r → G r ≤ (2 * α / β) * r ^ α} with hSdef
  have hSne : S.Nonempty := by
    obtain ⟨R, hR1, hR⟩ := exists_eventual_rpow_bound_of_le (F := F) hα hβ hχ hF
    exact ⟨R, hR1, hR⟩
  have hSbdd : BddBelow S := ⟨1, fun b hb => hb.1⟩
  refine ⟨sInf S, ?_, ?_, ?_⟩
  · exact le_csInf hSne (fun b hb => hb.1)
  · intro r hr
    rcases lt_or_eq_of_le hr with hlt | heq
    · obtain ⟨b, hbS, hbr⟩ := (csInf_lt_iff hSbdd hSne).mp hlt
      exact hbS.2 r (le_of_lt hbr)
    · subst heq
      have hkey : ∀ r : ℝ, sInf S < r → G (sInf S) ≤ (2 * α / β) * r ^ α := by
        intro r hr
        obtain ⟨b, hbS, hbr⟩ := (csInf_lt_iff hSbdd hSne).mp hr
        exact le_trans (hGmono (le_trans (csInf_le hSbdd hbS) (le_of_lt hbr)))
          (hbS.2 r (le_of_lt hbr))
      have htend : Tendsto (fun r : ℝ => (2 * α / β) * r ^ α) (𝓝[>] (sInf S))
          (𝓝 ((2 * α / β) * (sInf S) ^ α)) := by
        have h1 : ContinuousAt (fun r : ℝ => r ^ α) (sInf S) :=
          Real.continuousAt_rpow_const _ _ (Or.inr hα.le)
        exact (continuousAt_const.mul h1).mono_left nhdsWithin_le_nhds
      exact le_of_tendsto_of_tendsto tendsto_const_nhds htend
        (by filter_upwards [self_mem_nhdsWithin] with r hr; exact hkey r hr)
  · intro b hb1 hbS
    exact csInf_le hSbdd ⟨hb1, hbS⟩

/-- **The pair `(hbdd, hmin)` of Lemma I.4.9, from finiteness of the uncut mean.**

For the cut-off family of an antitone profile: if the uncut expected cluster volume at `β`
is finite, then there is a *least* threshold `r₀` with
`E_{β,r}|K_o| ≤ (2α/β) r^α` for every `r ≥ r₀`, and every admissible threshold is at
least `r₀`.  This is exactly the pair of hypotheses `hbdd` and `hmin` of
`VolumeMoments.FirstMoment.first_moment_bound_all_beta`, so with this file the whole
sharpness bootstrap of Lemma I.4.9 depends on the *single* model input "the uncut mean at
`β` is finite" for every `β < β_c` (the source's `P_{(1-ε)β_c}`).

It does **not** prove that input: existence of an infinite-mean subcritical parameter is not
excluded here. -/
theorem cutoff_minimal_sharpness_threshold_of_uncut_ne_top {d : ℕ} {K : ℝ → ℝ}
    (hK : AntitoneOn K (Set.Ioi 0)) (hKtop : Tendsto K atTop (𝓝 0))
    (hK0 : K 0 = 0) (hKnn : ∀ t, 0 < t → 0 ≤ K t)
    {α : ℝ} (hα : 0 < α) {β : NNReal} (hβ : 0 < (β : ℝ)) (o : Fin d → ℤ)
    (hfin : (∫⁻ ω, clusterVol ω o ∂(longRangeMeasure
        (kernelJ (fun y : Fin d → ℤ => K ((linfNorm y : ℕ) : ℝ)) (profile_even K))
        (uncutKernel_nonneg hKnn hK0 d) β)) ≠ ⊤) :
    ∃ r₀ : ℝ, 1 ≤ r₀ ∧
      (∀ r : ℝ, r₀ ≤ r → (∫⁻ ω, clusterVol ω o ∂(longRangeMeasure (cutoffSymKernel K d r)
          (fun e => cutoffSymKernel_nonneg' hK d r e) β)).toReal
          ≤ (2 * α / (β : ℝ)) * r ^ α) ∧
      (∀ b : ℝ, 1 ≤ b → (∀ r : ℝ, b ≤ r →
          (∫⁻ ω, clusterVol ω o ∂(longRangeMeasure (cutoffSymKernel K d r)
            (fun e => cutoffSymKernel_nonneg' hK d r e) β)).toReal
            ≤ (2 * α / (β : ℝ)) * r ^ α) → r₀ ≤ b) :=
  exists_minimal_eventual_rpow_bound
    (F := fun r : ℝ => ∫⁻ ω, clusterVol ω o ∂(longRangeMeasure (cutoffSymKernel K d r)
      (fun e => cutoffSymKernel_nonneg' hK d r e) β))
    hα hβ hfin
    (fun r => lintegral_clusterVol_cutoff_le hK hKtop hK0 hKnn d β o r)
    (monotone_lintegral_clusterVol_cutoff hK d β o)

/-- **`hmeet` in the exact shape used by Lemma I.4.9**: at every fixed cut-off radius `r`,
the cut-off first moment `E_{β,r}|K_o|` is left continuous in `β` at `βc > 0`. -/
theorem tendsto_lintegral_clusterVol_cutoff_Iio {d : ℕ} {K : ℝ → ℝ}
    (hK : AntitoneOn K (Set.Ioi 0)) (r : ℝ) {βc : ℝ} (hβc : 0 < βc) (o : Fin d → ℤ) :
    Tendsto (fun β : ℝ => ∫⁻ ω, clusterVol ω o ∂(longRangeMeasure (cutoffSymKernel K d r)
        (fun e => cutoffSymKernel_nonneg' hK d r e) (NNReal.mk (max β 0) (le_max_right β 0))))
      (𝓝[<] βc)
      (𝓝 (∫⁻ ω, clusterVol ω o ∂(longRangeMeasure (cutoffSymKernel K d r)
        (fun e => cutoffSymKernel_nonneg' hK d r e)
        (NNReal.mk (max βc 0) (le_max_right βc 0))))) :=
  tendsto_lintegral_clusterVol_longRangeMeasure (J := cutoffSymKernel K d r)
    (fun e => cutoffSymKernel_nonneg' hK d r e) hβc o

/-- **Real-valued left continuity at a finite endpoint.** The `ℝ≥0∞` convergence
from `tendsto_lintegral_clusterVol_longRangeMeasure` can be converted with `toReal`
precisely because the mean at `βc` is finite. This premise is not inferred from
criticality or zero percolation probability. -/
theorem tendsto_toReal_lintegral_clusterVol_longRangeMeasure {J : Sym2 V → ℝ}
    (hJ : ∀ e : Sym2 V, 0 ≤ J e) {βc : ℝ} (hβc : 0 < βc) (o : V)
    (hfin : (∫⁻ ω, clusterVol ω o ∂(longRangeMeasure J hJ
      (NNReal.mk (max βc 0) (le_max_right βc 0)))) ≠ ∞) :
    Tendsto (fun β : ℝ => (∫⁻ ω, clusterVol ω o ∂(longRangeMeasure J hJ
        (NNReal.mk (max β 0) (le_max_right β 0)))).toReal)
      (𝓝[<] βc)
      (𝓝 (∫⁻ ω, clusterVol ω o ∂(longRangeMeasure J hJ
        (NNReal.mk (max βc 0) (le_max_right βc 0)))).toReal) := by
  exact (ENNReal.tendsto_toReal hfin).comp
    (tendsto_lintegral_clusterVol_longRangeMeasure hJ hβc o)

/-- **Real-valued `hmeet` at a finite endpoint cutoff mean.** This is the form
used by the real-valued first-moment bootstrap. -/
theorem tendsto_toReal_lintegral_clusterVol_cutoff_Iio {d : ℕ} {K : ℝ → ℝ}
    (hK : AntitoneOn K (Set.Ioi 0)) (r : ℝ) {βc : ℝ} (hβc : 0 < βc)
    (o : Fin d → ℤ)
    (hfin : (∫⁻ ω, clusterVol ω o ∂(longRangeMeasure (cutoffSymKernel K d r)
      (fun e => cutoffSymKernel_nonneg' hK d r e)
      (NNReal.mk (max βc 0) (le_max_right βc 0)))) ≠ ∞) :
    Tendsto (fun β : ℝ => (∫⁻ ω, clusterVol ω o ∂(longRangeMeasure (cutoffSymKernel K d r)
        (fun e => cutoffSymKernel_nonneg' hK d r e)
        (NNReal.mk (max β 0) (le_max_right β 0)))).toReal)
      (𝓝[<] βc)
      (𝓝 (∫⁻ ω, clusterVol ω o ∂(longRangeMeasure (cutoffSymKernel K d r)
        (fun e => cutoffSymKernel_nonneg' hK d r e)
        (NNReal.mk (max βc 0) (le_max_right βc 0)))).toReal) := by
  exact (ENNReal.tendsto_toReal hfin).comp
    (tendsto_lintegral_clusterVol_cutoff_Iio hK r hβc o)

/-- **The remaining premise in a single form.**

For the cut-off family of an antitone profile `K`, a bound on `E_{β,r}|K_o|` that is uniform
in the cut-off radius, with a finite constant, is *equivalent* to finiteness of the uncut mean
`E_β|K_o|`.  So "the cut-off first moment is bounded uniformly in `r`", the hypothesis used by
`RussoInf/Sharpness.lean` and by the sharpness bootstrap, and the source's `P_{(1-ε)β_c}` are
the same single statement.  Neither side is proved here; this only fixes which statement is
missing. -/
theorem exists_uniform_cutoff_bound_iff_uncut_ne_top {d : ℕ} {K : ℝ → ℝ}
    (hK : AntitoneOn K (Set.Ioi 0)) (hKtop : Tendsto K atTop (𝓝 0))
    (hK0 : K 0 = 0) (hKnn : ∀ t, 0 < t → 0 ≤ K t) (β : NNReal) (o : Fin d → ℤ) :
    (∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ r : ℝ,
        (∫⁻ ω, clusterVol ω o ∂(longRangeMeasure (cutoffSymKernel K d r)
          (fun e => cutoffSymKernel_nonneg' hK d r e) β)) ≤ C) ↔
      (∫⁻ ω, clusterVol ω o ∂(longRangeMeasure
        (kernelJ (fun y : Fin d → ℤ => K ((linfNorm y : ℕ) : ℝ)) (profile_even K))
        (uncutKernel_nonneg hKnn hK0 d) β)) ≠ ⊤ := by
  constructor
  · rintro ⟨C, hCtop, hC⟩
    refine ne_top_of_le_ne_top hCtop ?_
    exact le_of_forall_lintegral_clusterVol_cutoff_le hK hKtop hK0 hKnn d β o C hC
  · intro hfin
    exact ⟨_, hfin, fun r => lintegral_clusterVol_cutoff_le hK hKtop hK0 hKnn d β o r⟩

end PercLib.CriticalLRP
