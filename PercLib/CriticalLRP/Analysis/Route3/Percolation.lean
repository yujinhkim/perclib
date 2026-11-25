/- Integrated from independently rebuilt Ultramath work.
Production base 37c0efc68ae8ef365d8d155bc931fd784fdfde2b.
Scratch source: ../../.ultramath/smwvnrt0i/m2/Percolation.lean.
-/

module

public import PercLib.CriticalLRP.Analysis.Route3.Main
public import PercLib.CriticalLRP.Orchestration.Defs
public import PercLib.CriticalLRP.Analysis.Cutoff.Defs

/-!
# Proofs: `clusterVol` as an integer-valued variable, and the instantiation

`clusterVol ω 0` is `|K_0|` as an extended natural, hence pointwise either `⊤` or a natural
number, and at least `1`.  Both facts are recorded here because the layer cake and the
`E|K|^2 ≥ 1` step of the optimization need them.
-/

@[expose] public section

set_option autoImplicit false

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP

variable {V : Type*} [Countable V]

/-- `|K_v|` is integer-valued: pointwise it is either `∞` or a natural number.  This is the
`hint` hypothesis of `Tightness.lintegral_eq_tsum_meas_ge` and of
`Analysis.Route3.cube_lintegral_le_of_tail`. -/
theorem clusterVol_eq_top_or_nat (ω : Config V) (v : V) :
    clusterVol ω v = ⊤ ∨ ∃ m : ℕ, clusterVol ω v = (m : ℝ≥0∞) := by
  rcases eq_or_ne (cluster ω v).encard (⊤ : ℕ∞) with h | h
  · left
    rw [clusterVol_eq_encard, h]
    simp
  · obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.1 h
    exact Or.inr ⟨m, by rw [clusterVol_eq_encard, ← hm]; exact ENat.toENNReal_coe m⟩

/-- `|K_v| ≥ 1`: the cluster of `v` contains `v`. -/
theorem one_le_clusterVol (ω : Config V) (v : V) : 1 ≤ clusterVol ω v := by
  rcases clusterVol_eq_top_or_nat (V := V) ω v with h | ⟨m, hm⟩
  · rw [h]; exact le_top
  · have hpos : (0 : ℝ≥0∞) < (m : ℝ≥0∞) := by rw [← hm]; exact clusterVol_pos ω v
    have hm0 : m ≠ 0 := by
      intro h0
      rw [h0] at hpos
      simp at hpos
    rw [hm]
    exact_mod_cast Nat.one_le_iff_ne_zero.2 hm0

theorem isIncreasing_clusterVol_ge (v : V) (n : ℝ≥0∞) :
    IsIncreasing {ω : Config V | n ≤ clusterVol ω v} := by
  intro ω ω' hle hω
  exact le_trans hω (clusterVol_mono (fun e he => hle he) v)

end PercLib.CriticalLRP

namespace PercLib.CriticalLRP.Orchestration

open PercLib.CriticalLRP.Analysis.Route3

variable (M : SourceModelData)

/-- **Route 3 of Proposition I.4.15 at the source cut-off law.**

The cube of the first cut-off moment is dominated by `(4C+1)^3` times the second cut-off
moment, at every radius `r`, given (i) the infinite-volume `n^{-1/2}` critical volume-tail
bound and (ii) finite-volume domination. -/
theorem cutMoment_one_cube_le_two {C : ℝ} (hC : 0 ≤ C) (r : ℝ)
    (hTail : ∀ n : ℕ, 1 ≤ n →
      M.criticalLaw {ω : Config M.V | (n : ℝ≥0∞) ≤ clusterVol ω (0 : M.V)} ≤ tailEnvelope C n)
    (hDom : ∀ n : ℕ,
      M.cutLaw r {ω : Config M.V | (n : ℝ≥0∞) ≤ clusterVol ω (0 : M.V)}
        ≤ M.criticalLaw {ω : Config M.V | (n : ℝ≥0∞) ≤ clusterVol ω (0 : M.V)}) :
    (M.cutMoment 1 r) ^ 3 ≤ ENNReal.ofReal (ratioConst C) * M.cutMoment 2 r := by
  have hmeas : Measurable fun ω : Config M.V => clusterVol ω (0 : M.V) := measurable_clusterVol 0
  have hint : ∀ ω : Config M.V,
      clusterVol ω (0 : M.V) = ⊤ ∨ ∃ m : ℕ, clusterVol ω (0 : M.V) = (m : ℝ≥0∞) :=
    fun ω => PercLib.CriticalLRP.clusterVol_eq_top_or_nat ω (0 : M.V)
  have hX1 : ∀ ω : Config M.V, 1 ≤ clusterVol ω (0 : M.V) :=
    fun ω => PercLib.CriticalLRP.one_le_clusterVol ω (0 : M.V)
  have hkey := cube_lintegral_le_of_tail (μ := M.cutLaw r)
    (X := fun ω : Config M.V => clusterVol ω (0 : M.V)) hmeas hint hX1 hC
    (fun n hn => le_trans (hDom n) (hTail n hn))
  simpa [SourceModelData.cutMoment, pow_one] using hkey

/-! ## Finite-volume domination is a theorem, not an input

The cut-off kernel is dominated by the full kernel at the same intensity, so stochastic
monotonicity of the long-range law (`edgeMeasure_mono_of_le`) gives
`P_{β_c,r}(A) ≤ P_{β_c}(A)` for every increasing measurable `A`.  This is hypothesis (ii) of
`cutMoment_one_cube_le_two`, proved here for `r > 0` (the only range the source uses). -/

theorem bernoulliEdgeProb_mono_kernel {J J' : Sym2 M.V → ℝ} (hJ : ∀ e, 0 ≤ J e)
    (hJ' : ∀ e, 0 ≤ J' e) (hJJ' : ∀ e, J e ≤ J' e) (β : ℝ≥0) (e : Sym2 M.V) :
    PercLib.CriticalLRP.bernoulliEdgeProb J hJ β e
      ≤ PercLib.CriticalLRP.bernoulliEdgeProb J' hJ' β e := by
  rw [← Subtype.coe_le_coe, PercLib.CriticalLRP.bernoulliEdgeProb_coe,
    PercLib.CriticalLRP.bernoulliEdgeProb_coe]
  have hβ : (0 : ℝ) ≤ (β : ℝ) := β.2
  have h1 : (β : ℝ) * J e ≤ (β : ℝ) * J' e := mul_le_mul_of_nonneg_left (hJJ' e) hβ
  have h2 : Real.exp (-((β : ℝ) * J' e)) ≤ Real.exp (-((β : ℝ) * J e)) :=
    Real.exp_le_exp.2 (by linarith)
  linarith

theorem cutoffProfile_le {K : ℝ → ℝ} (hK : ∀ s : ℝ, 0 < s → 0 ≤ K s) {r : ℝ} (hr : 0 < r)
    (s : ℝ) : FiniteVolume.cutoffProfile K r s ≤ K s := by
  by_cases h : s ≤ r
  · rw [FiniteVolume.cutoffProfile_of_le h]
    have := hK r hr
    linarith
  · rw [FiniteVolume.cutoffProfile_of_lt (not_le.1 h)]
    have hs : 0 < s := lt_trans hr (not_le.1 h)
    have := hK s hs
    linarith

theorem cutKernel_le_kernel {r : ℝ} (hr : 0 < r) (e : Sym2 M.V) :
    M.cutKernel r e ≤ M.kernel e := by
  induction e using Sym2.ind with
  | h x y =>
    rw [SourceModelData.cutKernel, SourceModelData.kernel, cutRadialSym, radialSym_mk, radialSym_mk]
    by_cases h : x = y
    · simp [h]
    · rw [ite_eq_right h, ite_eq_right h]
      exact cutoffProfile_le M.K_nonneg hr (M.S.dist x y)

theorem cutLaw_le_criticalLaw {r : ℝ} (hr : 0 < r) {A : Set (Config M.V)}
    (hA : MeasurableSet A) (hinc : IsIncreasing A) : M.cutLaw r A ≤ M.criticalLaw A := by
  have h := PercLib.CriticalLRP.edgeMeasure_mono_of_le
    (p := PercLib.CriticalLRP.bernoulliEdgeProb (M.cutKernel r) (M.cutKernel_nonneg r) M.betaCrit)
    (q := PercLib.CriticalLRP.bernoulliEdgeProb M.kernel M.kernel_nonneg M.betaCrit)
    (fun e => bernoulliEdgeProb_mono_kernel M (M.cutKernel_nonneg r) M.kernel_nonneg
      (fun e => cutKernel_le_kernel (M := M) hr e) M.betaCrit e) hA hinc
  simpa [SourceModelData.cutLaw, SourceModelData.criticalLaw, SourceModelData.law,
    PercLib.CriticalLRP.longRangeMeasure] using h

theorem cutLaw_tail_le_criticalLaw {r : ℝ} (hr : 0 < r) (n : ℕ) :
    M.cutLaw r {ω : Config M.V | (n : ℝ≥0∞) ≤ clusterVol ω (0 : M.V)}
      ≤ M.criticalLaw {ω : Config M.V | (n : ℝ≥0∞) ≤ clusterVol ω (0 : M.V)} :=
  cutLaw_le_criticalLaw M hr (measurable_clusterVol 0 measurableSet_Ici)
    (PercLib.CriticalLRP.isIncreasing_clusterVol_ge 0 (n : ℝ≥0∞))

/-- **Route 3 of Proposition I.4.15 at the source cut-off law, with only the citation-level
volume-tail input.**  For `r > 0`, if the infinite-volume critical volume tail satisfies
`P_{β_c}(|K| ≥ n) ≤ C/√n`, then `(E_{β_c,r}|K|)^3 ≤ (4C+1)^3 E_{β_c,r}|K|^2`. -/
theorem cutMoment_one_cube_le_two_of_tail {C : ℝ} (hC : 0 ≤ C) {r : ℝ} (hr : 0 < r)
    (hTail : ∀ n : ℕ, 1 ≤ n →
      M.criticalLaw {ω : Config M.V | (n : ℝ≥0∞) ≤ clusterVol ω (0 : M.V)} ≤ tailEnvelope C n) :
    (M.cutMoment 1 r) ^ 3 ≤ ENNReal.ofReal (ratioConst C) * M.cutMoment 2 r :=
  cutMoment_one_cube_le_two M hC r hTail (fun n => cutLaw_tail_le_criticalLaw (M := M) hr n)

end PercLib.CriticalLRP.Orchestration
