/-
# Monotone convergence of every natural cluster moment at the cutoff

The first-moment proof in `CutoffLimit` uses the finite-path exhaustion of
connection events.  This file applies the same exhaustion directly to cluster
volumes on the common mark space, and then integrates arbitrary natural powers.
No moment finiteness, sharpness, or tree-graph bound is assumed.
-/
module

public import PercLib.CriticalLRP.MomentMonotonicity.MomentTransfer

set_option autoImplicit false

@[expose] public section

open MeasureTheory Measure ProbabilityTheory unitInterval Filter Topology
open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP.CutoffMomentTransfer

open PercLib.CriticalLRP FiniteVolume CutoffKernel CutoffLimit TreeExpansion

variable {V : Type*} [Countable V]

/-- On the common mark space, an increasing family of edge probabilities whose
limit is `q` exhausts every cluster volume.  The supremum may be `⊤`. -/
theorem clusterVol_atParameter_eq_iSup {p : ℕ → Sym2 V → unitInterval}
    {q : Sym2 V → unitInterval}
    (hmono : ∀ (n : ℕ) (e : Sym2 V), p n e ≤ p (n + 1) e)
    (hlim : ∀ e : Sym2 V,
      Tendsto (fun n : ℕ => ((p n e : unitInterval) : ℝ)) atTop
        (𝓝 ((q e : unitInterval) : ℝ)))
    (u : Sym2 V → ℝ) (o : V) :
    clusterVol (atParameter q u) o =
      ⨆ n : ℕ, clusterVol (atParameter (p n) u) o := by
  have hpq : ∀ (n : ℕ) (e : Sym2 V), p n e ≤ q e :=
    le_of_le_succ_of_tendsto hmono hlim
  have hle (n : ℕ) : atParameter (p n) u ≤ atParameter q u := by
    intro e he
    exact lt_of_lt_of_le he (Subtype.coe_le_coe.mpr (hpq n e))
  have hsucc (n : ℕ) : atParameter (p n) u ≤ atParameter (p (n + 1)) u := by
    intro e he
    exact lt_of_lt_of_le he (Subtype.coe_le_coe.mpr (hmono n e))
  have hsubset (n : ℕ) :
      cluster (atParameter (p n) u) o ⊆ cluster (atParameter q u) o :=
    cluster_mono (hle n) o
  have hind (y : V) :
      (⨆ n : ℕ, (cluster (atParameter (p n) u) o).indicator
        (fun _ => (1 : ℝ≥0∞)) y) =
      (cluster (atParameter q u) o).indicator (fun _ => (1 : ℝ≥0∞)) y := by
    by_cases hy : y ∈ cluster (atParameter q u) o
    · obtain ⟨n, hn⟩ := exists_connects_atParameter_of_connects hmono hlim
        (mem_cluster_iff.mp hy)
      have hnmem : y ∈ cluster (atParameter (p n) u) o := mem_cluster_iff.mpr hn
      apply le_antisymm
      · refine iSup_le fun m => ?_
        by_cases hm : y ∈ cluster (atParameter (p m) u) o
        · rw [Set.indicator_of_mem hm, Set.indicator_of_mem (hsubset m hm)]
        · rw [Set.indicator_of_notMem hm]
          exact zero_le
      · rw [Set.indicator_of_mem hy]
        exact le_iSup_of_le n (by rw [Set.indicator_of_mem hnmem])
    · have hn : ∀ n : ℕ, y ∉ cluster (atParameter (p n) u) o :=
        fun n h => hy (hsubset n h)
      simp [Set.indicator_of_notMem, hy, hn]
  rw [clusterVol_eq_tsum]
  calc
    (∑' y : V, (cluster (atParameter q u) o).indicator
        (fun _ => (1 : ℝ≥0∞)) y) =
        ∑' y : V, ⨆ n : ℕ, (cluster (atParameter (p n) u) o).indicator
          (fun _ => (1 : ℝ≥0∞)) y := tsum_congr fun y => (hind y).symm
    _ = ⨆ n : ℕ, ∑' y : V, (cluster (atParameter (p n) u) o).indicator
        (fun _ => (1 : ℝ≥0∞)) y := by
      symm
      apply iSup_tsum_of_monotone
      intro n y
      by_cases hy : y ∈ cluster (atParameter (p n) u) o
      · rw [Set.indicator_of_mem hy,
          Set.indicator_of_mem (cluster_mono (hsucc n) o hy)]
      · rw [Set.indicator_of_notMem hy]
        exact zero_le
    _ = ⨆ n : ℕ, clusterVol (atParameter (p n) u) o :=
      iSup_congr fun n => (clusterVol_eq_tsum _ _).symm

/-- **Monotone convergence of all natural moments for any increasing family of
independent edge laws.**  Both sides are allowed to be infinite. -/
theorem iSup_lintegral_clusterVol_pow {p : ℕ → Sym2 V → unitInterval}
    {q : Sym2 V → unitInterval}
    (hmono : ∀ (n : ℕ) (e : Sym2 V), p n e ≤ p (n + 1) e)
    (hlim : ∀ e : Sym2 V,
      Tendsto (fun n : ℕ => ((p n e : unitInterval) : ℝ)) atTop
        (𝓝 ((q e : unitInterval) : ℝ)))
    (o : V) (k : ℕ) :
    (⨆ n : ℕ, ∫⁻ ω, clusterVol ω o ^ k ∂(edgeMeasure (p n))) =
      ∫⁻ ω, clusterVol ω o ^ k ∂(edgeMeasure q) := by
  have hstep (r : Sym2 V → unitInterval) :
      (∫⁻ ω, clusterVol ω o ^ k ∂(edgeMeasure r)) =
        ∫⁻ u : Sym2 V → ℝ, clusterVol (atParameter r u) o ^ k ∂(markMeasure V) := by
    conv_lhs => rw [← markMeasure_map_atParameter r]
    exact lintegral_map ((measurable_clusterVol o).pow_const k)
      (measurable_atParameter r)
  rw [iSup_congr fun n => hstep (p n), hstep q]
  have hpt (u : Sym2 V → ℝ) :
      clusterVol (atParameter q u) o ^ k =
        ⨆ n : ℕ, clusterVol (atParameter (p n) u) o ^ k := by
    rw [clusterVol_atParameter_eq_iSup hmono hlim u o, ENNReal.iSup_pow]
  simp_rw [hpt]
  rw [lintegral_iSup]
  · intro n
    exact ((measurable_clusterVol o).comp (measurable_atParameter (p n))).pow_const k
  · intro m n hmn u
    apply pow_le_pow_left' _ k
    apply clusterVol_mono _ o
    intro e he
    exact lt_of_lt_of_le he (Subtype.coe_le_coe.mpr
      (monotone_nat_of_le_succ (fun j => hmono j e) hmn))

/-- Real-parameter version of all-order monotone convergence. -/
theorem iSup_lintegral_clusterVol_pow_real {p : ℝ → Sym2 V → unitInterval}
    {q : Sym2 V → unitInterval}
    (hmono : ∀ (r r' : ℝ) (e : Sym2 V), r ≤ r' → p r e ≤ p r' e)
    (hlim : ∀ e : Sym2 V,
      Tendsto (fun r : ℝ => ((p r e : unitInterval) : ℝ)) atTop
        (𝓝 ((q e : unitInterval) : ℝ)))
    (o : V) (k : ℕ) :
    (⨆ r : ℝ, ∫⁻ ω, clusterVol ω o ^ k ∂(edgeMeasure (p r))) =
      ∫⁻ ω, clusterVol ω o ^ k ∂(edgeMeasure q) := by
  have hmonoR : Monotone fun r : ℝ =>
      ∫⁻ ω, clusterVol ω o ^ k ∂(edgeMeasure (p r)) :=
    fun r r' hrr' => lintegral_clusterVol_pow_mono_of_le
      (fun e => hmono r r' e hrr') o k
  rw [iSup_real_eq_iSup_nat hmonoR]
  exact iSup_lintegral_clusterVol_pow
    (p := fun n : ℕ => p (n : ℝ))
    (fun n e => hmono _ _ e (by push_cast; linarith))
    (fun e => (hlim e).comp tendsto_natCast_atTop_atTop) o k

/-- **Every natural moment of the loop-safe cutoff model increases to its uncut
value as the cutoff radius tends to infinity.**  This does not assert finiteness
of either side. -/
theorem iSup_lintegral_clusterVol_pow_cutoff {K : ℝ → ℝ}
    (hK : AntitoneOn K (Set.Ioi 0)) (hKtop : Tendsto K atTop (𝓝 0))
    (hK0 : K 0 = 0) (hKnn : ∀ t, 0 < t → 0 ≤ K t)
    (d : ℕ) (β : NNReal) (o : Fin d → ℤ) (k : ℕ) :
    (⨆ r : ℝ, ∫⁻ ω, clusterVol ω o ^ k ∂(longRangeMeasure (cutoffSymKernel K d r)
        (fun e => cutoffSymKernel_nonneg' hK d r e) β)) =
      ∫⁻ ω, clusterVol ω o ^ k ∂(longRangeMeasure (kernelJ
        (fun y : Fin d → ℤ => K ((linfNorm y : ℕ) : ℝ)) (profile_even (d := d) K))
        (uncutKernel_nonneg hKnn hK0 d) β) :=
  iSup_lintegral_clusterVol_pow_real
    (p := fun (r : ℝ) (e : Sym2 (Fin d → ℤ)) => bernoulliEdgeProb
      (cutoffSymKernel K d r) (fun e => cutoffSymKernel_nonneg' hK d r e) β e)
    (q := bernoulliEdgeProb (kernelJ
      (fun y : Fin d → ℤ => K ((linfNorm y : ℕ) : ℝ)) (profile_even (d := d) K))
      (uncutKernel_nonneg hKnn hK0 d) β)
    (fun _r _r' e hrr' => bernoulliEdgeProb_mono_kernel
      (fun e => cutoffSymKernel_mono_r' hK hrr' e) _ _ β e)
    (fun e => tendsto_bernoulliEdgeProb_cutoff hK hKtop hK0 hKnn d β e) o k

/-- Cutoff moments are nondecreasing in the cutoff radius at every order. -/
theorem monotone_lintegral_clusterVol_pow_cutoff {K : ℝ → ℝ}
    (hK : AntitoneOn K (Set.Ioi 0)) (d : ℕ) (β : NNReal)
    (o : Fin d → ℤ) (k : ℕ) :
    Monotone fun r : ℝ => ∫⁻ ω, clusterVol ω o ^ k
      ∂(longRangeMeasure (cutoffSymKernel K d r)
        (fun e => cutoffSymKernel_nonneg' hK d r e) β) :=
  fun _r _r' hrr' => lintegral_clusterVol_pow_mono_of_le
    (fun e => bernoulliEdgeProb_mono_kernel
      (fun e => cutoffSymKernel_mono_r' hK hrr' e) _ _ β e) o k

/-- **Extended-real convergence `E_{β,r}|K_o|^k → E_β|K_o|^k`** for every natural
`k`, including divergence to `⊤`. -/
theorem tendsto_lintegral_clusterVol_pow_cutoff {K : ℝ → ℝ}
    (hK : AntitoneOn K (Set.Ioi 0)) (hKtop : Tendsto K atTop (𝓝 0))
    (hK0 : K 0 = 0) (hKnn : ∀ t, 0 < t → 0 ≤ K t)
    (d : ℕ) (β : NNReal) (o : Fin d → ℤ) (k : ℕ) :
    Tendsto (fun r : ℝ => ∫⁻ ω, clusterVol ω o ^ k
      ∂(longRangeMeasure (cutoffSymKernel K d r)
        (fun e => cutoffSymKernel_nonneg' hK d r e) β)) atTop
      (𝓝 (∫⁻ ω, clusterVol ω o ^ k ∂(longRangeMeasure (kernelJ
        (fun y : Fin d → ℤ => K ((linfNorm y : ℕ) : ℝ)) (profile_even (d := d) K))
        (uncutKernel_nonneg hKnn hK0 d) β))) := by
  rw [← iSup_lintegral_clusterVol_pow_cutoff hK hKtop hK0 hKnn d β o k]
  exact tendsto_atTop_iSup (monotone_lintegral_clusterVol_pow_cutoff hK d β o k)

/-- At each fixed cutoff, every natural moment is bounded by its uncut value. -/
theorem lintegral_clusterVol_pow_cutoff_le {K : ℝ → ℝ}
    (hK : AntitoneOn K (Set.Ioi 0)) (hKtop : Tendsto K atTop (𝓝 0))
    (hK0 : K 0 = 0) (hKnn : ∀ t, 0 < t → 0 ≤ K t)
    (d : ℕ) (β : NNReal) (o : Fin d → ℤ) (k : ℕ) (r : ℝ) :
    (∫⁻ ω, clusterVol ω o ^ k ∂(longRangeMeasure (cutoffSymKernel K d r)
        (fun e => cutoffSymKernel_nonneg' hK d r e) β)) ≤
      ∫⁻ ω, clusterVol ω o ^ k ∂(longRangeMeasure (kernelJ
        (fun y : Fin d → ℤ => K ((linfNorm y : ℕ) : ℝ)) (profile_even (d := d) K))
        (uncutKernel_nonneg hKnn hK0 d) β) := by
  rw [← iSup_lintegral_clusterVol_pow_cutoff hK hKtop hK0 hKnn d β o k]
  exact le_iSup (fun r : ℝ => ∫⁻ ω, clusterVol ω o ^ k
    ∂(longRangeMeasure (cutoffSymKernel K d r)
      (fun e => cutoffSymKernel_nonneg' hK d r e) β)) r

/-- A finite bound uniform in the cutoff transfers to the uncut moment.  The
converse bound is `lintegral_clusterVol_pow_cutoff_le`; no such uniform bound is
constructed here. -/
theorem lintegral_clusterVol_pow_uncut_ne_top_of_forall_cutoff_le
    {K : ℝ → ℝ}
    (hK : AntitoneOn K (Set.Ioi 0)) (hKtop : Tendsto K atTop (𝓝 0))
    (hK0 : K 0 = 0) (hKnn : ∀ t, 0 < t → 0 ≤ K t)
    (d : ℕ) (β : NNReal) (o : Fin d → ℤ) (k : ℕ) (C : ℝ≥0∞) (hC : C ≠ ⊤)
    (hbound : ∀ r : ℝ, (∫⁻ ω, clusterVol ω o ^ k
      ∂(longRangeMeasure (cutoffSymKernel K d r)
        (fun e => cutoffSymKernel_nonneg' hK d r e) β)) ≤ C) :
    (∫⁻ ω, clusterVol ω o ^ k ∂(longRangeMeasure (kernelJ
      (fun y : Fin d → ℤ => K ((linfNorm y : ℕ) : ℝ)) (profile_even (d := d) K))
      (uncutKernel_nonneg hKnn hK0 d) β)) ≠ ⊤ := by
  rw [← iSup_lintegral_clusterVol_pow_cutoff hK hKtop hK0 hKnn d β o k]
  exact ne_top_of_le_ne_top hC (iSup_le hbound)

/-- The complete cutoff comparison used in Proposition I.4.2.  At any two
intensities `β ≤ γ`, the cutoff law is monotone in intensity and is dominated
by the uncut law at the larger intensity.  The statement includes arbitrary
increasing measurable events, every natural cluster moment, and the two-point
function.  It says nothing about finiteness of the dominating moments. -/
theorem cutoff_mono_beta_and_le_uncut {K : ℝ → ℝ}
    (hK : AntitoneOn K (Set.Ioi 0)) (hKtop : Tendsto K atTop (𝓝 0))
    (hK0 : K 0 = 0) (hKnn : ∀ t, 0 < t → 0 ≤ K t)
    (d : ℕ) {β γ : NNReal} (hβγ : β ≤ γ) (r : ℝ) :
    (∀ A : Set (Config (Fin d → ℤ)), MeasurableSet A → IsIncreasing A →
      longRangeMeasure (cutoffSymKernel K d r)
          (fun e => cutoffSymKernel_nonneg' hK d r e) β A ≤
        longRangeMeasure (cutoffSymKernel K d r)
          (fun e => cutoffSymKernel_nonneg' hK d r e) γ A ∧
      longRangeMeasure (cutoffSymKernel K d r)
          (fun e => cutoffSymKernel_nonneg' hK d r e) γ A ≤
        longRangeMeasure (kernelJ
          (fun y : Fin d → ℤ => K ((linfNorm y : ℕ) : ℝ)) (profile_even (d := d) K))
          (uncutKernel_nonneg hKnn hK0 d) γ A) ∧
    (∀ (o : Fin d → ℤ) (k : ℕ),
      (∫⁻ ω, clusterVol ω o ^ k ∂(longRangeMeasure (cutoffSymKernel K d r)
          (fun e => cutoffSymKernel_nonneg' hK d r e) β)) ≤
        ∫⁻ ω, clusterVol ω o ^ k ∂(longRangeMeasure (cutoffSymKernel K d r)
          (fun e => cutoffSymKernel_nonneg' hK d r e) γ) ∧
      (∫⁻ ω, clusterVol ω o ^ k ∂(longRangeMeasure (cutoffSymKernel K d r)
          (fun e => cutoffSymKernel_nonneg' hK d r e) γ)) ≤
        ∫⁻ ω, clusterVol ω o ^ k ∂(longRangeMeasure (kernelJ
          (fun y : Fin d → ℤ => K ((linfNorm y : ℕ) : ℝ)) (profile_even (d := d) K))
          (uncutKernel_nonneg hKnn hK0 d) γ)) ∧
    (∀ x y : Fin d → ℤ,
      twoPointFunction (cutoffSymKernel K d r)
          (fun e => cutoffSymKernel_nonneg' hK d r e) β x y ≤
        twoPointFunction (cutoffSymKernel K d r)
          (fun e => cutoffSymKernel_nonneg' hK d r e) γ x y ∧
      twoPointFunction (cutoffSymKernel K d r)
          (fun e => cutoffSymKernel_nonneg' hK d r e) γ x y ≤
        twoPointFunction (kernelJ
          (fun y : Fin d → ℤ => K ((linfNorm y : ℕ) : ℝ)) (profile_even (d := d) K))
          (uncutKernel_nonneg hKnn hK0 d) γ x y) := by
  refine ⟨?_, ?_, ?_⟩
  · intro A hA hinc
    exact ⟨longRangeMeasure_mono_apply
        (fun e => cutoffSymKernel_nonneg' hK d r e) hβγ hA hinc,
      longRangeMeasure_mono_kernel (cutoffSymKernel_le_uncut hKnn hK0 r)
        (fun e => cutoffSymKernel_nonneg' hK d r e)
        (uncutKernel_nonneg hKnn hK0 d) γ hA hinc⟩
  · intro o k
    refine ⟨lintegral_clusterVol_pow_mono_of_le
      (fun e => bernoulliEdgeProb_mono (cutoffSymKernel K d r)
        (fun e => cutoffSymKernel_nonneg' hK d r e) hβγ e) o k, ?_⟩
    exact lintegral_clusterVol_pow_cutoff_le hK hKtop hK0 hKnn d γ o k r
  · intro x y
    exact ⟨twoPointFunction_mono (fun e => cutoffSymKernel_nonneg' hK d r e)
      hβγ x y, twoPointFunction_cutoff_le hK hKnn hK0 d γ r x y⟩

/-- The fourth-moment part of `cutoff_mono_beta_and_le_uncut`, including both
comparisons in the source's application of Proposition I.4.2. -/
theorem cutoff_fourthMoment_mono_beta_and_le_uncut {K : ℝ → ℝ}
    (hK : AntitoneOn K (Set.Ioi 0)) (hKtop : Tendsto K atTop (𝓝 0))
    (hK0 : K 0 = 0) (hKnn : ∀ t, 0 < t → 0 ≤ K t)
    (d : ℕ) {β γ : NNReal} (hβγ : β ≤ γ) (r : ℝ) (o : Fin d → ℤ) :
    (∫⁻ ω, clusterVol ω o ^ 4 ∂(longRangeMeasure (cutoffSymKernel K d r)
        (fun e => cutoffSymKernel_nonneg' hK d r e) β)) ≤
      ∫⁻ ω, clusterVol ω o ^ 4 ∂(longRangeMeasure (cutoffSymKernel K d r)
        (fun e => cutoffSymKernel_nonneg' hK d r e) γ) ∧
    (∫⁻ ω, clusterVol ω o ^ 4 ∂(longRangeMeasure (cutoffSymKernel K d r)
        (fun e => cutoffSymKernel_nonneg' hK d r e) γ)) ≤
      ∫⁻ ω, clusterVol ω o ^ 4 ∂(longRangeMeasure (kernelJ
        (fun y : Fin d → ℤ => K ((linfNorm y : ℕ) : ℝ)) (profile_even (d := d) K))
        (uncutKernel_nonneg hKnn hK0 d) γ) :=
  (cutoff_mono_beta_and_le_uncut hK hKtop hK0 hKnn d hβγ r).2.1 o 4

/-- Raw sup-norm term-level check: the fourth-moment comparison applies to
this power law after converting `cardFun` to `clusterVol`.  The paper's
unit-ball normalization uses the normalized norm `2‖·‖∞`, or equivalently an
explicit constant profile/intensity rescaling, rather than raw `linfNorm`. -/
example {d : ℕ} {α : ℝ} (hα : 0 < (d : ℝ) + α) {β γ : NNReal}
    (hβγ : β ≤ γ) (r : ℝ) (o : Fin d → ℤ) :
    (∫⁻ ω, (Percolation.cardFun (cluster ω o)) ^ 4
      ∂(longRangeMeasure (cutoffSymKernel (modelProfile d α) d r)
        (fun e => cutoffSymKernel_nonneg' (modelProfile_antitoneOn d hα.le) d r e) β)) ≤
      ∫⁻ ω, (Percolation.cardFun (cluster ω o)) ^ 4
        ∂(longRangeMeasure (cutoffSymKernel (modelProfile d α) d r)
          (fun e => cutoffSymKernel_nonneg' (modelProfile_antitoneOn d hα.le) d r e) γ) ∧
    (∫⁻ ω, (Percolation.cardFun (cluster ω o)) ^ 4
      ∂(longRangeMeasure (cutoffSymKernel (modelProfile d α) d r)
        (fun e => cutoffSymKernel_nonneg' (modelProfile_antitoneOn d hα.le) d r e) γ)) ≤
      ∫⁻ ω, (Percolation.cardFun (cluster ω o)) ^ 4
        ∂(longRangeMeasure (kernelJ
          (fun y : Fin d → ℤ => modelProfile d α ((linfNorm y : ℕ) : ℝ))
          (profile_even (d := d) (modelProfile d α)))
          (uncutKernel_nonneg (fun _ ht => (modelProfile_pos ht).le)
            (modelProfile_zero hα) d) γ) := by
  simpa only [Percolation.cardFun_eq_encard] using
    cutoff_fourthMoment_mono_beta_and_le_uncut
      (modelProfile_antitoneOn d hα.le) (tendsto_modelProfile hα)
      (modelProfile_zero hα) (fun _ ht => (modelProfile_pos ht).le) d hβγ r o

#print axioms PercLib.CriticalLRP.CutoffMomentTransfer.clusterVol_atParameter_eq_iSup
#print axioms PercLib.CriticalLRP.CutoffMomentTransfer.iSup_lintegral_clusterVol_pow
#print axioms PercLib.CriticalLRP.CutoffMomentTransfer.iSup_lintegral_clusterVol_pow_real
#print axioms PercLib.CriticalLRP.CutoffMomentTransfer.iSup_lintegral_clusterVol_pow_cutoff
#print axioms PercLib.CriticalLRP.CutoffMomentTransfer.monotone_lintegral_clusterVol_pow_cutoff
#print axioms PercLib.CriticalLRP.CutoffMomentTransfer.tendsto_lintegral_clusterVol_pow_cutoff
#print axioms PercLib.CriticalLRP.CutoffMomentTransfer.lintegral_clusterVol_pow_cutoff_le
#print axioms PercLib.CriticalLRP.CutoffMomentTransfer.lintegral_clusterVol_pow_uncut_ne_top_of_forall_cutoff_le

#print axioms PercLib.CriticalLRP.CutoffMomentTransfer.cutoff_mono_beta_and_le_uncut
#print axioms PercLib.CriticalLRP.CutoffMomentTransfer.cutoff_fourthMoment_mono_beta_and_le_uncut

end PercLib.CriticalLRP.CutoffMomentTransfer
