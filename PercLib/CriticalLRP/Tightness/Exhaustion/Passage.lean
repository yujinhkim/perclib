/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
# The exhaustion passage for the per-scale bounds (2.8) and (2.9)

Source: T. Hutchcroft, arXiv:2008.11197v2, proof of Theorem 2.3, final paragraph.
-/
module

public import PercLib.CriticalLRP.Tightness.Exhaustion.Window

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

set_option autoImplicit true

@[expose] public section

open MeasureTheory Set Finset
open scoped ENNReal

namespace PercLib.CriticalLRP

namespace Exhaustion

variable {V : Type*} [Countable V]

/-! ### Identification of the limit objects with the repository's cluster volumes -/

/-- The unrestricted window volume is the repository's `|K_u ∩ W|`. -/
theorem volFull_eq_clusterVolIn (ω : Config V) (u : V) (W : Finset V) :
    volFull ω u W = clusterVolIn ω u (W : Set V) := by
  classical
  have hset : (cluster ω u) ∩ (W : Set V) = ((W.filter (fun y => Connects ω u y) : Finset V) : Set V) := by
    ext y
    simp only [Set.mem_inter_iff, Finset.mem_coe, Finset.mem_filter, mem_cluster_iff]
    tauto
  rw [volFull, clusterVolIn, hset, Set.encard_coe_eq_coe_finsetCard]
  push_cast
  rfl

/-- The unrestricted window maximum is the repository's `|K_max(W)|`. -/
theorem maxVolFull_eq_clusterMaxVol (ω : Config V) (W : Finset V) :
    maxVolFull ω W = Percolation.clusterMaxVol ω W := by
  simp only [maxVolFull, Percolation.clusterMaxVol, volFull_eq_clusterVolIn]

/-- The restricted maximum is dominated by the true maximum. -/
lemma maxVol_le_maxVolFull (A : Set V) (ω : Config V) (W : Finset V) :
    maxVol A ω W ≤ maxVolFull ω W := by
  classical
  refine Finset.sup_le (fun w hw => ?_)
  exact (vol_le_volFull A ω w W).trans (Finset.le_sup (f := fun w => volFull ω w W) hw)

/-! ### The increasing event sequences -/

lemma event_vol_mono {A : ℕ → Set V} (hmono : Monotone A) (t : ℝ≥0∞) (u : V) (W : Finset V) :
    Monotone (fun r => {ω : Config V | t ≤ vol (A r) ω u W}) :=
  fun r s hrs ω hω => hω.trans (vol_mono (hmono hrs) ω u W)

lemma event_maxVol_mono {A : ℕ → Set V} (hmono : Monotone A) (t : ℝ≥0∞) (W : Finset V) :
    Monotone (fun r => {ω : Config V | t ≤ maxVol (A r) ω W}) :=
  fun r s hrs ω hω => hω.trans (maxVol_mono (hmono hrs) ω W)

lemma iUnion_event_vol {A : ℕ → Set V} (hmono : Monotone A) (hcover : Covers A) (t : ℝ≥0∞)
    (u : V) (W : Finset V) :
    (⋃ r, {ω : Config V | t ≤ vol (A r) ω u W}) = {ω : Config V | t ≤ volFull ω u W} := by
  ext ω
  simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨r, hr⟩
    exact hr.trans (vol_le_volFull (A r) ω u W)
  · intro h
    obtain ⟨R, hR⟩ := vol_eventually_eq hmono hcover ω u W
    exact ⟨R, by rwa [hR]⟩

lemma iUnion_event_maxVol {A : ℕ → Set V} (hmono : Monotone A) (hcover : Covers A) (t : ℝ≥0∞)
    (W : Finset V) :
    (⋃ r, {ω : Config V | t ≤ maxVol (A r) ω W}) = {ω : Config V | t ≤ maxVolFull ω W} := by
  ext ω
  simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨r, hr⟩
    exact hr.trans (maxVol_le_maxVolFull (A r) ω W)
  · intro h
    obtain ⟨R, hR⟩ := maxVol_eventually_eq hmono hcover ω W
    exact ⟨R, by rwa [hR]⟩

/-! ### The passage (2.8) and (2.9) from finite subgraphs to the countable graph -/

/-- **Exhaustion passage for (2.8).**  If the per-scale bound
`P(|K_max(W)| ≥ 3^k λ) ≤ P(|K_max(W)| ≥ λ)^(3^(k-1)+1)` holds in every finite subgraph of a
monotone exhaustion covering the vertex set, then it holds for the countable graph, with the
window maximum taken over clusters of the whole graph. -/
theorem per_scale_of_finite {μ : Measure (Config V)} {A : ℕ → Set V} (hmono : Monotone A)
    (hcover : Covers A) (W : Finset V) {lam : ℝ} {k : ℕ}
    (hfin : ∀ r, μ {ω : Config V | ENNReal.ofReal (3 ^ k * lam) ≤ maxVol (A r) ω W} ≤
      (μ {ω : Config V | ENNReal.ofReal lam ≤ maxVol (A r) ω W}) ^ (3 ^ (k - 1) + 1)) :
    μ {ω : Config V | ENNReal.ofReal (3 ^ k * lam) ≤ Percolation.clusterMaxVol ω W} ≤
      (μ {ω : Config V | ENNReal.ofReal lam ≤ Percolation.clusterMaxVol ω W}) ^
        (3 ^ (k - 1) + 1) := by
  have h := tendsto_pow_transfer (E := fun r => {ω : Config V | ENNReal.ofReal (3 ^ k * lam) ≤
      maxVol (A r) ω W}) (F := fun r => {ω : Config V | ENNReal.ofReal lam ≤ maxVol (A r) ω W})
    (E' := {ω : Config V | ENNReal.ofReal (3 ^ k * lam) ≤ Percolation.clusterMaxVol ω W})
    (F' := {ω : Config V | ENNReal.ofReal lam ≤ Percolation.clusterMaxVol ω W})
    (event_maxVol_mono hmono _ W) (event_maxVol_mono hmono _ W)
    (by rw [iUnion_event_maxVol hmono hcover]; simp only [maxVolFull_eq_clusterMaxVol])
    (by rw [iUnion_event_maxVol hmono hcover]; simp only [maxVolFull_eq_clusterMaxVol]) hfin
  simpa using h

/-- **Exhaustion passage for (2.9).**  Same statement for the single cluster, with the product
shape `P(|K_max(W)| ≥ λ)^(3^(k-1)) * P(|K_u ∩ W| ≥ λ)` on the right. -/
theorem per_scale_single_of_finite {μ : Measure (Config V)} {A : ℕ → Set V} (hmono : Monotone A)
    (hcover : Covers A) (W : Finset V) (u : V) {lam : ℝ} {k : ℕ}
    (hfin : ∀ r, μ {ω : Config V | ENNReal.ofReal (3 ^ k * lam) ≤ vol (A r) ω u W} ≤
      (μ {ω : Config V | ENNReal.ofReal lam ≤ maxVol (A r) ω W}) ^ (3 ^ (k - 1)) *
        μ {ω : Config V | ENNReal.ofReal lam ≤ vol (A r) ω u W}) :
    μ {ω : Config V | ENNReal.ofReal (3 ^ k * lam) ≤ clusterVolIn ω u (W : Set V)} ≤
      (μ {ω : Config V | ENNReal.ofReal lam ≤ Percolation.clusterMaxVol ω W}) ^ (3 ^ (k - 1)) *
        μ {ω : Config V | ENNReal.ofReal lam ≤ clusterVolIn ω u (W : Set V)} := by
  have h := tendsto_prod_transfer
    (E := fun r => {ω : Config V | ENNReal.ofReal (3 ^ k * lam) ≤ vol (A r) ω u W})
    (F := fun r => {ω : Config V | ENNReal.ofReal lam ≤ maxVol (A r) ω W})
    (G := fun r => {ω : Config V | ENNReal.ofReal lam ≤ vol (A r) ω u W})
    (E' := {ω : Config V | ENNReal.ofReal (3 ^ k * lam) ≤ volFull ω u W})
    (F' := {ω : Config V | ENNReal.ofReal lam ≤ maxVolFull ω W})
    (G' := {ω : Config V | ENNReal.ofReal lam ≤ volFull ω u W})
    (event_vol_mono hmono _ u W) (event_maxVol_mono hmono _ W) (event_vol_mono hmono _ u W)
    (iUnion_event_vol hmono hcover _ u W).symm (iUnion_event_maxVol hmono hcover _ W).symm
    (iUnion_event_vol hmono hcover _ u W).symm hfin
  simpa only [volFull_eq_clusterVolIn, maxVolFull_eq_clusterMaxVol] using h

/-- `Covers` from a monotone exhaustion whose union is everything. -/
lemma covers_of_iUnion_eq_univ {A : ℕ → Set V} (hmono : Monotone A)
    (hun : (⋃ r, A r) = univ) : Covers A := by
  classical
  intro s
  have hmem : ∀ y ∈ s, ∃ r, y ∈ A r := by
    intro y _
    have : y ∈ (⋃ r, A r) := by rw [hun]; exact Set.mem_univ y
    exact Set.mem_iUnion.mp this
  let rho : V → ℕ := fun y => if h : y ∈ s then Classical.choose (hmem y h) else 0
  refine ⟨s.sup rho, fun y hy => ?_⟩
  have hspec : y ∈ A (rho y) := by
    simp only [rho, dite_eq_left (Finset.mem_coe.mp hy)]
    exact Classical.choose_spec (hmem y (Finset.mem_coe.mp hy))
  exact hmono (Finset.le_sup (f := rho) (Finset.mem_coe.mp hy)) hspec

/-! ## Whole parameter families -/

/-- **Exhaustion passage for the whole family (2.8).**  If every finite subgraph of a monotone
exhaustion satisfies the per-scale bound for all real `lam` and all `k`, then so does the
countable graph.  Note that the passage itself needs no hypothesis such as `lam ≥ 1` or `k ≥ 1`:
those belong to the finite-graph proof of Theorem 2.3. -/
theorem per_scale_family_of_finite {μ : Measure (Config V)} {A : ℕ → Set V} (hmono : Monotone A)
    (hcover : Covers A) (W : Finset V)
    (hfin : ∀ (r : ℕ) (lam : ℝ) (k : ℕ),
      μ {ω : Config V | ENNReal.ofReal (3 ^ k * lam) ≤ maxVol (A r) ω W} ≤
        (μ {ω : Config V | ENNReal.ofReal lam ≤ maxVol (A r) ω W}) ^ (3 ^ (k - 1) + 1)) :
    ∀ (lam : ℝ) (k : ℕ),
      μ {ω : Config V | ENNReal.ofReal (3 ^ k * lam) ≤ Percolation.clusterMaxVol ω W} ≤
        (μ {ω : Config V | ENNReal.ofReal lam ≤ Percolation.clusterMaxVol ω W}) ^
          (3 ^ (k - 1) + 1) :=
  fun lam k => per_scale_of_finite hmono hcover W (fun r => hfin r lam k)

/-- **Exhaustion passage for the whole family (2.9).** -/
theorem per_scale_single_family_of_finite {μ : Measure (Config V)} {A : ℕ → Set V}
    (hmono : Monotone A) (hcover : Covers A) (W : Finset V) (u : V)
    (hfin : ∀ (r : ℕ) (lam : ℝ) (k : ℕ),
      μ {ω : Config V | ENNReal.ofReal (3 ^ k * lam) ≤ vol (A r) ω u W} ≤
        (μ {ω : Config V | ENNReal.ofReal lam ≤ maxVol (A r) ω W}) ^ (3 ^ (k - 1)) *
          μ {ω : Config V | ENNReal.ofReal lam ≤ vol (A r) ω u W}) :
    ∀ (lam : ℝ) (k : ℕ),
      μ {ω : Config V | ENNReal.ofReal (3 ^ k * lam) ≤ clusterVolIn ω u (W : Set V)} ≤
        (μ {ω : Config V | ENNReal.ofReal lam ≤ Percolation.clusterMaxVol ω W}) ^ (3 ^ (k - 1)) *
          μ {ω : Config V | ENNReal.ofReal lam ≤ clusterVolIn ω u (W : Set V)} :=
  fun lam k => per_scale_single_of_finite hmono hcover W u (fun r => hfin r lam k)

/-- The same passage under the long-range percolation law `P_β` of the repository
(`longRangeMeasure J hJ β`), i.e. with no assumption on the weighted graph beyond countability
and on `β ≥ 0` beyond `β : ℝ≥0`. -/
theorem per_scale_longRange_of_finite {J : Sym2 V → ℝ} (hJ : ∀ e, 0 ≤ J e) {β : NNReal}
    {A : ℕ → Set V} (hmono : Monotone A) (hcover : Covers A) (W : Finset V)
    (hfin : ∀ (r : ℕ) (lam : ℝ) (k : ℕ),
      longRangeMeasure J hJ β {ω : Config V | ENNReal.ofReal (3 ^ k * lam) ≤ maxVol (A r) ω W} ≤
        (longRangeMeasure J hJ β {ω : Config V | ENNReal.ofReal lam ≤ maxVol (A r) ω W}) ^
          (3 ^ (k - 1) + 1)) :
    ∀ (lam : ℝ) (k : ℕ),
      longRangeMeasure J hJ β
          {ω : Config V | ENNReal.ofReal (3 ^ k * lam) ≤ Percolation.clusterMaxVol ω W} ≤
        (longRangeMeasure J hJ β
          {ω : Config V | ENNReal.ofReal lam ≤ Percolation.clusterMaxVol ω W}) ^
          (3 ^ (k - 1) + 1) :=
  per_scale_family_of_finite hmono hcover W hfin

end Exhaustion

end PercLib.CriticalLRP
