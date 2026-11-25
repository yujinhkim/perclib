/- Integrated from independently rebuilt Ultramath work.
Production base 70b027b0634874e65ce4bf8ec8fc8a7835e658e7.
Scratch source: repository-root .ultramath/smwwnvyp3/m3/.
-/

/- Case 1 (`d > 3α`) decorrelation estimate for Proposition I.4.20.
-/
module

public import PercLib.CriticalLRP.VolumeMoments.HigherMoments.I420Case1.Defs

/-!
# The Case 1 decorrelation estimate of Proposition I.4.20, from BK and FKG

Source: Tom Hutchcroft, *Critical long-range percolation I: High effective dimension*,
arXiv:2508.18807v1, proof of Proposition I.4.20, Case 1 (`d > 3α`), paper.txt lines
2831--2861.  For `0 ≤ ℓ ≤ p - 1` the paper proves

```
0 ≤ |B_r| E|K|^{ℓ+1} E|K|^{p-ℓ} − E[ |K|^{ℓ+1} ∑_{y∈B_r} 1(y∉K)|K_y|^{p-ℓ} ]
  ≤ E[ |K|^{p+1} |K ∩ B_r| ]  ≤  E|K|^{p+2}  ⪯_p  (E|K|)^{2p+3}  ≍_p  r^{(2p+3)α},
```

then `|B_r| E|K|^{ℓ+1}E|K|^{p-ℓ} ≍ r^{d+2pα}` and `d + 2pα > (2p+3)α` (which holds
because `d > 3α`) give (I.4.20), hence (I.4.21), which is the decorrelation input of
`VolumeMoments.HigherMoments.SecondInduction.derivative_ratio_tendsto`.

## What is proved here

* `mixedExcl_le_prodFactor` — the lower half `0 ≤ …`, from Lemma I.2.1(i)
  (`Hrest.twoCluster_ennreal`, i.e. BK) applied with the increasing functionals
  `|K|^a` and `|K|^b`.
* `prodFactor_le_mixedExcl_add_window` — the upper half, from the Harris--FKG side of
  Lemma I.2.1 (`Hrest.hrest_generic`), summed over `y ∈ B`: the exact identity
  `∑_y 1(y ∈ K_o) |K_o|^a |K_y|^b = |K_o|^{a+b} |K_o ∩ B|` (the clusters agree on the
  connection event) is what turns the `y`-sum into the mixed cluster-window moment.
* `windowMoment_le_powMoment` — `E[|K|^{p+1}|K ∩ B|] ≤ E|K|^{p+2}`.
* `ratio_tendsto_one_of_window_bound` — the purely real squeeze
  `1 − W/P ≤ A/P ≤ 1` with `W ⪯ r^{(2p+3)α}` and `P ⪰ r^{d+2pα}`.
* `case1_decorrelation` — the assembled estimate, in exactly the shape of the
  `hAmid`/`hAend` hypotheses of `SecondInduction.derivative_ratio_tendsto`.

The only inputs that are *not* proved here are the source's asymptotic order inputs,
carried as explicit hypotheses: homogeneity (transitivity of the weighted graph),
finiteness of `E|K|^{p+2}`, the tree-graph/regular-variation upper bound
`E|K|^{p+2} ⪯ r^{(2p+3)α}`, and the lower bound combining `|B_r| ≍ r^d` with
`E|K|^m ≍ r^{(2m-1)α}` in the shape `c r^{d+2pα} ≤ |B_r| E|K|^{ℓ+1} E|K|^{p-ℓ}`.
No numerical substitution and no `Fintype V` restriction is used.
-/

@[expose] public section

noncomputable section

open MeasureTheory Measure ProbabilityTheory unitInterval Filter
open scoped ENNReal Topology

set_option linter.unusedSectionVars false

namespace PercLib.CriticalLRP

namespace I420Case1

variable {V : Type*} [Countable V]

/-! ## 1.  `cardFun` of a cluster is the cluster volume, and powers of increasing
continuous functionals are continuous from below -/

theorem cardFun_cluster_eq_clusterVol (ω : Config V) (v : V) :
    Percolation.cardFun (cluster ω v) = clusterVol ω v := by
  rw [Percolation.cardFun_eq_encard, clusterVol_eq_encard]

/-- `cardFun` is continuous from below along a monotone union. -/
theorem cardFun_iUnion_monotone (S : ℕ → Set V) (hS : Monotone S) :
    Percolation.cardFun (⋃ n, S n) = ⨆ n, Percolation.cardFun (S n) := by
  refine le_antisymm ?_ (iSup_le fun n => Percolation.cardFun_mono (Set.subset_iUnion S n))
  rw [Percolation.cardFun]
  refine iSup_le fun m => ?_
  by_cases h : ∃ t : Finset V, m ≤ t.card ∧ (t : Set V) ⊆ ⋃ n, S n
  · obtain ⟨t, ht, htS⟩ := h
    rw [ite_eq_left ⟨t, ht, htS⟩, mul_one]
    have hex : ∀ v ∈ t, ∃ n, v ∈ S n := by
      intro v hv
      exact Set.mem_iUnion.mp (htS hv)
    classical
    obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ v ∈ t, v ∈ S N := by
      refine ⟨t.sup (fun v => if hv : v ∈ t then Classical.choose (hex v hv) else 0), ?_⟩
      intro v hv
      have hv' : v ∈ t := hv
      have hspec := Classical.choose_spec (hex v hv)
      exact hS (Finset.le_sup (f := fun v => if hv : v ∈ t then Classical.choose (hex v hv) else 0)
        hv') (by simpa [hv'] using hspec)
    have htS' : (t : Set V) ⊆ S N := fun v hv => hN v hv
    have hle : m ≤ Percolation.cardFun (S N) := by
      rw [Percolation.cardFun]
      exact le_iSup_of_le m (by rw [ite_eq_left ⟨t, ht, htS'⟩, mul_one])
    exact le_trans hle (le_iSup (fun n => Percolation.cardFun (S n)) N)
  · rw [ite_eq_right h, mul_zero]
    exact zero_le

/-- Powers of a monotone functional that is continuous from below along the edge
exhaustion are again continuous from below.  Here `F` plays the role of `|K_x|^a`. -/
theorem pow_cont_of_cont {F : Set V → ℝ≥0∞}
    (𝓔 : ℕ → Finset (Sym2 V))
    (hFmono : ∀ S T : Set V, S ⊆ T → F S ≤ F T) {x : V}
    (hFcont : ∀ (ω : Config V) (s : ℝ≥0∞), s < F (cluster ω x) →
      ∃ n, s < F (cluster (ω ∩ (𝓔 n : Set (Sym2 V))) x))
    (k : ℕ) :
    ∀ (ω : Config V) (s : ℝ≥0∞), s < (F (cluster ω x)) ^ k →
      ∃ n, s < (F (cluster (ω ∩ (𝓔 n : Set (Sym2 V))) x)) ^ k := by
  intro ω s hs
  have hEq : F (cluster ω x) = ⨆ n, F (cluster (ω ∩ (𝓔 n : Set (Sym2 V))) x) := by
    refine le_antisymm ?_ (iSup_le fun n =>
      hFmono _ _ (cluster_mono (fun e he => Set.mem_of_mem_inter_left he) x))
    · by_contra hcon
      have hlt : (⨆ n, F (cluster (ω ∩ (𝓔 n : Set (Sym2 V))) x)) < F (cluster ω x) :=
        lt_of_not_ge hcon
      obtain ⟨n, hn⟩ := hFcont ω _ hlt
      exact absurd hn (not_lt.mpr (le_iSup (fun n => F (cluster (ω ∩ (𝓔 n : Set (Sym2 V))) x)) n))
  rw [hEq, ENNReal.iSup_pow] at hs
  exact lt_iSup_iff.mp hs

/-! ## 2.  Lemma I.2.1 for the functionals `|K|^a` -/

/-- The disconnection indicator of `y ∉ K_o` is the indicator of `¬ o ↔ y`. -/
theorem indicator_compl_cluster (ω : Config V) (o y : V) :
    (cluster ω o)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) y =
      {ω' : Config V | ¬ Connects ω' o y}.indicator (fun _ => (1 : ℝ≥0∞)) ω := by
  by_cases h : Connects ω o y
  · have hy : y ∈ cluster ω o := mem_cluster_iff.mpr h
    rw [Set.indicator_of_notMem (by simpa using hy), Set.indicator_of_notMem (by simpa using h)]
  · have hy : y ∉ cluster ω o := by simpa [mem_cluster_iff] using h
    rw [Set.indicator_of_mem (by simpa using hy), Set.indicator_of_mem (by simpa using h)]

/-- The connection indicator of `y ∈ K_o` is the indicator of `o ↔ y`. -/
theorem indicator_cluster (ω : Config V) (o y : V) :
    (cluster ω o).indicator (fun _ => (1 : ℝ≥0∞)) y =
      {ω' : Config V | Connects ω' o y}.indicator (fun _ => (1 : ℝ≥0∞)) ω := by
  by_cases h : Connects ω o y
  · have hy : y ∈ cluster ω o := mem_cluster_iff.mpr h
    rw [Set.indicator_of_mem hy, Set.indicator_of_mem (by simpa using h)]
  · have hy : y ∉ cluster ω o := by simpa [mem_cluster_iff] using h
    rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem (by simpa using h)]

/-- **Lemma I.2.1(i) at a single `y`**, for the functionals `|K|^a` and `|K|^b`:
`E[1(o ↮ y)|K_o|^a|K_y|^b] ≤ E|K_o|^a · E|K_y|^b`. -/
theorem hrest_pow_le {π : Sym2 V → unitInterval} (hπ : ∀ e, π e < 1)
    (𝓔 : ℕ → Finset (Sym2 V)) (h𝓔mono : Monotone 𝓔) (h𝓔 : ∀ e : Sym2 V, ∃ n, e ∈ 𝓔 n)
    (o y : V) (a b : ℕ) :
    ∫⁻ ω, {ω' : Config V | ¬ Connects ω' o y}.indicator (fun _ => (1 : ℝ≥0∞)) ω *
        (clusterVol ω o ^ a * clusterVol ω y ^ b) ∂(edgeMeasure π)
      ≤ powMomentAt π a o * powMomentAt π b y := by
  have h := Hrest.twoCluster_ennreal (π := π) hπ o y 𝓔 h𝓔mono h𝓔
    (F := fun S => Percolation.cardFun S ^ a) (G := fun S => Percolation.cardFun S ^ b)
    (fun S T hST => pow_le_pow_left' (Percolation.cardFun_mono hST) a)
    (fun S T hST => pow_le_pow_left' (Percolation.cardFun_mono hST) b)
    (pow_cont_of_cont (x := o) 𝓔 (Percolation.cardFun_mono)
      (Hrest.cardFun_cont_canonical 𝓔 h𝓔mono h𝓔 o) a)
    (pow_cont_of_cont (x := y) 𝓔 (Percolation.cardFun_mono)
      (Hrest.cardFun_cont_canonical 𝓔 h𝓔mono h𝓔 y) b)
    ((Hrest.measurable_cardFun_cluster_canonical o).pow_const a)
    ((Hrest.measurable_cardFun_cluster_canonical y).pow_const b)
  simpa only [cardFun_cluster_eq_clusterVol, powMomentAt] using h

/-- **The Harris--FKG half of Lemma I.2.1 at a single `y`**:
`E|K_o|^a E|K_y|^b − E[1(o ↮ y)|K_o|^a|K_y|^b] ≤ E[1(o ↔ y)|K_o|^a|K_o|^b]`.
The right-hand side has both factors at `o` because the two clusters agree on
`{o ↔ y}`. -/
theorem hrest_pow_le_add {π : Sym2 V → unitInterval} (hπ : ∀ e, π e < 1)
    (𝓔 : ℕ → Finset (Sym2 V)) (h𝓔mono : Monotone 𝓔) (h𝓔 : ∀ e : Sym2 V, ∃ n, e ∈ 𝓔 n)
    (o y : V) (a b : ℕ) :
    powMomentAt π a o * powMomentAt π b y
      ≤ (∫⁻ ω, {ω' : Config V | ¬ Connects ω' o y}.indicator (fun _ => (1 : ℝ≥0∞)) ω *
            (clusterVol ω o ^ a * clusterVol ω y ^ b) ∂(edgeMeasure π))
        + ∫⁻ ω, {ω' : Config V | Connects ω' o y}.indicator (fun _ => (1 : ℝ≥0∞)) ω *
            (clusterVol ω o ^ a * clusterVol ω o ^ b) ∂(edgeMeasure π) := by
  have h := Hrest.hrest_generic (π := π) hπ o y 𝓔 h𝓔mono h𝓔
    (F := fun S => Percolation.cardFun S ^ a) (G := fun S => Percolation.cardFun S ^ b)
    (fun S T hST => pow_le_pow_left' (Percolation.cardFun_mono hST) a)
    (fun S T hST => pow_le_pow_left' (Percolation.cardFun_mono hST) b)
    (pow_cont_of_cont (x := o) 𝓔 (Percolation.cardFun_mono)
      (Hrest.cardFun_cont_canonical 𝓔 h𝓔mono h𝓔 o) a)
    (pow_cont_of_cont (x := y) 𝓔 (Percolation.cardFun_mono)
      (Hrest.cardFun_cont_canonical 𝓔 h𝓔mono h𝓔 y) b)
    ((Hrest.measurable_cardFun_cluster_canonical o).pow_const a)
    ((Hrest.measurable_cardFun_cluster_canonical y).pow_const b)
  rw [tsub_le_iff_right, add_comm] at h
  simpa only [cardFun_cluster_eq_clusterVol, powMomentAt] using h

/-! ## 3.  The excluded expectation and the window moment as `y`-sums -/

theorem mixedExcl_eq_sum_lintegral (π : Sym2 V → unitInterval) (o : V) (a b : ℕ)
    (B : Finset V) :
    mixedExcl π o a b B =
      ∑ y ∈ B, ∫⁻ ω, {ω' : Config V | ¬ Connects ω' o y}.indicator
          (fun _ => (1 : ℝ≥0∞)) ω * (clusterVol ω o ^ a * clusterVol ω y ^ b)
        ∂(edgeMeasure π) := by
  rw [mixedExcl]
  have hpt : ∀ ω : Config V, clusterVol ω o ^ a *
        ∑ y ∈ B, (cluster ω o)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) y * clusterVol ω y ^ b
      = ∑ y ∈ B, {ω' : Config V | ¬ Connects ω' o y}.indicator (fun _ => (1 : ℝ≥0∞)) ω *
          (clusterVol ω o ^ a * clusterVol ω y ^ b) := by
    intro ω
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [indicator_compl_cluster]
    ring
  rw [lintegral_congr hpt, lintegral_finsetSum]
  intro y _
  exact (measurable_const.indicator (measurableSet_connects o y).compl).mul
    ((measurable_clusterVol o).pow_const a |>.mul (measurable_clusterVol y |>.pow_const b))

theorem windowMoment_eq_sum_lintegral (π : Sym2 V → unitInterval) (o : V) (a b : ℕ)
    (B : Finset V) :
    windowMoment π o (a + b) B =
      ∑ y ∈ B, ∫⁻ ω, {ω' : Config V | Connects ω' o y}.indicator
          (fun _ => (1 : ℝ≥0∞)) ω * (clusterVol ω o ^ a * clusterVol ω o ^ b)
        ∂(edgeMeasure π) := by
  rw [windowMoment]
  have hpt : ∀ ω : Config V, clusterVol ω o ^ (a + b) * clusterVolIn ω o (B : Set V)
      = ∑ y ∈ B, {ω' : Config V | Connects ω' o y}.indicator (fun _ => (1 : ℝ≥0∞)) ω *
          (clusterVol ω o ^ a * clusterVol ω o ^ b) := by
    intro ω
    rw [clusterVolIn_coe_finset, Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    by_cases hy : y ∈ cluster ω o
    · have hc : Connects ω o y := mem_cluster_iff.mp hy
      rw [ite_eq_left hy, Set.indicator_of_mem (by simpa using hc), one_mul, mul_one, ← pow_add]
    · have hc : ¬ Connects ω o y := by simpa [mem_cluster_iff] using hy
      rw [ite_eq_right hy, Set.indicator_of_notMem (by simpa using hc), zero_mul, mul_zero]
  rw [lintegral_congr hpt, lintegral_finsetSum]
  intro y _
  exact (measurable_const.indicator (measurableSet_connects o y)).mul
    ((measurable_clusterVol o).pow_const a |>.mul (measurable_clusterVol o |>.pow_const b))

/-! ## 4.  The two halves of the Case 1 discrepancy -/

/-- **The lower half** `A_ℓ(r) ≤ |B| E|K|^a E|K|^b` of the Case 1 display,
from the BK direction of Lemma I.2.1. -/
theorem mixedExcl_le_prodFactor {π : Sym2 V → unitInterval} (hπ : ∀ e, π e < 1)
    (𝓔 : ℕ → Finset (Sym2 V)) (h𝓔mono : Monotone 𝓔) (h𝓔 : ∀ e : Sym2 V, ∃ n, e ∈ 𝓔 n)
    (o : V) (a b : ℕ) (B : Finset V) :
    mixedExcl π o a b B ≤ prodFactor π o a b B := by
  rw [mixedExcl_eq_sum_lintegral, prodFactor]
  exact Finset.sum_le_sum fun y _ => hrest_pow_le hπ 𝓔 h𝓔mono h𝓔 o y a b

/-- **The upper half** of the Case 1 display: the excluded mixed marked expectation
is at most the product factor plus the mixed cluster-window moment,
`A_ℓ(r) + E[|K|^{a+b}|K ∩ B|] ≥ |B| E|K|^a E|K|^b`. -/
theorem prodFactor_le_mixedExcl_add_window {π : Sym2 V → unitInterval} (hπ : ∀ e, π e < 1)
    (𝓔 : ℕ → Finset (Sym2 V)) (h𝓔mono : Monotone 𝓔) (h𝓔 : ∀ e : Sym2 V, ∃ n, e ∈ 𝓔 n)
    (o : V) (a b : ℕ) (B : Finset V) :
    prodFactor π o a b B ≤ mixedExcl π o a b B + windowMoment π o (a + b) B := by
  rw [mixedExcl_eq_sum_lintegral, windowMoment_eq_sum_lintegral, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun y _ => hrest_pow_le_add hπ 𝓔 h𝓔mono h𝓔 o y a b

/-- `E[|K_o|^k |K_o ∩ B|] ≤ E|K_o|^{k+1}`: the mixed cluster-window moment is
dominated by the next ordinary cluster moment. -/
theorem windowMoment_le_powMoment (π : Sym2 V → unitInterval) (o : V) (k : ℕ) (B : Finset V) :
    windowMoment π o k B ≤ powMomentAt π (k + 1) o := by
  rw [windowMoment, powMomentAt]
  refine lintegral_mono fun ω => ?_
  have hle : clusterVolIn ω o (B : Set V) ≤ clusterVol ω o := by
    rw [← clusterVolIn_univ]
    exact clusterVolIn_mono (Set.subset_univ _)
  calc clusterVol ω o ^ k * clusterVolIn ω o (B : Set V) ≤ clusterVol ω o ^ k * clusterVol ω o :=
        by gcongr
    _ = clusterVol ω o ^ (k + 1) := by rw [pow_succ]

theorem windowMoment_ne_top {π : Sym2 V → unitInterval} {o : V} {k : ℕ} {B : Finset V}
    (h : powMomentAt π (k + 1) o ≠ ⊤) : windowMoment π o k B ≠ ⊤ :=
  ne_top_of_le_ne_top h (windowMoment_le_powMoment π o k B)

/-! ## 5.  Real-valued form of the discrepancy -/

theorem prodFactor_toReal (π : Sym2 V → unitInterval) (o : V) (a b : ℕ) (B : Finset V)
    (hhom : ∀ y ∈ B, powMomentAt π b y = powMomentAt π b o) :
    (prodFactor π o a b B).toReal = (B.card : ℝ) * (momR π a o * momR π b o) := by
  rw [prodFactor]
  have h1 : ∑ y ∈ B, powMomentAt π a o * powMomentAt π b y
      = ∑ _y ∈ B, powMomentAt π a o * powMomentAt π b o :=
    Finset.sum_congr rfl fun y hy => by rw [hhom y hy]
  rw [h1, Finset.sum_const, nsmul_eq_mul]
  simp only [momR, ENNReal.toReal_mul, ENNReal.toReal_natCast]

/-- **The Case 1 discrepancy inequality in `ℝ`:**
`|B| E|K|^a E|K|^b − A_ℓ(r) ≤ E[|K|^{a+b}|K ∩ B|]`. -/
theorem discrepancy_toReal {π : Sym2 V → unitInterval} (hπ : ∀ e, π e < 1)
    (𝓔 : ℕ → Finset (Sym2 V)) (h𝓔mono : Monotone 𝓔) (h𝓔 : ∀ e : Sym2 V, ∃ n, e ∈ 𝓔 n)
    (o : V) (a b : ℕ) (B : Finset V)
    (hPtop : prodFactor π o a b B ≠ ⊤) (hWtop : windowMoment π o (a + b) B ≠ ⊤) :
    (prodFactor π o a b B).toReal - (mixedExcl π o a b B).toReal
      ≤ (windowMoment π o (a + b) B).toReal := by
  have hAP : mixedExcl π o a b B ≤ prodFactor π o a b B :=
    mixedExcl_le_prodFactor hπ 𝓔 h𝓔mono h𝓔 o a b B
  have hsum : prodFactor π o a b B ≤ mixedExcl π o a b B + windowMoment π o (a + b) B :=
    prodFactor_le_mixedExcl_add_window hπ 𝓔 h𝓔mono h𝓔 o a b B
  have hsum' : prodFactor π o a b B ≤ windowMoment π o (a + b) B + mixedExcl π o a b B := by
    rw [add_comm]; exact hsum
  have hsub : prodFactor π o a b B - mixedExcl π o a b B ≤ windowMoment π o (a + b) B :=
    tsub_le_iff_right.mpr hsum'
  have h1 : (prodFactor π o a b B - mixedExcl π o a b B).toReal
      ≤ (windowMoment π o (a + b) B).toReal :=
    ENNReal.toReal_mono hWtop hsub
  rwa [ENNReal.toReal_sub_of_le hAP hPtop] at h1

/-- `0 ≤ A_ℓ(r)` and `A_ℓ(r) ≤ |B| E|K|^a E|K|^b` in `ℝ`. -/
theorem mixedExcl_toReal_le_prodFactor_toReal {π : Sym2 V → unitInterval} (hπ : ∀ e, π e < 1)
    (𝓔 : ℕ → Finset (Sym2 V)) (h𝓔mono : Monotone 𝓔) (h𝓔 : ∀ e : Sym2 V, ∃ n, e ∈ 𝓔 n)
    (o : V) (a b : ℕ) (B : Finset V) (hPtop : prodFactor π o a b B ≠ ⊤) :
    (mixedExcl π o a b B).toReal ≤ (prodFactor π o a b B).toReal :=
  ENNReal.toReal_mono hPtop (mixedExcl_le_prodFactor hπ 𝓔 h𝓔mono h𝓔 o a b B)

/-! ## 6.  The real squeeze and the exponent arithmetic -/

/-- **The Case 1 squeeze.**  If `A ≤ P`, `P − A ≤ W`, `W ≤ C r^γ` and `c r^δ ≤ P` with
`c > 0` and `γ < δ`, then `A/P → 1`. -/
theorem ratio_tendsto_one_of_window_bound {A P W : ℝ → ℝ} {γ δ C c : ℝ}
    (hC : 0 ≤ C) (hc : 0 < c) (hγδ : γ < δ)
    (hAP : ∀ r : ℝ, 0 < r → A r ≤ P r)
    (hdiff : ∀ r : ℝ, 0 < r → P r - A r ≤ W r)
    (hW : ∀ r : ℝ, 0 < r → W r ≤ C * r ^ γ)
    (hP : ∀ r : ℝ, 0 < r → c * r ^ δ ≤ P r) :
    Tendsto (fun r : ℝ => A r / P r) atTop (𝓝 1) := by
  have hpos : ∀ r : ℝ, 0 < r → 0 < P r := fun r hr =>
    lt_of_lt_of_le (mul_pos hc (Real.rpow_pos_of_pos hr δ)) (hP r hr)
  have hupper : ∀ r : ℝ, 0 < r → (P r - A r) / P r ≤ (C / c) * r ^ (γ - δ) := by
    intro r hr
    have hPr : 0 < P r := hpos r hr
    have hstep1 : (P r - A r) / P r ≤ W r / P r :=
      div_le_div_of_nonneg_right (hdiff r hr) (le_of_lt hPr)
    have hcd : 0 < c * r ^ δ := mul_pos hc (Real.rpow_pos_of_pos hr δ)
    have hstep2 : W r / P r ≤ (C * r ^ γ) / (c * r ^ δ) :=
      div_le_div₀ (mul_nonneg hC (Real.rpow_nonneg (le_of_lt hr) γ)) (hW r hr) hcd (hP r hr)
    have hstep3 : (C * r ^ γ) / (c * r ^ δ) = (C / c) * r ^ (γ - δ) := by
      rw [Real.rpow_sub hr, div_mul_div_comm]
    rw [hstep3] at hstep2
    linarith [hstep1, hstep2]
  have hlim : Tendsto (fun r : ℝ => (C / c) * r ^ (γ - δ)) atTop (𝓝 0) := by
    have hy : 0 < δ - γ := by linarith
    have h := (tendsto_rpow_neg_atTop hy).const_mul (C / c)
    have hfun : (fun r : ℝ => (C / c) * r ^ (-(δ - γ))) = fun r : ℝ => (C / c) * r ^ (γ - δ) := by
      funext r
      rw [neg_sub]
    rw [hfun] at h
    simpa using h
  have hlow : Tendsto (fun r : ℝ => 1 - (C / c) * r ^ (γ - δ)) atTop (𝓝 1) := by
    have h1c : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
    have h := h1c.sub hlim
    simpa using h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
    have hPr : 0 < P r := hpos r hr
    have hkey : 1 - (P r - A r) / P r = A r / P r := by
      field_simp
      ring
    linarith [hupper r hr, hkey.le, hkey.ge]
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
    exact (div_le_one (hpos r hr)).mpr (hAP r hr)

/-- **The exponent computation of Case 1.**  Since `d > 3α`, the moment index
`d + 2pα` of `|B_r| E|K|^{ℓ+1} E|K|^{p-ℓ}` strictly exceeds the tree-graph index
`(2p+3)α` of `E|K|^{p+2}`. -/
theorem exponent_lt_of_three_alpha_lt {α d : ℝ} (p : ℕ) (hd : 3 * α < d) :
    ((2 * (p : ℝ) + 3) * α) < d + 2 * (p : ℝ) * α := by
  nlinarith

/-! ## 7.  The assembled Case 1 decorrelation estimate -/

/-- **Case 1 of Proposition I.4.20** (`d > 3α`), in the shape consumed by
`SecondInduction.derivative_ratio_tendsto`.

For the canonical independent-edge law `edgeMeasure π` on `Config V`, a base point `o`,
`p`, `ℓ ≤ p`, exponents `α > 0` and `d > 3α`, and a family of windows `B r`, assume the
source's inputs

* `hhom` — homogeneity of the `(p-ℓ)`-th moment (transitivity of the weighted graph);
* `hmomtop` — finiteness of `E|K|^{p+2}`;
* `hWmom` — the tree-graph + regular-variation bound `E|K|^{p+2} ⪯ r^{(2p+3)α}`;
* `hP` — the lower bound `c r^{d+2pα} ≤ |B_r| E|K|^{ℓ+1} E|K|^{p-ℓ}`.

Then the exact excluded mixed marked expectation satisfies
`A_ℓ(r)/(|B_r| E|K|^{ℓ+1} E|K|^{p-ℓ}) → 1`, i.e. (I.4.20) holds.  The discrepancy
itself is not assumed: it is `discrepancy_toReal`, proved from BK/FKG. -/
theorem case1_decorrelation
    (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1) (o : V)
    (𝓔 : ℕ → Finset (Sym2 V)) (h𝓔mono : Monotone 𝓔) (h𝓔 : ∀ e : Sym2 V, ∃ n, e ∈ 𝓔 n)
    (p ℓ : ℕ) (hℓ : ℓ ≤ p)
    {α d C c : ℝ} (hC : 0 ≤ C) (hd : 3 * α < d) (hc : 0 < c)
    (B : ℝ → Finset V)
    (hhom : ∀ (r : ℝ) (y : V), y ∈ B r → powMomentAt π (p - ℓ) y = powMomentAt π (p - ℓ) o)
    (hmomtop : powMomentAt π (p + 2) o ≠ ⊤)
    (hWmom : ∀ r : ℝ, 0 < r → momR π (p + 2) o ≤ C * r ^ ((2 * (p : ℝ) + 3) * α))
    (hP : ∀ r : ℝ, 0 < r →
      c * r ^ (d + 2 * (p : ℝ) * α) ≤
        (B r).card * (momR π (ℓ + 1) o * momR π (p - ℓ) o)) :
    Tendsto (fun r : ℝ => (mixedExcl π o (ℓ + 1) (p - ℓ) (B r)).toReal /
      ((B r).card * (momR π (ℓ + 1) o * momR π (p - ℓ) o))) atTop (𝓝 1) := by
  have hab : ℓ + 1 + (p - ℓ) = p + 1 := by omega
  have hab' : ℓ + 1 + (p - ℓ) + 1 = p + 2 := by omega
  have hPtop : ∀ r : ℝ, 0 < r → prodFactor π o (ℓ + 1) (p - ℓ) (B r) ≠ ⊤ := by
    intro r hr htop
    have hval : (prodFactor π o (ℓ + 1) (p - ℓ) (B r)).toReal
        = (B r).card * (momR π (ℓ + 1) o * momR π (p - ℓ) o) :=
      prodFactor_toReal π o (ℓ + 1) (p - ℓ) (B r) (fun y hy => hhom r y hy)
    rw [htop, ENNReal.toReal_top] at hval
    have hpos : (0 : ℝ) < c * r ^ (d + 2 * (p : ℝ) * α) :=
      mul_pos hc (Real.rpow_pos_of_pos hr _)
    have hle := hP r hr
    rw [← hval] at hle
    linarith
  have hdiff : ∀ r : ℝ, 0 < r →
      (B r).card * (momR π (ℓ + 1) o * momR π (p - ℓ) o)
        - (mixedExcl π o (ℓ + 1) (p - ℓ) (B r)).toReal
        ≤ (windowMoment π o (p + 1) (B r)).toReal := by
    intro r hr
    have hPt := hPtop r hr
    have hWt : windowMoment π o (ℓ + 1 + (p - ℓ)) (B r) ≠ ⊤ :=
      windowMoment_ne_top (by rw [hab']; exact hmomtop)
    have hdisc := discrepancy_toReal (π := π) hπ 𝓔 h𝓔mono h𝓔 o (ℓ + 1) (p - ℓ) (B r) hPt hWt
    have hval : (prodFactor π o (ℓ + 1) (p - ℓ) (B r)).toReal
        = (B r).card * (momR π (ℓ + 1) o * momR π (p - ℓ) o) :=
      prodFactor_toReal π o (ℓ + 1) (p - ℓ) (B r) (fun y hy => hhom r y hy)
    rw [hab] at hdisc
    rwa [hval] at hdisc
  have hW : ∀ r : ℝ, 0 < r →
      (windowMoment π o (p + 1) (B r)).toReal ≤ C * r ^ ((2 * (p : ℝ) + 3) * α) := by
    intro r hr
    have hle : windowMoment π o (p + 1) (B r) ≤ powMomentAt π (p + 2) o := by
      have h := windowMoment_le_powMoment π o (p + 1) (B r)
      rwa [show p + 1 + 1 = p + 2 by omega] at h
    have hmono : (windowMoment π o (p + 1) (B r)).toReal ≤ (powMomentAt π (p + 2) o).toReal :=
      ENNReal.toReal_mono hmomtop hle
    exact le_trans hmono (hWmom r hr)
  have hAP : ∀ r : ℝ, 0 < r →
      (mixedExcl π o (ℓ + 1) (p - ℓ) (B r)).toReal
        ≤ (B r).card * (momR π (ℓ + 1) o * momR π (p - ℓ) o) := by
    intro r hr
    have hPt := hPtop r hr
    have hle := mixedExcl_toReal_le_prodFactor_toReal (π := π) hπ 𝓔 h𝓔mono h𝓔 o (ℓ + 1) (p - ℓ)
      (B r) hPt
    have hval : (prodFactor π o (ℓ + 1) (p - ℓ) (B r)).toReal
        = (B r).card * (momR π (ℓ + 1) o * momR π (p - ℓ) o) :=
      prodFactor_toReal π o (ℓ + 1) (p - ℓ) (B r) (fun y hy => hhom r y hy)
    rwa [hval] at hle
  exact ratio_tendsto_one_of_window_bound hC hc
    (exponent_lt_of_three_alpha_lt p hd) hAP hdiff hW hP

end I420Case1

end PercLib.CriticalLRP
