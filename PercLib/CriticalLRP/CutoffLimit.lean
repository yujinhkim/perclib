/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
Provenance: written for Hutchcroft, "Critical long-range percolation I: High effective
dimension", arXiv:2508.18807v1, Definition I.1.5 and the monotone coupling of §I.3
(display (I.3.1), p. 29), where the paper passes between `P_{βc,r}` and `P_{βc}`.

# Monotone convergence of the cut-off first moment in the cut-off radius

This file proves, for the cut-off kernel `J_r` of Definition I.1.5, the two statements the
paper uses when it compares the cut-off model with the uncut one:

* `P_{β,r}(x ↔ y)` is nondecreasing in `r` and increases to `P_β(x ↔ y)`
  (`iSup_edgeMeasure_connects_cutoff`);
* `E_{β,r}|K_o|` is nondecreasing in `r` and increases to `E_β|K_o|`, including the case
  `E_β|K_o| = ⊤` (`iSup_lintegral_clusterVol_cutoff`, `tendsto_lintegral_clusterVol_cutoff`);
* consequently, if `E_β|K_o| = ⊤` then `E_{β,r}|K_o| → ⊤` as `r → ∞`
  (`tendsto_lintegral_clusterVol_cutoff_top`) and every finite `C` is eventually exceeded
  (`exists_lintegral_clusterVol_cutoff_ge`).

## Method (no smoothness, no sharpness, no mean bounds assumed)

The engine is the monotone coupling of `CountableProduct/Marks.lean`: every law `P_π` is the
image of one mark measure under `u ↦ {e : u_e < π_e}`, and the map is monotone in `π`.  The one
non-formal fact used is that **connectivity is witnessed by a finite path**: on a fixed mark
configuration `u`, if `Connects (atParameter q u) v w` then, because a path has finitely many
edges and each inequality `u_e < q_e` is eventually satisfied along a monotone family
`p n ↑ q`, there is `n` with `Connects (atParameter (p n) u) v w`
(`exists_connects_atParameter_of_connects`).  Hence the preimages of the connection event
*saturate* (`⋃ n (atParameter (p n))⁻¹ {v ↔ w} = (atParameter q)⁻¹ {v ↔ w}`), and continuity
from below for the mark measure gives `P_{p n}(v ↔ w) ↑ P_q(v ↔ w)`.  Summing over `w` with
`lintegral_clusterVol_eq_tsum_connSet` and the sup/`tsum` commutation
`iSup_tsum_of_monotone` gives the first moment.

## Interface notes

* `sample`/`uncut` model: the uncut kernel of a profile `K` is
  `kernelJ (fun y => K ‖y‖_∞)`, i.e. `J(x,y) = K(‖y − x‖_∞)`.  The hypothesis `hK0 : K 0 = 0`
  is exactly the paper's factor `1(x ≠ y)`: it makes the diagonal of the uncut kernel agree
  with the diagonal `0` of `CutoffKernel.cutoffSymKernel`, so the two families differ only on
  edges of finite length.  (For the model profile `r ↦ r^{-d-α}` this holds by the `rpow`
  convention `0 ^ (-(d+α)) = 0`.)
* `β : NNReal` and `K` is an arbitrary nonnegative antitone profile with `K → 0` at infinity;
  no regularity beyond antitonicity on `(0,∞)` and `Tendsto K atTop (𝓝 0)` is used.
* `CutoffKernel.cutoffSymKernel_nonneg'` extends the nonnegativity of `J_r` to all real `r`,
  which lets the supremum run over all `r : ℝ` rather than over `r ≥ 1`.

## Not claimed

No sharpness theorem, no bound on `E_{βc,r}|K|` in terms of `r`, and no derivative in `r`
(see `RussoDominated`/`SpatialDominated` for the capped Russo machinery).  In particular the
uncut mean `E_β|K_o|` is *not* proved finite or infinite anywhere here: infiniteness is only
ever a hypothesis.

No `sorry`, no `admit`, no `native_decide`, no custom axioms.
-/
module

public import PercLib.CriticalLRP.MassTransportI41
public import PercLib.CriticalLRP.Correlation.I411.DiagramAssembly
public import PercLib.CriticalLRP.TreeExpansion.SymmetricGroup.Expectation.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import PercLib.CriticalLRP.KernelGeometry
public import PercLib.CriticalLRP.Correlation.Susceptibility

set_option autoImplicit true

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

@[expose] public section

open MeasureTheory Measure ProbabilityTheory unitInterval Filter Topology
open scoped ENNReal Topology

namespace PercLib.CriticalLRP

variable {V : Type*} [Countable V]

/-! ## Monotone edge-probability families exhaust the connection event -/

theorem exists_lt_of_tendsto {p : ℕ → Sym2 V → unitInterval} {q : Sym2 V → unitInterval}
    (hlim : ∀ e : Sym2 V,
      Tendsto (fun n : ℕ => ((p n e : unitInterval) : ℝ)) atTop (𝓝 ((q e : unitInterval) : ℝ)))
    {u : Sym2 V → ℝ} {e : Sym2 V} (h : u e < ((q e : unitInterval) : ℝ)) :
    ∃ N : ℕ, u e < ((p N e : unitInterval) : ℝ) := by
  have hmem : ∀ᶠ n : ℕ in atTop, u e < ((p n e : unitInterval) : ℝ) :=
    (hlim e).eventually (Ioi_mem_nhds h)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hmem
  exact ⟨N, hN N le_rfl⟩

theorem exists_forall_mem_list_lt {p : ℕ → Sym2 V → unitInterval}
    (hmonoE : ∀ e : Sym2 V, Monotone (fun n : ℕ => ((p n e : unitInterval) : ℝ)))
    (u : Sym2 V → ℝ) :
    ∀ (l : List (Sym2 V)), (∀ e ∈ l, ∃ N : ℕ, u e < ((p N e : unitInterval) : ℝ)) →
      ∃ N : ℕ, ∀ e ∈ l, u e < ((p N e : unitInterval) : ℝ) := by
  intro l
  induction l with
  | nil => intro _; exact ⟨0, by simp⟩
  | cons head tail ih =>
      intro h
      obtain ⟨N₁, h₁⟩ := h head (by simp)
      obtain ⟨N₂, h₂⟩ := ih (fun e he => h e (by simp [he]))
      refine ⟨max N₁ N₂, fun e he => ?_⟩
      rcases List.mem_cons.mp he with hhead | he'
      · have hfin : u head < ((p (max N₁ N₂) head : unitInterval) : ℝ) :=
          lt_of_lt_of_le h₁ (hmonoE head (le_max_left N₁ N₂))
        simpa only [hhead] using hfin
      · exact lt_of_lt_of_le (h₂ e he') (hmonoE e (le_max_right N₁ N₂))

theorem monotone_coe_of_mono {p : ℕ → Sym2 V → unitInterval}
    (hmono : ∀ (n : ℕ) (e : Sym2 V), p n e ≤ p (n + 1) e) (e : Sym2 V) :
    Monotone (fun n : ℕ => ((p n e : unitInterval) : ℝ)) := by
  have hmi : Monotone (fun n : ℕ => p n e) := monotone_nat_of_le_succ fun n => hmono n e
  exact fun a b hab => Subtype.coe_le_coe.mpr (hmi hab)

/-- **The connection event is exhausted.** -/
theorem exists_connects_atParameter_of_connects {p : ℕ → Sym2 V → unitInterval}
    {q : Sym2 V → unitInterval}
    (hmono : ∀ (n : ℕ) (e : Sym2 V), p n e ≤ p (n + 1) e)
    (hlim : ∀ e : Sym2 V,
      Tendsto (fun n : ℕ => ((p n e : unitInterval) : ℝ)) atTop (𝓝 ((q e : unitInterval) : ℝ)))
    {u : Sym2 V → ℝ} {v w : V} (h : Connects (atParameter q u) v w) :
    ∃ n : ℕ, Connects (atParameter (p n) u) v w := by
  classical
  obtain ⟨walk, hwalk⟩ := pathConnects_iff.mpr h
  have hmonoE := monotone_coe_of_mono hmono
  have hex : ∀ e ∈ walk.edges, ∃ N : ℕ, u e < ((p N e : unitInterval) : ℝ) := by
    intro e he
    exact exists_lt_of_tendsto hlim (hwalk e he)
  obtain ⟨N, hN⟩ := exists_forall_mem_list_lt hmonoE u walk.edges hex
  exact ⟨N, pathConnects_iff.mp ⟨walk, fun e he => hN e he⟩⟩

/-- Pointwise domination follows from monotone convergence of the edge probabilities. -/
theorem le_of_le_succ_of_tendsto {p : ℕ → Sym2 V → unitInterval} {q : Sym2 V → unitInterval}
    (hmono : ∀ (n : ℕ) (e : Sym2 V), p n e ≤ p (n + 1) e)
    (hlim : ∀ e : Sym2 V,
      Tendsto (fun n : ℕ => ((p n e : unitInterval) : ℝ)) atTop (𝓝 ((q e : unitInterval) : ℝ)))
    (n : ℕ) (e : Sym2 V) : p n e ≤ q e := by
  refine Subtype.coe_le_coe.mp ?_
  have hmonoE := monotone_coe_of_mono hmono e
  exact ge_of_tendsto (hlim e) (eventually_atTop.mpr ⟨n, fun m hm => hmonoE hm⟩)


/-! ## Measures of monotone unions -/

theorem iSup_measure_iUnion {α : Type*} [MeasurableSpace α] {μ : Measure α} {s : ℕ → Set α}
    (hmono : Monotone s) : (⨆ n : ℕ, μ (s n)) = μ (⋃ n, s n) := by
  refine le_antisymm (iSup_le fun n => measure_mono (Set.subset_iUnion s n)) ?_
  exact le_of_tendsto (tendsto_measure_iUnion_atTop (μ := μ) hmono)
    (Eventually.of_forall fun n => le_iSup (fun n => μ (s n)) n)

/-! ## Monotone convergence of the connection probabilities -/

theorem iSup_edgeMeasure_connects {p : ℕ → Sym2 V → unitInterval} {q : Sym2 V → unitInterval}
    (hmono : ∀ (n : ℕ) (e : Sym2 V), p n e ≤ p (n + 1) e)
    (hlim : ∀ e : Sym2 V,
      Tendsto (fun n : ℕ => ((p n e : unitInterval) : ℝ)) atTop (𝓝 ((q e : unitInterval) : ℝ)))
    (v w : V) :
    (⨆ n : ℕ, edgeMeasure (p n) {ω : Config V | Connects ω v w})
      = edgeMeasure q {ω : Config V | Connects ω v w} := by
  classical
  set A : Set (Config V) := {ω | Connects ω v w} with hAdef
  have hA : MeasurableSet A := measurableSet_connects v w
  have hinc : IsIncreasing A := isIncreasing_connects v w
  have hpq : ∀ (n : ℕ) (e : Sym2 V), p n e ≤ q e := le_of_le_succ_of_tendsto hmono hlim
  have hmark : ∀ r : Sym2 V → unitInterval,
      edgeMeasure r A = (markMeasure V) ((atParameter r) ⁻¹' A) := by
    intro r
    rw [← markMeasure_map_atParameter r, Measure.map_apply (measurable_atParameter r) hA]
  have hsub : ∀ n : ℕ, (atParameter (p n)) ⁻¹' A ⊆ (atParameter q) ⁻¹' A := by
    intro n u hu
    refine hinc ?_ hu
    intro e he
    exact lt_of_lt_of_le he (Subtype.coe_le_coe.mpr (hpq n e))
  have hcover : (atParameter q) ⁻¹' A ⊆ ⋃ n, (atParameter (p n)) ⁻¹' A := by
    intro u hu
    exact Set.mem_iUnion.mpr (exists_connects_atParameter_of_connects hmono hlim hu)
  have hunion : (⋃ n, (atParameter (p n)) ⁻¹' A) = (atParameter q) ⁻¹' A :=
    Set.Subset.antisymm (Set.iUnion_subset hsub) hcover
  have hmonoB : Monotone fun n => (atParameter (p n)) ⁻¹' A := by
    intro n m hnm u hu
    refine hinc ?_ hu
    intro e he
    exact lt_of_lt_of_le he
      (Subtype.coe_le_coe.mpr (monotone_nat_of_le_succ (fun k => hmono k e) hnm))
  calc (⨆ n, edgeMeasure (p n) A)
      = ⨆ n, (markMeasure V) ((atParameter (p n)) ⁻¹' A) := iSup_congr fun n => hmark (p n)
    _ = (markMeasure V) (⋃ n, (atParameter (p n)) ⁻¹' A) :=
        iSup_measure_iUnion (μ := markMeasure V) hmonoB
    _ = (markMeasure V) ((atParameter q) ⁻¹' A) := by rw [hunion]
    _ = edgeMeasure q A := (hmark q).symm

/-! ## Supremum and `tsum` commute for monotone families -/

theorem iSup_add_of_mono {a b : ℕ → ℝ≥0∞} (ha : Monotone a) (hb : Monotone b) :
    (⨆ n, (a n + b n)) = (⨆ n, a n) + (⨆ n, b n) := by
  refine le_antisymm (iSup_le fun n => add_le_add (le_iSup a n) (le_iSup b n)) ?_
  rw [ENNReal.iSup_add]
  refine iSup_le fun n => ?_
  rw [add_comm (a n), ENNReal.iSup_add]
  refine iSup_le fun m => ?_
  calc b m + a n ≤ b (max n m) + a (max n m) :=
        add_le_add (hb (le_max_right n m)) (ha (le_max_left n m))
    _ = a (max n m) + b (max n m) := add_comm _ _
    _ ≤ ⨆ k, (a k + b k) := le_iSup (fun k => a k + b k) (max n m)

theorem iSup_finset_sum_of_mono {ι : Type*} (s : Finset ι) {f : ℕ → ι → ℝ≥0∞}
    (hmono : ∀ (n : ℕ) (i : ι), f n i ≤ f (n + 1) i) :
    (⨆ n, ∑ i ∈ s, f n i) = ∑ i ∈ s, ⨆ n, f n i := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      have h1 : Monotone fun n => f n a := monotone_nat_of_le_succ fun n => hmono n a
      have h2 : Monotone fun n => ∑ i ∈ s, f n i :=
        monotone_nat_of_le_succ fun n => Finset.sum_le_sum fun i _ => hmono n i
      have hstep : ∀ n, ∑ i ∈ insert a s, f n i = f n a + ∑ i ∈ s, f n i :=
        fun n => Finset.sum_insert ha
      rw [iSup_congr hstep, Finset.sum_insert ha, iSup_add_of_mono h1 h2, ih]

theorem iSup_tsum_of_monotone {ι : Type*} {f : ℕ → ι → ℝ≥0∞}
    (hmono : ∀ (n : ℕ) (i : ι), f n i ≤ f (n + 1) i) :
    (⨆ n, ∑' i, f n i) = ∑' i, ⨆ n, f n i := by
  have h1 : ∀ n : ℕ, ∑' i, f n i = ⨆ s : Finset ι, ∑ i ∈ s, f n i :=
    fun n => ENNReal.tsum_eq_iSup_sum
  rw [iSup_congr h1, ENNReal.tsum_eq_iSup_sum, iSup_comm]
  exact iSup_congr fun s => iSup_finset_sum_of_mono s hmono

/-! ## Monotone convergence of the expected cluster volume -/

theorem iSup_lintegral_clusterVol {p : ℕ → Sym2 V → unitInterval} {q : Sym2 V → unitInterval}
    (hmono : ∀ (n : ℕ) (e : Sym2 V), p n e ≤ p (n + 1) e)
    (hlim : ∀ e : Sym2 V,
      Tendsto (fun n : ℕ => ((p n e : unitInterval) : ℝ)) atTop (𝓝 ((q e : unitInterval) : ℝ)))
    (o : V) :
    (⨆ n : ℕ, ∫⁻ ω, clusterVol ω o ∂(edgeMeasure (p n)))
      = ∫⁻ ω, clusterVol ω o ∂(edgeMeasure q) := by
  have hstep : ∀ r : Sym2 V → unitInterval,
      (∫⁻ ω, clusterVol ω o ∂(edgeMeasure r)) = ∑' y : V, edgeMeasure r (connSet o y) :=
    fun r => lintegral_clusterVol_eq_tsum_connSet r o
  have hL : (⨆ n : ℕ, ∫⁻ ω, clusterVol ω o ∂(edgeMeasure (p n)))
      = ⨆ n : ℕ, ∑' y : V, edgeMeasure (p n) (connSet o y) := iSup_congr fun n => hstep (p n)
  rw [hL, hstep q]
  rw [iSup_tsum_of_monotone (f := fun n y => edgeMeasure (p n) (connSet o y))]
  · exact tsum_congr fun y => iSup_edgeMeasure_connects hmono hlim o y
  · intro n y
    exact edgeMeasure_mono_of_le (fun e => hmono n e) (measurableSet_connects o y)
      (isIncreasing_connects o y)


/-! ## Domination of the expected cluster volume -/

theorem lintegral_clusterVol_mono {p q : Sym2 V → unitInterval} (hpq : ∀ e, p e ≤ q e) (o : V) :
    (∫⁻ ω, clusterVol ω o ∂(edgeMeasure p)) ≤ ∫⁻ ω, clusterVol ω o ∂(edgeMeasure q) := by
  rw [lintegral_clusterVol_eq_tsum_connSet p o, lintegral_clusterVol_eq_tsum_connSet q o]
  exact ENNReal.tsum_le_tsum fun y =>
    edgeMeasure_mono_of_le hpq (measurableSet_connects o y) (isIncreasing_connects o y)

/-! ## Passing from a real cut-off parameter to the natural one -/

theorem iSup_real_eq_iSup_nat {α : Type*} [CompleteLattice α] {f : ℝ → α} (hmono : Monotone f) :
    (⨆ r : ℝ, f r) = ⨆ n : ℕ, f n := by
  refine le_antisymm (iSup_le fun r => ?_) (iSup_le fun n => le_iSup f (n : ℝ))
  exact le_iSup_of_le (f := fun n : ℕ => f n) ⌈r⌉₊ (hmono (Nat.le_ceil r))

/-- Monotone convergence in a real parameter. -/
theorem iSup_lintegral_clusterVol_real {p : ℝ → Sym2 V → unitInterval} {q : Sym2 V → unitInterval}
    (hmono : ∀ (r r' : ℝ) (e : Sym2 V), r ≤ r' → p r e ≤ p r' e)
    (hlim : ∀ e : Sym2 V,
      Tendsto (fun r : ℝ => ((p r e : unitInterval) : ℝ)) atTop (𝓝 ((q e : unitInterval) : ℝ)))
    (o : V) :
    (⨆ r : ℝ, ∫⁻ ω, clusterVol ω o ∂(edgeMeasure (p r)))
      = ∫⁻ ω, clusterVol ω o ∂(edgeMeasure q) := by
  have hmonoR : Monotone fun r : ℝ => ∫⁻ ω, clusterVol ω o ∂(edgeMeasure (p r)) :=
    fun r r' hrr' => lintegral_clusterVol_mono (fun e => hmono r r' e hrr') o
  rw [iSup_real_eq_iSup_nat hmonoR]
  refine iSup_lintegral_clusterVol (p := fun n : ℕ => p (n : ℝ)) ?_ ?_ o
  · intro n e
    exact hmono _ _ e (by push_cast; linarith)
  · intro e
    exact (hlim e).comp tendsto_natCast_atTop_atTop

end PercLib.CriticalLRP

namespace PercLib.CriticalLRP.CutoffLimit

open PercLib.CriticalLRP.FiniteVolume CutoffKernel TreeExpansion

variable {d : ℕ} {K : ℝ → ℝ}

/-- The radial profile evaluated at the sup-norm distance is even. -/
theorem profile_even (K : ℝ → ℝ) (y : Fin d → ℤ) :
    K ((linfNorm (-y) : ℕ) : ℝ) = K ((linfNorm y : ℕ) : ℝ) := by
  rw [linfNorm_neg]

/-- `linfNorm (x - y) > 0` for distinct lattice points. -/
theorem linfNorm_sub_pos {x y : Fin d → ℤ} (h : x ≠ y) : 0 < linfNorm (x - y) := by
  rcases Nat.eq_zero_or_pos (linfNorm (x - y)) with h0 | h0
  · exact absurd (sub_eq_zero.mp (linfNorm_eq_zero_iff.mp h0)) h
  · exact h0

theorem linfNorm_sub_pos_real {x y : Fin d → ℤ} (h : x ≠ y) :
    (0 : ℝ) < ((linfNorm (x - y) : ℕ) : ℝ) := by
  exact_mod_cast linfNorm_sub_pos h

/-- The profile is nonnegative at every lattice distance, including `0`. -/
theorem profile_nonneg (hKnn : ∀ t, 0 < t → 0 ≤ K t) (hK0 : K 0 = 0) (d : ℕ)
    (y : Fin d → ℤ) : 0 ≤ K ((linfNorm y : ℕ) : ℝ) := by
  rcases Nat.eq_zero_or_pos (linfNorm y) with h | h
  · rw [h]
    simp only [Nat.cast_zero]
    exact le_of_eq hK0.symm
  · exact hKnn _ (by exact_mod_cast h)

/-- The uncut lattice kernel of a radial profile is nonnegative. -/
theorem uncutKernel_nonneg (hKnn : ∀ t, 0 < t → 0 ≤ K t) (hK0 : K 0 = 0) (d : ℕ)
    (e : Sym2 (Fin d → ℤ)) :
    0 ≤ kernelJ (fun y : Fin d → ℤ => K ((linfNorm y : ℕ) : ℝ)) (profile_even (d := d) K) e := by
  induction e using Sym2.ind with
  | _ x y =>
    show 0 ≤ K ((linfNorm (y - x) : ℕ) : ℝ)
    exact profile_nonneg hKnn hK0 d (y - x)

/-- The cut-off kernel of Definition I.1.5 is nonnegative for every real cut-off. -/
theorem cutoffSymKernel_nonneg' (hK : AntitoneOn K (Set.Ioi 0)) (d : ℕ) (r : ℝ)
    (e : Sym2 (Fin d → ℤ)) : 0 ≤ cutoffSymKernel K d r e := by
  by_cases hr : 0 < r
  · exact cutoffSymKernel_nonneg hK hr e
  · push Not at hr
    induction e using Sym2.ind with
    | _ x y =>
      rw [cutoffSymKernel_mk]
      by_cases hxy : x = y
      · rw [ite_eq_left hxy]
      · rw [ite_eq_right hxy]
        refine le_of_eq (cutoffProfile_of_lt ?_).symm
        linarith [linfNorm_sub_pos_real hxy]

/-- `J_r ≤ J_{r'}` for all real cut-offs `r ≤ r'` (Definition I.1.5). -/
theorem cutoffSymKernel_mono_r' (hK : AntitoneOn K (Set.Ioi 0)) {r r' : ℝ} (h : r ≤ r')
    (e : Sym2 (Fin d → ℤ)) : cutoffSymKernel K d r e ≤ cutoffSymKernel K d r' e := by
  induction e using Sym2.ind with
  | _ x y =>
    rw [cutoffSymKernel_mk, cutoffSymKernel_mk]
    by_cases hxy : x = y
    · rw [ite_eq_left hxy, ite_eq_left hxy]
    · rw [ite_eq_right hxy, ite_eq_right hxy]
      rcases le_or_gt r 0 with hr | hr
      · rw [cutoffProfile_of_lt (by linarith [linfNorm_sub_pos_real hxy] : r < ((linfNorm (x - y) : ℕ) : ℝ))]
        rcases le_or_gt ((linfNorm (x - y) : ℕ) : ℝ) r' with hsr | hsr
        · have hr' : (0 : ℝ) < r' := lt_of_lt_of_le (linfNorm_sub_pos_real hxy) hsr
          rw [cutoffProfile_of_le hsr]
          have hle := hK (Set.mem_Ioi.mpr (linfNorm_sub_pos_real hxy)) hr' hsr
          linarith
        · rw [cutoffProfile_of_lt hsr]
      · exact cutoffProfile_mono_r hK hr (lt_of_lt_of_le hr h) (linfNorm_sub_pos_real hxy) h

/-- The cut-off kernels converge pointwise to the uncut kernel as `r → ∞`. -/
theorem tendsto_cutoffSymKernel (hKtop : Tendsto K atTop (𝓝 0)) (hK0 : K 0 = 0) (d : ℕ)
    (e : Sym2 (Fin d → ℤ)) :
    Tendsto (fun r : ℝ => cutoffSymKernel K d r e) atTop
      (𝓝 (kernelJ (fun y : Fin d → ℤ => K ((linfNorm y : ℕ) : ℝ)) (profile_even (d := d) K) e)) := by
  induction e using Sym2.ind with
  | _ x y =>
    show Tendsto (fun r : ℝ => cutoffSymKernel K d r s(x, y)) atTop
      (𝓝 (K ((linfNorm (y - x) : ℕ) : ℝ)))
    rw [show ((linfNorm (y - x) : ℕ) : ℝ) = ((linfNorm (x - y) : ℕ) : ℝ) from by
      rw [show y - x = -(x - y) by abel, linfNorm_neg]]
    by_cases hxy : x = y
    · have hconst : (fun r : ℝ => cutoffSymKernel K d r s(x, y)) = fun _ => (0 : ℝ) := by
        funext r
        rw [cutoffSymKernel_mk, ite_eq_left hxy]
      have hzero : ((linfNorm (x - y) : ℕ) : ℝ) = 0 := by
        rw [show x - y = (0 : Fin d → ℤ) by rw [hxy]; abel, linfNorm_eq_zero_iff.mpr rfl]
        simp
      rw [hconst, hzero, hK0]
      exact tendsto_const_nhds
    · refine Tendsto.congr' ?_ (tendsto_cutoffProfile (K := K)
        (s := ((linfNorm (x - y) : ℕ) : ℝ)) hKtop)
      filter_upwards with r
      rw [cutoffSymKernel_mk, ite_eq_right hxy]

theorem tendsto_cutoffSymKernel_nat (hKtop : Tendsto K atTop (𝓝 0)) (hK0 : K 0 = 0) (d : ℕ)
    (e : Sym2 (Fin d → ℤ)) :
    Tendsto (fun n : ℕ => cutoffSymKernel K d ((n : ℝ)) e) atTop
      (𝓝 (kernelJ (fun y : Fin d → ℤ => K ((linfNorm y : ℕ) : ℝ)) (profile_even (d := d) K) e)) :=
  (tendsto_cutoffSymKernel hKtop hK0 d e).comp tendsto_natCast_atTop_atTop

/-- Convergence of the cut-off edge-open probabilities to the uncut ones. -/
theorem tendsto_bernoulliEdgeProb_cutoff_nat (hK : AntitoneOn K (Set.Ioi 0))
    (hKtop : Tendsto K atTop (𝓝 0)) (hK0 : K 0 = 0) (hKnn : ∀ t, 0 < t → 0 ≤ K t)
    (d : ℕ) (β : NNReal) (e : Sym2 (Fin d → ℤ)) :
    Tendsto (fun n : ℕ =>
        ((bernoulliEdgeProb (cutoffSymKernel K d ((n : ℝ)))
          (fun e => cutoffSymKernel_nonneg' hK d ((n : ℝ)) e) β e : unitInterval) : ℝ)) atTop
      (𝓝 ((bernoulliEdgeProb (kernelJ (fun y : Fin d → ℤ => K ((linfNorm y : ℕ) : ℝ))
        (profile_even (d := d) K)) (uncutKernel_nonneg hKnn hK0 d) β e : unitInterval) : ℝ)) := by
  have hk := tendsto_cutoffSymKernel_nat hKtop hK0 d e
  have hcont : Continuous fun t : ℝ => (1 : ℝ) - Real.exp (-((β : ℝ) * t)) := by fun_prop
  have h1 : Tendsto (fun n : ℕ =>
      (1 : ℝ) - Real.exp (-((β : ℝ) * cutoffSymKernel K d ((n : ℝ)) e))) atTop
      (𝓝 ((1 : ℝ) - Real.exp (-((β : ℝ) *
        kernelJ (fun y : Fin d → ℤ => K ((linfNorm y : ℕ) : ℝ)) (profile_even (d := d) K) e)))) :=
    (hcont.tendsto _).comp hk
  simpa only [bernoulliEdgeProb_coe] using h1


/-! ## The main limit theorems for the cut-off model -/

/-- Convergence of the cut-off edge-open probabilities (real cut-off parameter). -/
theorem tendsto_bernoulliEdgeProb_cutoff (hK : AntitoneOn K (Set.Ioi 0))
    (hKtop : Tendsto K atTop (𝓝 0)) (hK0 : K 0 = 0) (hKnn : ∀ t, 0 < t → 0 ≤ K t)
    (d : ℕ) (β : NNReal) (e : Sym2 (Fin d → ℤ)) :
    Tendsto (fun r : ℝ =>
        ((bernoulliEdgeProb (cutoffSymKernel K d r)
          (fun e => cutoffSymKernel_nonneg' hK d r e) β e : unitInterval) : ℝ)) atTop
      (𝓝 ((bernoulliEdgeProb (kernelJ (fun y : Fin d → ℤ => K ((linfNorm y : ℕ) : ℝ))
        (profile_even (d := d) K)) (uncutKernel_nonneg hKnn hK0 d) β e : unitInterval) : ℝ)) := by
  have hk := tendsto_cutoffSymKernel hKtop hK0 d e
  have hcont : Continuous fun t : ℝ => (1 : ℝ) - Real.exp (-((β : ℝ) * t)) := by fun_prop
  have h1 : Tendsto (fun r : ℝ =>
      (1 : ℝ) - Real.exp (-((β : ℝ) * cutoffSymKernel K d r e))) atTop
      (𝓝 ((1 : ℝ) - Real.exp (-((β : ℝ) *
        kernelJ (fun y : Fin d → ℤ => K ((linfNorm y : ℕ) : ℝ)) (profile_even (d := d) K) e)))) :=
    (hcont.tendsto _).comp hk
  simpa only [bernoulliEdgeProb_coe] using h1

/-- **The cut-off connection probabilities increase to the uncut ones** (real `r → ∞`). -/
theorem iSup_edgeMeasure_connects_cutoff (hK : AntitoneOn K (Set.Ioi 0))
    (hKtop : Tendsto K atTop (𝓝 0)) (hK0 : K 0 = 0) (hKnn : ∀ t, 0 < t → 0 ≤ K t)
    (d : ℕ) (β : NNReal) (v w : Fin d → ℤ) :
    (⨆ r : ℝ, edgeMeasure (bernoulliEdgeProb (cutoffSymKernel K d r)
        (fun e => cutoffSymKernel_nonneg' hK d r e) β) {ω : Config (Fin d → ℤ) | Connects ω v w})
      = edgeMeasure (bernoulliEdgeProb (kernelJ (fun y : Fin d → ℤ => K ((linfNorm y : ℕ) : ℝ))
        (profile_even (d := d) K)) (uncutKernel_nonneg hKnn hK0 d) β)
        {ω : Config (Fin d → ℤ) | Connects ω v w} := by
  have hnat := iSup_edgeMeasure_connects (p := fun (n : ℕ) (e : Sym2 (Fin d → ℤ)) => bernoulliEdgeProb
      (cutoffSymKernel K d ((n : ℝ))) (fun e => cutoffSymKernel_nonneg' hK d ((n : ℝ)) e) β e)
    (q := bernoulliEdgeProb (kernelJ (fun y : Fin d → ℤ => K ((linfNorm y : ℕ) : ℝ))
      (profile_even (d := d) K)) (uncutKernel_nonneg hKnn hK0 d) β)
    (fun n e => bernoulliEdgeProb_mono_kernel
      (fun e => cutoffSymKernel_mono_r' hK (by push_cast; linarith) e) _ _ β e)
    (fun e => tendsto_bernoulliEdgeProb_cutoff_nat hK hKtop hK0 hKnn d β e) v w
  have hmonoR : Monotone fun r : ℝ => edgeMeasure (bernoulliEdgeProb (cutoffSymKernel K d r)
      (fun e => cutoffSymKernel_nonneg' hK d r e) β) {ω : Config (Fin d → ℤ) | Connects ω v w} :=
    fun r r' hrr' => edgeMeasure_mono_of_le
      (fun e => bernoulliEdgeProb_mono_kernel (fun e => cutoffSymKernel_mono_r' hK hrr' e)
        _ _ β e) (measurableSet_connects v w) (isIncreasing_connects v w)
  rw [iSup_real_eq_iSup_nat hmonoR]
  exact hnat

/-- **The expected cut-off cluster volume increases to the uncut one** (real `r → ∞`). -/
theorem iSup_lintegral_clusterVol_cutoff (hK : AntitoneOn K (Set.Ioi 0))
    (hKtop : Tendsto K atTop (𝓝 0)) (hK0 : K 0 = 0) (hKnn : ∀ t, 0 < t → 0 ≤ K t)
    (d : ℕ) (β : NNReal) (o : Fin d → ℤ) :
    (⨆ r : ℝ, ∫⁻ ω, clusterVol ω o ∂(longRangeMeasure (cutoffSymKernel K d r)
        (fun e => cutoffSymKernel_nonneg' hK d r e) β))
      = ∫⁻ ω, clusterVol ω o ∂(longRangeMeasure (kernelJ
        (fun y : Fin d → ℤ => K ((linfNorm y : ℕ) : ℝ)) (profile_even (d := d) K))
        (uncutKernel_nonneg hKnn hK0 d) β) :=
  iSup_lintegral_clusterVol_real
    (p := fun (r : ℝ) (e : Sym2 (Fin d → ℤ)) => bernoulliEdgeProb (cutoffSymKernel K d r)
      (fun e => cutoffSymKernel_nonneg' hK d r e) β e)
    (q := bernoulliEdgeProb (kernelJ (fun y : Fin d → ℤ => K ((linfNorm y : ℕ) : ℝ))
      (profile_even (d := d) K)) (uncutKernel_nonneg hKnn hK0 d) β)
    (fun _r _r' e hrr' => bernoulliEdgeProb_mono_kernel
      (fun e => cutoffSymKernel_mono_r' hK hrr' e) _ _ β e)
    (fun e => tendsto_bernoulliEdgeProb_cutoff hK hKtop hK0 hKnn d β e) o

/-- The cut-off expected cluster volume is at most the uncut one, for every `r`. -/
theorem lintegral_clusterVol_cutoff_le (hK : AntitoneOn K (Set.Ioi 0))
    (hKtop : Tendsto K atTop (𝓝 0)) (hK0 : K 0 = 0) (hKnn : ∀ t, 0 < t → 0 ≤ K t)
    (d : ℕ) (β : NNReal) (o : Fin d → ℤ) (r : ℝ) :
    (∫⁻ ω, clusterVol ω o ∂(longRangeMeasure (cutoffSymKernel K d r)
        (fun e => cutoffSymKernel_nonneg' hK d r e) β))
      ≤ ∫⁻ ω, clusterVol ω o ∂(longRangeMeasure (kernelJ
        (fun y : Fin d → ℤ => K ((linfNorm y : ℕ) : ℝ)) (profile_even (d := d) K))
        (uncutKernel_nonneg hKnn hK0 d) β) := by
  rw [← iSup_lintegral_clusterVol_cutoff hK hKtop hK0 hKnn d β o]
  exact le_iSup (fun r : ℝ => ∫⁻ ω, clusterVol ω o ∂(longRangeMeasure (cutoffSymKernel K d r)
    (fun e => cutoffSymKernel_nonneg' hK d r e) β)) r

/-- **`E_{β,r}|K| → E_β|K|`** as `r → ∞`, in the extended sense (including the value `⊤`). -/
theorem tendsto_lintegral_clusterVol_cutoff (hK : AntitoneOn K (Set.Ioi 0))
    (hKtop : Tendsto K atTop (𝓝 0)) (hK0 : K 0 = 0) (hKnn : ∀ t, 0 < t → 0 ≤ K t)
    (d : ℕ) (β : NNReal) (o : Fin d → ℤ) :
    Tendsto (fun r : ℝ => ∫⁻ ω, clusterVol ω o ∂(longRangeMeasure (cutoffSymKernel K d r)
        (fun e => cutoffSymKernel_nonneg' hK d r e) β)) atTop
      (𝓝 (∫⁻ ω, clusterVol ω o ∂(longRangeMeasure (kernelJ
        (fun y : Fin d → ℤ => K ((linfNorm y : ℕ) : ℝ)) (profile_even (d := d) K))
        (uncutKernel_nonneg hKnn hK0 d) β))) := by
  have hmonoR : Monotone fun r : ℝ => ∫⁻ ω, clusterVol ω o ∂(longRangeMeasure
      (cutoffSymKernel K d r) (fun e => cutoffSymKernel_nonneg' hK d r e) β) :=
    fun r r' hrr' => lintegral_clusterVol_mono
      (fun e => bernoulliEdgeProb_mono_kernel (fun e => cutoffSymKernel_mono_r' hK hrr' e)
        _ _ β e) o
  rw [← iSup_lintegral_clusterVol_cutoff hK hKtop hK0 hKnn d β o]
  exact tendsto_atTop_iSup hmonoR

/-- **Divergence in the cut-off radius.**  If the uncut expected cluster volume is infinite,
the cut-off expected cluster volume diverges to `⊤`. -/
theorem tendsto_lintegral_clusterVol_cutoff_top (hK : AntitoneOn K (Set.Ioi 0))
    (hKtop : Tendsto K atTop (𝓝 0)) (hK0 : K 0 = 0) (hKnn : ∀ t, 0 < t → 0 ≤ K t)
    (d : ℕ) (β : NNReal) (o : Fin d → ℤ)
    (hinf : (∫⁻ ω, clusterVol ω o ∂(longRangeMeasure (kernelJ
        (fun y : Fin d → ℤ => K ((linfNorm y : ℕ) : ℝ)) (profile_even (d := d) K))
        (uncutKernel_nonneg hKnn hK0 d) β)) = ⊤) :
    Tendsto (fun r : ℝ => ∫⁻ ω, clusterVol ω o ∂(longRangeMeasure (cutoffSymKernel K d r)
        (fun e => cutoffSymKernel_nonneg' hK d r e) β)) atTop (𝓝 ⊤) := by
  have h := tendsto_lintegral_clusterVol_cutoff hK hKtop hK0 hKnn d β o
  rwa [hinf] at h

/-- Pointwise form of the divergence: for every finite `C` there is a cut-off radius `r > 0`
whose expected cluster volume is at least `C`. -/
theorem exists_lintegral_clusterVol_cutoff_ge (hK : AntitoneOn K (Set.Ioi 0))
    (hKtop : Tendsto K atTop (𝓝 0)) (hK0 : K 0 = 0) (hKnn : ∀ t, 0 < t → 0 ≤ K t)
    (d : ℕ) (β : NNReal) (o : Fin d → ℤ)
    (hinf : (∫⁻ ω, clusterVol ω o ∂(longRangeMeasure (kernelJ
        (fun y : Fin d → ℤ => K ((linfNorm y : ℕ) : ℝ)) (profile_even (d := d) K))
        (uncutKernel_nonneg hKnn hK0 d) β)) = ⊤)
    (C : ℝ≥0∞) (hC : C ≠ ⊤) :
    ∃ r : ℝ, 0 < r ∧ C ≤ ∫⁻ ω, clusterVol ω o ∂(longRangeMeasure (cutoffSymKernel K d r)
        (fun e => cutoffSymKernel_nonneg' hK d r e) β) := by
  obtain ⟨r, hr⟩ : ∃ r : ℝ, C ≤ ∫⁻ ω, clusterVol ω o ∂(longRangeMeasure
      (cutoffSymKernel K d r) (fun e => cutoffSymKernel_nonneg' hK d r e) β) := by
    by_contra hcon
    push Not at hcon
    have hle : (⨆ r : ℝ, ∫⁻ ω, clusterVol ω o ∂(longRangeMeasure (cutoffSymKernel K d r)
        (fun e => cutoffSymKernel_nonneg' hK d r e) β)) ≤ C :=
      iSup_le fun r => le_of_lt (hcon r)
    rw [iSup_lintegral_clusterVol_cutoff hK hKtop hK0 hKnn d β o, hinf] at hle
    exact hC (top_le_iff.mp hle)
  refine ⟨max r 1, lt_of_lt_of_le zero_lt_one (le_max_right r 1), le_trans hr ?_⟩
  exact lintegral_clusterVol_mono
    (fun e => bernoulliEdgeProb_mono_kernel
      (fun e => cutoffSymKernel_mono_r' hK (le_max_left r 1) e) _ _ β e) o

/-- **`J_r ≤ J`**: the cut-off kernel is dominated by the uncut kernel, for every real `r`. -/
theorem cutoffSymKernel_le_uncut (hKnn : ∀ t, 0 < t → 0 ≤ K t) (hK0 : K 0 = 0) (r : ℝ)
    (e : Sym2 (Fin d → ℤ)) :
    cutoffSymKernel K d r e
      ≤ kernelJ (fun y : Fin d → ℤ => K ((linfNorm y : ℕ) : ℝ)) (profile_even (d := d) K) e := by
  induction e using Sym2.ind with
  | _ x y =>
    show cutoffSymKernel K d r s(x, y) ≤ K ((linfNorm (y - x) : ℕ) : ℝ)
    rw [show ((linfNorm (y - x) : ℕ) : ℝ) = ((linfNorm (x - y) : ℕ) : ℝ) from by
      rw [show y - x = -(x - y) by abel, linfNorm_neg]]
    rw [cutoffSymKernel_mk]
    by_cases hxy : x = y
    · rw [ite_eq_left hxy]
      have hz : ((linfNorm (x - y) : ℕ) : ℝ) = 0 := by
        rw [show x - y = (0 : Fin d → ℤ) by rw [hxy]; abel, linfNorm_eq_zero_iff.mpr rfl]
        simp
      rw [hz, hK0]
    · rw [ite_eq_right hxy]
      rcases le_or_gt r 0 with hr | hr
      · rw [cutoffProfile_of_lt (by linarith [linfNorm_sub_pos_real hxy])]
        exact profile_nonneg hKnn hK0 d (x - y)
      · exact cutoffProfile_le hKnn (linfNorm_sub_pos_real hxy) hr

/-- The cut-off two-point function is nondecreasing in the cut-off radius. -/
theorem twoPointFunction_cutoff_mono_r (hK : AntitoneOn K (Set.Ioi 0)) {r r' : ℝ} (h : r ≤ r')
    (d : ℕ) (β : NNReal) (x y : Fin d → ℤ) :
    twoPointFunction (cutoffSymKernel K d r) (fun e => cutoffSymKernel_nonneg' hK d r e) β x y
      ≤ twoPointFunction (cutoffSymKernel K d r') (fun e => cutoffSymKernel_nonneg' hK d r' e)
        β x y :=
  longRangeMeasure_mono_kernel (fun e => cutoffSymKernel_mono_r' hK h e) _ _ β
    (measurableSet_connects x y) (isIncreasing_connects x y)

/-- The cut-off two-point function is dominated by the uncut one. -/
theorem twoPointFunction_cutoff_le (hK : AntitoneOn K (Set.Ioi 0))
    (hKnn : ∀ t, 0 < t → 0 ≤ K t) (hK0 : K 0 = 0) (d : ℕ) (β : NNReal) (r : ℝ)
    (x y : Fin d → ℤ) :
    twoPointFunction (cutoffSymKernel K d r) (fun e => cutoffSymKernel_nonneg' hK d r e) β x y
      ≤ twoPointFunction (kernelJ (fun z : Fin d → ℤ => K ((linfNorm z : ℕ) : ℝ))
        (profile_even (d := d) K)) (uncutKernel_nonneg hKnn hK0 d) β x y :=
  longRangeMeasure_mono_kernel (fun e => cutoffSymKernel_le_uncut hKnn hK0 r e) _ _ β
    (measurableSet_connects x y) (isIncreasing_connects x y)

/-- **`r ↦ E_{β,r}|K_o|` is nondecreasing.** -/
theorem monotone_lintegral_clusterVol_cutoff (hK : AntitoneOn K (Set.Ioi 0))
    (d : ℕ) (β : NNReal) (o : Fin d → ℤ) :
    Monotone fun r : ℝ => ∫⁻ ω, clusterVol ω o ∂(longRangeMeasure (cutoffSymKernel K d r)
      (fun e => cutoffSymKernel_nonneg' hK d r e) β) :=
  fun _r _r' hrr' => lintegral_clusterVol_mono
    (fun e => bernoulliEdgeProb_mono_kernel (fun e => cutoffSymKernel_mono_r' hK hrr' e)
      _ _ β e) o

/-- **Transfer of uniform cut-off bounds**: a bound on `E_{β,r}|K_o|` that is uniform in the
cut-off radius bounds the uncut mean `E_β|K_o|`.  This is the monotone-convergence converse of
`lintegral_clusterVol_cutoff_le`, and the mechanism by which a uniform-in-`r` cut-off estimate
would give finiteness of the uncut first moment (no such estimate is produced here). -/
theorem le_of_forall_lintegral_clusterVol_cutoff_le (hK : AntitoneOn K (Set.Ioi 0))
    (hKtop : Tendsto K atTop (𝓝 0)) (hK0 : K 0 = 0) (hKnn : ∀ t, 0 < t → 0 ≤ K t)
    (d : ℕ) (β : NNReal) (o : Fin d → ℤ) (C : ℝ≥0∞)
    (hC : ∀ r : ℝ, (∫⁻ ω, clusterVol ω o ∂(longRangeMeasure (cutoffSymKernel K d r)
      (fun e => cutoffSymKernel_nonneg' hK d r e) β)) ≤ C) :
    (∫⁻ ω, clusterVol ω o ∂(longRangeMeasure (kernelJ
        (fun y : Fin d → ℤ => K ((linfNorm y : ℕ) : ℝ)) (profile_even (d := d) K))
        (uncutKernel_nonneg hKnn hK0 d) β)) ≤ C := by
  rw [← iSup_lintegral_clusterVol_cutoff hK hKtop hK0 hKnn d β o]
  exact iSup_le hC

/-! ## Non-vacuity: the power-law profile of Definition I.1.3 satisfies the hypotheses -/

theorem tendsto_modelProfile {d : ℕ} {α : ℝ} (hα : 0 < (d : ℝ) + α) :
    Tendsto (modelProfile d α) atTop (𝓝 0) := by
  refine Tendsto.congr' ?_ (tendsto_rpow_neg_atTop hα)
  filter_upwards with s
  rw [modelProfile]
  congr 1
  ring

theorem modelProfile_zero {d : ℕ} {α : ℝ} (hα : 0 < (d : ℝ) + α) : modelProfile d α 0 = 0 := by
  rw [modelProfile]
  exact Real.zero_rpow (by linarith : (-(d : ℝ) - α) ≠ 0)

/-- The model profile `r ↦ r^{-(d+α)}` of Definition I.1.3 satisfies every hypothesis used
above, as soon as `0 < d + α`.  (Compiled witness that the interface is inhabited by the
source's own kernel.) -/
theorem modelProfile_hypotheses {d : ℕ} {α : ℝ} (hα : 0 < (d : ℝ) + α) :
    AntitoneOn (modelProfile d α) (Set.Ioi 0) ∧
      (∀ t, 0 < t → 0 ≤ modelProfile d α t) ∧
      modelProfile d α 0 = 0 ∧
      Tendsto (modelProfile d α) atTop (𝓝 0) :=
  ⟨modelProfile_antitoneOn d hα.le, fun t ht => (modelProfile_pos ht).le,
    modelProfile_zero hα, tendsto_modelProfile hα⟩

/-- The main limit theorem instantiated at the power-law profile of Definition I.1.3. -/
theorem iSup_lintegral_clusterVol_cutoff_modelProfile {d : ℕ} {α : ℝ}
    (hα : 0 < (d : ℝ) + α) (β : NNReal) (o : Fin d → ℤ) :
    (⨆ r : ℝ, ∫⁻ ω, clusterVol ω o ∂(longRangeMeasure
        (cutoffSymKernel (modelProfile d α) d r)
        (fun e => cutoffSymKernel_nonneg' (modelProfile_antitoneOn d hα.le) d r e) β))
      = ∫⁻ ω, clusterVol ω o ∂(longRangeMeasure (kernelJ
        (fun y : Fin d → ℤ => modelProfile d α ((linfNorm y : ℕ) : ℝ))
        (profile_even (d := d) (modelProfile d α)))
        (uncutKernel_nonneg (fun t ht => (modelProfile_pos ht).le)
          (modelProfile_zero hα) d) β) :=
  iSup_lintegral_clusterVol_cutoff (modelProfile_antitoneOn d hα.le) (tendsto_modelProfile hα)
    (modelProfile_zero hα) (fun t ht => (modelProfile_pos ht).le) d β o

end PercLib.CriticalLRP.CutoffLimit


/-! ## Axiom audit -/

#print axioms PercLib.CriticalLRP.exists_connects_atParameter_of_connects
#print axioms PercLib.CriticalLRP.iSup_edgeMeasure_connects
#print axioms PercLib.CriticalLRP.iSup_tsum_of_monotone
#print axioms PercLib.CriticalLRP.iSup_lintegral_clusterVol
#print axioms PercLib.CriticalLRP.iSup_lintegral_clusterVol_real
#print axioms PercLib.CriticalLRP.CutoffLimit.iSup_edgeMeasure_connects_cutoff
#print axioms PercLib.CriticalLRP.CutoffLimit.iSup_lintegral_clusterVol_cutoff
#print axioms PercLib.CriticalLRP.CutoffLimit.tendsto_lintegral_clusterVol_cutoff
#print axioms PercLib.CriticalLRP.CutoffLimit.tendsto_lintegral_clusterVol_cutoff_top
#print axioms PercLib.CriticalLRP.CutoffLimit.exists_lintegral_clusterVol_cutoff_ge
#print axioms PercLib.CriticalLRP.CutoffLimit.twoPointFunction_cutoff_le
#print axioms PercLib.CriticalLRP.CutoffLimit.le_of_forall_lintegral_clusterVol_cutoff_le
#print axioms PercLib.CriticalLRP.CutoffLimit.modelProfile_hypotheses
#print axioms PercLib.CriticalLRP.CutoffLimit.iSup_lintegral_clusterVol_cutoff_modelProfile
