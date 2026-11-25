/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
# Russo's formula in infinite volume: the pivot-flux exchange

Deliverable of swarm `smwga3bqk`, member `m3`, direction D (infinite-volume Russo exchange).

Source: Tom Hutchcroft, *Critical long-range percolation I: High effective dimension*,
arXiv:2508.18807v1, Lemma I.4.1 and its proof (p. 34-36).

## What is proved here (sorry-free, no new axioms)

1. `FiniteVolume.expectation_flip_eq_pivotalMass` — the flip expectation of an observable under a
   finite independent-Bernoulli law equals the classical pivotal mass.

2. `pivotalFlux_cutFun` — the `forceOn`-based pivotal flux of a *window* functional
   `cutFun S g ω = g (ω ∩ S)` on the countable configuration space equals the finite pivotal mass of
   the restricted product law.  This is the missing bridge between `CylinderRusso` (finite pivotal
   masses) and `RussoInf` (infinite pivotal fluxes).

3. `hasDerivAt_integral_cutFun` — **the finite-window Russo identity in pivotal-flux form**:
   the `r`-derivative of `r ↦ ∫ cutFun S g dP_r` is the finite sum `∑_{e ∈ S} c_e(r) ·
   pivotalFlux (P_r) (cutFun S g) e` of pivotal fluxes over the window.

4. `flipDiff_cutFun_eq_zero_of_notMem(_touchSet)`, `abs_pivotalFlux_cutFun_le` — locality of the
   window pivot and the single-edge touching bound `|pivot| ≤ 2 sup|g| · P(e touches K_o)`.

5. `tendsto_windowFlux` — **the finite-window pivotal sums converge pointwise in the parameter to
   the infinite pivotal series** `∑'_e c_e(r) · pivotalFlux (P_r) g e`, using dominated convergence
   for series with the summability of the pivotal weights.

6. `hasDerivAt_integral_of_windowFlux` — the abstract exchange theorem: exact finite-window
   derivative identities + pointwise convergence of the window expectations + **local uniform
   convergence of the window fluxes** `⟹` `HasDerivAt` of the limit expectation with the infinite
   pivotal flux as derivative.

7. `exists_finset_cluster`, `clusterVol_cutConfig_tendsto`, `tendsto_cappedClusterVol_cutConfig`,
   `tendsto_integral_cutFun` — along any edge-exhausting sequence of finite windows the truncated
   clusters grow to the full cluster, the cluster volumes converge, and the window expectations of
   the capped cluster volume converge to the infinite-volume expectation.

8. `summable_abs_weight_touch` — **summability of the pivotal-flux weight**
   `e ↦ |c e| · P(e touches K_o)` from a per-vertex degree bound and finite expected cluster volume,
   with total mass at most `D · E|K_o|` (the "finite pivotal flux" input of the paper).

9. `hasDerivAt_integral_cappedClusterVol_of_sharpness` — the assembled reduction:
   for a family of independent edge laws with derivatives `c`, the capped cluster-volume functional,
   and an edge-exhausting window sequence, **the only remaining input is the local uniform
   convergence (`hunif`) of the window fluxes to the infinite pivotal flux**; the finite-window
   identities, the pointwise convergence of the window expectations and the summability of the flux
   weights are all discharged from the paper's hypotheses (degree bound + finite expected cluster
   volume).

10. `cutoffPiFamily`, `hasDerivAt_integral_cappedClusterVol_cutoff` — the concrete instantiation
   for the cut-off long-range model on `ℤ^d` with `q_e(r) = 1 - exp(-β J_r(e))`,
   `J_r(e) = 1(|e| ≤ r)(K(|e|) − K(r))`: the derivative of `r ↦ ∫ cappedClusterVol dP_r` is the
   infinite pivotal flux, with edge derivatives `cutoffEdgeDeriv` and the cut-off degree bound
   `β|J'(r)|(2⌈r⌉₊+1)^d` discharged from `RussoInf/CutoffFlux`.

## The remaining gap, stated exactly

`hunif` in `hasDerivAt_integral_cappedClusterVol_of_sharpness` is *not* a re-statement of the
conclusion: it is the uniform-in-parameter estimate

  `∑_{e ∈ S_k} c_r(e) · pivotalFlux (P_r) (cutFun (S_k) g) e  ⟶  Φ(r)`  locally uniformly in `r`.

Pointwise convergence in `r` is proved (`tendsto_windowFlux`).  What is missing is the uniformity:
one must control `∑_e |c_r(e)| · E[ |pivot flux of g - pivot flux of cutFun (S_k) g| ]` uniformly in
`r` on a compact corner-free interval.  The natural route is a uniform bound on
`E_{P_r}[|K_o| - |K_o ∩ B_k|]` that is uniform in `r` (monotone comparison in `r` supplies the
`r`-uniformity, and the single-edge-forced measures appearing in the pivot difference require the
insertion-tolerance/restoration input of the paper, Lemma I.4.12 and its use of sharpness).  This is
exactly the paper's "standard consequence of the sharpness of the phase transition" (proof of
Lemma I.4.1), and it is **not** formalized here or in the repository.

## Not claimed

No claim is made that Lemma I.4.1 (the full infinite-volume derivative formula at unrestricted
cluster moments), the ODE (I.4.2)-(I.4.5), universal tightness (I.2.3), the canonical excursion
measure, or any of the paper's main theorems is proved.
-/
module

public import PercLib.CriticalLRP.RussoInf.Capstone
public import PercLib.CriticalLRP.CylinderRusso
public import PercLib.CriticalLRP.CountableProduct.Compatibility
public import PercLib.CriticalLRP.CountableProduct.ClusterFinset
public import PercLib.CriticalLRP.RussoInf.CutoffFlux

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

set_option autoImplicit true


set_option linter.unusedSectionVars false

@[expose] public section

open MeasureTheory Measure Filter Finset
open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Countable V]

/-- The configuration obtained from `ω` by deleting every edge outside the finite edge set `S`. -/
def cutConfig (S : Finset (Sym2 V)) (ω : Config V) : Config V := ω ∩ (S : Set (Sym2 V))

theorem cutConfig_subset (S : Finset (Sym2 V)) (ω : Config V) : cutConfig S ω ⊆ ω :=
  Set.inter_subset_left

theorem cutConfig_mono_S {S T : Finset (Sym2 V)} (hST : S ⊆ T) (ω : Config V) :
    cutConfig S ω ⊆ cutConfig T ω := by
  intro e he
  exact ⟨he.1, hST he.2⟩

/-- The functional `g` evaluated on the configuration with all edges outside `S` deleted. -/
def cutFun (S : Finset (Sym2 V)) (g : Config V → ℝ) (ω : Config V) : ℝ := g (cutConfig S ω)

theorem cutFun_mono {S T : Finset (Sym2 V)} (hST : S ⊆ T) {g : Config V → ℝ} (hg : Monotone g) :
    cutFun S g ≤ cutFun T g := fun ω => hg (cutConfig_mono_S hST ω)

theorem cutFun_le {S : Finset (Sym2 V)} {g : Config V → ℝ} (hg : Monotone g) :
    cutFun S g ≤ g := fun ω => hg (cutConfig_subset S ω)

theorem measurable_cutFun {S : Finset (Sym2 V)} {g : Config V → ℝ} (hg : Measurable g) :
    Measurable (cutFun S g) := by
  classical
  have h : Measurable (cutConfig S) := by
    rw [show cutConfig S = fun ω : Config V => ω ∩ (S : Set (Sym2 V)) from rfl]
    fun_prop
  exact hg.comp h

theorem measurable_cutConfig (S : Finset (Sym2 V)) : Measurable (cutConfig S (V := V)) := by
  classical
  rw [show cutConfig S = fun ω : Config V => ω ∩ (S : Set (Sym2 V)) from rfl]
  fun_prop

/-- The configuration reconstructed from a truth assignment on the finite edge set `S`. -/
def restrConfig (S : Finset (Sym2 V)) (y : S → Prop) : Config V :=
  {e | ∃ h : e ∈ S, y ⟨e, h⟩}

theorem restrConfig_restrict (S : Finset (Sym2 V)) (ω : Config V) :
    restrConfig S (S.restrict ω) = cutConfig S ω := by
  classical
  ext e
  constructor
  · rintro ⟨h, hh⟩
    exact ⟨hh, h⟩
  · rintro ⟨he, heS⟩
    exact ⟨heS, he⟩

theorem cutFun_eq_restrict (S : Finset (Sym2 V)) (g : Config V → ℝ) :
    ∃ G : (S → Prop) → ℝ, ∃ _ : True, ∀ ω : Config V, cutFun S g ω = G (S.restrict ω) := by
  classical
  refine ⟨fun y => g (restrConfig S y), trivial, fun ω => ?_⟩
  simp only [cutFun]
  rw [← restrConfig_restrict S ω]

/-- Restriction to a finite edge set commutes with forcing the state of an edge inside it. -/
theorem restrict_forceOn (S : Finset (Sym2 V)) {e : Sym2 V} (he : e ∈ S)
    (η ω : Config V) :
    S.restrict (forceOn {e} η ω) = Function.update (S.restrict ω) ⟨e, he⟩ (η e) := by
  classical
  funext i
  obtain ⟨e', he'⟩ := i
  change forceOn {e} η ω e' = Function.update (S.restrict ω) ⟨e, he⟩ (η e) ⟨e', he'⟩
  rw [Function.update_apply]
  by_cases h : e' = e
  · subst h
    rw [ite_eq_left rfl]
    apply propext
    change e' ∈ (ω \ {e'} ∪ η ∩ {e'}) ↔ e' ∈ η
    simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_sdiff, Set.mem_singleton_iff]
    tauto
  · have hne : (⟨e', he'⟩ : S) ≠ (⟨e, he⟩ : S) := fun hc => h (congrArg Subtype.val hc)
    rw [ite_eq_right hne]
    apply propext
    change e' ∈ (ω \ {e} ∪ η ∩ {e}) ↔ e' ∈ ω
    simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_sdiff, Set.mem_singleton_iff]
    tauto

/-- Restriction commutes with forcing an edge of `S` open. -/
theorem restrict_forceOn_open (S : Finset (Sym2 V)) {e : Sym2 V} (he : e ∈ S) (ω : Config V) :
    S.restrict (forceOn {e} {e} ω) = Function.update (S.restrict ω) ⟨e, he⟩ True := by
  classical
  rw [restrict_forceOn S he]
  congr 1
  exact propext ⟨fun _ => trivial, fun _ => rfl⟩

/-- Restriction commutes with forcing an edge of `S` closed. -/
theorem restrict_forceOn_closed (S : Finset (Sym2 V)) {e : Sym2 V} (he : e ∈ S) (ω : Config V) :
    S.restrict (forceOn {e} ∅ ω) = Function.update (S.restrict ω) ⟨e, he⟩ False := by
  classical
  rw [restrict_forceOn S he]
  congr 1

end PercLib.CriticalLRP

namespace PercLib.CriticalLRP

variable {V : Type*} [Countable V]

/-- Pointwise form of `cutFun_eq_restrict`. -/
theorem cutFun_apply (S : Finset (Sym2 V)) (g : Config V → ℝ) (ω : Config V) :
    cutFun S g ω = g (restrConfig S (S.restrict ω)) := by
  rw [cutFun, ← restrConfig_restrict S ω]

end PercLib.CriticalLRP


set_option linter.unusedSectionVars false

open MeasureTheory Measure Filter Finset
open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP
namespace FiniteVolume

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem configurationLaw_insert_notMem (p : ι → ℝ) {e : ι} {τ : Configuration ι}
    (h : e ∉ τ) :
    configurationLaw p (insert e τ) = p e * sliceWeight p e τ := by
  unfold configurationLaw sliceWeight
  rw [← mul_prod_erase (univ : Finset ι)
    (fun e' => if e' ∈ insert e τ then p e' else 1 - p e') (mem_univ e)]
  congr 1
  · simp [h]
  · refine prod_congr rfl fun e' he' => ?_
    have hne : e' ≠ e := (mem_erase.mp he').1
    by_cases hmem : e' ∈ τ
    · have : e' ∈ insert e τ := mem_insert_of_mem hmem
      simp [hmem, this]
    · have hnot : e' ∉ insert e τ := by
        simp [hmem, hne]
      simp [hmem, hnot]

theorem add_configurationLaw_insert_notMem (p : ι → ℝ) {e : ι} {τ : Configuration ι}
    (h : e ∉ τ) :
    configurationLaw p τ + configurationLaw p (insert e τ) = sliceWeight p e τ := by
  rw [configurationLaw_insert_notMem p h, configurationLaw_eq_sliceWeight, ite_eq_right h]
  ring

/-- The map `c ↦ c.erase e` is a bijection from `{c : e ∈ c}` to `{τ : e ∉ τ}`. -/
theorem sum_erase_eq_sum_insert (F : Configuration ι → ℝ) :
    (∑ c ∈ (univ : Finset (Configuration ι)).filter (fun c => e ∈ c), F c)
      = ∑ τ ∈ (univ : Finset (Configuration ι)).filter (fun τ => ¬ e ∈ τ), F (insert e τ) := by
  classical
  refine sum_nbij' (fun c => c.erase e) (fun τ => insert e τ) ?_ ?_ ?_ ?_ ?_
  · intro c hc
    simp only [mem_filter, mem_univ, true_and] at hc ⊢
    exact notMem_erase e c
  · intro τ hτ
    simp only [mem_filter, mem_univ, true_and] at hτ ⊢
    exact mem_insert_self e τ
  · intro c hc
    simp only [mem_filter, mem_univ, true_and] at hc
    exact insert_erase hc
  · intro τ hτ
    simp only [mem_filter, mem_univ, true_and] at hτ
    exact erase_insert hτ
  · intro c hc
    simp only [mem_filter, mem_univ, true_and] at hc
    rw [insert_erase hc]

/-- **Flip expectation equals pivotal mass.**  The expectation of
`X (insert e ω) - X (ω.erase e)` under the product law is the pivotal mass of `e` for `X`. -/
theorem expectation_flip_eq_pivotalMass (p : ι → ℝ) (e : ι) (X : Configuration ι → ℝ) :
    expectation p (fun c => X (insert e c) - X (c.erase e)) = pivotalMass p e X := by
  classical
  -- abbreviation for the `e`-free configurations
  set T : Finset (Configuration ι) :=
    (univ : Finset (Configuration ι)).filter (fun τ => ¬ e ∈ τ) with hT
  have hmemT : ∀ τ : Configuration ι, τ ∈ T ↔ e ∉ τ := by
    intro τ; rw [hT]; simp
  -- the "open" flip
  have hA : ∑ c : Configuration ι, configurationLaw p c * X (insert e c)
      = ∑ τ ∈ T, (configurationLaw p τ + configurationLaw p (insert e τ)) * X (insert e τ) := by
    rw [← Finset.sum_filter_add_sum_filter_not (s := (univ : Finset (Configuration ι)))
      (p := fun c => e ∈ c) (f := fun c => configurationLaw p c * X (insert e c))]
    have h1 : ∑ c ∈ (univ : Finset (Configuration ι)).filter (fun c => e ∈ c),
          configurationLaw p c * X (insert e c)
        = ∑ τ ∈ T, configurationLaw p (insert e τ) * X (insert e τ) := by
      rw [sum_erase_eq_sum_insert (e := e)]
      refine Finset.sum_congr rfl fun τ _ => ?_
      simp
    rw [h1, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun τ _ => ?_
    ring
  -- the "closed" flip
  have hB : ∑ c : Configuration ι, configurationLaw p c * X (c.erase e)
      = ∑ τ ∈ T, (configurationLaw p τ + configurationLaw p (insert e τ)) * X τ := by
    rw [← Finset.sum_filter_add_sum_filter_not (s := (univ : Finset (Configuration ι)))
      (p := fun c => e ∈ c) (f := fun c => configurationLaw p c * X (c.erase e))]
    have h1 : ∑ c ∈ (univ : Finset (Configuration ι)).filter (fun c => ¬ e ∈ c),
          configurationLaw p c * X (c.erase e)
        = ∑ τ ∈ T, configurationLaw p τ * X τ := by
      refine Finset.sum_congr rfl fun c hc => ?_
      have hc' : c ∈ T := hc
      rw [hmemT] at hc'
      rw [erase_eq_of_notMem hc']
    have h2 : ∑ c ∈ (univ : Finset (Configuration ι)).filter (fun c => e ∈ c),
          configurationLaw p c * X (c.erase e)
        = ∑ τ ∈ T, configurationLaw p (insert e τ) * X τ := by
      rw [sum_erase_eq_sum_insert (e := e)]
      refine Finset.sum_congr rfl fun τ hτ => ?_
      rw [erase_insert ((hmemT τ).mp hτ)]
    rw [h1, h2, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun τ _ => ?_
    ring
  have hsplit : expectation p (fun c => X (insert e c) - X (c.erase e))
      = (∑ c : Configuration ι, configurationLaw p c * X (insert e c))
        - ∑ c : Configuration ι, configurationLaw p c * X (c.erase e) := by
    rw [expectation, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun c _ => by ring
  rw [hsplit, hA, hB, ← Finset.sum_sub_distrib, pivotalMass, hT]
  refine Finset.sum_congr rfl fun τ hτ => ?_
  simp only [mem_filter, mem_univ, true_and] at hτ
  have h := add_configurationLaw_insert_notMem p hτ
  calc (configurationLaw p τ + configurationLaw p (insert e τ)) * X (insert e τ)
        - (configurationLaw p τ + configurationLaw p (insert e τ)) * X τ
      = (configurationLaw p τ + configurationLaw p (insert e τ))
          * (X (insert e τ) - X τ) := by ring
    _ = sliceWeight p e τ * (X (insert e τ) - X τ) := by rw [h]

end FiniteVolume

end PercLib.CriticalLRP


set_option linter.unusedSectionVars false

open MeasureTheory Measure Filter Finset
open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Countable V]

/-- **Pivotal flux of a window functional is a finite pivotal mass.** -/
theorem pivotalFlux_cutFun (π : Sym2 V → unitInterval) (S : Finset (Sym2 V))
    (g : Config V → ℝ) {e : Sym2 V} (he : e ∈ S) :
    pivotalFlux (edgeMeasure π) (cutFun S g) e
      = FiniteVolume.pivotalMass (fun i : S => (π i : ℝ)) ⟨e, he⟩
          (fun c : Configuration S => g (restrConfig S (fun i : S => i ∈ c))) := by
  classical
  set G : (S → Prop) → ℝ := fun y => g (restrConfig S y) with hG
  set X : Configuration S → ℝ := fun c => G (fun i : S => i ∈ c) with hX
  -- the flip difference in terms of the restricted configuration
  have hflip : ∀ ω : Config V, flipDiff (cutFun S g) e ω
      = G (Function.update (S.restrict ω) ⟨e, he⟩ True)
        - G (Function.update (S.restrict ω) ⟨e, he⟩ False) := by
    intro ω
    simp only [flipDiff, cutFun_apply, hG]
    rw [restrict_forceOn_open S he, restrict_forceOn_closed S he]
  have hcyl : ∫ ω : Config V, (G (Function.update (S.restrict ω) ⟨e, he⟩ True)
        - G (Function.update (S.restrict ω) ⟨e, he⟩ False)) ∂(edgeMeasure π)
      = expectation (fun i : S => (π i : ℝ))
          (fun c : Configuration S =>
            G (Function.update (fun i : S => i ∈ c) ⟨e, he⟩ True)
              - G (Function.update (fun i : S => i ∈ c) ⟨e, he⟩ False)) := by
    have h := integral_edgeMeasure_cylinder (V := V) π S
      (fun y : S → Prop => G (Function.update y ⟨e, he⟩ True)
        - G (Function.update y ⟨e, he⟩ False))
    simpa only [X] using h
  -- rewriting the two updates as insertion/erasure of the edge `⟨e, he⟩`
  have hT : ∀ c : Configuration S,
      Function.update (fun i : S => i ∈ c) ⟨e, he⟩ True
        = fun i : S => i ∈ insert ⟨e, he⟩ c := by
    intro c
    funext i
    by_cases h : i = ⟨e, he⟩
    · subst h
      simp
    · rw [Function.update_of_ne h]
      apply propext
      simp [h]
  have hF : ∀ c : Configuration S,
      Function.update (fun i : S => i ∈ c) ⟨e, he⟩ False
        = fun i : S => i ∈ erase c ⟨e, he⟩ := by
    intro c
    funext i
    by_cases h : i = ⟨e, he⟩
    · subst h
      simp
    · rw [Function.update_of_ne h]
      apply propext
      simp [h]
  have hXc : ∀ c : Configuration S, G (fun i : S => i ∈ c) = X c := fun c => rfl
  rw [pivotalFlux]
  simp only [hflip]
  rw [hcyl]
  simp only [hT, hF, hXc]
  exact FiniteVolume.expectation_flip_eq_pivotalMass (fun i : S => (π i : ℝ)) ⟨e, he⟩ X

end PercLib.CriticalLRP


set_option linter.unusedSectionVars false

open MeasureTheory Measure Filter Finset
open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Countable V]

/-- Deleting the edges outside `S` commutes with forcing an edge that is not in `S`. -/
theorem cutConfig_forceOn_of_notMem (S : Finset (Sym2 V)) {e : Sym2 V} (he : e ∉ S)
    (η ω : Config V) :
    cutConfig S (forceOn {e} η ω) = cutConfig S ω := by
  classical
  ext e'
  by_cases h : e' = e
  · subst h
    simp [cutConfig, he]
  · simp [cutConfig, forceOn, h]

/-- Deleting the edges outside `S` commutes with forcing an edge that is in `S`. -/
theorem cutConfig_forceOn_of_mem (S : Finset (Sym2 V)) {e : Sym2 V} (he : e ∈ S)
    (η ω : Config V) :
    cutConfig S (forceOn {e} η ω) = forceOn {e} η (cutConfig S ω) := by
  classical
  ext e'
  by_cases h : e' = e
  · subst h
    simp [cutConfig, forceOn, he]
  · simp [cutConfig, forceOn, h]

/-- The flip difference of a window functional vanishes at edges outside the window. -/
theorem flipDiff_cutFun_eq_zero_of_notMem {S : Finset (Sym2 V)} {e : Sym2 V} (he : e ∉ S)
    (g : Config V → ℝ) (ω : Config V) : flipDiff (cutFun S g) e ω = 0 := by
  unfold flipDiff cutFun
  rw [cutConfig_forceOn_of_notMem S he, cutConfig_forceOn_of_notMem S he, sub_self]

/-- The flip difference of a window functional vanishes at edges which do not touch the window
cluster of `o`, for any functional determined by that cluster. -/
theorem flipDiff_cutFun_eq_zero_of_notMem_touchSet {S : Finset (Sym2 V)} {e : Sym2 V} (he : e ∈ S)
    {g : Config V → ℝ} {o : V}
    (hdep : ∀ ω η : Config V, cluster ω o = cluster η o → g ω = g η) (ω : Config V)
    (h : e ∉ touchSet (cutConfig S ω) o) : flipDiff (cutFun S g) e ω = 0 := by
  unfold flipDiff cutFun
  rw [cutConfig_forceOn_of_mem S he, cutConfig_forceOn_of_mem S he]
  have h1 : g (forceOn {e} {e} (cutConfig S ω)) = g (cutConfig S ω) :=
    hdep _ _ (cluster_forceOn_singleton_eq_of_notMem_touchSet h {e})
  have h2 : g (forceOn {e} ∅ (cutConfig S ω)) = g (cutConfig S ω) :=
    hdep _ _ (cluster_forceOn_singleton_eq_of_notMem_touchSet h ∅)
  rw [h1, h2, sub_self]

/-- **Locality of the window pivot.**  For a bounded measurable functional of the cluster of `o`,
the absolute pivotal flux of a window functional obeys the single-edge touching bound. -/
theorem abs_pivotalFlux_cutFun_le {S : Finset (Sym2 V)} {o : V} (μ : Measure (Config V))
    [IsProbabilityMeasure μ] {g : Config V → ℝ} {m : ℝ} (hm : 0 ≤ m)
    (hbound : ∀ ω, |g ω| ≤ m) (hmeas : Measurable g)
    (hdep : ∀ ω η : Config V, cluster ω o = cluster η o → g ω = g η) (e : Sym2 V) :
    |pivotalFlux μ (cutFun S g) e|
      ≤ 2 * m * μ.real {ω : Config V | e ∈ touchSet ω o} := by
  classical
  set s : Set (Config V) := {ω : Config V | e ∈ touchSet ω o} with hs_def
  have hs : MeasurableSet s := measurableSet_touchSet_mem e
  have hmeasf : Measurable (flipDiff (cutFun S g) e) := by
    unfold flipDiff
    exact ((measurable_cutFun hmeas).comp (measurable_forceOn _ _)).sub
      ((measurable_cutFun hmeas).comp (measurable_forceOn _ _))
  have hpt : ∀ ω, ‖flipDiff (cutFun S g) e ω‖ ≤ (2 * m) * (s.indicator (fun _ => (1 : ℝ)) ω) := by
    intro ω
    by_cases h : e ∈ touchSet ω o
    · have hmem : ω ∈ s := h
      rw [Real.norm_eq_abs, Set.indicator_of_mem hmem, mul_one]
      exact abs_flipDiff_le_sup (fun ω => hbound (cutConfig S ω)) e ω
    · have hmem : ω ∉ s := h
      rw [Set.indicator_of_notMem hmem, mul_zero, Real.norm_eq_abs]
      by_cases he : e ∈ S
      · rw [flipDiff_cutFun_eq_zero_of_notMem_touchSet he hdep ω]
        · simp
        · intro hc
          obtain ⟨v, hv, hcv⟩ := mem_touchSet.mp hc
          exact h (mem_touchSet.mpr ⟨v, hv, cluster_mono (cutConfig_subset S ω) o hcv⟩)
      · rw [flipDiff_cutFun_eq_zero_of_notMem he]
        simp
  have hind : Integrable (fun ω => (s.indicator (fun _ => (1 : ℝ)) ω)) μ := by
    refine Integrable.of_bound (Measurable.aestronglyMeasurable ?_) 1 ?_
    · fun_prop
    · filter_upwards with ω
      rw [Real.norm_eq_abs]
      by_cases hmem : ω ∈ s <;> simp [Set.indicator_apply, hmem]
  have hInt : Integrable (fun ω => (2 * m) * (s.indicator (fun _ => (1 : ℝ)) ω)) μ :=
    hind.const_mul _
  calc |pivotalFlux μ (cutFun S g) e| = |∫ ω, flipDiff (cutFun S g) e ω ∂μ| := rfl
    _ ≤ ∫ ω, ‖flipDiff (cutFun S g) e ω‖ ∂μ := by
        simpa only [Real.norm_eq_abs] using
          (norm_integral_le_integral_norm (fun ω => flipDiff (cutFun S g) e ω) (μ := μ))
    _ ≤ ∫ ω, (2 * m) * (s.indicator (fun _ => (1 : ℝ)) ω) ∂μ :=
        integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _) hInt
          (Eventually.of_forall hpt)
    _ = (2 * m) * μ.real s := by
        rw [integral_const_mul,
          show ∫ a, s.indicator (fun _ => (1 : ℝ)) a ∂μ = μ.real s from
            integral_indicator_one hs]

/-- **The finite-window Russo derivative.**  The derivative of the expectation of a window
functional is the finite sum of pivotal fluxes over the window's edges. -/
theorem hasDerivAt_integral_cutFun (πt : ℝ → Sym2 V → unitInterval) (π' : Sym2 V → ℝ)
    (S : Finset (Sym2 V)) (g : Config V → ℝ) {t : ℝ}
    (hderiv : ∀ e : Sym2 V, HasDerivAt (fun t' => ((πt t' e : unitInterval) : ℝ)) (π' e) t) :
    HasDerivAt (fun t' => ∫ ω : Config V, cutFun S g ω ∂(edgeMeasure (πt t')))
      (∑ e : S, π' e.1 * pivotalFlux (edgeMeasure (πt t)) (cutFun S g) e.1) t := by
  classical
  have hcyl := hasDerivAt_integral_edgeMeasure_cylinder (V := V) πt π' S
    (fun y : S → Prop => g (restrConfig S y)) hderiv
  have hL : (fun t' => ∫ ω : Config V, cutFun S g ω ∂(edgeMeasure (πt t')))
      = fun t' => ∫ ω : Config V, (fun y : S → Prop => g (restrConfig S y)) (S.restrict ω)
          ∂(edgeMeasure (πt t')) := by
    funext t'
    exact integral_congr_ae (Eventually.of_forall fun ω => (cutFun_apply S g ω))
  rw [hL]
  refine hcyl.congr_deriv ?_
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [pivotalFlux_cutFun (πt t) S g e.2]

end PercLib.CriticalLRP


set_option linter.unusedSectionVars false

open MeasureTheory Measure Filter Finset
open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Countable V]

/-- The pivotal flux of a window functional vanishes for edges outside the window. -/
theorem pivotalFlux_cutFun_eq_zero_of_notMem (μ : Measure (Config V)) {S : Finset (Sym2 V)}
    {e : Sym2 V} (he : e ∉ S) (g : Config V → ℝ) :
    pivotalFlux μ (cutFun S g) e = 0 := by
  unfold pivotalFlux
  simp only [flipDiff_cutFun_eq_zero_of_notMem he]
  simp

/-- **Pointwise convergence of window pivots.**  Along any edge-exhausting sequence of windows, the
pivotal flux of the window functional converges to the pivotal flux of the limit functional. -/
theorem tendsto_pivotalFlux_cutFun {o : V} (μ : Measure (Config V)) [IsProbabilityMeasure μ]
    (S : ℕ → Finset (Sym2 V)) {g : Config V → ℝ} {m : ℝ} (hm : 0 ≤ m)
    (hbound : ∀ ω, |g ω| ≤ m) (hmeas : Measurable g)
    (hdep : ∀ ω η : Config V, cluster ω o = cluster η o → g ω = g η)
    (hcont : ∀ ω : Config V, Tendsto (fun n => cutFun (S n) g ω) atTop (𝓝 (g ω)))
    (e : Sym2 V) :
    Tendsto (fun n => pivotalFlux μ (cutFun (S n) g) e) atTop (𝓝 (pivotalFlux μ g e)) := by
  classical
  have hpoint : ∀ ω : Config V,
      Tendsto (fun n => flipDiff (cutFun (S n) g) e ω) atTop (𝓝 (flipDiff g e ω)) := by
    intro ω
    have h1 : Tendsto (fun n => cutFun (S n) g (forceOn {e} {e} ω)) atTop
        (𝓝 (g (forceOn {e} {e} ω))) := hcont _
    have h2 : Tendsto (fun n => cutFun (S n) g (forceOn {e} ∅ ω)) atTop
        (𝓝 (g (forceOn {e} ∅ ω))) := hcont _
    exact h1.sub h2
  have hmeasn : ∀ n, AEStronglyMeasurable (fun ω => flipDiff (cutFun (S n) g) e ω) μ := by
    intro n
    exact ((measurable_cutFun hmeas).comp (measurable_forceOn _ _) |>.sub
      ((measurable_cutFun hmeas).comp (measurable_forceOn _ _))).aestronglyMeasurable
  have hbnd : ∀ n, ∀ᵐ ω ∂μ, ‖flipDiff (cutFun (S n) g) e ω‖ ≤ 2 * m := by
    intro n
    filter_upwards with ω
    rw [Real.norm_eq_abs]
    exact abs_flipDiff_le_sup (fun ω => hbound (cutConfig (S n) ω)) e ω
  have hboundint : Integrable (fun _ : Config V => 2 * m) μ := integrable_const _
  have := tendsto_integral_of_dominated_convergence (μ := μ) (F := fun n ω =>
      flipDiff (cutFun (S n) g) e ω) (f := fun ω => flipDiff g e ω)
      (bound := fun _ => 2 * m) hmeasn hboundint hbnd
    (Eventually.of_forall hpoint)
  simpa only [pivotalFlux] using this

/-- **Convergence of the finite-window pivotal sums to the infinite pivotal series.** -/
theorem tendsto_windowFlux {o : V} (μ : Measure (Config V)) [IsProbabilityMeasure μ]
    (S : ℕ → Finset (Sym2 V)) {g : Config V → ℝ} {m : ℝ} (hm : 0 ≤ m)
    (hbound : ∀ ω, |g ω| ≤ m) (hmeas : Measurable g)
    (hdep : ∀ ω η : Config V, cluster ω o = cluster η o → g ω = g η)
    (hcont : ∀ ω : Config V, Tendsto (fun n => cutFun (S n) g ω) atTop (𝓝 (g ω)))
    (c : Sym2 V → ℝ)
    (hdom : Summable fun e => |c e| * (2 * m * μ.real {ω : Config V | e ∈ touchSet ω o})) :
    Tendsto (fun n => ∑ e ∈ S n, c e * pivotalFlux μ (cutFun (S n) g) e) atTop
      (𝓝 (∑' e, c e * pivotalFlux μ g e)) := by
  classical
  have hlim : ∀ e : Sym2 V,
      Tendsto (fun n => c e * pivotalFlux μ (cutFun (S n) g) e) atTop
        (𝓝 (c e * pivotalFlux μ g e)) :=
    fun e => (tendsto_pivotalFlux_cutFun μ S hm hbound hmeas hdep hcont e).const_mul (c e)
  have hbnd : ∀ n : ℕ, ∀ e : Sym2 V,
      ‖c e * pivotalFlux μ (cutFun (S n) g) e‖
        ≤ |c e| * (2 * m * μ.real {ω : Config V | e ∈ touchSet ω o}) := by
    intro n e
    rw [Real.norm_eq_abs, abs_mul]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    exact abs_pivotalFlux_cutFun_le μ hm hbound hmeas hdep e
  have hmain := tendsto_tsum_of_dominated_convergence (𝓕 := atTop)
    (f := fun n (e : Sym2 V) => c e * pivotalFlux μ (cutFun (S n) g) e)
    (g := fun e => c e * pivotalFlux μ g e)
    (bound := fun e => |c e| * (2 * m * μ.real {ω : Config V | e ∈ touchSet ω o}))
    hdom hlim (Eventually.of_forall hbnd)
  have hfin : ∀ n : ℕ, (∑' e : Sym2 V, c e * pivotalFlux μ (cutFun (S n) g) e)
      = ∑ e ∈ S n, c e * pivotalFlux μ (cutFun (S n) g) e := by
    intro n
    refine tsum_eq_sum fun e he => ?_
    rw [pivotalFlux_cutFun_eq_zero_of_notMem μ he, mul_zero]
  simpa only [hfin] using hmain

end PercLib.CriticalLRP


set_option linter.unusedSectionVars false

open MeasureTheory Measure Filter Finset
open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Countable V]

/-- **Infinite-volume Russo exchange (abstract form).**

`μ : ℝ → Measure (Config V)` is a family of probability measures, `g` a functional, `S n` an
increasing sequence of windows and `Φ` the candidate infinite pivotal flux.  If

* every window functional has the exact finite-window Russo derivative `∑_{e ∈ S n} c_r(e) ·
  pivotalFlux (μ r) (cutFun (S n) g) e`,
* the window expectations converge pointwise in the parameter to those of `g`, and
* the window fluxes converge to `Φ` locally uniformly on the open parameter set `I`,

then the expectation of `g` is differentiable on `I` with derivative `Φ`. -/
theorem hasDerivAt_integral_of_windowFlux
    (S : ℕ → Finset (Sym2 V)) (μ : ℝ → Measure (Config V))
    [∀ r : ℝ, IsProbabilityMeasure (μ r)] (c : ℝ → Sym2 V → ℝ) {g : Config V → ℝ}
    {Φ : ℝ → ℝ} {I : Set ℝ} (hI : IsOpen I) {r0 : ℝ}
    (hderiv : ∀ n : ℕ, ∀ r ∈ I,
      HasDerivAt (fun r' => ∫ ω : Config V, cutFun (S n) g ω ∂(μ r'))
        (∑ e ∈ S n, c r e * pivotalFlux (μ r) (cutFun (S n) g) e) r)
    (hconv : ∀ r ∈ I, Tendsto (fun n => ∫ ω : Config V, cutFun (S n) g ω ∂(μ r)) atTop
      (𝓝 (∫ ω : Config V, g ω ∂(μ r))))
    (hunif : TendstoLocallyUniformlyOn
      (fun n r => ∑ e ∈ S n, c r e * pivotalFlux (μ r) (cutFun (S n) g) e) Φ atTop I)
    (hr0 : r0 ∈ I) :
    HasDerivAt (fun r => ∫ ω : Config V, g ω ∂(μ r)) (Φ r0) r0 :=
  hasDerivAt_of_tendstoLocallyUniformlyOn hI hunif (Eventually.of_forall hderiv) hconv hr0

end PercLib.CriticalLRP


set_option linter.unusedSectionVars false

open MeasureTheory Measure Filter Finset
open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Countable V]

/-- Every vertex of the cluster of `o` is connected to `o` using only a finite set of open edges. -/
theorem exists_finset_cluster {ω : Config V} {o v : V} (hv : v ∈ cluster ω o) :
    ∃ T : Finset (Sym2 V), (T : Set (Sym2 V)) ⊆ ω ∧ v ∈ cluster (T : Set (Sym2 V)) o := by
  classical
  have h : Relation.ReflTransGen (openGraph ω).Adj o v := by
    have hc : Connects ω o v := (mem_cluster_iff).mp hv
    rw [Connects, SimpleGraph.reachable_iff_reflTransGen] at hc
    exact hc
  clear hv
  induction h with
  | refl => exact ⟨∅, by simp, cluster_mem_self _ _⟩
  | @tail a b _ hab ih =>
    obtain ⟨T, hT, ha⟩ := ih
    rw [openGraph_adj] at hab
    obtain ⟨hne, hedge⟩ := hab
    refine ⟨insert s(a, b) T, ?_, ?_⟩
    · intro e he
      rcases Finset.mem_insert.mp he with rfl | he
      · exact hedge
      · exact hT he
    · have hsub : (T : Set (Sym2 V)) ⊆ ((insert s(a, b) T : Finset (Sym2 V)) : Set (Sym2 V)) := by
        intro e he; exact Finset.mem_coe.mpr (Finset.mem_insert_of_mem (Finset.mem_coe.mp he))
      have hconn : Connects ((insert s(a, b) T : Finset (Sym2 V)) : Set (Sym2 V)) o a :=
        connects_mono (fun e he => hsub he) (mem_cluster_iff.mp ha)
      have hstep : (openGraph ((insert s(a, b) T : Finset (Sym2 V)) : Set (Sym2 V))).Adj a b := by
        rw [openGraph_adj]
        exact ⟨hne, Finset.mem_coe.mpr (Finset.mem_insert_self _ _)⟩
      exact mem_cluster_iff.mpr (hconn.trans hstep.reachable)

/-- For an increasing sequence of edge sets with union everything, the truncated cluster of `o`
eventually contains any given vertex of the cluster. -/
theorem eventually_mem_cluster_cutConfig (S : ℕ → Finset (Sym2 V)) (hSmono : Monotone S)
    (hS : ∀ e : Sym2 V, ∃ n, e ∈ S n) (ω : Config V) {o v : V} (hv : v ∈ cluster ω o) :
    ∀ᶠ n in atTop, v ∈ cluster (cutConfig (S n) ω) o := by
  classical
  obtain ⟨T, hT, hTc⟩ := exists_finset_cluster hv
  -- the finite set `T` is eventually contained in `S n`
  have hTfin : ∃ N, T ⊆ S N := by
    choose N hN using hS
    refine ⟨T.sup N, fun e he => ?_⟩
    exact hSmono (Finset.le_sup (f := N) he) (hN e)
  obtain ⟨N, hN⟩ := hTfin
  refine eventually_atTop.mpr ⟨N, fun n hn => ?_⟩
  have hsub : T ⊆ S n := fun e he => hSmono hn (hN he)
  have hT' : (T : Set (Sym2 V)) ⊆ cutConfig (S n) ω := by
    intro e he
    exact ⟨hT he, Finset.mem_coe.mpr (hsub (Finset.mem_coe.mp he))⟩
  exact cluster_mono (fun e he => hT' he) o hTc

/-- **Cluster volumes of the truncated configurations converge to the full cluster volume.** -/
theorem clusterVol_cutConfig_tendsto (S : ℕ → Finset (Sym2 V)) (hSmono : Monotone S)
    (hS : ∀ e : Sym2 V, ∃ n, e ∈ S n) (ω : Config V) (o : V) :
    Tendsto (fun n => clusterVol (cutConfig (S n) ω) o) atTop (𝓝 (clusterVol ω o)) := by
  classical
  have hmono : Monotone fun n => clusterVol (cutConfig (S n) ω) o := by
    intro m n hmn
    refine clusterVol_mono (ω := cutConfig (S m) ω) (ω' := cutConfig (S n) ω) (fun e he => ?_) o
    exact ⟨he.1, hSmono hmn he.2⟩
  have hsup : (⨆ n, clusterVol (cutConfig (S n) ω) o) = clusterVol ω o := by
    refine le_antisymm (iSup_le fun n => ?_) ?_
    · exact clusterVol_mono (ω := cutConfig (S n) ω) (ω' := ω) (fun e he => he.1) o
    · rw [clusterVol_eq_tsum, ENNReal.tsum_eq_iSup_sum]
      refine iSup_le fun s => ?_
      -- every vertex of the finite set `s` that lies in the cluster is eventually in the truncation
      have hev : ∀ᶠ n in atTop, ∀ v ∈ s,
          (cluster ω o).indicator (fun _ => (1 : ℝ≥0∞)) v
            = (cluster (cutConfig (S n) ω) o).indicator (fun _ => (1 : ℝ≥0∞)) v := by
        rw [eventually_all_finset]
        intro v _
        by_cases hv : v ∈ cluster ω o
        · filter_upwards [eventually_mem_cluster_cutConfig S hSmono hS ω hv] with n hn
          rw [Set.indicator_of_mem hv, Set.indicator_of_mem hn]
        · filter_upwards with n
          have hnot : v ∉ cluster (cutConfig (S n) ω) o := fun hc =>
            hv (cluster_mono (ω := cutConfig (S n) ω) (ω' := ω) (fun e he => he.1) o hc)
          rw [Set.indicator_of_notMem hv, Set.indicator_of_notMem hnot]
      obtain ⟨N, hN⟩ := eventually_atTop.mp hev
      have hn : ∀ v ∈ s, (cluster ω o).indicator (fun _ => (1 : ℝ≥0∞)) v
          = (cluster (cutConfig (S N) ω) o).indicator (fun _ => (1 : ℝ≥0∞)) v :=
        fun v hv => hN N le_rfl v hv
      rw [Finset.sum_congr rfl hn]
      calc ∑ v ∈ s, (cluster (cutConfig (S N) ω) o).indicator (fun _ => (1 : ℝ≥0∞)) v
          ≤ ∑' v, (cluster (cutConfig (S N) ω) o).indicator (fun _ => (1 : ℝ≥0∞)) v :=
            ENNReal.sum_le_tsum s
        _ = clusterVol (cutConfig (S N) ω) o := (clusterVol_eq_tsum (cutConfig (S N) ω) o).symm
        _ ≤ ⨆ m, clusterVol (cutConfig (S m) ω) o :=
            le_iSup (fun m => clusterVol (cutConfig (S m) ω) o) N
  rw [← hsup]
  exact tendsto_atTop_iSup hmono

end PercLib.CriticalLRP


set_option linter.unusedSectionVars false

open MeasureTheory Measure Filter Finset
open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Countable V]

/-- **The pivotal weight is summable.**  If the edge weights `c` have per-vertex mass at most `D`
and the expected cluster volume of `o` is finite, then `e ↦ |c e| · P(e touches K_o)` is summable,
with total mass at most `D · E|K_o|`. -/
theorem summable_abs_weight_touch {o : V} (μ : Measure (Config V)) [IsProbabilityMeasure μ]
    (c : Sym2 V → ℝ) {D : ℝ} (hD : 0 ≤ D)
    (hdeg : ∀ x : V, ∀ u : Finset (Sym2 V),
      ∑ e ∈ u, |c e| * (if x ∈ e then (1 : ℝ) else 0) ≤ D)
    (hvol : ∫⁻ ω, clusterVol ω o ∂μ ≠ ⊤) :
    Summable fun e : Sym2 V => |c e| * μ.real {ω : Config V | e ∈ touchSet ω o} := by
  classical
  refine summable_of_sum_le (c := D * (∫⁻ ω, clusterVol ω o ∂μ).toReal)
    (fun e => mul_nonneg (abs_nonneg _) (measureReal_nonneg)) ?_
  intro u
  -- integrability of the single-edge weight
  have hind : ∀ e : Sym2 V, Integrable (fun ω : Config V =>
      |c e| * (if e ∈ touchSet ω o then (1 : ℝ) else 0)) μ := by
    intro e
    refine Integrable.const_mul (Integrable.of_bound (Measurable.aestronglyMeasurable ?_) 1 ?_) _
    · exact measurable_touchInd e
    · filter_upwards with ω
      rw [Real.norm_eq_abs]
      by_cases h : e ∈ touchSet ω o <;> simp [h]
  have hswap : ∑ e ∈ u, |c e| * μ.real {ω : Config V | e ∈ touchSet ω o}
      = ∫ ω, (∑ e ∈ u, |c e| * (if e ∈ touchSet ω o then (1 : ℝ) else 0)) ∂μ := by
    have hterm : ∀ e : Sym2 V, |c e| * μ.real {ω : Config V | e ∈ touchSet ω o}
        = ∫ ω, |c e| * (if e ∈ touchSet ω o then (1 : ℝ) else 0) ∂μ := by
      intro e
      rw [integral_const_mul, integral_touchInd μ e]
    rw [Finset.sum_congr rfl (fun e _ => hterm e)]
    exact (integral_finsetSum u (fun e _ => hind e)).symm
  -- the pointwise bound by the degree constant times the truncated cluster cardinality
  have hcardFun : ∀ u : Finset (Sym2 V), (fun ω : Config V =>
      (((edgeVertices u).filter (fun x => x ∈ cluster ω o)).card : ℝ))
      = fun ω => ∑ x ∈ edgeVertices u, (if x ∈ cluster ω o then (1 : ℝ) else 0) := by
    intro u
    funext ω
    rw [Finset.card_filter]
    push_cast
    rfl
  have hcardInt : Integrable (fun ω : Config V =>
      D * (((edgeVertices u).filter (fun x => x ∈ cluster ω o)).card : ℝ)) μ := by
    have hmeas : Measurable fun ω : Config V =>
        (((edgeVertices u).filter (fun x => x ∈ cluster ω o)).card : ℝ) := by
      rw [hcardFun u]
      exact Finset.measurable_sum _ fun x _ => measurable_clusterInd x
    refine Integrable.const_mul (Integrable.of_bound hmeas.aestronglyMeasurable
      ((edgeVertices u).card : ℝ) ?_) _
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hle : ((edgeVertices u).filter (fun x => x ∈ cluster ω o)).card
        ≤ (edgeVertices u).card := Finset.card_filter_le _ _
    exact_mod_cast hle
  have h3 : ∫ ω, (∑ e ∈ u, |c e| * (if e ∈ touchSet ω o then (1 : ℝ) else 0)) ∂μ
      ≤ ∫ ω, D * (((edgeVertices u).filter (fun x => x ∈ cluster ω o)).card : ℝ) ∂μ := by
    refine integral_mono_of_nonneg (Eventually.of_forall fun ω =>
      Finset.sum_nonneg fun e _ => by positivity) (hcardInt) (Eventually.of_forall fun ω => ?_)
    exact sum_touchSet_weight_le (o := o) c hdeg u ω
  have h4 : ∫ ω, D * (((edgeVertices u).filter (fun x => x ∈ cluster ω o)).card : ℝ) ∂μ
      = D * ∑ x ∈ edgeVertices u, μ.real {ω : Config V | x ∈ cluster ω o} := by
    have hpt : ∀ ω : Config V,
        D * (((edgeVertices u).filter (fun x => x ∈ cluster ω o)).card : ℝ)
          = D * ∑ x ∈ edgeVertices u, (if x ∈ cluster ω o then (1 : ℝ) else 0) := by
      intro ω
      rw [congrFun (hcardFun u) ω]
    calc ∫ ω, D * (((edgeVertices u).filter (fun x => x ∈ cluster ω o)).card : ℝ) ∂μ
        = ∫ ω, D * ∑ x ∈ edgeVertices u,
            (if x ∈ cluster ω o then (1 : ℝ) else 0) ∂μ :=
          integral_congr_ae (Eventually.of_forall hpt)
      _ = D * ∫ ω, ∑ x ∈ edgeVertices u,
            (if x ∈ cluster ω o then (1 : ℝ) else 0) ∂μ := integral_const_mul D _
      _ = D * ∑ x ∈ edgeVertices u, μ.real {ω : Config V | x ∈ cluster ω o} := by
          rw [integral_finsetSum _ (fun x _ => integrable_clusterInd μ x)]
          congr 1
          exact Finset.sum_congr rfl fun x _ => integral_clusterInd μ x
  have h5 : ∑ x ∈ edgeVertices u, μ.real {ω : Config V | x ∈ cluster ω o}
      ≤ (∫⁻ ω, clusterVol ω o ∂μ).toReal := by
    have hsplit : ∑ x ∈ edgeVertices u, μ {ω : Config V | x ∈ cluster ω o}
        ≤ ∫⁻ ω, clusterVol ω o ∂μ := by
      have hL : ∑ x ∈ edgeVertices u, μ {ω : Config V | x ∈ cluster ω o}
          = ∫⁻ ω, ∑ x ∈ edgeVertices u,
              (if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0) ∂μ := by
        rw [lintegral_finsetSum]
        · exact Finset.sum_congr rfl fun x _ => (lintegral_clusterIndENN μ x).symm
        · intro x _
          exact measurable_clusterIndENN (o := o) x
      rw [hL]
      refine lintegral_mono fun ω => ?_
      rw [clusterVol_eq_tsum]
      exact ENNReal.sum_le_tsum (edgeVertices u)
    calc ∑ x ∈ edgeVertices u, μ.real {ω : Config V | x ∈ cluster ω o}
        = (∑ x ∈ edgeVertices u, μ {ω : Config V | x ∈ cluster ω o}).toReal := by
          rw [ENNReal.toReal_sum (fun x _ => measure_ne_top _ _)]
          rfl
      _ ≤ (∫⁻ ω, clusterVol ω o ∂μ).toReal := ENNReal.toReal_mono hvol hsplit
  calc ∑ e ∈ u, |c e| * μ.real {ω : Config V | e ∈ touchSet ω o}
      = ∫ ω, (∑ e ∈ u, |c e| * (if e ∈ touchSet ω o then (1 : ℝ) else 0)) ∂μ := hswap
    _ ≤ ∫ ω, D * (((edgeVertices u).filter (fun x => x ∈ cluster ω o)).card : ℝ) ∂μ := h3
    _ = D * ∑ x ∈ edgeVertices u, μ.real {ω : Config V | x ∈ cluster ω o} := h4
    _ ≤ D * (∫⁻ ω, clusterVol ω o ∂μ).toReal :=
        mul_le_mul_of_nonneg_left h5 hD

end PercLib.CriticalLRP


set_option linter.unusedSectionVars false

open MeasureTheory Measure Filter Finset
open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Countable V]

/-- **The capped cluster volume of the truncated configurations converges pointwise.** -/
theorem tendsto_cappedClusterVol_cutConfig (S : ℕ → Finset (Sym2 V)) (hSmono : Monotone S)
    (hS : ∀ e : Sym2 V, ∃ n, e ∈ S n) (o : V) (p : ℕ) (n' m' : ℝ) (ω : Config V) :
    Tendsto (fun k => cappedClusterVol o p n' m' (cutConfig (S k) ω)) atTop
      (𝓝 (cappedClusterVol o p n' m' ω)) := by
  classical
  have hvol := clusterVol_cutConfig_tendsto S hSmono hS ω o
  have h1 : Tendsto (fun k => clusterVol (cutConfig (S k) ω) o ⊓ ENNReal.ofReal n') atTop
      (𝓝 (clusterVol ω o ⊓ ENNReal.ofReal n')) :=
    hvol.min tendsto_const_nhds
  have hne : clusterVol ω o ⊓ ENNReal.ofReal n' ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (inf_le_right)
  have h2 : Tendsto (fun k => (clusterVol (cutConfig (S k) ω) o ⊓ ENNReal.ofReal n').toReal)
      atTop (𝓝 ((clusterVol ω o ⊓ ENNReal.ofReal n').toReal)) :=
    ENNReal.tendsto_toReal hne |>.comp h1
  have h3 : Tendsto (fun k => ((clusterVol (cutConfig (S k) ω) o ⊓ ENNReal.ofReal n').toReal) ^ p)
      atTop (𝓝 (((clusterVol ω o ⊓ ENNReal.ofReal n').toReal) ^ p)) := h2.pow p
  exact h3.min tendsto_const_nhds

/-- **Window expectations converge to the infinite-volume expectation.** -/
theorem tendsto_integral_cutFun (S : ℕ → Finset (Sym2 V)) (hSmono : Monotone S)
    (hS : ∀ e : Sym2 V, ∃ n, e ∈ S n) (o : V) (p : ℕ) (n' m' : ℝ) (hm' : 0 ≤ m')
    (μ : Measure (Config V)) [IsProbabilityMeasure μ] :
    Tendsto (fun k => ∫ ω : Config V, cutFun (S k) (cappedClusterVol o p n' m') ω ∂μ) atTop
      (𝓝 (∫ ω : Config V, cappedClusterVol o p n' m' ω ∂μ)) := by
  classical
  have hmeas : ∀ k, AEStronglyMeasurable
      (fun ω : Config V => cutFun (S k) (cappedClusterVol o p n' m') ω) μ :=
    fun k => (measurable_cutFun (measurable_cappedClusterVol o p n' m')).aestronglyMeasurable
  have hboundint : Integrable (fun _ : Config V => max m' 0) μ := integrable_const _
  have hbnd : ∀ k, ∀ᵐ ω ∂μ, ‖cutFun (S k) (cappedClusterVol o p n' m') ω‖ ≤ max m' 0 := by
    intro k
    filter_upwards with ω
    rw [Real.norm_eq_abs]
    exact cappedClusterVol_bound o p n' m' hm' _
  exact tendsto_integral_of_dominated_convergence (μ := μ)
    (F := fun k ω => cutFun (S k) (cappedClusterVol o p n' m') ω)
    (f := fun ω => cappedClusterVol o p n' m' ω) (bound := fun _ => max m' 0)
    hmeas hboundint hbnd (Eventually.of_forall fun ω =>
      tendsto_cappedClusterVol_cutConfig S hSmono hS o p n' m' ω)

/-- **Infinite-volume Russo for the capped cluster-volume functional (reduced form).**

For a family `π` of independent edge laws with `r`-derivatives `c`, an edge-exhausting sequence of
windows `S k`, and the capped cluster-volume functional `g` of `o`, the expectation of `g` is
differentiable at `r0` with derivative the infinite pivotal flux `Φ`, provided

* `hdom`: the pivotal flux weights are summable for every parameter in `I` (finite expected
  cluster volume; `RussoInf/Capstone`),
* `hunif`: the window fluxes converge to `Φ` locally uniformly near `r0`.

All other inputs are discharged: the finite-window Russo identities (`hasDerivAt_integral_cutFun`),
the pointwise convergence of window expectations (`tendsto_integral_cutFun`) and the pointwise
convergence of window fluxes to the infinite pivotal series (`tendsto_windowFlux`). -/
theorem hasDerivAt_integral_cappedClusterVol
    (o : V) (p : ℕ) (n' m' : ℝ) (hm' : 0 ≤ m')
    (S : ℕ → Finset (Sym2 V)) (hSmono : Monotone S) (hS : ∀ e : Sym2 V, ∃ n, e ∈ S n)
    (π : ℝ → Sym2 V → unitInterval) (c : ℝ → Sym2 V → ℝ)
    {I : Set ℝ} (hI : IsOpen I) {r0 : ℝ} (hr0 : r0 ∈ I)
    (hderiv : ∀ e : Sym2 V, ∀ r ∈ I,
      HasDerivAt (fun r' => ((π r' e : unitInterval) : ℝ)) (c r e) r)
    (hdom : ∀ r ∈ I, Summable fun e : Sym2 V =>
      |c r e| * (2 * max m' 0 * (edgeMeasure (π r)).real {ω : Config V | e ∈ touchSet ω o}))
    (Φ : ℝ → ℝ)
    (hunif : TendstoLocallyUniformlyOn
      (fun k r => ∑ e ∈ S k, c r e *
        pivotalFlux (edgeMeasure (π r)) (cutFun (S k) (cappedClusterVol o p n' m')) e) Φ atTop I) :
    HasDerivAt (fun r => ∫ ω : Config V, cappedClusterVol o p n' m' ω ∂(edgeMeasure (π r)))
      (Φ r0) r0 := by
  classical
  refine hasDerivAt_integral_of_windowFlux S (fun r => edgeMeasure (π r)) c hI ?_ ?_ hunif hr0
  · intro k r hr
    have h := hasDerivAt_integral_cutFun π (c r) (S k) (cappedClusterVol o p n' m')
      (fun e => hderiv e r hr)
    have hsum : (∑ e : S k, c r (e : Sym2 V) *
          pivotalFlux (edgeMeasure (π r)) (cutFun (S k) (cappedClusterVol o p n' m')) (e : Sym2 V))
        = ∑ e ∈ S k, c r e *
          pivotalFlux (edgeMeasure (π r)) (cutFun (S k) (cappedClusterVol o p n' m')) e := by
      exact Finset.sum_coe_sort (S k) (fun e => c r e *
        pivotalFlux (edgeMeasure (π r)) (cutFun (S k) (cappedClusterVol o p n' m')) e)
    exact h.congr_deriv hsum
  · intro r _
    exact tendsto_integral_cutFun S hSmono hS o p n' m' hm' (edgeMeasure (π r))

end PercLib.CriticalLRP

namespace PercLib.CriticalLRP

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Countable V]

/-- **Infinite-volume Russo for the capped cluster volume, with the paper's inputs.**

Same as `hasDerivAt_integral_cappedClusterVol`, but with the flux domination hypothesis replaced by
the two quantitative inputs the paper actually uses: a per-vertex bound `D r` on the total flux
weight (`hdeg`, the degree bound of the cut-off graph) and finiteness of the expected cluster volume
(`hvol`, the sharpness input).  The domination then follows from
`summable_abs_weight_touch`. -/
theorem hasDerivAt_integral_cappedClusterVol_of_sharpness
    (o : V) (p : ℕ) (n' m' : ℝ) (hm' : 0 ≤ m')
    (S : ℕ → Finset (Sym2 V)) (hSmono : Monotone S) (hS : ∀ e : Sym2 V, ∃ n, e ∈ S n)
    (π : ℝ → Sym2 V → unitInterval) (c : ℝ → Sym2 V → ℝ) (D : ℝ → ℝ)
    {I : Set ℝ} (hI : IsOpen I) {r0 : ℝ} (hr0 : r0 ∈ I)
    (hderiv : ∀ e : Sym2 V, ∀ r ∈ I,
      HasDerivAt (fun r' => ((π r' e : unitInterval) : ℝ)) (c r e) r)
    (hD : ∀ r ∈ I, 0 ≤ D r)
    (hdeg : ∀ r ∈ I, ∀ x : V, ∀ u : Finset (Sym2 V),
      ∑ e ∈ u, |c r e| * (if x ∈ e then (1 : ℝ) else 0) ≤ D r)
    (hvol : ∀ r ∈ I, ∫⁻ ω : Config V, clusterVol ω o ∂(edgeMeasure (π r)) ≠ ⊤)
    (Φ : ℝ → ℝ)
    (hunif : TendstoLocallyUniformlyOn
      (fun k r => ∑ e ∈ S k, c r e *
        pivotalFlux (edgeMeasure (π r)) (cutFun (S k) (cappedClusterVol o p n' m')) e) Φ atTop I) :
    HasDerivAt (fun r => ∫ ω : Config V, cappedClusterVol o p n' m' ω ∂(edgeMeasure (π r)))
      (Φ r0) r0 := by
  classical
  refine hasDerivAt_integral_cappedClusterVol o p n' m' hm' S hSmono hS π c hI hr0
    hderiv (fun r hr => ?_) Φ hunif
  have hsum := summable_abs_weight_touch (o := o) (edgeMeasure (π r)) (c r) (hD r hr)
    (hdeg r hr) (hvol r hr)
  have h2 := hsum.mul_left (2 * max m' 0)
  simpa only [mul_assoc, mul_comm, mul_left_comm] using h2

end PercLib.CriticalLRP


set_option linter.unusedSectionVars false

open MeasureTheory Measure Filter Finset
open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP

attribute [local instance] Classical.propDecidable

variable {d : ℕ}

/-- The cut-off edge probability family of Definition I.1.5 as a family of `unitInterval`s. -/
noncomputable def cutoffPiFamily (β : ℝ) (K : ℝ → ℝ) (hβ : 0 ≤ β)
    (hprof : ∀ (r : ℝ) (e : Sym2 (Fin d → ℤ)),
      0 ≤ FiniteVolume.cutoffProfile K r (FiniteVolume.edgeLen e))
    (r : ℝ) (e : Sym2 (Fin d → ℤ)) : unitInterval :=
  ⟨longRangeEdgeProbability β (FiniteVolume.cutoffProfile K r (FiniteVolume.edgeLen e)),
    longRangeEdgeProbability_mem_Icc hβ (hprof r e)⟩

@[simp] theorem cutoffPiFamily_coe (β : ℝ) (K : ℝ → ℝ) (hβ : 0 ≤ β)
    (hprof : ∀ (r : ℝ) (e : Sym2 (Fin d → ℤ)),
      0 ≤ FiniteVolume.cutoffProfile K r (FiniteVolume.edgeLen e))
    (r : ℝ) (e : Sym2 (Fin d → ℤ)) :
    ((cutoffPiFamily (d := d) β K hβ hprof r e : unitInterval) : ℝ)
      = longRangeEdgeProbability β (FiniteVolume.cutoffProfile K r (FiniteVolume.edgeLen e)) := rfl

/-- **Infinite-volume Russo for the cut-off model (reduced form).**

For the cut-off long-range model on `ℤ^d` with profile `K`, derivative scale `K'` (so that
`d/dr K = -K'`), away from edge lengths (`hne`), the expectation of the capped cluster-volume
functional of `o` has derivative equal to the infinite pivotal flux `Φ`, provided the expected
cluster volume is finite for every parameter in `I` (the sharpness input) and the finite-window
pivotal fluxes converge to `Φ` locally uniformly on `I` (the remaining obligation). -/
theorem hasDerivAt_integral_cappedClusterVol_cutoff
    (o : Fin d → ℤ) (p : ℕ) (n' m' : ℝ) (hm' : 0 ≤ m')
    (S : ℕ → Finset (Sym2 (Fin d → ℤ))) (hSmono : Monotone S)
    (hS : ∀ e : Sym2 (Fin d → ℤ), ∃ n, e ∈ S n)
    {β K' : ℝ} (hβ : 0 ≤ β) (hK' : 0 ≤ K') {K : ℝ → ℝ}
    (hprof : ∀ (r : ℝ) (e : Sym2 (Fin d → ℤ)),
      0 ≤ FiniteVolume.cutoffProfile K r (FiniteVolume.edgeLen e))
    {I : Set ℝ} (hI : IsOpen I) {r0 : ℝ} (hr0 : r0 ∈ I)
    (hderivK : ∀ r ∈ I, HasDerivAt K (-K') r)
    (hne : ∀ r ∈ I, ∀ e : Sym2 (Fin d → ℤ), FiniteVolume.edgeLen e ≠ r)
    (hvol : ∀ r ∈ I, ∫⁻ ω : Config (Fin d → ℤ), clusterVol ω o
      ∂(edgeMeasure (cutoffPiFamily (d := d) β K hβ hprof r)) ≠ ⊤)
    (Φ : ℝ → ℝ)
    (hunif : TendstoLocallyUniformlyOn
      (fun k r => ∑ e ∈ S k, CutoffFlux.cutoffEdgeDeriv K β K' r e *
        pivotalFlux (edgeMeasure (cutoffPiFamily (d := d) β K hβ hprof r))
          (cutFun (S k) (cappedClusterVol o p n' m')) e) Φ atTop I) :
    HasDerivAt (fun r => ∫ ω : Config (Fin d → ℤ), cappedClusterVol o p n' m' ω
      ∂(edgeMeasure (cutoffPiFamily (d := d) β K hβ hprof r))) (Φ r0) r0 := by
  classical
  refine hasDerivAt_integral_cappedClusterVol_of_sharpness o p n' m' hm' S hSmono hS
    (cutoffPiFamily (d := d) β K hβ hprof) (fun r e => CutoffFlux.cutoffEdgeDeriv K β K' r e)
    (fun r => β * K' * ((2 * ⌈r⌉₊ + 1) ^ d : ℕ)) hI hr0 ?_ ?_ ?_ hvol Φ hunif
  · intro e r hr
    have h := CutoffFlux.cutoffEdgeDeriv_hasDerivAt (K := K) (β := β) (K' := K') (r := r)
      (e := e) (hne r hr e) (hderivK r hr)
    simpa only [cutoffPiFamily_coe] using h
  · intro r _
    positivity
  · intro r _ x u
    have h := CutoffFlux.cutoff_edgeDeriv_degree (d := d) (K := K) (β := β) (K' := K') (r := r)
      hβ hK' (fun e => longRangeEdgeProbability_nonneg hβ (hprof r e))
      (fun e => longRangeEdgeProbability_le_one hβ (hprof r e)) x u
    refine le_of_eq ?_ |>.trans h
    refine Finset.sum_congr rfl fun e _ => ?_
    exact congrArg (fun t => |CutoffFlux.cutoffEdgeDeriv K β K' r e| * t)
      (CutoffFlux.ite_inst_irrel _ _ (1 : ℝ) 0)

end PercLib.CriticalLRP
