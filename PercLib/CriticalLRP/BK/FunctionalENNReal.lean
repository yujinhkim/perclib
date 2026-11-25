/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
# Lemma I.2.1 with `ℝ≥0∞`-valued functionals: cluster sizes with infinite clusters

The real-valued form of Lemma I.2.1 (`LemmaI21Final.lean`) requires `F (K_x) ∈ ℝ`.  The functionals
that occur in the moment estimates of Hutchcroft, arXiv:2508.18807v1, Section I.4 are `|K_x|^p`,
which take the value `+∞` on infinite clusters, so a formulation with values in `ℝ≥0∞` is the
natural one.

Here we obtain it from the real-valued form by truncation `F ∧ n` followed by monotone convergence
(`lintegral_iSup` and `iSup_mul_iSup_eq`).  No new BK input is used: the truncations are still
continuous from below, so the hypotheses are literally the same as in the real-valued case, except
that the level-set condition ranges over `s : ℝ≥0∞` and the conclusion is an inequality in `ℝ≥0∞`
without `ofReal`.
-/
module

public import PercLib.CriticalLRP.BK.GraphConsequences
public import PercLib.CriticalLRP.BK.LayerCake
public import PercLib.CriticalLRP.BK.InternalWitness
public import PercLib.CriticalLRP.BK.FunctionalFromBelow

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

set_option autoImplicit true

@[expose] public section

namespace PercLib.CriticalLRP

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

section Truncation
attribute [local instance] Classical.propDecidable

/-- Pointwise truncation `x ↦ min (f x, n)` of an `ℝ≥0∞`-valued function, as a real-valued
function. -/
noncomputable def truncFun {α : Type*} (n : ℕ) (f : α → ℝ≥0∞) : α → ℝ :=
  fun a => (min (f a) (n : ℝ≥0∞)).toReal

theorem truncFun_nonneg {α : Type*} (n : ℕ) (f : α → ℝ≥0∞) (a : α) : 0 ≤ truncFun n f a :=
  ENNReal.toReal_nonneg

theorem ofReal_truncFun {α : Type*} (n : ℕ) (f : α → ℝ≥0∞) (a : α) :
    ENNReal.ofReal (truncFun n f a) = min (f a) (n : ℝ≥0∞) :=
  ENNReal.ofReal_toReal (by simp)

theorem iSup_min_natCast (a : ℝ≥0∞) : (⨆ n : ℕ, min a (n : ℝ≥0∞)) = a := by
  refine le_antisymm (iSup_le fun n => min_le_left _ _) ?_
  by_cases ha : a = ⊤
  · rw [ha]
    simp only [min_top_left]
    exact ENNReal.iSup_natCast ▸ le_rfl
  · refine le_iSup_of_le (Nat.ceil a.toReal) ?_
    refine le_of_eq ?_
    rw [min_eq_left]
    calc a = ENNReal.ofReal a.toReal := (ENNReal.ofReal_toReal ha).symm
      _ ≤ ENNReal.ofReal ((Nat.ceil a.toReal : ℕ) : ℝ) := ENNReal.ofReal_le_ofReal (Nat.le_ceil _)
      _ = ((Nat.ceil a.toReal : ℕ) : ℝ≥0∞) := ENNReal.ofReal_natCast _

theorem iSup_ofReal_truncFun {α : Type*} (f : α → ℝ≥0∞) (a : α) :
    (⨆ n, ENNReal.ofReal (truncFun n f a)) = f a := by
  simp only [ofReal_truncFun]
  exact iSup_min_natCast (f a)

theorem monotone_ofReal_truncFun {α : Type*} (f : α → ℝ≥0∞) (a : α) :
    Monotone fun n => ENNReal.ofReal (truncFun n f a) := by
  intro m n hmn
  simp only [ofReal_truncFun]
  exact min_le_min le_rfl (by exact_mod_cast hmn)

theorem measurable_truncFun {α : Type*} [MeasurableSpace α] {f : α → ℝ≥0∞} (hf : Measurable f)
    (n : ℕ) : Measurable (truncFun n f) :=
  ENNReal.measurable_toReal.comp (hf.min measurable_const)

theorem truncFun_mono_fun {α : Type*} {f g : α → ℝ≥0∞} (h : ∀ a, f a ≤ g a) (n : ℕ) :
    ∀ a, truncFun n f a ≤ truncFun n g a :=
  fun a => ENNReal.toReal_mono (by simp) (min_le_min (h a) le_rfl)

/-- The layer-cake/monotone-convergence identity for truncations. -/
theorem lintegral_eq_iSup_truncFun {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ a, f a ∂μ = ⨆ n, ∫⁻ a, ENNReal.ofReal (truncFun n f a) ∂μ := by
  rw [← lintegral_iSup (fun n => (measurable_truncFun hf n).ennreal_ofReal)
    (fun m n hmn a => monotone_ofReal_truncFun f a hmn)]
  congr 1
  funext a
  exact (iSup_ofReal_truncFun f a).symm

/-- Truncation preserves monotonicity under `⊆` for functionals of vertex sets. -/
theorem truncFun_mono_set {F : Set V → ℝ≥0∞} (hF : ∀ S T : Set V, S ⊆ T → F S ≤ F T) (n : ℕ) :
    ∀ S T : Set V, S ⊆ T → truncFun n F S ≤ truncFun n F T := by
  intro S T hST
  exact ENNReal.toReal_mono (by simp) (min_le_min (hF S T hST) le_rfl)

/-- Truncation preserves continuity from below. -/
theorem truncFun_cont (𝓔 : ℕ → Finset E) {G : BondGraph V E} {F : Set V → ℝ≥0∞} (x : V) (n : ℕ)
    (hFcont : ∀ (ω : Set E) (s : ℝ≥0∞), s < F (cluster G ω x) →
      ∃ m, s < F (cluster G (ω ∩ (𝓔 m : Set E)) x)) :
    ∀ (ω : Set E) (s : ℝ), s < truncFun n F (cluster G ω x) →
      ∃ m, s < truncFun n F (cluster G (ω ∩ (𝓔 m : Set E)) x) := by
  intro ω s hs
  rcases lt_or_ge s 0 with hs0 | hs0
  · exact ⟨0, lt_of_lt_of_le hs0 (truncFun_nonneg n F _)⟩
  · have h1 : ENNReal.ofReal s < min (F (cluster G ω x)) (n : ℝ≥0∞) := by
      rw [← ofReal_truncFun]
      exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hs0).mpr hs
    have h2 : ENNReal.ofReal s < F (cluster G ω x) := lt_of_lt_of_le h1 (min_le_left _ _)
    obtain ⟨m, hm⟩ := hFcont ω _ h2
    refine ⟨m, ?_⟩
    rw [← ENNReal.ofReal_lt_ofReal_iff_of_nonneg hs0, ofReal_truncFun]
    exact lt_min hm (lt_of_lt_of_le h1 (min_le_right _ _))

/-- Truncation preserves measurability of the cluster functional. -/
theorem measurable_truncFun_cluster [Countable E] {G : BondGraph V E} {F : Set V → ℝ≥0∞} {x : V}
    (hF : Measurable fun ω : Set E => F (cluster G ω x)) (n : ℕ) :
    Measurable fun ω : Set E => truncFun n F (cluster G ω x) :=
  measurable_truncFun hF n

end Truncation

section ENNRealForm
attribute [local instance] Classical.propDecidable

/-- **Lemma I.2.1(i) for `ℝ≥0∞`-valued increasing functionals**, e.g. `F (K_x) = |K_x|^p` with the
convention `|K| = ∞` for infinite clusters.  The hypotheses are the same continuity-from-below and
measurability conditions as in the real-valued case. -/
theorem twoCluster_functional_ennreal [Countable E] (G : BondGraph V E)
    (p : E → unitInterval) (hp : ∀ e, p e < 1) (x y : V) (𝓔 : ℕ → Finset E)
    (h𝓔mono : Monotone 𝓔) (h𝓔 : ∀ e : E, ∃ n, e ∈ 𝓔 n)
    {F H : Set V → ℝ≥0∞}
    (hFmono : ∀ S T : Set V, S ⊆ T → F S ≤ F T)
    (hHmono : ∀ S T : Set V, S ⊆ T → H S ≤ H T)
    (hFcont : ∀ (ω : Set E) (s : ℝ≥0∞), s < F (cluster G ω x) →
      ∃ n, s < F (cluster G (ω ∩ (𝓔 n : Set E)) x))
    (hHcont : ∀ (ω : Set E) (s : ℝ≥0∞), s < H (cluster G ω y) →
      ∃ n, s < H (cluster G (ω ∩ (𝓔 n : Set E)) y))
    (hFmeas : Measurable fun ω : Set E => F (cluster G ω x))
    (hHmeas : Measurable fun ω : Set E => H (cluster G ω y)) :
    ∫⁻ ω, ({ω : Set E | ¬ Conn G ω x y}).indicator (fun _ => (1 : ℝ≥0∞)) ω *
        (F (cluster G ω x) * H (cluster G ω y)) ∂(edgeLaw p)
      ≤ (∫⁻ ω, F (cluster G ω x) ∂(edgeLaw p)) *
          (∫⁻ ω, H (cluster G ω y) ∂(edgeLaw p)) := by
  -- the truncated real-valued inequality, in `ℝ≥0∞` form
  have hstep : ∀ n : ℕ,
      ∫⁻ ω, ({ω : Set E | ¬ Conn G ω x y}).indicator (fun _ => (1 : ℝ≥0∞)) ω *
        (min (F (cluster G ω x)) (n : ℝ≥0∞) * min (H (cluster G ω y)) (n : ℝ≥0∞))
        ∂(edgeLaw p)
      ≤ (∫⁻ ω, min (F (cluster G ω x)) (n : ℝ≥0∞) ∂(edgeLaw p)) *
          (∫⁻ ω, min (H (cluster G ω y)) (n : ℝ≥0∞) ∂(edgeLaw p)) := by
    intro n
    have h := twoCluster_functional_lintegral_le G p hp x y 𝓔 h𝓔mono h𝓔
      (truncFun_nonneg n F) (truncFun_nonneg n H) (truncFun_mono_set hFmono n)
      (truncFun_mono_set hHmono n) (truncFun_cont 𝓔 x n hFcont) (truncFun_cont 𝓔 y n hHcont)
      (measurable_truncFun_cluster hFmeas n) (measurable_truncFun_cluster hHmeas n)
    simpa only [ofReal_truncFun, ENNReal.ofReal_mul (truncFun_nonneg n F _)] using h
  -- monotone convergence on both sides
  have hmono_pt : Monotone fun n : ℕ => (fun ω : Set E =>
      ({ω : Set E | ¬ Conn G ω x y}).indicator (fun _ => (1 : ℝ≥0∞)) ω *
        (min (F (cluster G ω x)) (n : ℝ≥0∞) * min (H (cluster G ω y)) (n : ℝ≥0∞))) := by
    intro m n hmn ω
    refine mul_le_mul' le_rfl (mul_le_mul' ?_ ?_)
    · exact min_le_min le_rfl (by exact_mod_cast hmn)
    · exact min_le_min le_rfl (by exact_mod_cast hmn)
  have hmeasn : ∀ n : ℕ, Measurable fun ω : Set E =>
      ({ω : Set E | ¬ Conn G ω x y}).indicator (fun _ => (1 : ℝ≥0∞)) ω *
        (min (F (cluster G ω x)) (n : ℝ≥0∞) * min (H (cluster G ω y)) (n : ℝ≥0∞)) := fun n =>
    Measurable.mul (measurable_const.indicator (measurableSet_conn G x y).compl)
      ((hFmeas.min measurable_const).mul (hHmeas.min measurable_const))
  have hL : ∫⁻ ω, ({ω : Set E | ¬ Conn G ω x y}).indicator (fun _ => (1 : ℝ≥0∞)) ω *
        (F (cluster G ω x) * H (cluster G ω y)) ∂(edgeLaw p)
      = ⨆ n : ℕ, ∫⁻ ω, ({ω : Set E | ¬ Conn G ω x y}).indicator (fun _ => (1 : ℝ≥0∞)) ω *
        (min (F (cluster G ω x)) (n : ℝ≥0∞) * min (H (cluster G ω y)) (n : ℝ≥0∞))
        ∂(edgeLaw p) := by
    have h1 : ∫⁻ ω, (⨆ n : ℕ, ({ω : Set E | ¬ Conn G ω x y}).indicator (fun _ => (1 : ℝ≥0∞)) ω *
        (min (F (cluster G ω x)) (n : ℝ≥0∞) * min (H (cluster G ω y)) (n : ℝ≥0∞)))
        ∂(edgeLaw p)
        = ⨆ n : ℕ, ∫⁻ ω, ({ω : Set E | ¬ Conn G ω x y}).indicator (fun _ => (1 : ℝ≥0∞)) ω *
        (min (F (cluster G ω x)) (n : ℝ≥0∞) * min (H (cluster G ω y)) (n : ℝ≥0∞))
        ∂(edgeLaw p) := lintegral_iSup hmeasn hmono_pt
    rw [← h1]
    congr 1
    funext ω
    conv_lhs =>
      rw [← iSup_min_natCast (F (cluster G ω x)), ← iSup_min_natCast (H (cluster G ω y)),
        iSup_mul_iSup_eq
          (fun n : ℕ => min (F (cluster G ω x)) (n : ℝ≥0∞))
          (fun n : ℕ => min (H (cluster G ω y)) (n : ℝ≥0∞))
          (fun m n hmn => min_le_min le_rfl (by exact_mod_cast hmn))
          (fun m n hmn => min_le_min le_rfl (by exact_mod_cast hmn))]
    rw [ENNReal.mul_iSup]
  rw [hL]
  calc ⨆ n : ℕ, ∫⁻ ω, ({ω : Set E | ¬ Conn G ω x y}).indicator (fun _ => (1 : ℝ≥0∞)) ω *
        (min (F (cluster G ω x)) (n : ℝ≥0∞) * min (H (cluster G ω y)) (n : ℝ≥0∞))
        ∂(edgeLaw p)
      ≤ ⨆ n : ℕ, (∫⁻ ω, min (F (cluster G ω x)) (n : ℝ≥0∞) ∂(edgeLaw p)) *
          (∫⁻ ω, min (H (cluster G ω y)) (n : ℝ≥0∞) ∂(edgeLaw p)) := iSup_mono hstep
    _ = (⨆ n : ℕ, ∫⁻ ω, min (F (cluster G ω x)) (n : ℝ≥0∞) ∂(edgeLaw p)) *
          (⨆ n : ℕ, ∫⁻ ω, min (H (cluster G ω y)) (n : ℝ≥0∞) ∂(edgeLaw p)) :=
        (iSup_mul_iSup_eq
          (fun n : ℕ => ∫⁻ ω, min (F (cluster G ω x)) (n : ℝ≥0∞) ∂(edgeLaw p))
          (fun n : ℕ => ∫⁻ ω, min (H (cluster G ω y)) (n : ℝ≥0∞) ∂(edgeLaw p))
          (fun m n hmn => lintegral_mono fun ω => min_le_min le_rfl (by exact_mod_cast hmn))
          (fun m n hmn => lintegral_mono fun ω => min_le_min le_rfl (by exact_mod_cast hmn))).symm
    _ = (∫⁻ ω, F (cluster G ω x) ∂(edgeLaw p)) *
          (∫⁻ ω, H (cluster G ω y) ∂(edgeLaw p)) := by
        rw [lintegral_eq_iSup_truncFun hFmeas, lintegral_eq_iSup_truncFun hHmeas]
        simp only [ofReal_truncFun]

end ENNRealForm

end Percolation

end PercLib.CriticalLRP
