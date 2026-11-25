/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
# The maximum cluster size `|K_max(W)|` in the canonical model

For a finite window `W` the paper defines `|K_max(W)| = max{|K_x ∩ W| : x ∈ V}`, the size of the
largest block in the partition of `W` by clusters.  Since every cluster meeting `W` contains a
vertex of `W`, this is `max{|K_w ∩ W| : w ∈ W}`, which we take as the definition for a finite
`W`.  We prove it is measurable and integer-valued, so that the paper's edian `M_β(W)` (defined
from its tail probabilities) is a well-defined natural number as soon as the edian exists.
-/
module

public import PercLib.CriticalLRP.Tightness.Canonical

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

set_option autoImplicit true

@[expose] public section

open MeasureTheory Set Filter Finset
open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP

namespace Percolation

universe u

variable {V : Type u} [Countable V]

/-- The sup of a finite family of integer-valued (or `⊤`) extended reals is integer-valued
(or `⊤`). -/
lemma finset_sup_integer {ι : Type*} (s : Finset ι) (f : ι → ℝ≥0∞)
    (h : ∀ i ∈ s, f i = ⊤ ∨ ∃ n : ℕ, f i = (n : ℝ≥0∞)) :
    s.sup f = ⊤ ∨ ∃ n : ℕ, s.sup f = (n : ℝ≥0∞) := by
  classical
  induction s using Finset.induction with
  | empty =>
    right
    exact ⟨0, by simp⟩
  | insert a s ha ih =>
    have ha' := h a (Finset.mem_insert_self a s)
    have hs' : ∀ i ∈ s, f i = ⊤ ∨ ∃ n : ℕ, f i = (n : ℝ≥0∞) :=
      fun i hi => h i (Finset.mem_insert_of_mem hi)
    have ih' := ih hs'
    rw [Finset.sup_insert]
    rcases ha' with h1 | ⟨m, h1⟩ <;> rcases ih' with h2 | ⟨n, h2⟩
    · left; rw [h1, h2]; simp
    · left; rw [h1, h2]; simp
    · left; rw [h1, h2]; simp
    · right
      refine ⟨max m n, ?_⟩
      rw [h1, h2]
      push_cast
      by_cases hmn : m ≤ n
      · rw [max_eq_right hmn, max_eq_right (by exact_mod_cast hmn)]
      · rw [max_eq_left (Nat.le_of_not_le hmn),
          max_eq_left (by exact_mod_cast Nat.le_of_not_le hmn)]

/-- `|K_max(W)|`, the largest `|K_w ∩ W|` over the window, for a finite window `W`. -/
noncomputable def clusterMaxVol (ω : Config V) (W : Finset V) : ℝ≥0∞ :=
  W.sup (fun w => clusterVolIn ω w (W : Set V))

lemma measurable_clusterMaxVol (W : Finset V) :
    Measurable fun ω : Config V => clusterMaxVol ω W := by
  classical
  have : ∀ (Λ : Set V) (W : Finset V),
      Measurable fun ω : Config V => W.sup (fun w => clusterVolIn ω w Λ) := by
    intro Λ W
    induction W using Finset.induction with
    | empty => simp
    | insert a s ha ih =>
      have hstep : (fun ω : Config V => (insert a s).sup (fun w => clusterVolIn ω w Λ))
          = fun ω => clusterVolIn ω a Λ ⊔ s.sup (fun w => clusterVolIn ω w Λ) := by
        funext ω
        rw [Finset.sup_insert]
      rw [hstep]
      exact (measurable_clusterVolIn a Λ).sup ih
  exact this (W : Set V) W

lemma clusterMaxVol_integer (ω : Config V) (W : Finset V) :
    clusterMaxVol ω W = ⊤ ∨ ∃ n : ℕ, clusterMaxVol ω W = (n : ℝ≥0∞) :=
  finset_sup_integer W _ (fun w _ => clusterVolIn_integer ω w _)

lemma clusterVolIn_le_clusterMaxVol (ω : Config V) {W : Finset V} {w : V} (hw : w ∈ W) :
    clusterVolIn ω w (W : Set V) ≤ clusterMaxVol ω W :=
  Finset.le_sup (f := fun w => clusterVolIn ω w (W : Set V)) hw

/-- `|K_v ∩ W| ≤ |K_max(W)|`: the hypothesis of `tail_single_of_max` holds definitionally. -/
lemma clusterVolIn_le_clusterMaxVol' (v : V) (W : Finset V) (hv : v ∈ W) :
    ∀ ω : Config V, clusterVolIn ω v (W : Set V) ≤ clusterMaxVol ω W :=
  fun ω => clusterVolIn_le_clusterMaxVol ω hv

/-- The paper's edian `M_β(W) = min{n : P(|K_max(W)| ≥ n) ≤ e^{-1}}` of the maximum cluster
size, for a finite window `W`, given the explicit existence hypothesis (a.e. finiteness). -/
noncomputable def edianMaxVol (μ : Measure (Config V)) (W : Finset V)
    (hex : ∃ n : ℕ, μ {ω | (n : ℝ≥0∞) ≤ clusterMaxVol ω W} ≤ ENNReal.ofReal (Real.exp (-1))) :
    ℕ :=
  edianOf μ (fun ω => clusterMaxVol ω W) hex

lemma edianMaxVol_spec {μ : Measure (Config V)} (W : Finset V)
    (hex : ∃ n : ℕ, μ {ω | (n : ℝ≥0∞) ≤ clusterMaxVol ω W} ≤ ENNReal.ofReal (Real.exp (-1))) :
    μ {ω | (edianMaxVol μ W hex : ℝ≥0∞) ≤ clusterMaxVol ω W} ≤
      ENNReal.ofReal (Real.exp (-1)) :=
  edianOf_spec

lemma one_le_edianMaxVol {μ : Measure (Config V)} [IsProbabilityMeasure μ] (W : Finset V)
    (hex : ∃ n : ℕ, μ {ω | (n : ℝ≥0∞) ≤ clusterMaxVol ω W} ≤ ENNReal.ofReal (Real.exp (-1))) :
    1 ≤ edianMaxVol μ W hex :=
  one_le_edianOf

/-- **Corollary I.2.5 at the paper's scale `M_β(W)`**: for `v ∈ W` finite, the truncated cluster
cardinality `|K_v ∩ W|` satisfies `E|K_v∩W|^{p+q} ⪯_{p,q} M_β(W)^q E|K_v∩W|^p`, given the
universal-tightness inputs of Theorem I.2.3 at the scale of the maximum cluster size. -/
theorem corollary_I_2_5_at_edian {μ : Measure (Config V)} (v : V) (W : Finset V) (hv : v ∈ W)
    {M : ℕ}
    (h : UniversalTightnessI23 μ (fun ω => clusterMaxVol ω W)
      (fun ω => clusterVolIn ω v (W : Set V)) M)
    (p q : ℕ) (hp : 1 ≤ p) :
    ∫⁻ ω, clusterVolIn ω v (W : Set V) ^ (p + q) ∂μ
      ≤ ENNReal.ofReal (Tightness.momentConst p q) * ENNReal.ofReal ((M : ℝ) ^ q) *
        ∫⁻ ω, clusterVolIn ω v (W : Set V) ^ p ∂μ :=
  corollary_I_2_5_of_I_2_3 h (measurable_clusterVolIn v _)
    (fun ω => clusterVolIn_integer ω v _) p q hp

end Percolation

end PercLib.CriticalLRP
