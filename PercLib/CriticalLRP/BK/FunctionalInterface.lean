/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
# Lemma I.2.1 without an explicit exhaustion parameter

The main theorems of `LemmaI21Final.lean` / `LemmaI21ENNReal.lean` / `LemmaI21Card.lean` take an
arbitrary finite exhaustion `𝓔 : ℕ → Finset E` of the edge set.  For countable edge sets one can
use the canonical exhaustion `edgeExhaustion` of `BK/Association.lean`; this file provides the
resulting statements, whose interface is just `[Encodable E]` (in particular `[Countable E]`).
-/
module

public import PercLib.CriticalLRP.BK.GraphConsequences
public import PercLib.CriticalLRP.BK.FunctionalFromBelow
public import PercLib.CriticalLRP.BK.FunctionalENNReal
public import PercLib.CriticalLRP.BK.ClusterCardinal

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

section Interface
attribute [local instance] Classical.propDecidable
variable [Encodable E]

theorem edgeExhaustion_mono' : Monotone (edgeExhaustion (E := E)) := edgeExhaustion_mono

theorem edgeExhaustion_cover (e : E) : ∃ n, e ∈ edgeExhaustion (E := E) n := by
  obtain ⟨n, hn⟩ := subset_edgeExhaustion ({e} : Finset E)
  exact ⟨n, hn (Finset.mem_singleton_self e)⟩

/-- **Lemma I.2.1(i)**, real-valued form, with the canonical exhaustion. -/
theorem twoCluster_functional_lintegral_le' (G : BondGraph V E) (p : E → unitInterval)
    (hp : ∀ e, p e < 1) (x y : V) {F H : Set V → ℝ}
    (hF0 : ∀ S, 0 ≤ F S) (hH0 : ∀ S, 0 ≤ H S)
    (hFmono : ∀ S T : Set V, S ⊆ T → F S ≤ F T)
    (hHmono : ∀ S T : Set V, S ⊆ T → H S ≤ H T)
    (hFcont : ∀ (ω : Set E) (s : ℝ), s < F (cluster G ω x) →
      ∃ n, s < F (cluster G (ω ∩ (edgeExhaustion (E := E) n : Set E)) x))
    (hHcont : ∀ (ω : Set E) (s : ℝ), s < H (cluster G ω y) →
      ∃ n, s < H (cluster G (ω ∩ (edgeExhaustion (E := E) n : Set E)) y))
    (hFmeas : Measurable fun ω => F (cluster G ω x))
    (hHmeas : Measurable fun ω => H (cluster G ω y)) :
    ∫⁻ ω, ({ω : Set E | ¬ Conn G ω x y}).indicator (fun _ => (1 : ℝ≥0∞)) ω *
        ENNReal.ofReal (F (cluster G ω x) * H (cluster G ω y)) ∂(edgeLaw p)
      ≤ (∫⁻ ω, ENNReal.ofReal (F (cluster G ω x)) ∂(edgeLaw p)) *
          (∫⁻ ω, ENNReal.ofReal (H (cluster G ω y)) ∂(edgeLaw p)) :=
  twoCluster_functional_lintegral_le G p hp x y (edgeExhaustion (E := E)) edgeExhaustion_mono
    edgeExhaustion_cover hF0 hH0 hFmono hHmono hFcont hHcont hFmeas hHmeas

/-- **Lemma I.2.1(i)** for the extended cluster cardinality, with the canonical exhaustion. -/
theorem twoCluster_cardFun_lintegral' (G : BondGraph V E) (p : E → unitInterval)
    (hp : ∀ e, p e < 1) (x y : V) :
    ∫⁻ ω, ({ω : Set E | ¬ Conn G ω x y}).indicator (fun _ => (1 : ℝ≥0∞)) ω *
        (cardFun (cluster G ω x) * cardFun (cluster G ω y)) ∂(edgeLaw p)
      ≤ (∫⁻ ω, cardFun (cluster G ω x) ∂(edgeLaw p)) *
          (∫⁻ ω, cardFun (cluster G ω y) ∂(edgeLaw p)) :=
  twoCluster_cardFun_lintegral G p hp x y (edgeExhaustion (E := E)) edgeExhaustion_mono
    edgeExhaustion_cover

end Interface

end Percolation

end PercLib.CriticalLRP
