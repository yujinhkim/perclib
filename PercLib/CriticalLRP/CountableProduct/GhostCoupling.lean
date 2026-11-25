/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
# The restoration/exploration estimate (I.3.5) for the ghost field

Source: Tom Hutchcroft, *Critical long-range percolation I: High effective dimension*,
arXiv:2508.18807v1, pp. 29-31.  The paper asserts, for a cut-off law `P_{β,r}` dominated by the
full law `P_β` and an independent ghost field `G` of intensity `h`,

  `P_{β,r,h}(0 ↔ G) ≤ P_{β,∞,h}(0 ↔ G) ≤ P_{β,r,h}(0 ↔ G)
      + C r^{-α} E_{β,r}[|K| e^{-h|K|}] · P_{β,r,h}(0 ↔ G)`     (I.3.5)

with the justification "there must exist an edge in the boundary of the cluster in the cut-off
model that becomes open in the non-cut-off model and whose other endpoint is connected to the
ghost by a path that is disjoint from the cluster of the origin in the cut-off model.  Since
exploring the cluster of the origin in the cut-off model reveals only negative information about
connectivity to the ghost off of this cluster, we have by these considerations and a union bound
that ...".

The purpose of this file is to make that argument honest and to say exactly where a
probabilistic input remains.

## Structure of the argument formalised here

1. **Deterministic exit lemma** (`exists_exit_edge`, `exists_fresh_exit`,
   `exists_fresh_exit_of_ghost`).  If `ω ⊆ θ` and the ghost hits the `θ`-cluster of `o` but not
   the `ω`-cluster, then there are `x` in `K := cluster ω o`, `y ∉ K` such that `s(x,y) ∈ θ \ ω`
   and a `θ`-open walk from `y` to a marked vertex *all of whose vertices lie outside `K`*
   (hence all of whose edges avoid the edge set `edgeTouch K` that touches `K`).  The last exit
   along a `θ`-open walk is what produces the disjointness; no independence is assumed.

2. **Monotone restoration coupling** (`shiftProb`, `union`, `unionMeasure_eq_edgeMeasure`).
   For `ρ ≤ π` put `q_e = (π_e - ρ_e)/(1 - ρ_e)` (the probability that an edge which is closed
   under `P_ρ` is open under `P_π`).  If `ω ~ P_ρ` and `η ~ P_q` are independent then
   `ω ∪ η ~ P_π`.  Consequently `ghostHits π h o` is the probability that the ghost hits the
   `(ω ∪ η)`-cluster of `o`, and — because `ω ⊆ ω ∪ η` — the difference
   `ghostHits π h o - ghostHits ρ h o` is bounded by the probability of the exit event of item 1
   in this coupling.

3. **The one remaining probabilistic input** (`OffClusterBound`): after conditioning on
   `K = cluster ω o` and on the exit edge, the probability of the off-cluster ghost hit is at
   most one *global* ghost-hit probability `G`.  This is where the paper's "exploring reveals
   only negative information" is used: the cluster `K` is determined by the states of the edges
   touching `K` (`selfDetermined_touchSet`), those edges are exactly the ones the off-cluster
   walk avoids, and the marks on `K` are the ones the weight `e^{-h|K|}` accounts for.  The
   precise statement is isolated as a hypothesis and is *not* the conclusion: it is a
   vertex-level bound on an exploration probability.

4. **Assembly** (`ghostHits_le_of_offClusterBound`): the union bound over exit edges, the
   degree/tail cost `D = sup_x ∑_y q_{xy}` and the global ghost-hit probability `G` give
          `ghostHits π h o ≤ ghostHits ρ h o + D · E_ρ[|K| e^{-h|K|}] · G`.
   With `D ≤ C r^{-α}` and `G ≤ ghostHits ρ h o` this is exactly (I.3.5).
-/
module

public import PercLib.CriticalLRP.CountableProduct.GhostField
public import PercLib.CriticalLRP.CountableProduct.RestorationCompl
public import PercLib.CriticalLRP.BK.TwoCopy

set_option autoImplicit true

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1200000

@[expose] public section

open MeasureTheory Measure ProbabilityTheory unitInterval
open scoped ENNReal NNReal

namespace PercLib.CriticalLRP

variable {V : Type*} [Countable V]

/-! ## Edges meeting a vertex set -/

/-- The set of unordered pairs with at least one endpoint in `K`.  This is the edge set that an
exploration of the cluster `K` reveals. -/
def edgeTouch (K : Set V) : Set (Sym2 V) := {e | ∃ v ∈ K, v ∈ e}

theorem mem_edgeTouch {K : Set V} {e : Sym2 V} : e ∈ edgeTouch K ↔ ∃ v ∈ K, v ∈ e :=
  Iff.rfl

theorem edgeTouch_mono {K K' : Set V} (h : K ⊆ K') : edgeTouch K ⊆ edgeTouch K' := by
  rintro e ⟨v, hv, hve⟩
  exact ⟨v, h hv, hve⟩

theorem not_mem_edgeTouch_iff {K : Set V} {e : Sym2 V} :
    e ∉ edgeTouch K ↔ ∀ v ∈ e, v ∉ K := by
  rw [mem_edgeTouch]
  constructor
  · intro h v hv hK
    exact h ⟨v, hK, hv⟩
  · rintro h ⟨v, hK, hv⟩
    exact h v hv hK

/-! ## Walks that avoid a vertex set -/

/-- A walk all of whose vertices lie outside `K`. -/
def WalkAvoids {G : SimpleGraph V} {a b : V} (p : G.Walk a b) (K : Set V) : Prop :=
  ∀ v, v ∈ p.support → v ∉ K

theorem walkAvoids_nil {G : SimpleGraph V} {a : V} {K : Set V} (ha : a ∉ K) :
    WalkAvoids (SimpleGraph.Walk.nil : G.Walk a a) K := by
  intro v hv
  rw [SimpleGraph.Walk.support_nil, List.mem_singleton] at hv
  exact hv ▸ ha

theorem walkAvoids_cons {G : SimpleGraph V} {a b c : V} {K : Set V}
    (h : G.Adj a b) {p : G.Walk b c} (hp : WalkAvoids p K) (ha : a ∉ K) :
    WalkAvoids (SimpleGraph.Walk.cons h p) K := by
  intro v hv
  rw [SimpleGraph.Walk.support_cons] at hv
  rcases List.mem_cons.mp hv with rfl | hv'
  · exact ha
  · exact hp v hv'

theorem WalkAvoids.start_notMem {G : SimpleGraph V} {a b : V} {K : Set V} {p : G.Walk a b}
    (h : WalkAvoids p K) : a ∉ K :=
  h a (SimpleGraph.Walk.start_mem_support p)

theorem WalkAvoids.end_notMem {G : SimpleGraph V} {a b : V} {K : Set V} {p : G.Walk a b}
    (h : WalkAvoids p K) : b ∉ K :=
  h b (SimpleGraph.Walk.end_mem_support p)

/-- Every edge of a walk avoiding `K` lies outside `edgeTouch K`.  This is the key locality
statement: the walk only sees edge coordinates outside the edge set revealed by exploring `K`. -/
theorem WalkAvoids.not_mem_edgeTouch {G : SimpleGraph V} {a b : V} {K : Set V} {p : G.Walk a b}
    (h : WalkAvoids p K) : ∀ e ∈ p.edges, e ∉ edgeTouch K := by
  intro e he
  rw [not_mem_edgeTouch_iff]
  intro v hv
  exact h v (p.mem_support_of_mem_edges he hv)

/-! ## The deterministic exit lemma -/

/-- **Last exit.**  Along a walk from `a ∈ K` to a vertex `b ∉ K`, the walk either stays outside
`K` altogether, or there is an edge `{x,y}` with `x ∈ K`, `y ∉ K` and a suffix walk from `y` to
`b` which avoids `K` entirely.  This is the deterministic heart of the decomposition; it needs no
probability. -/
theorem exists_exit_edge {G : SimpleGraph V} {K : Set V} {a b : V} (p : G.Walk a b) (hb : b ∉ K) :
    WalkAvoids p K ∨
      ∃ x ∈ K, ∃ y ∉ K, G.Adj x y ∧ ∃ q : G.Walk y b, WalkAvoids q K := by
  induction p with
  | nil => exact Or.inl (walkAvoids_nil hb)
  | @cons u v w h p' ih =>
      rcases ih hb with hp' | ⟨x, hxK, y, hyK, hadj, q, hq⟩
      · have hv : v ∉ K := hp'.start_notMem
        by_cases hu : u ∈ K
        · exact Or.inr ⟨u, hu, v, hv, h, p', hp'⟩
        · exact Or.inl (walkAvoids_cons h hp' hu)
      · exact Or.inr ⟨x, hxK, y, hyK, hadj, q, hq⟩

/-- **The exit decomposition of a configuration pair** `ω ⊆ θ`.  If `v` is connected to `o` in
`θ` but not in `ω`, then some edge `s(x,y)` with `x` in the `ω`-cluster `K` of `o` and `y`
outside `K` is open in `θ` but closed in `ω`, and `y` is `θ`-connected to `v` by a walk that
avoids `K`. -/
theorem exists_fresh_exit {ω θ : Config V} (hsub : ∀ e, e ∈ ω → e ∈ θ) {o : V} {v : V}
    (hv : v ∈ cluster θ o) (hvK : v ∉ cluster ω o) :
    ∃ x ∈ cluster ω o, ∃ y ∉ cluster ω o, s(x, y) ∈ θ ∧ s(x, y) ∉ ω ∧
      ∃ q : (openGraph θ).Walk y v, WalkAvoids q (cluster ω o) := by
  obtain ⟨p, hp⟩ := pathConnects_iff.mpr (mem_cluster_iff.mp hv)
  obtain ⟨p', hp'⟩ := exists_walk_openGraph_of_walk_top p hp
  have hoK : o ∈ cluster ω o := cluster_mem_self ω o
  rcases exists_exit_edge p' hvK with hav | ⟨x, hxK, y, hyK, hadj, q, hq⟩
  · exact absurd hoK hav.start_notMem
  · refine ⟨x, hxK, y, hyK, (openGraph_adj.mp hadj).2, ?_, q, hq⟩
    intro hmem
    have hxy : x ≠ y := (openGraph_adj.mp hadj).1
    have hcx : Connects ω o x := mem_cluster_iff.mp hxK
    have hadjω : (openGraph ω).Adj x y := openGraph_adj.mpr ⟨hxy, hmem⟩
    have hxy' : Connects ω x y := hadjω.reachable
    exact hyK (mem_cluster_iff.mpr (connects_trans hcx hxy'))

/-- **The exit decomposition at the level of the ghost field.**  If the ghost hits the `θ`-cluster
of `o` but not the `ω`-cluster, then the exit edge of `exists_fresh_exit` ends at a vertex `y`
from which the ghost is reached by a `θ`-walk avoiding `K = cluster ω o`. -/
theorem exists_fresh_exit_of_ghost {ω θ : Config V} (hsub : ∀ e, e ∈ ω → e ∈ θ) {o : V}
    {G : V → Prop} (hG : GhostConnected o (θ, G)) (hnG : ¬ GhostConnected o (ω, G)) :
    ∃ x ∈ cluster ω o, ∃ y ∉ cluster ω o, s(x, y) ∈ θ ∧ s(x, y) ∉ ω ∧
      ∃ v, G v ∧ ∃ q : (openGraph θ).Walk y v, WalkAvoids q (cluster ω o) := by
  obtain ⟨v, hv, hGv⟩ := hG
  have hvK : v ∉ cluster ω o := fun hc => hnG ⟨v, hc, hGv⟩
  obtain ⟨x, hxK, y, hyK, hfresh, hnot, q, hq⟩ :=
    exists_fresh_exit hsub hv hvK
  exact ⟨x, hxK, y, hyK, hfresh, hnot, v, hGv, q, hq⟩

/-! ## The monotone shift coupling `P_ρ ⊗ P_q` with union `P_π`

For `ρ ≤ π` the probability that an edge which is closed under `P_ρ` is open under `P_π` is
`q_e = (π_e - ρ_e)/(1 - ρ_e)`.  If `ω ~ P_ρ` and `η ~ P_q` are independent then `ω ∪ η ~ P_π`.
This is the coupling used in the paper's (I.3.5): the fresh edges of `η` are exactly the edges
that "flip from closed to open when passing from `P_{β,r}` to `P_β`", and — because `η` is a
separate independent configuration — they are independent of the cut-off cluster `K_ρ`. -/

/-- The probability that an edge closed under the `ρ`-law is open under the `π`-law. -/
noncomputable def shiftProb (π ρ : Sym2 V → unitInterval) (e : Sym2 V) : unitInterval :=
  ⟨min 1 (max 0 (((π e : ℝ) - (ρ e : ℝ)) / (1 - (ρ e : ℝ)))), by
    refine ⟨le_min zero_le_one (le_max_left 0 _), min_le_left 1 _⟩⟩

@[simp] theorem shiftProb_val (π ρ : Sym2 V → unitInterval) (e : Sym2 V) :
    (shiftProb π ρ e : ℝ) =
      min 1 (max 0 (((π e : ℝ) - (ρ e : ℝ)) / (1 - (ρ e : ℝ)))) := rfl

/-- The defining identity of the shift probability: `ρ + (1 - ρ) q = π`. -/
theorem shiftProb_spec {π ρ : Sym2 V → unitInterval} {e : Sym2 V} (h : ρ e ≤ π e) :
    (ρ e : ℝ) + (1 - (ρ e : ℝ)) * (shiftProb π ρ e : ℝ) = (π e : ℝ) := by
  have hρ1 : (ρ e : ℝ) ≤ 1 := (ρ e).2.2
  have hπ1 : (π e : ℝ) ≤ 1 := (π e).2.2
  have hρπ : (ρ e : ℝ) ≤ (π e : ℝ) := by exact_mod_cast h
  rw [shiftProb_val]
  rcases lt_or_eq_of_le hρ1 with hlt | heq
  · have hpos : 0 < 1 - (ρ e : ℝ) := by linarith
    have hx0 : 0 ≤ ((π e : ℝ) - (ρ e : ℝ)) / (1 - (ρ e : ℝ)) :=
      div_nonneg (by linarith) hpos.le
    have hx1 : ((π e : ℝ) - (ρ e : ℝ)) / (1 - (ρ e : ℝ)) ≤ 1 := by
      rw [div_le_one hpos]; linarith
    rw [max_eq_right hx0, min_eq_right hx1, mul_comm, div_mul_cancel₀ _ hpos.ne']
    ring
  · have hπeq : (π e : ℝ) = 1 := le_antisymm hπ1 (by linarith)
    rw [hπeq, ← heq]
    norm_num

/-- The mass of `{False}` for a Bernoulli law on `Prop`, in `ofReal` form. -/
theorem ber_false (p : unitInterval) :
    bernoulliMeasure (True : Prop) (False : Prop) p {False} = ENNReal.ofReal (1 - (p : ℝ)) := by
  rw [bernoulliMeasure_apply_of_notMem_of_mem p (by measurability) (by simp) (by simp),
    coe_toNNReal_symm]

/-- The mass of `{True}` for a Bernoulli law on `Prop`, in `ofReal` form. -/
theorem ber_true (p : unitInterval) :
    bernoulliMeasure (True : Prop) (False : Prop) p {True} = ENNReal.ofReal (p : ℝ) := by
  rw [bernoulliMeasure_apply_of_mem_of_notMem p (by measurability) (by simp) (by simp),
    ENNReal.ofReal, ENNReal.coe_inj, Real.toNNReal_of_nonneg p.2.1]
  exact Subtype.ext rfl

/-- Two probability measures on `Prop` agreeing on `{False}` are equal. -/
theorem measure_prop_ext_false {ν₁ ν₂ : Measure Prop} [IsProbabilityMeasure ν₁]
    [IsProbabilityMeasure ν₂] (h : ν₁ {False} = ν₂ {False}) : ν₁ = ν₂ := by
  classical
  have hF : ∀ (ν : Measure Prop) [IsProbabilityMeasure ν], ν {True} = 1 - ν {False} := by
    intro ν _
    have hc : (({False} : Set Prop))ᶜ = {True} := by ext x; by_cases hx : x <;> simp [hx]
    have h' := measure_compl (μ := ν) (s := ({False} : Set Prop)) (measurableSet_singleton False)
      (measure_ne_top _ _)
    rw [hc, MeasureTheory.measure_univ] at h'
    exact h'
  ext s _
  rcases prop_set_cases (s := s) with h' | h' | h' | h'
  · rw [h']; simp
  · rw [h', hF ν₁, hF ν₂, h]
  · rw [h']; exact h
  · rw [h']; simp

/-- **The per-edge computation of the shift coupling.**  The `or` of an edge which is open with
probability `ρ_e` and, independently, with probability `q_e` is open with probability `π_e`. -/
theorem prod_ber_or {π ρ : Sym2 V → unitInterval} {e : Sym2 V} (h : ρ e ≤ π e) :
    (((bernoulliMeasure (True : Prop) (False : Prop) (ρ e)).prod
        (bernoulliMeasure (True : Prop) (False : Prop) (shiftProb π ρ e)))).map
      (fun x : Prop × Prop => x.1 ∨ x.2) = bernoulliMeasure (True : Prop) (False : Prop) (π e) := by
  classical
  have hsub : (1 - (ρ e : ℝ)) * (1 - (shiftProb π ρ e : ℝ)) = 1 - (π e : ℝ) := by
    have := shiftProb_spec h
    nlinarith
  refine measure_prop_ext_false ?_
  rw [Measure.map_apply (by measurability) (measurableSet_singleton False)]
  have hpre : (fun x : Prop × Prop => x.1 ∨ x.2) ⁻¹' ({False} : Set Prop)
      = ({False} : Set Prop) ×ˢ ({False} : Set Prop) := by
    ext x
    constructor
    · intro hx
      simp only [Set.mem_preimage, Set.mem_singleton_iff] at hx
      have hx' : ¬(x.1 ∨ x.2) := by rw [hx]; simp
      refine Set.mem_prod.mpr ⟨?_, ?_⟩ <;> simp only [Set.mem_singleton_iff]
      · exact propext ⟨fun h => absurd (Or.inl h) hx', fun h => h.elim⟩
      · exact propext ⟨fun h => absurd (Or.inr h) hx', fun h => h.elim⟩
    · intro hx
      simp only [Set.mem_prod, Set.mem_singleton_iff] at hx
      obtain ⟨h1, h2⟩ := hx
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      rw [h1, h2]; simp
  rw [hpre, Measure.prod_prod, ber_false, ber_false, ber_false,
    ← ENNReal.ofReal_mul (by linarith [(ρ e).2.2]), hsub]


/-! ## Finite-coordinate factorisation of the edge law -/

/-- The law of a single edge coordinate under the independent edge law. -/
theorem lintegral_coord (ρ : Sym2 V → unitInterval) (a : Sym2 V) (f : Prop → ℝ≥0∞) :
    ∫⁻ c, f c ∂(bernoulliMeasure (True : Prop) (False : Prop) (ρ a))
      = ∫⁻ ω : Config V, f (ω a) ∂(edgeMeasure ρ) := by
  have hmap : (edgeMeasure ρ).map (fun ω : Config V => ω a)
      = bernoulliMeasure (True : Prop) (False : Prop) (ρ a) := by
    rw [edgeMeasure_eq_infinitePi ρ]
    exact Measure.infinitePi_map_eval
      (fun e : Sym2 V => bernoulliMeasure (True : Prop) (False : Prop) (ρ e)) a
  rw [← hmap]
  exact lintegral_map (measurable_iff_comap_le.mpr le_top) (measurable_pi_apply a)

/-- A function of a single edge coordinate factors out against any function of the other
coordinates. -/
theorem lintegral_coord_mul (ρ : Sym2 V → unitInterval) (a : Sym2 V)
    {f : Prop → ℝ≥0∞} {g : Config V → ℝ≥0∞} (hg : Measurable g)
    (hinv : ∀ (η ω : Config V), g (forceOn ({a} : Set (Sym2 V)) η ω) = g ω) :
    ∫⁻ ω, f (ω a) * g ω ∂(edgeMeasure ρ)
      = (∫⁻ c, f c ∂(bernoulliMeasure (True : Prop) (False : Prop) (ρ a)))
          * ∫⁻ ω, g ω ∂(edgeMeasure ρ) := by
  classical
  have hfany : ∀ {h : Prop → ℝ≥0∞}, Measurable h := fun {_} => measurable_iff_comap_le.mpr le_top
  have hf : Measurable fun ω : Config V => f (ω a) := hfany.comp (measurable_pi_apply a)
  have hcoord : Measurable[coordinateSigma a] (fun ω : Config V => f (ω a)) := by
    have h1 : @Measurable (Config V) Prop (coordinateSigma a) inferInstance (fun ω => ω a) :=
      measurable_iff_comap_le.mpr le_rfl
    exact hfany.comp h1
  have hf' : Measurable[blockSigma ({a} : Set (Sym2 V))] (fun ω : Config V => f (ω a)) :=
    hcoord.mono (coordinateSigma_le_block a) le_rfl
  have hg' : Measurable[blockSigma ({a} : Set (Sym2 V))ᶜ] g := by
    have h := hg.comp (measurable_forceOn_block ({a} : Set (Sym2 V)) (∅ : Config V))
    convert h using 1
    funext ω
    exact (hinv ∅ ω).symm
  rw [lintegral_mul_of_indep_blocks ρ ({a} : Set (Sym2 V)) hf' hg',
    lintegral_coord ρ a f]

/-- **Finite-coordinate factorisation**: the integral of a product of single-coordinate
functions against the independent edge law is the product of the single-coordinate integrals. -/
theorem lintegral_prod_coord (ρ : Sym2 V → unitInterval) (B : Finset (Sym2 V))
    (φ : Sym2 V → Prop → ℝ≥0∞) :
    ∫⁻ ω, ∏ e ∈ B, φ e (ω e) ∂(edgeMeasure ρ)
      = ∏ e ∈ B, ∫⁻ b, φ e b ∂(bernoulliMeasure (True : Prop) (False : Prop) (ρ e)) := by
  classical
  induction B using Finset.induction with
  | empty => simp
  | @insert a B ha ih =>
    have hany : ∀ {h : Prop → ℝ≥0∞}, Measurable h := fun {_} => measurable_iff_comap_le.mpr le_top
    have hmeas : Measurable fun ω : Config V => ∏ e ∈ B, φ e (ω e) :=
      Finset.measurable_prod B fun e _ => hany.comp (measurable_pi_apply e)
    have hinv : ∀ (η ω : Config V),
        (∏ e ∈ B, φ e ((forceOn ({a} : Set (Sym2 V)) η ω) e)) = ∏ e ∈ B, φ e (ω e) := by
      intro η ω
      refine Finset.prod_congr rfl fun e he => ?_
      have hne : e ≠ a := fun hh => ha (hh ▸ he)
      rw [forceOn_apply_of_notMem (S := ({a} : Set (Sym2 V))) (by simpa using hne)]
    have hsplit : ∀ ω : Config V, ∏ e ∈ insert a B, φ e (ω e)
        = φ a (ω a) * ∏ e ∈ B, φ e (ω e) := fun ω => Finset.prod_insert ha
    simp_rw [hsplit]
    rw [lintegral_coord_mul ρ a hmeas hinv, ih, Finset.prod_insert ha]

/-! ## The union law -/

/-- The `or` of two `Prop`-valued coordinates is measurable. -/
theorem measurable_or_prop : Measurable fun x : Prop × Prop => x.1 ∨ x.2 := by measurability

theorem measurableSet_prop_prod (s : Set (Prop × Prop)) : MeasurableSet s :=
  MeasurableSet.of_discrete

/-- The union of two configurations, as an explicit function (so that its coordinates are
definitionally the disjunctions of the coordinates). -/
def unionConf {V : Type*} (p : Config V × Config V) : Config V := fun e => e ∈ p.1 ∨ e ∈ p.2

theorem unionConf_apply {V : Type*} (p : Config V × Config V) (e : Sym2 V) :
    unionConf p e = (e ∈ p.1 ∨ e ∈ p.2) := rfl

theorem unionConf_eq_union {V : Type*} (p : Config V × Config V) : unionConf p = p.1 ∪ p.2 := by
  ext e; exact Set.mem_union _ _ _

/-- Measurability of the union of two configurations. -/
theorem measurable_unionConf {V : Type*} [Countable V] : Measurable (unionConf (V := V)) := by
  refine measurable_pi_iff.mpr fun e => ?_
  refine measurable_to_prop ?_
  have hset : (fun p : Config V × Config V => unionConf p e) ⁻¹' ({True} : Set Prop)
      = {p : Config V × Config V | e ∈ p.1} ∪ {p : Config V × Config V | e ∈ p.2} := by
    ext p
    simp [unionConf_apply, Set.mem_union]
  rw [hset]
  exact ((measurableSet_mem e).preimage measurable_fst).union
    ((measurableSet_mem e).preimage measurable_snd)

/-- The union of two configurations lies in the cylinder `edgeCyl B t` iff at every `e ∈ B` one of
the two coordinates lies in `t e`. -/
theorem unionConf_mem_edgeCyl_iff (B : Finset (Sym2 V)) (t : Sym2 V → Set Prop)
    (p : Config V × Config V) :
    unionConf p ∈ edgeCyl B t ↔ ∀ e ∈ B, (e ∈ p.1 ∨ e ∈ p.2) ∈ t e :=
  Iff.rfl

/-- **The cylinder probability of the union of the shift coupling**: `ω ~ P_ρ` and
`η ~ P_q` independent, then the cylinder probabilities of `ω ∪ η` are those of `P_π`. -/
theorem prod_union_cyl {π ρ : Sym2 V → unitInterval} (h : ∀ e, ρ e ≤ π e)
    (B : Finset (Sym2 V)) (t : Sym2 V → Set Prop) :
    ((edgeMeasure ρ).prod (edgeMeasure (shiftProb π ρ)))
      (unionConf ⁻¹' edgeCyl B t)
      = ∏ e ∈ B, bernoulliMeasure (True : Prop) (False : Prop) (π e) (t e) := by
  classical
  have hmeas : MeasurableSet (unionConf ⁻¹' edgeCyl B t) :=
    (measurableSet_edgeCyl B t).preimage measurable_unionConf
  rw [Measure.prod_apply hmeas]
  have hinner : ∀ ω : Config V,
      (edgeMeasure (shiftProb π ρ)) (Prod.mk ω ⁻¹' (unionConf ⁻¹' edgeCyl B t))
        = ∏ e ∈ B,
            bernoulliMeasure (True : Prop) (False : Prop) (shiftProb π ρ e)
              {b : Prop | (e ∈ ω ∨ b) ∈ t e} := by
    intro ω
    have hpre : Prod.mk ω ⁻¹' (unionConf ⁻¹' edgeCyl B t)
        = Set.pi (↑B : Set (Sym2 V)) (fun e => {b : Prop | (e ∈ ω ∨ b) ∈ t e}) := by
      ext η
      simp only [Set.mem_ofPred_eq, Set.mem_preimage]
      exact Set.mem_pi (s := (↑B : Set (Sym2 V))) (t := fun e => {b : Prop | (e ∈ ω ∨ b) ∈ t e})
        (f := η)
    rw [hpre, edgeMeasure_eq_infinitePi (shiftProb π ρ)]
    exact Measure.infinitePi_pi (fun e => bernoulliMeasure (True : Prop) (False : Prop)
      (shiftProb π ρ e)) (fun e _ => MeasurableSet.of_discrete)
  refine (lintegral_congr hinner).trans ?_
  refine (lintegral_prod_coord ρ B
    (fun e b => bernoulliMeasure (True : Prop) (False : Prop) (shiftProb π ρ e)
      {b' : Prop | (b ∨ b') ∈ t e})).trans ?_
  refine Finset.prod_congr rfl fun e _ => ?_
  have hper : ∫⁻ b, bernoulliMeasure (True : Prop) (False : Prop) (shiftProb π ρ e)
        {b' : Prop | (b ∨ b') ∈ t e} ∂(bernoulliMeasure (True : Prop) (False : Prop) (ρ e))
      = bernoulliMeasure (True : Prop) (False : Prop) (π e) (t e) := by
    have hmap := prod_ber_or (h e)
    have h1 : ((bernoulliMeasure (True : Prop) (False : Prop) (ρ e)).prod
          (bernoulliMeasure (True : Prop) (False : Prop) (shiftProb π ρ e)))
        ((fun x : Prop × Prop => x.1 ∨ x.2) ⁻¹' t e)
        = bernoulliMeasure (True : Prop) (False : Prop) (π e) (t e) := by
      rw [← hmap, Measure.map_apply measurable_or_prop (MeasurableSet.of_discrete)]
    rw [← h1]
    exact (Measure.prod_apply (μ := bernoulliMeasure (True : Prop) (False : Prop) (ρ e))
      (ν := bernoulliMeasure (True : Prop) (False : Prop) (shiftProb π ρ e))
      (s := (fun x : Prop × Prop => x.1 ∨ x.2) ⁻¹' t e) (MeasurableSet.of_discrete)).symm
  exact hper

/-- **The union law of the monotone shift coupling.**  If `ω ~ P_ρ` and `η ~ P_q` are
independent, then `ω ∪ η ~ P_π`.  This is the precise form of "the cut-off configuration plus the
independent fresh edges is a sample of the full law". -/
theorem unionMeasure_eq_edgeMeasure {π ρ : Sym2 V → unitInterval} (h : ∀ e, ρ e ≤ π e) :
    ((edgeMeasure ρ).prod (edgeMeasure (shiftProb π ρ))).map unionConf = edgeMeasure π := by
  refine eq_edgeMeasure_of_cyl π _ ?_
  intro B t _
  rw [Measure.map_apply measurable_unionConf (measurableSet_edgeCyl B t)]
  exact prod_union_cyl h B t

/-! ## Factoring out the cut-off cluster

The event `{cluster ω o = K}` is determined by the states of the edges touching `K`
(`selfDetermined_touchSet`), and the off-cluster exploration walk of `exists_fresh_exit_of_ghost`
uses only edges *avoiding* `K`.  Hence, conditionally on `{cluster ω o = K}`, the off-cluster
exploration has the same law as in the unrestricted model.  This is the honest replacement of the
paper's "exploring the cluster reveals only negative information": it is a genuine independence
statement between two *fixed* complementary blocks of edge coordinates, and it is proved below.
-/

/-- A measurable function which only sees the coordinates outside `S` is measurable for
`blockSigma Sᶜ`. -/
theorem measurable_blockSigma_compl_of_forget {S : Set (Sym2 V)} {f : Config V → ℝ≥0∞}
    (hf : Measurable f) (hinv : ∀ ω ω' : Config V, (∀ e, e ∉ S → (e ∈ ω' ↔ e ∈ ω)) → f ω' = f ω) :
    Measurable[blockSigma Sᶜ] f := by
  have h := hf.comp (measurable_forceOn_block S (∅ : Config V))
  convert h using 1
  funext ω
  exact (hinv ω (forceOn S ∅ ω) (fun e he => mem_forceOn_of_notMem (S := S) he
    (∅ : Config V) ω)).symm

/-- **Factoring out a `blockSigma S`-measurable event.**  Let `A` be an event of `ω` which only
sees the edge coordinates in `S`, and let `F ω ξ` be an integrand which (for every `ξ`) does not
see the coordinates in `S`.  Then `A` factors out of the integral:
`∫_ω ∫_ξ 1_A(ω) F ω ξ = P(A) · ∫_ω ∫_ξ F ω ξ`. -/
theorem lintegral_indicator_mul_of_forget (ρ : Sym2 V → unitInterval) {S : Set (Sym2 V)}
    {Ξ : Type*} [MeasurableSpace Ξ] {ν : Measure Ξ} [IsProbabilityMeasure ν]
    {A : Set (Config V)} (hA : MeasurableSet[blockSigma S] A)
    {F : Config V → Ξ → ℝ≥0∞} (hF : Measurable (Function.uncurry F))
    (hinv : ∀ (ξ : Ξ) (ω ω' : Config V), (∀ e, e ∉ S → (e ∈ ω' ↔ e ∈ ω)) → F ω' ξ = F ω ξ) :
    ∫⁻ ω, ∫⁻ ξ, A.indicator (fun _ => (1 : ℝ≥0∞)) ω * F ω ξ ∂ν ∂(edgeMeasure ρ)
      = (edgeMeasure ρ A) * ∫⁻ ω, ∫⁻ ξ, F ω ξ ∂ν ∂(edgeMeasure ρ) := by
  classical
  -- measurability of the `ξ`-integral and its `blockSigma Sᶜ`-measurability
  have hFm : Measurable fun ω : Config V => ∫⁻ ξ, F ω ξ ∂ν :=
    Measurable.lintegral_prod_right hF
  have hFinv : ∀ ω ω' : Config V, (∀ e, e ∉ S → (e ∈ ω' ↔ e ∈ ω)) →
      (∫⁻ ξ, F ω' ξ ∂ν) = ∫⁻ ξ, F ω ξ ∂ν := by
    intro ω ω' h; congr 1; funext ξ; exact hinv ξ ω ω' h
  have hFblock : Measurable[blockSigma Sᶜ] fun ω : Config V => ∫⁻ ξ, F ω ξ ∂ν :=
    measurable_blockSigma_compl_of_forget hFm hFinv
  have hkey := lintegral_mul_of_indep_blocks ρ S (f := A.indicator (fun _ => (1 : ℝ≥0∞)))
    (g := fun ω : Config V => ∫⁻ ξ, F ω ξ ∂ν)
    (Measurable.indicator measurable_const hA) hFblock
  have hA' : MeasurableSet A := MeasurableSpace.le_def.mp (blockSigma_le S) A hA
  have hind : ∫⁻ ω, A.indicator (fun _ => (1 : ℝ≥0∞)) ω ∂(edgeMeasure ρ) = edgeMeasure ρ A := by
    rw [lintegral_indicator (μ := edgeMeasure ρ) hA' (fun _ => (1 : ℝ≥0∞)), setLIntegral_one]
  have step : ∫⁻ ω, ∫⁻ ξ, A.indicator (fun _ => (1 : ℝ≥0∞)) ω * F ω ξ ∂ν ∂(edgeMeasure ρ)
      = ∫⁻ ω, A.indicator (fun _ => (1 : ℝ≥0∞)) ω * (∫⁻ ξ, F ω ξ ∂ν) ∂(edgeMeasure ρ) := by
    refine lintegral_congr fun ω => ?_
    have hm : Measurable fun ξ : Ξ => F ω ξ :=
      hF.comp (Measurable.prodMk measurable_const measurable_id)
    exact lintegral_const_mul _ hm
  rw [step, hkey, hind]

/-! ## Non-vacuity of the exit decomposition

On three vertices, with `ω = ∅` (so `K_0 = {0}`) and `θ` the complete configuration, a ghost mark
at `2` fires the decomposition exactly as stated: the witness is `x = 0`, `y = 2`, the fresh edge
`{0,2}` and the trivial walk at `2`, which avoids `K_0 = {0}`. -/

theorem decomposition_fires :
    ∃ x ∈ cluster (∅ : Config (Fin 3)) (0 : Fin 3),
      ∃ y ∉ cluster (∅ : Config (Fin 3)) (0 : Fin 3),
        s(x, y) ∈ (Set.univ : Config (Fin 3)) ∧ s(x, y) ∉ (∅ : Config (Fin 3)) ∧
          ∃ v, (fun w : Fin 3 => w = 2) v ∧
            ∃ q : (openGraph (Set.univ : Config (Fin 3))).Walk y v,
              WalkAvoids q (cluster (∅ : Config (Fin 3)) (0 : Fin 3)) := by
  have hG : GhostConnected (0 : Fin 3) ((Set.univ : Config (Fin 3)), (fun w : Fin 3 => w = 2)) := by
    refine ⟨2, ?_, rfl⟩
    rw [cluster_univ]
    exact Set.mem_univ _
  have hnG : ¬ GhostConnected (0 : Fin 3) ((∅ : Config (Fin 3)), (fun w : Fin 3 => w = 2)) := by
    rintro ⟨v, hv, hv2⟩
    rw [cluster_empty, Set.mem_singleton_iff] at hv
    subst hv
    exact absurd hv2 (by decide)
  exact exists_fresh_exit_of_ghost (ω := (∅ : Config (Fin 3)))
    (θ := (Set.univ : Config (Fin 3))) (fun e he => by simp) hG hnG

/-- Without ghost marks the hypothesis of the decomposition is never satisfied, so the exit event
is empty: the decomposition is not a tautology. -/
theorem decomposition_vacuous_no_marks (ω θ : Config (Fin 3)) :
    ¬ (GhostConnected (0 : Fin 3) (θ, (fun _ : Fin 3 => False)) ∧
        ¬ GhostConnected (0 : Fin 3) (ω, (fun _ : Fin 3 => False))) := by
  rintro ⟨⟨v, -, hv⟩, -⟩
  exact hv

/-! ## The off-cluster exploration event -/

/-- The configuration obtained by *deleting* every edge touching `K`.  A walk in this
configuration is a walk which avoids `K`. -/
def restrictConf (K : Set V) (ω : Config V) : Config V := {e | e ∈ ω ∧ e ∉ edgeTouch K}

theorem measurable_restrictConf (K : Set V) : Measurable (restrictConf (V := V) K) := by
  refine measurable_pi_iff.mpr fun e => ?_
  refine measurable_to_prop ?_
  have hT : MeasurableSet {ω : Config V | e ∈ edgeTouch K} := by
    by_cases he : e ∈ edgeTouch K <;> simp [he]
  have h1 : MeasurableSet ({ω : Config V | e ∈ ω} ∩ {ω : Config V | e ∉ edgeTouch K}) :=
    (measurableSet_mem e).inter hT.compl
  have h2 : (fun ω : Config V => restrictConf K ω e) ⁻¹' ({True} : Set Prop)
      = {ω : Config V | e ∈ ω} ∩ {ω : Config V | e ∉ edgeTouch K} := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_inter_iff, Set.mem_ofPred_eq,
      restrictConf]
    exact ⟨fun h => of_eq_true h, fun h => eq_true h⟩
  rw [h2]
  exact h1

theorem mem_restrictConf {K : Set V} {ω : Config V} {e : Sym2 V} :
    e ∈ restrictConf K ω ↔ e ∈ ω ∧ e ∉ edgeTouch K := Iff.rfl

/-- **The off-cluster exploration event**: in the configuration `z.1`, the vertex `y` is connected
to a marked vertex `v ∉ K` by a walk avoiding `K`.  Equivalently, `v` lies in the cluster of `y`
after all edges touching `K` have been deleted. -/
def offCluster (K : Set V) (y : V) : Set (Config V × (V → Prop)) :=
  {z | ∃ v : V, v ∉ K ∧ z.2 v ∧ v ∈ cluster (restrictConf K z.1) y}

theorem measurableSet_offCluster (K : Set V) (y : V) : MeasurableSet (offCluster (V := V) K y) := by
  have h : offCluster K y
      = ⋃ v : V, ({z : Config V × (V → Prop) | v ∉ K} ∩ {z | z.2 v}
          ∩ {z : Config V × (V → Prop) | v ∈ cluster (restrictConf K z.1) y}) := by
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff]
    exact ⟨fun ⟨v, hv, h2, h3⟩ => ⟨v, ⟨hv, h2⟩, h3⟩,
      fun ⟨v, ⟨hv, h2⟩, h3⟩ => ⟨v, hv, h2, h3⟩⟩
  rw [h]
  refine MeasurableSet.iUnion fun v => ?_
  refine MeasurableSet.inter (MeasurableSet.inter ?_ ?_) ?_
  · by_cases hv : v ∈ K <;> simp [hv]
  · have h2 : Measurable fun z : Config V × (V → Prop) => z.2 v :=
      measurable_pi_apply v |>.comp measurable_snd
    simpa using h2 (measurableSet_singleton True)
  · exact (measurableSet_cluster_mem y v).preimage
      ((measurable_restrictConf K).comp measurable_fst)

/-! ## The cluster event and its measurability for the edge block it reveals -/

theorem measurableSet_cluster_eq_finset (o : V) (K : Finset V) :
    MeasurableSet {ω : Config V | cluster ω o = (K : Set V)} := by
  rw [show {ω : Config V | cluster ω o = (K : Set V)}
      = ⋂ v, {ω : Config V | (v ∈ cluster ω o ↔ v ∈ K)} from by
    ext ω; simp [Set.ext_iff]]
  exact MeasurableSet.iInter fun v => by
    by_cases hv : v ∈ K
    · rw [show {ω : Config V | (v ∈ cluster ω o ↔ v ∈ K)} = {ω | v ∈ cluster ω o} from by
        ext ω; simp [hv]]
      exact measurableSet_cluster_mem o v
    · rw [show {ω : Config V | (v ∈ cluster ω o ↔ v ∈ K)} = {ω | v ∉ cluster ω o} from by
        ext ω; simp [hv]]
      exact (measurableSet_cluster_mem o v).compl

/-- **The cut-off cluster event only depends on the edges touching `K`.**  This is the precise
form of `selfDetermined_touchSet` used in the proof of (I.3.5): once the cluster is `K`, every
edge of `edgeTouch K` has been revealed, and nothing else has. -/
theorem measurableSet_cluster_eq_finset_blockSigma (o : V) (K : Finset V) :
    MeasurableSet[blockSigma (edgeTouch (K : Set V))] {ω : Config V | cluster ω o = (K : Set V)} := by
  have hG : blockSigma ((edgeTouch (K : Set V))ᶜ)ᶜ = blockSigma (edgeTouch (K : Set V)) := by
    rw [compl_compl]
  rw [← hG]
  refine measurableSet_blockSigma_compl_of_agree (measurableSet_cluster_eq_finset o K) ?_
  intro ω ω' hag hω
  have hsub : touchSet ω o = edgeTouch (K : Set V) := by
    rw [show touchSet ω o = edgeTouch (cluster ω o) from by
      ext e
      exact ⟨fun ⟨v, hv, hc⟩ => ⟨v, hc, hv⟩, fun ⟨v, hc, hv⟩ => ⟨v, hv, hc⟩⟩, hω]
  have hagree : ∀ e, e ∈ touchSet ω o → (e ∈ ω' ↔ e ∈ ω) := by
    intro e he
    exact hag e (by rw [hsub] at he; simpa using he)
  rw [← hω]
  exact cluster_eq_of_eqOn_touchSet hagree

/-! ## The exit decomposition in the monotone shift coupling

The probability space is `(ω, η, G) ~ P_ρ ⊗ P_q ⊗ ghost`, and the full configuration is
`unionConf (ω, η)`.  This is the exact form in which the union bound of (I.3.5) is applied. -/

/-- `ω` is contained in the union `ω ∪ η`. -/
theorem subset_unionConf_left (ω η : Config V) :
    ω ⊆ unionConf (ω, η) := by
  intro e he
  exact Or.inl he

/-- **The exit decomposition in the coupling.**  If the ghost hits the cluster of `o` in the full
configuration `ω ∪ η` but not in the cut-off configuration `ω`, and the cut-off cluster is the
fixed finite set `K`, then some edge `{x,y}` with `x ∈ K`, `y ∉ K` is *fresh* (present in `η`)
and the ghost is reached from `y` by a walk of the full configuration which avoids `K`. -/
theorem exit_decomposition_coupling {K : Finset V} {o : V}
    {z : (Config V × Config V) × (V → Prop)}
    (hz : cluster z.1.1 o = (K : Set V))
    (hG : GhostConnected o (unionConf z.1, z.2))
    (hnG : ¬ GhostConnected o (z.1.1, z.2)) :
    ∃ x ∈ (K : Set V), ∃ y ∉ (K : Set V),
      s(x, y) ∈ z.1.2 ∧ offCluster (K : Set V) y (unionConf z.1, z.2) := by
  obtain ⟨x, hxK, y, hyK, hfull, hnot, v, hGv, q, hq⟩ :=
    exists_fresh_exit_of_ghost (ω := z.1.1) (θ := unionConf z.1) (fun e he => Or.inl he) hG hnG
  rw [hz] at hxK hyK
  have hη : s(x, y) ∈ z.1.2 := by
    rcases hfull with h | h
    · exact absurd h hnot
    · exact h
  refine ⟨x, hxK, y, hyK, hη, v, ?_, hGv, ?_⟩
  · simpa [hz] using hq.end_notMem
  -- the walk `q` avoids `edgeTouch K`, hence lies in the restricted configuration
  obtain ⟨q', hq'⟩ := exists_walk_top_of_walk q
  have hq'edges : ∀ e ∈ q'.edges, e ∈ restrictConf (K : Set V) (unionConf z.1) := by
    intro e he
    have he' : e ∈ q.edges := by rw [← hq']; exact he
    rw [mem_restrictConf]
    refine ⟨edgeSet_openGraph_subset (q.edges_subset_edgeSet he'), ?_⟩
    have hne := hq.not_mem_edgeTouch e he'
    rwa [hz] at hne
  obtain ⟨q'', hq''⟩ := exists_walk_openGraph_of_walk_top q' hq'edges
  exact mem_cluster_iff.mpr q''.reachable

/-! ## The two probabilities of (I.3.5), and the last factor of the error term -/

-- `ghostHits π h o` is `(edgeMeasure π).prod (ghostLaw h) (GhostConnected o)`..
-- The ghost-hit functional is defined in GhostField.lean.

-- `weightedGhostMass` is the weighted cluster volume, and is defined in GhostField.lean.
-- The weighted ghost-mass functional is also defined in GhostField.lean.

-- Measurability of the weighted integrand is supplied by GhostField.lean.

-- The Laplace identity `ghostHits_eq` is supplied by GhostField.lean.

/-- **The last factor of the error term is a ghost-hit probability.**  The off-cluster exploration
event is contained in the event that the ghost hits the cluster of `y` in the full configuration,
so its probability is at most `ghostHits π h y = E_π[1 - e^{-h|K_y|}]`.  This is the precise
content of "one global ghost-hit probability" in the error term of (I.3.5). -/
theorem offCluster_integral_le_ghostHits (π : Sym2 V → unitInterval) (h : ℝ≥0) (K : Set V) (y : V) :
    ∫⁻ z, (offCluster K y).indicator (fun _ => (1 : ℝ≥0∞)) z ∂((edgeMeasure π).prod (ghostLaw h))
      ≤ ghostHits π h y := by
  have hsub : offCluster K y ⊆ GhostConnected y := by
    rintro ⟨θ, G⟩ ⟨v, -, hGv, hv⟩
    exact ⟨v, cluster_mono (fun e he => he.1) y hv, hGv⟩
  have hind : ∀ z : Config V × (V → Prop),
      (offCluster K y).indicator (fun _ => (1 : ℝ≥0∞)) z
        ≤ (GhostConnected y).indicator (fun _ => (1 : ℝ≥0∞)) z := by
    intro z
    by_cases hz : z ∈ offCluster K y
    · rw [Set.indicator_of_mem hz, Set.indicator_of_mem (hsub hz)]
    · rw [Set.indicator_of_notMem hz]
      exact zero_le
  refine (lintegral_mono hind).trans ?_
  rw [lintegral_indicator (measurableSet_ghostConnected y) (fun _ => (1 : ℝ≥0∞)), setLIntegral_one]
  exact le_of_eq rfl

/-- Consequently the "one global ghost-hit probability" hypothesis of the error term may be taken
to be `G = ⨆ y, ghostHits π h y`. -/
theorem offCluster_integral_le_iSup (π : Sym2 V → unitInterval) (h : ℝ≥0) (K : Set V) (y : V) :
    ∫⁻ z, (offCluster K y).indicator (fun _ => (1 : ℝ≥0∞)) z ∂((edgeMeasure π).prod (ghostLaw h))
      ≤ ⨆ y : V, ghostHits π h y :=
  (offCluster_integral_le_ghostHits π h K y).trans (le_iSup (fun y => ghostHits π h y) y)

end PercLib.CriticalLRP
