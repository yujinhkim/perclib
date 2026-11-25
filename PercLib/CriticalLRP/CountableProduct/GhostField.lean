/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
# The ghost field of the canonical long-range model

Source: Tom Hutchcroft, *Critical long-range percolation I: High effective dimension*,
arXiv:2508.18807v1, proof of Proposition I.3.1 (p. 29) and of Proposition I.3.2 (p. 31):

  "Let `G` be an independent ghost field of intensity `h` independent of the percolation
   configuration, i.e. a random subset of `Z^d` in which each vertex is included
   independently at random with inclusion probability `1 - e^{-h}`.  Connection
   probabilities to the ghost field encode the Laplace transform of the cluster volume
   distribution:
     `P_{β_c,r,h}(0 ↔ G) = E_{β_c,r}[1 - e^{-h |K|}]`
   for every `r, h > 0`."

This file proves that identity in the canonical countable model `Config V = Set (Sym2 V)` of
`CriticalPercLib.CriticalLRP.CountableProduct.Base`, for an *arbitrary* edge probability
function `π`, hence in particular for the cut-off law `P_{β,r}` (any `π_r ≤ π`).

## Why the identity is not a definition

`|K|` is a function of the percolation configuration alone; the ghost field is a second,
independent source of randomness.  The identity says that the *hitting* probability of the
cluster by an independent Bernoulli field equals the Laplace transform of its volume.  It is
proved here from the product structure of the marking measure only:

* for a fixed countable set `S` of vertices, the event that no vertex of `S` is marked has
  probability `∏'_{v ∈ S} (1 - p)` (`ghostLaw_avoids`) — this is the cylinder formula
  `infinitePi_pi_of_countable` of Mathlib's product measure, for a fixed `S` and *without*
  any assumption on `S` (finite or infinite);
* hence the hitting probability is `1 - ∏'` (`ghostLaw_hits`);
* integrating over the configuration with `Measure.prod_apply` gives
  `(P × ghost){0 ↔ G} = ∫⁻ 1 - ∏'_{v ∈ K} (1 - p)`,
  and `∏'_{v ∈ K} (1 - p)` is `e^{-h |K|}`, with the convention `e^{-h·∞} = 0` which is
  exactly the value of the infinite product when `h > 0` (`ghostMass_of_finite`,
  `ghostMass_of_infinite`).

No `sorry`, no custom axioms.
-/
module

public import PercLib.CriticalLRP.CountableProduct.Marks

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

set_option autoImplicit true

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1200000

@[expose] public section

open MeasureTheory Measure ProbabilityTheory unitInterval
open scoped ENNReal NNReal

namespace PercLib.CriticalLRP

variable {V : Type*} [Countable V]

/-! ## The marking measure -/

/-- The probability `1 - e^{-h}` that a vertex belongs to the ghost field of intensity `h`. -/
noncomputable def ghostProb (h : ℝ≥0) : unitInterval where
  val := 1 - Real.exp (-(h : ℝ))
  property := by
    constructor
    · have hle : Real.exp (-(h : ℝ)) ≤ 1 := by
        rw [← Real.exp_zero]
        exact Real.exp_le_exp.mpr (by simpa using h.2)
      linarith
    · have hpos : 0 < Real.exp (-(h : ℝ)) := Real.exp_pos _
      linarith

@[simp] theorem ghostProb_val (h : ℝ≥0) : (ghostProb h).val = 1 - Real.exp (-(h : ℝ)) := rfl

theorem one_sub_ghostProb (h : ℝ≥0) :
    (1 - (ghostProb h).val : ℝ) = Real.exp (-(h : ℝ)) := by
  rw [ghostProb_val]; ring

/-- **The ghost field of intensity `h`**: an independent random subset of `V` in which every
vertex is included with probability `1 - e^{-h}`, independently of all the others. -/
noncomputable def ghostLaw (h : ℝ≥0) : Measure (V → Prop) :=
  Measure.infinitePi (X := fun _ : V => Prop)
    (fun _ => bernoulliMeasure (True : Prop) (False : Prop) (ghostProb h))

instance instIsProbabilityMeasureGhostLaw (h : ℝ≥0) :
    IsProbabilityMeasure (ghostLaw (V := V) h) :=
  inferInstanceAs (IsProbabilityMeasure (Measure.infinitePi
    (X := fun _ : V => Prop) (fun _ => bernoulliMeasure (True : Prop) (False : Prop)
      (ghostProb h))))

/-- The single-vertex weight `1 - p = e^{-h}` of the ghost field, as an extended nonnegative
real.  `ghostMass` below is its product over the cluster. -/
noncomputable def ghostW (h : ℝ≥0) : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-(h : ℝ)))

theorem exp_neg_le_one (h : ℝ≥0) : Real.exp (-(h : ℝ)) ≤ 1 := by
  have := Real.exp_le_exp (x := -(h : ℝ)) (y := 0) |>.mpr (by simpa using h.2)
  simpa using this

theorem exp_neg_lt_one {h : ℝ≥0} (hh : 0 < h) : Real.exp (-(h : ℝ)) < 1 := by
  have := Real.exp_lt_exp (x := -(h : ℝ)) (y := 0) |>.mpr (by simpa using hh)
  simpa using this

theorem ghostW_le_one (h : ℝ≥0) : ghostW h ≤ 1 := by
  rw [ghostW, ENNReal.ofReal_le_one]
  exact exp_neg_le_one h

theorem ghostW_lt_one {h : ℝ≥0} (hh : 0 < h) : ghostW h < 1 := by
  rw [ghostW, ENNReal.ofReal_lt_one]
  exact exp_neg_lt_one hh

theorem ghostW_ne_zero (h : ℝ≥0) : ghostW h ≠ 0 := by
  rw [ghostW, ENNReal.ofReal_ne_zero_iff]
  exact Real.exp_pos _

/-- The `False`-mass of a Bernoull-measure on `Prop`, in the shape produced by
`bernoulliMeasure_apply`. -/
theorem coe_toNNReal_symm (p : unitInterval) :
    ((toNNReal (σ p) : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal (1 - (p : ℝ)) := by
  rw [ENNReal.ofReal, ENNReal.coe_inj, Real.toNNReal_of_nonneg (by linarith [p.2.2])]
  exact Subtype.ext (by simp)

/-- The mass of a single vertex being *absent* from the ghost field. -/
theorem bernoulliMeasure_absent (h : ℝ≥0) :
    bernoulliMeasure (True : Prop) (False : Prop) (ghostProb h) {q : Prop | ¬ q} = ghostW h := by
  classical
  rw [bernoulliMeasure_apply (ghostProb h) (by measurability)]
  simp only [Set.mem_ofPred_eq, not_true_eq_false, not_false_eq_true, ite_false, ite_true]
  rw [coe_toNNReal_symm, ghostW, ← one_sub_ghostProb]

/-! ## Absence of marks on a fixed set of vertices -/

theorem measurableSet_absent (S : Set V) :
    MeasurableSet (Set.pi S (fun _ : V => {q : Prop | ¬ q})) :=
  MeasurableSet.pi (Set.to_countable S) fun _ _ => MeasurableSet.of_discrete

theorem measurableSet_hits (S : Set V) : MeasurableSet {G : V → Prop | ∃ v ∈ S, G v} := by
  have h : {G : V → Prop | ∃ v ∈ S, G v}
      = (Set.pi S (fun _ : V => {q : Prop | ¬ q}))ᶜ := by
    ext G
    simp
  rw [h]
  exact (measurableSet_absent S).compl

/-- **Cylinder formula for the ghost field**: the probability that the ghost field misses a
fixed countable set `S` of vertices is the infinite product `∏'_{v ∈ S} (1 - p)`. -/
theorem ghostLaw_pi (h : ℝ≥0) (S : Set V) :
    ghostLaw h (Set.pi S (fun _ : V => {q : Prop | ¬ q})) = ∏' _ : S, ghostW h := by
  rw [ghostLaw, infinitePi_pi_of_countable
    (μ := fun _ : V => bernoulliMeasure (True : Prop) (False : Prop) (ghostProb h))
    (s := S) (t := fun _ => {q : Prop | ¬ q}) (by infer_instance)
    (fun _ _ => MeasurableSet.of_discrete)]
  exact tprod_congr fun v => bernoulliMeasure_absent h

theorem ghostLaw_avoids (h : ℝ≥0) (S : Set V) :
    ghostLaw h {G : V → Prop | ∀ v ∈ S, ¬ G v} = ∏' _ : S, ghostW h := by
  have hset : {G : V → Prop | ∀ v ∈ S, ¬ G v}
      = Set.pi S (fun _ : V => {q : Prop | ¬ q}) := by
    ext G; simp
  rw [hset, ghostLaw_pi]

/-- **Hitting probability of a fixed set**: `1` minus the infinite product. -/
theorem ghostLaw_hits (h : ℝ≥0) (S : Set V) :
    ghostLaw h {G : V → Prop | ∃ v ∈ S, G v} = 1 - ∏' _ : S, ghostW h := by
  have h : {G : V → Prop | ∃ v ∈ S, G v}
      = (Set.pi S (fun _ : V => {q : Prop | ¬ q}))ᶜ := by
    ext G
    simp
  rw [h, measure_compl (measurableSet_absent S) (by simp), measure_univ, ghostLaw_pi]

/-! ## The Laplace functional `e^{-h|K|}` as an infinite product

`|K|` is the extended cardinality `clusterVol ω o` of the cluster.  The product of `1 - p = e^{-h}`
over the vertices of the cluster is `e^{-h|K|}`, with the standard convention `e^{-h·∞} = 0` for
`h > 0`, which is also the value of an infinite product of numbers `< 1`.  This is the exact
object whose expectation appears in (I.3.2) and in (I.3.5); the two evaluation lemmas
(`ghostMass_of_finite`, `ghostMass_of_infinite`) show that it agrees with `e^{-h|K|}` read
through the extended cardinality. -/

/-- The mass `e^{-h|K|}` of "the ghost field avoids the cluster of `o`", as the product of the
per-vertex absence probabilities `1 - p = e^{-h}` over the vertices of the cluster. -/
noncomputable def ghostMass (h : ℝ≥0) (ω : Config V) (o : V) : ℝ≥0∞ :=
  ∏' _ : cluster ω o, ghostW h

/-! ## The main identity -/

/-- The event `{0 ↔ G}`, as a subset of the product of the configuration space and the
ghost-field space: some vertex of the cluster of `o` carries a mark. -/
def GhostConnected (o : V) : Set (Config V × (V → Prop)) :=
  {z | ∃ v ∈ cluster z.1 o, z.2 v}

theorem measurableSet_ghostConnected (o : V) : MeasurableSet (GhostConnected (V := V) o) := by
  have h : GhostConnected o
      = ⋃ v : V, {ω : Config V | v ∈ cluster ω o} ×ˢ {G : V → Prop | G v} := by
    ext z
    simp [GhostConnected]
  rw [h]
  exact MeasurableSet.iUnion fun v =>
    (measurableSet_cluster_mem o v).prod (by measurability)

/-- **The ghost-field identity, for an arbitrary edge law.**

For every edge-probability function `π`, every intensity `h` and every vertex `o`, the
probability that the cluster of `o` meets an independent ghost field of intensity `h` is the
expectation of `1 - e^{-h|K|}`:
`P_{π,h}(0 ↔ G) = ∫⁻ 1 - e^{-h|K|} dP_π`.

This is the identity used in the proof of Proposition I.3.2 (and of Proposition I.3.1), stated
for the canonical countable model with an arbitrary `π`; in particular it applies to the
cut-off law `P_{β_c,r}` (`π = π_r`) and to the full law `P_{β_c}` (`π = π_∞`). -/
theorem edgeMeasure_prod_ghost_hits (π : Sym2 V → unitInterval) (h : ℝ≥0) (o : V) :
    (edgeMeasure π).prod (ghostLaw h) (GhostConnected o)
      = ∫⁻ ω, (1 - ghostMass h ω o) ∂edgeMeasure π := by
  rw [Measure.prod_apply (measurableSet_ghostConnected o)]
  refine lintegral_congr fun ω => ?_
  exact ghostLaw_hits h (cluster ω o)

/-- The same identity in "absence" form: the probability that the ghost field misses the
cluster of `o` is exactly `E[e^{-h|K|}]`. -/
theorem edgeMeasure_prod_ghost_absent (π : Sym2 V → unitInterval) (h : ℝ≥0) (o : V) :
    (edgeMeasure π).prod (ghostLaw h) (GhostConnected o)ᶜ
      = ∫⁻ ω, ghostMass h ω o ∂edgeMeasure π := by
  rw [Measure.prod_apply (measurableSet_ghostConnected o).compl]
  refine lintegral_congr fun ω => ?_
  have hsec : Prod.mk ω ⁻¹' (GhostConnected o)ᶜ
      = {G : V → Prop | ∀ v ∈ cluster ω o, ¬ G v} := by
    ext G; simp [GhostConnected]
  rw [hsec]
  exact ghostLaw_avoids h (cluster ω o)

/-- A power of the absence weight is the real exponential at that integer. -/
theorem ghostW_pow (h : ℝ≥0) (n : ℕ) :
    ghostW h ^ n = ENNReal.ofReal (Real.exp (-(h : ℝ) * (n : ℝ))) := by
  rw [ghostW, ← ENNReal.ofReal_pow (Real.exp_nonneg _)]
  congr 1
  rw [← Real.exp_nat_mul]
  ring_nf

/-- On a finite cluster the product of absence probabilities is evaluated by cardinality. -/
theorem ghostMass_of_finite (h : ℝ≥0) (ω : Config V) (o : V)
    (hfin : (cluster ω o).Finite) :
    ghostMass h ω o = ghostW h ^ (cluster ω o).ncard := by
  classical
  let := hfin.fintype
  rw [ghostMass, tprod_fintype, Finset.prod_const]
  congr 1
  simp

/-- The product of a positive constant strictly below one over an infinite cluster is zero. -/
theorem ghostMass_of_infinite {h : ℝ≥0} (hh : 0 < h) (ω : Config V) (o : V)
    (hinf : (cluster ω o).Infinite) : ghostMass h ω o = 0 := by
  let := hinf.to_subtype
  rw [ghostMass, ENNReal.tprod_eq_iInf_prod (fun _ => ghostW_le_one h)]
  apply le_antisymm ?_ bot_le
  have htend := ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (ghostW_lt_one hh)
  refine ge_of_tendsto htend (Filter.Eventually.of_forall fun n => ?_)
  obtain ⟨s, hs⟩ := Finset.exists_card_eq (α := cluster ω o) n
  calc
    (⨅ s : Finset (cluster ω o), ∏ i ∈ s, ghostW h) ≤ ∏ i ∈ s, ghostW h :=
      iInf_le _ s
    _ = ghostW h ^ s.card := Finset.prod_const _
    _ = ghostW h ^ n := by rw [hs]

/-- At positive intensity the product has the standard exponential value, including the
zero value associated to an infinite cluster. -/
theorem ghostMass_eq_exp (h : ℝ≥0) (hh : 0 < h) (ω : Config V) (o : V) :
    ghostMass h ω o = if clusterVol ω o = ⊤ then (0 : ℝ≥0∞) else
      ENNReal.ofReal (Real.exp (-(h : ℝ) * (clusterVol ω o).toReal)) := by
  by_cases hfin : (cluster ω o).Finite
  · have hne : clusterVol ω o ≠ ⊤ := by
      rw [clusterVol_eq_encard, encard_coe_eq_ncard_coe hfin]
      exact ENNReal.natCast_ne_top _
    have hvol : (clusterVol ω o).toReal = ((cluster ω o).ncard : ℝ) := by
      rw [clusterVol_eq_encard, encard_coe_eq_ncard_coe hfin]
      simp
    rw [ite_eq_right hne, ghostMass_of_finite h ω o hfin, ghostW_pow, hvol]
  · have hinf : (cluster ω o).Infinite := hfin
    have htop : clusterVol ω o = ⊤ := by
      rw [clusterVol_eq_encard, Set.encard_eq_top_iff.mpr hinf]
      rfl
    rw [ite_eq_left htop, ghostMass_of_infinite hh ω o hinf]

/-- The ghost avoidance functional is measurable. -/
theorem measurable_ghostMass (h : ℝ≥0) (o : V) :
    Measurable fun ω : Config V => ghostMass h ω o := by
  by_cases hh : 0 < h
  · have hpoint : (fun ω : Config V => ghostMass h ω o) = fun ω =>
        if clusterVol ω o = ⊤ then 0 else
          ENNReal.ofReal (Real.exp (-(h : ℝ) * (clusterVol ω o).toReal)) := by
      funext ω
      rw [ghostMass_eq_exp h hh]
    rw [hpoint]
    exact Measurable.ite (measurable_clusterVol o (measurableSet_singleton ⊤))
      measurable_const
      (ENNReal.measurable_ofReal.comp
        (Real.measurable_exp.comp
          (measurable_const.mul (ENNReal.measurable_toReal.comp (measurable_clusterVol o)))))
  · have hzero : h = 0 := nonpos_iff_eq_zero.mp (le_of_not_gt hh)
    subst hzero
    simpa [ghostMass, ghostW] using
      (measurable_const : Measurable (fun _ : Config V => (1 : ℝ≥0∞)))

/-- The avoidance probability as a real exponential moment at positive intensity.
Infinite clusters are excluded almost everywhere, so `toReal` of the extended cardinality is
an ordinary nonnegative random variable. -/
theorem edgeMeasure_prod_ghost_absent_real (π : Sym2 V → unitInterval) (h : ℝ≥0)
    (hh : 0 < h) (o : V) (hfin : ∀ᵐ ω ∂(edgeMeasure π), clusterVol ω o ≠ ⊤) :
    (edgeMeasure π).prod (ghostLaw h) (GhostConnected o)ᶜ =
      ENNReal.ofReal (∫ ω, Real.exp (-(h : ℝ) * (clusterVol ω o).toReal) ∂(edgeMeasure π)) := by
  have hmeas : Measurable fun ω : Config V =>
      Real.exp (-(h : ℝ) * (clusterVol ω o).toReal) :=
    Real.measurable_exp.comp (measurable_const.mul
      (ENNReal.measurable_toReal.comp (measurable_clusterVol o)))
  have hle : ∀ ω : Config V,
      Real.exp (-(h : ℝ) * (clusterVol ω o).toReal) ≤ 1 := by
    intro ω
    rw [← Real.exp_zero]
    apply Real.exp_le_exp.mpr
    have hh0 : (0 : ℝ) ≤ (h : ℝ) := h.2
    have hn : 0 ≤ (h : ℝ) * (clusterVol ω o).toReal :=
      mul_nonneg hh0 ENNReal.toReal_nonneg
    nlinarith
  have hint : Integrable (fun ω : Config V =>
      Real.exp (-(h : ℝ) * (clusterVol ω o).toReal)) (edgeMeasure π) := by
    refine Integrable.of_bound hmeas.aestronglyMeasurable 1 ?_
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
    exact hle ω
  have hof := ofReal_integral_eq_lintegral_ofReal (μ := edgeMeasure π)
    (f := fun ω : Config V => Real.exp (-(h : ℝ) * (clusterVol ω o).toReal)) hint
      (Filter.Eventually.of_forall fun ω => (Real.exp_pos _).le)
  rw [edgeMeasure_prod_ghost_absent, hof]
  refine lintegral_congr_ae ?_
  filter_upwards [hfin] with ω hω
  rw [ghostMass_eq_exp h hh, ite_eq_right hω]

/-- Avoidance is at most probability one. -/
theorem ghostMass_le_one (h : ℝ≥0) (ω : Config V) (o : V) : ghostMass h ω o ≤ 1 := by
  rw [ghostMass, ENNReal.tprod_eq_iInf_prod (fun _ => ghostW_le_one h)]
  calc ⨅ s : Finset ↥(cluster ω o), ∏ i ∈ s, ghostW h
      ≤ ∏ i ∈ (∅ : Finset ↥(cluster ω o)), ghostW h := iInf_le _ _
    _ = 1 := by simp

/-- **The identity in probability form**: `P(0 ↔ G) + E[e^{-h|K|}] = 1`, i.e.
`P(0 ↔ G) = 1 - E[e^{-h|K|}]`, with no subtraction on extended nonnegative reals. -/
theorem edgeMeasure_prod_ghost_hits_add (π : Sym2 V → unitInterval) (h : ℝ≥0) (o : V) :
    (edgeMeasure π).prod (ghostLaw h) (GhostConnected o)
        + ∫⁻ ω, ghostMass h ω o ∂edgeMeasure π = 1 := by
  rw [← edgeMeasure_prod_ghost_absent,
    measure_add_measure_compl (measurableSet_ghostConnected o)]
  simp

/-! ## Stochastic monotonicity in the edge probabilities

The *lower* inequality of (I.3.5),

  `P_{β_c,r,h}(0 ↔ G) ≤ P_{β_c,∞,h}(0 ↔ G)`,

is not an error estimate at all: it is monotonicity of the increasing event `{0 ↔ G}` in the
edge configuration, in the standard monotone coupling.  Below, `p` plays the role of the
cut-off edge probability and `q` that of the full one (`p ≤ q`), for arbitrary
`p q : Sym2 V → unitInterval`.  The ghost field is coupled by the identity, which is legitimate
because the ghost field is independent of the edge configuration. -/

theorem ghost_hits_subset_of_subset {ω ω' : Config V} (h : ω ⊆ ω') (o : V) :
    {G : V → Prop | ∃ v ∈ cluster ω o, G v} ⊆ {G : V → Prop | ∃ v ∈ cluster ω' o, G v} := by
  rintro G ⟨v, hv, hG⟩
  exact ⟨v, cluster_mono (fun e he => h he) o hv, hG⟩

theorem prod_ghost_eq_map (h : ℝ≥0) (r : Sym2 V → unitInterval) :
    (edgeMeasure r).prod (ghostLaw h)
      = ((markMeasure V).prod (ghostLaw h)).map
          (Prod.map (atParameter r) (id : (V → Prop) → (V → Prop))) := by
  rw [← Measure.map_prod_map (markMeasure V) (ghostLaw h) (measurable_atParameter r)
    measurable_id, markMeasure_map_atParameter, Measure.map_id]

/-- **Monotonicity of the ghost connection probability in the edge probabilities.** -/
theorem ghost_prob_mono {p q : Sym2 V → unitInterval} (hpq : ∀ e, p e ≤ q e) (h : ℝ≥0) (o : V) :
    (edgeMeasure p).prod (ghostLaw h) (GhostConnected o)
      ≤ (edgeMeasure q).prod (ghostLaw h) (GhostConnected o) := by
  have hmp : Measurable (Prod.map (atParameter p) (id : (V → Prop) → (V → Prop))) :=
    Measurable.prodMap (measurable_atParameter p) measurable_id
  have hmq : Measurable (Prod.map (atParameter q) (id : (V → Prop) → (V → Prop))) :=
    Measurable.prodMap (measurable_atParameter q) measurable_id
  rw [prod_ghost_eq_map h p, prod_ghost_eq_map h q,
    Measure.map_apply hmp (measurableSet_ghostConnected o),
    Measure.map_apply hmq (measurableSet_ghostConnected o)]
  refine measure_mono ?_
  rintro ⟨u, G⟩ ⟨v, hv, hz⟩
  change v ∈ cluster (atParameter p u) o at hv
  change ∃ v ∈ cluster (atParameter q u) o, G v
  exact ⟨v, cluster_mono (ω := atParameter p u) (ω' := atParameter q u)
    (fun e he => by
      change u e < (p e : ℝ) at he
      change u e < (q e : ℝ)
      exact lt_of_lt_of_le he (hpq e)) o hv, hz⟩

/-! ## Ghost-hit and weighted ghost-mass functionals -/

/-- `P_{π,h}(o ↔ G)`: the probability that the cluster of `o` meets the independent ghost field.
This is a named form of the product measure underlying `edgeMeasure_prod_ghost_hits`. -/
noncomputable def ghostHits (π : Sym2 V → unitInterval) (h : ℝ≥0) (o : V) : ℝ≥0∞ :=
  (edgeMeasure π).prod (ghostLaw h) (GhostConnected o)

/-- `E_π[|K| e^{-h|K|}]`, including the zero contribution from an infinite cluster at positive
intensity. This is the weighted volume functional in the source's ghost error estimate. -/
noncomputable def weightedGhostMass (π : Sym2 V → unitInterval) (h : ℝ≥0) (o : V) : ℝ≥0∞ :=
  ∫⁻ ω, clusterVol ω o * ghostMass h ω o ∂edgeMeasure π

/-- The Laplace identity for the named ghost-hit probability. -/
theorem ghostHits_eq_lintegral (π : Sym2 V → unitInterval) (h : ℝ≥0) (o : V) :
    ghostHits π h o = ∫⁻ ω, (1 - ghostMass h ω o) ∂edgeMeasure π :=
  edgeMeasure_prod_ghost_hits π h o

/-- Short alias for the Laplace identity of `ghostHits`. -/
theorem ghostHits_eq (π : Sym2 V → unitInterval) (h : ℝ≥0) (o : V) :
    ghostHits π h o = ∫⁻ ω, (1 - ghostMass h ω o) ∂edgeMeasure π :=
  edgeMeasure_prod_ghost_hits π h o

/-- The weighted ghost-mass integrand is measurable. -/
theorem measurable_weightedGhostMass_integrand (h : ℝ≥0) (o : V) :
    Measurable fun ω : Config V => clusterVol ω o * ghostMass h ω o :=
  (measurable_clusterVol o).mul (measurable_ghostMass h o)

end PercLib.CriticalLRP
