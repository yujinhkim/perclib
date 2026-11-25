/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
# Restoration at the random edge set touching the cluster of the origin

Source: Tom Hutchcroft, *Critical long-range percolation I: High effective dimension*,
arXiv:2508.18807v1, proof of Lemma I.4.12 (p. 39):

  "Let `ω` and `ω'` be independent percolation configurations, and let `ω̃` be defined by setting
   `ω̃(e) = ω(e)` for every edge `e` touching the cluster `K_0` of `0` in `ω` and
   `ω̃(e) = ω'(e)` for every other edge `e`, so that `ω̃` has the same law as `ω`."

Here `forceOn S η ω = (ω \ S) ∪ (η ∩ S)` replaces the coordinates in `S` by
those of `η`. The main theorem proves the genuinely random-set operation of
resampling the touch set: `(η, ω) ↦ forceOn (touchSet ω o) η ω` preserves the
Bernoulli product law. This is not fixed-set preservation: the source
configuration determines which coordinates are resampled.

The paper's complementary coupling `forceOn (touchSet ω o)ᶜ ω' ω` instead
keeps `ω` on edges touching its cluster and uses `ω'` elsewhere. Proving that
its law is unchanged is a separate open obligation, not a convention change or
a consequence established by this file. The deterministic touch-set invariance
lemmas below are also directed towards that complementary result.

No `sorry`, no custom axioms.
-/
module

public import PercLib.CriticalLRP.CountableProduct.EdgeTouch

set_option autoImplicit true

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

@[expose] public section

open MeasureTheory Measure ProbabilityTheory unitInterval
open scoped ENNReal NNReal

namespace PercLib.CriticalLRP

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Countable V]

/-- Membership in `forceOn S η ω` at an edge outside `S`. -/
theorem mem_forceOn_of_notMem {S : Set (Sym2 V)} {e : Sym2 V} (he : e ∉ S) (η ω : Config V) :
    (e ∈ forceOn S η ω ↔ e ∈ ω) :=
  iff_of_eq (forceOn_apply_of_notMem he η ω)

/-! ## The cluster is determined by the configuration on the edges touching it -/

/-- **The key invariance.**  If `ω'` agrees with `ω` on every edge touching the cluster of `o`
in `ω`, then the clusters of `o` in `ω` and `ω'` coincide. -/
theorem cluster_eq_of_eqOn_touchSet {ω ω' : Config V} {o : V}
    (h : ∀ e, e ∈ touchSet ω o → (e ∈ ω' ↔ e ∈ ω)) :
    cluster ω' o = cluster ω o := by
  apply Set.Subset.antisymm
  · -- `cluster ω' o ⊆ cluster ω o`
    intro w hw
    rw [mem_cluster_iff, Connects, SimpleGraph.reachable_iff_reflTransGen] at hw ⊢
    induction hw with
    | refl => exact Relation.ReflTransGen.refl
    | @tail a b hab hstep ih =>
      have ha : a ∈ cluster ω o := mem_cluster_iff.mpr (by
        rw [Connects, SimpleGraph.reachable_iff_reflTransGen]; exact ih)
      rw [openGraph_adj] at hstep
      obtain ⟨hne, hmem⟩ := hstep
      have hT : s(a, b) ∈ touchSet ω o := ⟨a, Sym2.mem_mk_left a b, ha⟩
      exact ih.tail (by rw [openGraph_adj]; exact ⟨hne, (h s(a, b) hT).mp hmem⟩)
  · -- `cluster ω o ⊆ cluster ω' o`
    intro w hw
    rw [mem_cluster_iff, Connects, SimpleGraph.reachable_iff_reflTransGen] at hw ⊢
    induction hw with
    | refl => exact Relation.ReflTransGen.refl
    | @tail a b hab hstep ih =>
      have ha : a ∈ cluster ω o := mem_cluster_iff.mpr (by
        rw [Connects, SimpleGraph.reachable_iff_reflTransGen]; exact hab)
      rw [openGraph_adj] at hstep
      obtain ⟨hne, hmem⟩ := hstep
      have hT : s(a, b) ∈ touchSet ω o := ⟨a, Sym2.mem_mk_left a b, ha⟩
      exact ih.tail (by rw [openGraph_adj]; exact ⟨hne, (h s(a, b) hT).mpr hmem⟩)

/-- Resampling the edges that do **not** touch the cluster of `o` leaves the cluster, and hence
the set of touching edges, unchanged. -/
theorem touchSet_forceOn_sdiff (ω η : Config V) (o : V) :
    touchSet (forceOn (touchSet ω o)ᶜ η ω) o = touchSet ω o := by
  have hcl := cluster_eq_of_eqOn_touchSet (ω := ω) (ω' := forceOn (touchSet ω o)ᶜ η ω) (o := o)
    (fun e he => mem_forceOn_of_notMem (by simpa using he) η ω)
  refine Set.ext fun e => ?_
  simp only [mem_touchSet]
  rw [hcl]

/-- **Single-edge form `(P)`.**  If `a` does not touch the cluster of `o`, then changing the state
of `a` alone leaves the cluster of `o` (and hence the touch set) unchanged. -/
theorem touchSet_forceOn_singleton_of_notMem {ω η : Config V} {o : V} {a : Sym2 V}
    (ha : a ∉ touchSet ω o) :
    touchSet (forceOn {a} η ω) o = touchSet ω o := by
  have hcl := cluster_eq_of_eqOn_touchSet (ω := ω) (ω' := forceOn {a} η ω) (o := o)
    (fun e he => mem_forceOn_of_notMem (by
      have hne : e ≠ a := fun h => ha (h ▸ he)
      simpa using hne) η ω)
  refine Set.ext fun e => ?_
  simp only [mem_touchSet]
  rw [hcl]


/-! ## Measurability and locality of the touch set -/

/-- Membership of a single edge in the touch set is measurable. -/
theorem measurableSet_mem_touchSet (o : V) (e : Sym2 V) :
    MeasurableSet {ω : Config V | e ∈ touchSet ω o} := by
  induction e using Sym2.ind with
  | _ x y =>
    have hset : {ω : Config V | s(x, y) ∈ touchSet ω o}
        = {ω : Config V | x ∈ cluster ω o} ∪ {ω : Config V | y ∈ cluster ω o} := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_union, mem_touchSet]
      constructor
      · rintro ⟨v, hv, hvc⟩
        rw [Sym2.mem_iff] at hv
        exact hv.elim (fun h => Or.inl (h ▸ hvc)) (fun h => Or.inr (h ▸ hvc))
      · rintro (h | h)
        · exact ⟨x, Sym2.mem_mk_left x y, h⟩
        · exact ⟨y, Sym2.mem_mk_right x y, h⟩
    rw [hset]
    exact (measurableSet_cluster_mem o x).union (measurableSet_cluster_mem o y)

theorem measurable_touchSet_mem (o : V) (e : Sym2 V) :
    Measurable fun ω : Config V => e ∈ touchSet ω o :=
  measurable_to_prop (by simpa using measurableSet_mem_touchSet o e)

theorem coordinateSigma_le_block (a : Sym2 V) :
    coordinateSigma a ≤ blockSigma ({(a : Sym2 V)} : Set (Sym2 V)) :=
  le_iSup_of_le a (le_iSup_of_le (by simp) le_rfl)

/-- **Locality `(L)`.**  Whether `a` touches the cluster of `o` depends only on the states of the
edges different from `a`. -/
theorem measurable_touchSet_mem_blockSigma (o : V) (a : Sym2 V) :
    Measurable[blockSigma ({(a : Sym2 V)} : Set (Sym2 V))ᶜ]
      fun ω : Config V => a ∈ touchSet ω o := by
  have hfac : Measurable[blockSigma ({(a : Sym2 V)} : Set (Sym2 V))ᶜ]
      (forceOn ({(a : Sym2 V)} : Set (Sym2 V)) (∅ : Config V)) :=
    measurable_forceOn_block _ _
  have h := (measurable_touchSet_mem o a).comp hfac
  convert h using 1
  funext ω
  exact propext (mem_touchSet_forceOn_singleton ω ∅ o a).symm

/-! ## The per-coordinate weight and the finite-coordinate product -/

/-- The Bernoulli weight of the event `t` at the edge `e`. -/
noncomputable def bfun (π : Sym2 V → unitInterval) (t : Sym2 V → Set Prop) (e : Sym2 V) : ℝ≥0∞ :=
  bernoulliMeasure (True : Prop) (False : Prop) (π e) (t e)

theorem measurableSet_eval (t : Sym2 V → Set Prop) (a : Sym2 V) :
    MeasurableSet {ω : Config V | ω a ∈ t a} :=
  measurable_pi_apply a (by measurability)

theorem edgeMeasure_eval (π : Sym2 V → unitInterval) (t : Sym2 V → Set Prop)
    (ht : ∀ e, MeasurableSet (t e)) (e : Sym2 V) :
    edgeMeasure π {ω : Config V | ω e ∈ t e} = bfun π t e := by
  have h := edgeMeasure_edgeCyl π {e} t ht
  simpa [bfun, edgeCyl] using h

/-- The one-coordinate integrand: `b e` where the edge touches the cluster, and the actual
indicator `1{ω e ∈ t e}` where it does not. -/
noncomputable def kap (π : Sym2 V → unitInterval) (o : V) (t : Sym2 V → Set Prop)
    (B : Finset (Sym2 V)) : Config V → ℝ≥0∞ :=
  fun ω => ∏ e ∈ B, (if e ∈ touchSet ω o then bfun π t e else if ω e ∈ t e then 1 else 0)

theorem measurable_kap {π : Sym2 V → unitInterval} {o : V} {t : Sym2 V → Set Prop}
    (B : Finset (Sym2 V)) : Measurable (kap π o t B) := by
  classical
  refine Finset.measurable_prod B ?_
  intro e _
  refine Measurable.ite (measurableSet_mem_touchSet o e) measurable_const ?_
  exact Measurable.ite (measurableSet_eval t e) measurable_const measurable_const

theorem kap_insert {π : Sym2 V → unitInterval} {o : V} {t : Sym2 V → Set Prop}
    {B : Finset (Sym2 V)} {a : Sym2 V} (ha : a ∉ B) (ω : Config V) :
    kap π o t (insert a B) ω
      = (if a ∈ touchSet ω o then bfun π t a else if ω a ∈ t a then 1 else 0) * kap π o t B ω := by
  simp only [kap, Finset.prod_insert ha]

/-- The truncated product `kap B · 1{a ∉ touchSet}` is invariant under changing the state of `a`
alone.  (Multiplying by the indicator is what makes this true: when `a` does touch the cluster the
product is simply set to zero.) -/
theorem kap_indicator_forceOn_singleton {π : Sym2 V → unitInterval} {o : V}
    {t : Sym2 V → Set Prop} {B : Finset (Sym2 V)} {a : Sym2 V} (ha : a ∉ B) (η ω : Config V) :
    kap π o t B (forceOn {a} η ω) * (if a ∈ touchSet (forceOn {a} η ω) o then 0 else 1)
      = kap π o t B ω * (if a ∈ touchSet ω o then 0 else 1) := by
  classical
  have hT : a ∈ touchSet (forceOn {a} η ω) o ↔ a ∈ touchSet ω o :=
    mem_touchSet_forceOn_singleton ω η o a
  by_cases h : a ∈ touchSet ω o
  · rw [ite_eq_left (hT.mpr h), ite_eq_left h, mul_zero, mul_zero]
  · rw [ite_eq_right (fun hh => h (hT.mp hh)), ite_eq_right h, mul_one, mul_one]
    have hTs : touchSet (forceOn {a} η ω) o = touchSet ω o :=
      touchSet_forceOn_singleton_of_notMem h
    simp only [kap, hTs]
    refine Finset.prod_congr rfl fun e he => ?_
    have hne : e ≠ a := fun hh => ha (hh ▸ he)
    rw [forceOn_apply_of_notMem (S := ({(a : Sym2 V)} : Set (Sym2 V))) (by simpa using hne)]

/-- **The key one-coordinate computation.**  If `G` is invariant under changing the single
coordinate `a` (in particular `G` is measurable for the `σ`-algebra of the other coordinates),
then averaging `G · 1{ω a ∈ t a}` factorises. -/
theorem lintegral_mul_eval_of_invariant {π : Sym2 V → unitInterval} {a : Sym2 V}
    {t : Sym2 V → Set Prop} {G : Config V → ℝ≥0∞}
    (hG : Measurable G)
    (hinv : ∀ η ω : Config V, G (forceOn {a} η ω) = G ω) :
    ∫⁻ ω, G ω * (if ω a ∈ t a then 1 else 0) ∂(edgeMeasure π)
      = bfun π t a * ∫⁻ ω, G ω ∂(edgeMeasure π) := by
  classical
  have hfac : Measurable[blockSigma ({(a : Sym2 V)} : Set (Sym2 V))ᶜ]
      (forceOn ({(a : Sym2 V)} : Set (Sym2 V)) (∅ : Config V)) :=
    measurable_forceOn_block _ _
  have hGblock : Measurable[blockSigma ({(a : Sym2 V)} : Set (Sym2 V))ᶜ] G := by
    have h := hG.comp hfac
    convert h using 1
    funext ω
    exact (hinv ∅ ω).symm
  have hcoord : Measurable[coordinateSigma a] fun ω : Config V => ω a :=
    measurable_iff_comap_le.mpr le_rfl
  have hind' : Measurable (fun p : Prop => if p ∈ t a then (1 : ℝ≥0∞) else 0) := by
    exact Measurable.ite (by measurability) measurable_const measurable_const
  have hc_coord : Measurable[coordinateSigma a]
      fun ω : Config V => if ω a ∈ t a then (1 : ℝ≥0∞) else 0 :=
    hind'.comp hcoord
  have hc_block : Measurable[blockSigma ({(a : Sym2 V)} : Set (Sym2 V))]
      fun ω : Config V => if ω a ∈ t a then (1 : ℝ≥0∞) else 0 :=
    hc_coord.mono (coordinateSigma_le_block a) le_rfl
  have hind : Indep (blockSigma ({(a : Sym2 V)} : Set (Sym2 V))ᶜ)
      (blockSigma ({(a : Sym2 V)} : Set (Sym2 V))) (edgeMeasure π) :=
    (independent_blocks π ({(a : Sym2 V)} : Set (Sym2 V))).symm
  have hkey := lintegral_mul_eq_lintegral_mul_lintegral_of_independent_measurableSpace
    (μ := edgeMeasure π) (blockSigma_le ({(a : Sym2 V)} : Set (Sym2 V))ᶜ)
    (blockSigma_le ({(a : Sym2 V)} : Set (Sym2 V))) hind hGblock hc_block
  rw [hkey]
  have hindicator : ∫⁻ ω : Config V, (if ω a ∈ t a then (1 : ℝ≥0∞) else 0) ∂(edgeMeasure π)
      = bfun π t a := by
    have h1 : (fun ω : Config V => if ω a ∈ t a then (1 : ℝ≥0∞) else 0)
        = {ω : Config V | ω a ∈ t a}.indicator (fun _ => (1 : ℝ≥0∞)) := by
      funext ω
      rw [Set.indicator_apply]
      simp
    rw [h1, lintegral_indicator (measurableSet_eval t a)]
    simp [edgeMeasure_eval π t (fun e => by measurability) a]
  rw [hindicator, mul_comm]

/-! ## The finite-coordinate integral -/

/-- **The finite-coordinate computation.**  For every finite set `B` of edges and every
measurable family of target sets `t`, the expectation of `kap B` is the product of the
per-edge Bernoulli weights.  The induction step splits the new coordinate `a` into the part where
`a` does not touch the cluster (on which `kap` is invariant by `(P)`, so the coordinate may be
kept) and the part where it does (where it is replaced by the Bernoulli weight); the averaging
step is `lintegral_mul_eval_of_invariant`. -/
theorem lintegral_kap (π : Sym2 V → unitInterval) (o : V) (t : Sym2 V → Set Prop)
    (_ht : ∀ e, MeasurableSet (t e)) (B : Finset (Sym2 V)) :
    ∫⁻ ω, kap π o t B ω ∂(edgeMeasure π) = ∏ e ∈ B, bfun π t e := by
  classical
  induction B using Finset.induction with
  | empty => simp [kap]
  | @insert a B ha ih =>
    set F : Config V → ℝ≥0∞ := kap π o t B with hF
    set iT : Config V → ℝ≥0∞ := fun ω => if a ∈ touchSet ω o then 1 else 0 with hiT
    set iTc : Config V → ℝ≥0∞ := fun ω => if a ∈ touchSet ω o then 0 else 1 with hiTc
    set J1 : Config V → ℝ≥0∞ := fun ω => F ω * (if a ∈ touchSet ω o then bfun π t a else 0)
      with hJ1
    set J2 : Config V → ℝ≥0∞ :=
      fun ω => F ω * (if a ∈ touchSet ω o then 0 else if ω a ∈ t a then 1 else 0) with hJ2
    have hFA : Measurable F := measurable_kap B
    have hiTA : Measurable iT :=
      Measurable.ite (measurableSet_mem_touchSet o a) measurable_const measurable_const
    have hiTcA : Measurable iTc :=
      Measurable.ite (measurableSet_mem_touchSet o a) measurable_const measurable_const
    have hJ1A : Measurable J1 :=
      hFA.mul (Measurable.ite (measurableSet_mem_touchSet o a) measurable_const measurable_const)
    have hJ2A : Measurable J2 :=
      hFA.mul (Measurable.ite (measurableSet_mem_touchSet o a) measurable_const
        (Measurable.ite (measurableSet_eval t a) measurable_const measurable_const))
    have hstep : ∀ ω, kap π o t (insert a B) ω = J1 ω + J2 ω := by
      intro ω
      rw [kap_insert ha ω, hJ1, hJ2, hF]
      by_cases h : a ∈ touchSet ω o
      · simp only [h, ite_eq_left, mul_zero, add_zero]
        exact mul_comm _ _
      · simp only [h, ite_false, mul_zero, zero_add]
        exact mul_comm _ _
    have hA : ∫⁻ ω, J1 ω ∂(edgeMeasure π)
        = bfun π t a * ∫⁻ ω, F ω * iT ω ∂(edgeMeasure π) := by
      have hfun : J1 = fun ω => ((F * iT) ω) * bfun π t a := by
        funext ω
        by_cases h : a ∈ touchSet ω o <;> simp [hJ1, hiT, h, Pi.mul_apply]
      rw [hfun, lintegral_mul_const (bfun π t a) (hFA.mul hiTA), mul_comm]
      simp only [Pi.mul_apply]
    have hB : ∫⁻ ω, J2 ω ∂(edgeMeasure π)
        = bfun π t a * ∫⁻ ω, F ω * iTc ω ∂(edgeMeasure π) := by
      have hfun : J2 = fun ω => ((F * iTc) ω) * (if ω a ∈ t a then 1 else 0) := by
        funext ω
        by_cases h : a ∈ touchSet ω o <;> simp [hJ2, hiTc, h, Pi.mul_apply]
      rw [hfun]
      exact lintegral_mul_eval_of_invariant (hFA.mul hiTcA)
        (fun η ω => kap_indicator_forceOn_singleton ha η ω)
    have hsum : ∫⁻ ω, F ω * iT ω ∂(edgeMeasure π)
          + ∫⁻ ω, F ω * iTc ω ∂(edgeMeasure π) = ∫⁻ ω, F ω ∂(edgeMeasure π) := by
      have h1 : ∫⁻ ω, F ω * iT ω ∂(edgeMeasure π) + ∫⁻ ω, F ω * iTc ω ∂(edgeMeasure π)
          = ∫⁻ ω, (F ω * iT ω + F ω * iTc ω) ∂(edgeMeasure π) :=
        (lintegral_add_left (hFA.mul hiTA) _).symm
      rw [h1]
      have hfun : (fun ω => F ω * iT ω + F ω * iTc ω) = F := by
        funext ω
        rw [← mul_add]
        have hone : iT ω + iTc ω = 1 := by
          by_cases h : a ∈ touchSet ω o <;> simp [hiT, hiTc, h]
        rw [hone, mul_one]
      rw [hfun]
    have hkey : ∫⁻ ω, (J1 ω + J2 ω) ∂(edgeMeasure π) = ∏ e ∈ insert a B, bfun π t e := by
      rw [lintegral_add_left hJ1A, hA, hB, ← mul_add, hsum, ih, Finset.prod_insert ha]
    rw [show ∫⁻ ω, kap π o t (insert a B) ω ∂(edgeMeasure π)
        = ∫⁻ ω, (J1 ω + J2 ω) ∂(edgeMeasure π) from by
      rw [show (fun ω => kap π o t (insert a B) ω) = fun ω => J1 ω + J2 ω from funext hstep]]
    exact hkey

/-! ## The inner measure and the cylinder probability -/

/-- Measurability of the event that the forced configuration lies in a cylinder. -/
theorem measurableSet_forceOn_cyl (o : V) (t : Sym2 V → Set Prop) (e : Sym2 V)
    (ht : MeasurableSet (t e)) :
    MeasurableSet {q : Config V × Config V | forceOn (touchSet q.1 o) q.2 q.1 e ∈ t e} := by
  classical
  have hF : Measurable fun q : Config V × Config V => forceOn (touchSet q.1 o) q.2 q.1 e := by
    refine measurable_to_prop ?_
    have hpre : (fun q : Config V × Config V => forceOn (touchSet q.1 o) q.2 q.1 e) ⁻¹' {True}
        = {q : Config V × Config V | forceOn (touchSet q.1 o) q.2 q.1 e} := by
      ext q; simp
    have hset : {q : Config V × Config V | forceOn (touchSet q.1 o) q.2 q.1 e}
        = ({q : Config V × Config V | e ∈ touchSet q.1 o} ∩ {q : Config V × Config V | q.2 e})
          ∪ ({q : Config V × Config V | e ∉ touchSet q.1 o} ∩
              {q : Config V × Config V | q.1 e}) := by
      ext q
      simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_union]
      exact forceOn_apply _ _ _ e
    rw [hpre, hset]
    refine MeasurableSet.union (MeasurableSet.inter ?_ ?_) (MeasurableSet.inter ?_ ?_)
    · exact (measurableSet_mem_touchSet o e).preimage measurable_fst
    · exact (measurableSet_mem e).preimage measurable_snd
    · exact (measurableSet_mem_touchSet o e).compl.preimage measurable_fst
    · exact (measurableSet_mem e).preimage measurable_fst
  exact hF ht

/-- **The inner measure.**  For a fixed configuration `ω`, the conditional law of
`η ↦ forceOn (touchSet ω o) η ω` is the product of the Bernoulli weights on the edges touching
the cluster of `o`, and of the actual states of `ω` elsewhere. -/
theorem inner_measure_eq_kap (π : Sym2 V → unitInterval) (o : V) (t : Sym2 V → Set Prop)
    (ht : ∀ e, MeasurableSet (t e)) (B : Finset (Sym2 V)) (ω : Config V) :
    (edgeMeasure π) {η : Config V | ∀ e ∈ B, forceOn (touchSet ω o) η ω e ∈ t e}
      = kap π o t B ω := by
  classical
  have hsets : ∀ η : Config V, (∀ e ∈ B, forceOn (touchSet ω o) η ω e ∈ t e) ↔
      (∀ e ∈ B.filter (fun e => e ∈ touchSet ω o), η e ∈ t e) ∧
        (∀ e ∈ B, e ∉ touchSet ω o → ω e ∈ t e) := by
    intro η
    constructor
    · intro H
      refine ⟨?_, ?_⟩
      · intro e he
        simp only [Finset.mem_filter] at he
        have h := H e he.1
        rwa [forceOn_apply_of_mem he.2] at h
      · intro e he hne
        have h := H e he
        rwa [forceOn_apply_of_notMem (S := touchSet ω o) (e := e) (η := η) (ω := ω) hne] at h
    · rintro ⟨H1, H2⟩ e he
      by_cases hS : e ∈ touchSet ω o
      · rw [forceOn_apply_of_mem hS]
        exact H1 e (by simp [hS, he])
      · rw [forceOn_apply_of_notMem (S := touchSet ω o) (e := e) (η := η) (ω := ω) hS]
        exact H2 e he hS
  have hset : {η : Config V | ∀ e ∈ B, forceOn (touchSet ω o) η ω e ∈ t e}
      = if (∀ e ∈ B, e ∉ touchSet ω o → ω e ∈ t e)
        then edgeCyl (B.filter (fun e => e ∈ touchSet ω o)) t else ∅ := by
    by_cases h : ∀ e ∈ B, e ∉ touchSet ω o → ω e ∈ t e
    · rw [ite_eq_left h]
      ext η
      simp only [Set.mem_ofPred_eq, edgeCyl, hsets η, Finset.mem_filter]
      exact and_iff_left h
    · rw [ite_eq_right h]
      ext η
      rw [Set.mem_ofPred_eq, hsets η]
      simp only [Set.mem_empty_iff_false, iff_false, not_and]
      exact fun _ => h
  -- the product identity: replacing the `kap` factors on the touching edges by the Bernoulli
  -- weights leaves the product unchanged
  have hprod : ∀ (D : Finset (Sym2 V)), (∀ e ∈ D, e ∉ touchSet ω o → ω e ∈ t e) →
      (∏ e ∈ D, (if e ∈ touchSet ω o then bfun π t e else if ω e ∈ t e then 1 else 0))
        = ∏ e ∈ D.filter (fun e => e ∈ touchSet ω o),
            bernoulliMeasure (True : Prop) (False : Prop) (π e) (t e) := by
    intro D
    induction D using Finset.induction with
    | empty => simp
    | @insert a D ha ih =>
      intro hD
      rw [Finset.prod_insert ha, Finset.filter_insert]
      by_cases hT : a ∈ touchSet ω o
      · rw [ite_eq_left hT, ite_eq_left hT, Finset.prod_insert (by simp [ha])]
        congr 1
        exact ih fun e he => hD e (Finset.mem_insert_of_mem he)
      · rw [ite_eq_right hT, ite_eq_right hT,
          ite_eq_left (hD a (Finset.mem_insert_self a D) hT), one_mul]
        exact ih fun e he => hD e (Finset.mem_insert_of_mem he)
  rw [hset]
  by_cases h : ∀ e ∈ B, e ∉ touchSet ω o → ω e ∈ t e
  · rw [ite_eq_left h, edgeMeasure_edgeCyl π _ t ht]
    rw [← hprod B h]
    rfl
  · rw [ite_eq_right h, measure_empty]
    have hex : ∃ e ∈ B, e ∉ touchSet ω o ∧ ω e ∉ t e := by
      by_contra hc
      exact h fun e he hne => by
        by_contra hω
        exact hc ⟨e, he, hne, hω⟩
    obtain ⟨e, heB, heS, hω⟩ := hex
    have hzero : kap π o t B ω = 0 := by
      simp only [kap]
      exact Finset.prod_eq_zero heB (by rw [ite_eq_right heS, ite_eq_right hω])
    rw [hzero]

/-! ## The restoration identity -/

theorem measurableSet_forceOn_cyl_finset (o : V) (t : Sym2 V → Set Prop) (B : Finset (Sym2 V))
    (ht : ∀ e, MeasurableSet (t e)) :
    MeasurableSet {q : Config V × Config V | ∀ e ∈ B, forceOn (touchSet q.1 o) q.2 q.1 e ∈ t e} := by
  rw [show {q : Config V × Config V | ∀ e ∈ B, forceOn (touchSet q.1 o) q.2 q.1 e ∈ t e}
      = ⋂ e ∈ B, {q : Config V × Config V | forceOn (touchSet q.1 o) q.2 q.1 e ∈ t e} from by
    ext q; simp]
  exact Finset.measurableSet_biInter B fun e _ => measurableSet_forceOn_cyl o t e (ht e)

theorem measurable_forceOn_touchSet_pair (o : V) :
    Measurable fun q : Config V × Config V => forceOn (touchSet q.1 o) q.2 q.1 := by
  refine measurable_pi_iff.mpr fun e => ?_
  refine measurable_to_prop ?_
  have h : MeasurableSet {q : Config V × Config V | forceOn (touchSet q.1 o) q.2 q.1 e} := by
    have h0 := measurableSet_forceOn_cyl (o := o) (t := fun _ => ({True} : Set Prop)) (e := e)
      (by measurability)
    simpa using h0
  have hpre : (fun q : Config V × Config V => forceOn (touchSet q.1 o) q.2 q.1 e) ⁻¹' {True}
      = {q : Config V × Config V | forceOn (touchSet q.1 o) q.2 q.1 e} := by
    ext q; simp
  rw [hpre]
  exact h

/-- **The cylinder probability of the restored configuration.**  For every finite set `B` of edges
and every measurable family `t`, the probability that the forced configuration is in the cylinder
event `edgeCyl B t` is the product of the Bernoulli weights. -/
theorem cylinder_prob_forceOn_touchSet (π : Sym2 V → unitInterval) (o : V)
    (B : Finset (Sym2 V)) (t : Sym2 V → Set Prop) (ht : ∀ e, MeasurableSet (t e)) :
    ((edgeMeasure π).prod (edgeMeasure π))
      ((fun q : Config V × Config V => forceOn (touchSet q.1 o) q.2 q.1) ⁻¹' edgeCyl B t)
      = ∏ e ∈ B, bernoulliMeasure (True : Prop) (False : Prop) (π e) (t e) := by
  have hpre : (fun q : Config V × Config V => forceOn (touchSet q.1 o) q.2 q.1) ⁻¹' edgeCyl B t
      = {q : Config V × Config V | ∀ e ∈ B, forceOn (touchSet q.1 o) q.2 q.1 e ∈ t e} := rfl
  rw [hpre, Measure.prod_apply (measurableSet_forceOn_cyl_finset o t B ht)]
  rw [show (fun ω => (edgeMeasure π)
        (Prod.mk ω ⁻¹' {q : Config V × Config V | ∀ e ∈ B, forceOn (touchSet q.1 o) q.2 q.1 e ∈ t e}))
      = kap π o t B from funext fun ω => inner_measure_eq_kap π o t ht B ω]
  exact lintegral_kap π o t ht B

/-- **Restoration at the random edge set touching the cluster of the origin.**
If `ω` and `η` are independent with law `edgeMeasure π`, then replacing the state of every edge
touching the cluster `K_0(ω)` of `o` by its state in the independent configuration `η` leaves the
law `edgeMeasure π` unchanged.  Equivalently: resampling the touch set of the origin is a
measure-preserving operation. -/
theorem edgeMeasure_map_forceOn_touchSet (π : Sym2 V → unitInterval) (o : V) :
    ((edgeMeasure π).prod (edgeMeasure π)).map
      (fun q : Config V × Config V => forceOn (touchSet q.1 o) q.2 q.1) = edgeMeasure π := by
  refine eq_edgeMeasure_of_cyl π _ ?_
  intro B t ht
  have hs : MeasurableSet (edgeCyl B t) := by
    rw [show edgeCyl B t = ⋂ e ∈ B, {ω : Config V | ω e ∈ t e} from by ext ω; simp [edgeCyl]]
    exact Finset.measurableSet_biInter B fun e _ => measurable_pi_apply e (ht e)
  rw [Measure.map_apply (measurable_forceOn_touchSet_pair o) hs]
  exact cylinder_prob_forceOn_touchSet π o B t ht

/-- **Random-touch-set resampling, with the pair in the order `(fresh, base)`.**
This resamples the touch set itself. The paper's complementary restoration, which keeps that
set fixed, is not asserted. -/
theorem edgeMeasure_map_forceOn_touchSet' (π : Sym2 V → unitInterval) (o : V) :
    ((edgeMeasure π).prod (edgeMeasure π)).map
      (fun p : Config V × Config V => forceOn (touchSet p.2 o) p.1 p.2) = edgeMeasure π := by
  have hswap : (fun p : Config V × Config V => forceOn (touchSet p.2 o) p.1 p.2)
      = (fun q : Config V × Config V => forceOn (touchSet q.1 o) q.2 q.1) ∘ Prod.swap := rfl
  rw [hswap, ← Measure.map_map (measurable_forceOn_touchSet_pair o) measurable_swap,
    Measure.prod_swap, edgeMeasure_map_forceOn_touchSet]

/-- **Restoration for long-range Bernoulli bond percolation.**  For the law `P_β` of §I.1.2
(edges open independently with probability `1 - exp(-β J e)`), resampling the set of edges
touching the cluster of `o` from an independent copy of `P_β` leaves `P_β` unchanged. -/
theorem longRangeMeasure_map_forceOn_touchSet (J : Sym2 V → ℝ) (hJ : ∀ e, 0 ≤ J e)
    (β : NNReal) (o : V) :
    ((longRangeMeasure J hJ β).prod (longRangeMeasure J hJ β)).map
      (fun p : Config V × Config V => forceOn (touchSet p.2 o) p.1 p.2) =
        longRangeMeasure J hJ β :=
  edgeMeasure_map_forceOn_touchSet' (bernoulliEdgeProb J hJ β) o


end PercLib.CriticalLRP
