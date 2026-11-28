/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Accepted and independently rebuilt from Ultramath `smwznoz6j`, member m7.
Latest independent rebuild at production HEAD `16d9f2aa1e83afeda3fc66117e38ed3352b2e567`; reviewed scratch source `.scratch/review-smwznoz6j/m7/Defs.lean`.
-/

/-
Ultramath swarm `smwznoz6j`, member `m7`, direction `d7` (A: the uncut critical volume tail).

# The uncut critical tail is exactly the uniform-in-radius cutoff tail

Source: Hutchcroft, *Critical long-range percolation I*, arXiv:2508.18807v1, proof of
Proposition I.4.15, Case 3, p. 47:

> Since the triangle condition implies the volume-tail upper bound
> `P_{β_c}(|K| ≥ n) ⪯ n^{-1/2}` [12, 75], ...

Production names that input `SourceModelData.CriticalVolumeTail` (uncut, infinite-lattice law,
pointwise in `n`) and proves that it *implies* every cutoff tail bound
(`cutLaw_tail_le_envelope`).  The converse is what this file proves:

* `SourceModelData.criticalLaw_eq_iSup_cutLaw` — for the increasing, finitely witnessed event
  `{|K_0| ≥ n}`, the *uncut* critical mass is the supremum of the cutoff masses over the
  radius.  Nothing about the tail's size is assumed; only the model fields
  (`K_antitone`, `K_nonneg`, `K_eq_integral`, `exists_error`) that already give
  `M.tendsto_K_atTop_zero`.

Consequently `SourceModelData.criticalVolumeTail_iff_uniform_cutTail`:

  `CriticalVolumeTail C ↔ ∀ r > 0, ∀ n ≥ 1, P_{β_c,r}(|K_0| ≥ n) ≤ C / √n`.

So the cited leaf is *not* a statement about a new object: it is exactly the statement that the
cutoff tails admit one constant `C` **uniform in the cutoff radius**.  Every proof of the leaf
must therefore produce `r`-uniform control; and, conversely, a bound at each fixed `r` with an
`r`-dependent constant is provably not enough (that is what the equivalence delimits).

Everything is kernel-checked; the only external inputs are the model fields.

Layout of this file (the run's convention puts the new definitions in `Defs.lean`; the theorems
that use them are here too, so that the artifact elaborates on its own): §1 the new edge
probability `uncutProb`, §2 the finite-edge cylinder tail `clusterEdgeCyl`, §3 the identification
of the tail event with `clusterCardLarge`, §4 the sup identity, §5 the uniform-in-radius
equivalence, §6 the general identity for increasing finitely witnessed events.
-/
module

public import PercLib.CriticalLRP.Analysis.SecondMomentCase3.CriticalVolumeTail.Main
public import PercLib.CriticalLRP.CountableProduct.LRPTailLevelSets
public import PercLib.CriticalLRP.MomentMonotonicity.SourceModelCutoffLimit
public import PercLib.CriticalLRP.Analysis.Route3.Percolation
public import PercLib.Probability.FiniteContinuity
public import PercLib.CriticalLRP.BK.Association

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.hashCommand false
set_option linter.style.longLine false
set_option linter.style.haveILetI false

@[expose] public section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP.Orchestration

namespace SourceModelData

variable (M : SourceModelData)

/-! ## §1 The uncut edge probability -/

/-- The edge-open profile of the *uncut* law at `β_c`.  `M.cutProb r` is the same construction
with the cutoff kernel, and `M.criticalLaw = edgeMeasure M.uncutProb` definitionally. -/
noncomputable def uncutProb : Sym2 M.V → unitInterval :=
  bernoulliEdgeProb M.kernel M.kernel_nonneg M.betaCrit

/-- The uncut critical law is the Bernoulli bond law of `uncutProb`. -/
theorem criticalLaw_eq_edgeMeasure : M.criticalLaw = edgeMeasure M.uncutProb := rfl

/-- `M.cutProb r` tends to `M.uncutProb` at every edge.  The real-valued form. -/
theorem tendsto_cutProb_real (e : Sym2 M.V) :
    Tendsto (fun r : ℝ => ((M.cutProb r e : unitInterval) : ℝ)) atTop
      (𝓝 ((M.uncutProb e : unitInterval) : ℝ)) := by
  have hk : Tendsto (fun r : ℝ => M.cutKernel r e) atTop (𝓝 (M.kernel e)) :=
    M.cutKernel_tendsto e
  have hcont : Continuous fun x : ℝ => 1 - Real.exp (-((M.betaCrit : ℝ) * x)) := by
    fun_prop
  have h := (hcont.tendsto (M.kernel e)).comp hk
  rw [show ((fun x : ℝ => 1 - Real.exp (-((M.betaCrit : ℝ) * x))) ∘ fun r : ℝ => M.cutKernel r e)
      = fun r : ℝ => 1 - Real.exp (-((M.betaCrit : ℝ) * M.cutKernel r e)) from rfl] at h
  simpa [SourceModelData.cutProb, SourceModelData.uncutProb,
    PercLib.CriticalLRP.bernoulliEdgeProb_coe] using h

/-- `M.cutProb r` tends to `M.uncutProb` at every edge, as open probabilities. -/
theorem tendsto_cutProb (e : Sym2 M.V) :
    Tendsto (fun r : ℝ => M.cutProb r e) atTop (𝓝 (M.uncutProb e)) :=
  tendsto_subtype_rng.mpr (M.tendsto_cutProb_real e)

/-! ## §2 The finite-edge cylinder tail -/

/-- The tail event `{|K_0| ≥ n}` cut down to a finite vertex window `Λ` and a finite edge set
`E`, read as a predicate on the configuration `E` only.  This is the exact shape to which the
finite-product cylinder formula applies: the probability depends on the edge probabilities of
`E` alone. -/
def clusterEdgeCyl (Λ : Finset M.V) (E : Finset (Sym2 M.V)) (n : ℕ) : Set (Set ↥E) :=
  {c | n ≤ (cluster (Subtype.val '' (c : Set ↥E)) (0 : M.V) ∩ (Λ : Set M.V)).ncard}

/-- `E`-restriction of a configuration. -/
theorem image_val_preimage (E : Finset (Sym2 M.V)) (ω : Config M.V) :
    (Subtype.val '' ((Subtype.val ⁻¹' (ω : Set (Sym2 M.V))) : Set ↥E) : Set (Sym2 M.V))
      = ω ∩ (E : Set (Sym2 M.V)) := by
  rw [Set.image_preimage_eq_inter_range, Subtype.range_coe]

/-- The finite-edge cylinder tail *is* the `E`-cylinder set `clusterEdgeCyl`. -/
theorem clusterEdgeCyl_eq (Λ : Finset M.V) (E : Finset (Sym2 M.V)) (n : ℕ) :
    {ω : Config M.V |
        n ≤ (cluster (ω ∩ (E : Set (Sym2 M.V))) (0 : M.V) ∩ (Λ : Set M.V)).ncard}
      = {ω : Config M.V | (Subtype.val ⁻¹' ω : Set ↥E) ∈ M.clusterEdgeCyl Λ E n} := by
  ext ω
  simp only [Set.mem_ofPred_eq, SourceModelData.clusterEdgeCyl]
  rw [image_val_preimage]

/-- **The finite-edge cylinder tails converge.**  At a fixed finite edge set the tail mass is a
polynomial in the (finitely many) edge probabilities, and those converge to the uncut ones by
`M.tendsto_cutProb`. -/
theorem tendsto_clusterEdgeCyl (Λ : Finset M.V) (E : Finset (Sym2 M.V)) (n : ℕ) :
    Tendsto
      (fun r : ℝ => M.cutLaw r {ω : Config M.V |
        n ≤ (cluster (ω ∩ (E : Set (Sym2 M.V))) (0 : M.V) ∩ (Λ : Set M.V)).ncard})
      atTop
      (𝓝 (M.criticalLaw {ω : Config M.V |
        n ≤ (cluster (ω ∩ (E : Set (Sym2 M.V))) (0 : M.V) ∩ (Λ : Set M.V)).ncard})) := by
  have h := PercLib.Probability.tendsto_prodBernoulli_cylinder (p := fun r : ℝ => M.cutProb r)
    (q := M.uncutProb) (fun e => M.tendsto_cutProb e) E (M.clusterEdgeCyl Λ E n)
  rw [M.clusterEdgeCyl_eq Λ E n]
  simpa [E1Sign.cutLaw_eq, SourceModelData.criticalLaw_eq_edgeMeasure,
    PercLib.CriticalLRP.edgeMeasure, PercLib.Percolation.Bond.law] using h

/-- The finite-edge cylinder tail sits inside `{|K_0| ≥ n}`. -/
theorem clusterEdgeCyl_subset (Λ : Finset M.V) (E : Finset (Sym2 M.V)) (n : ℕ) :
    {ω : Config M.V |
        n ≤ (cluster (ω ∩ (E : Set (Sym2 M.V))) (0 : M.V) ∩ (Λ : Set M.V)).ncard}
      ⊆ clusterCardLarge (0 : M.V) n := by
  intro ω hω
  classical
  have hfin : (cluster (ω ∩ (E : Set (Sym2 M.V))) (0 : M.V) ∩ (Λ : Set M.V)).Finite :=
    Λ.finite_toSet.subset Set.inter_subset_right
  refine ⟨hfin.toFinset, ?_, ?_⟩
  · rw [← Set.ncard_eq_toFinset_card _ hfin]
    exact hω
  · intro y hy
    have hy' : y ∈ cluster (ω ∩ (E : Set (Sym2 M.V))) (0 : M.V) ∩ (Λ : Set M.V) :=
      (Set.Finite.mem_toFinset hfin).mp hy
    exact connects_mono (fun e he => he.1) (mem_cluster_iff.mp hy'.1)

/-! ## §3 `{|K_0| ≥ n}` is the cluster-cardinality level set -/

/-- Production's tail event `{n ≤ |K_0|}` is the level set `clusterCardLarge 0 n`. -/
theorem clusterCardLarge_iff_le_clusterVol (ω : Config M.V) (n : ℕ) :
    ω ∈ clusterCardLarge (0 : M.V) n ↔ (n : ℝ≥0∞) ≤ clusterVol ω (0 : M.V) := by
  classical
  constructor
  · rintro ⟨t, ht, hconn⟩
    have hsub : (t : Set M.V) ⊆ cluster ω (0 : M.V) :=
      fun y hy => mem_cluster_iff.mpr (hconn y hy)
    have h1 : (t : Set M.V).encard ≤ (cluster ω (0 : M.V)).encard := Set.encard_le_encard hsub
    rw [Set.encard_coe_eq_coe_finsetCard] at h1
    have h2 : ((n : ℕ) : ℕ∞) ≤ (t.card : ℕ∞) := by exact_mod_cast ht
    have h3 : ((n : ℕ) : ℕ∞) ≤ (cluster ω (0 : M.V)).encard := le_trans h2 h1
    have h4 : ((n : ℕ) : ℝ≥0∞) ≤ ((cluster ω (0 : M.V)).encard : ℝ≥0∞) := by exact_mod_cast h3
    rwa [clusterVol_eq_encard]
  · intro h
    have h' : ((n : ℕ) : ℕ∞) ≤ (cluster ω (0 : M.V)).encard := by
      have := h
      rw [clusterVol_eq_encard] at this
      exact_mod_cast this
    obtain ⟨t, hts, hte⟩ := Set.exists_subset_encard_eq (s := cluster ω (0 : M.V))
      (k := ((n : ℕ) : ℕ∞)) h'
    have hne : t.encard ≠ ⊤ := by
      rw [hte]
      exact ENat.natCast_ne_top n
    have hfin : t.Finite := by
      by_contra hinf
      exact hne (Set.encard_eq_top_iff.mpr hinf)
    refine ⟨hfin.toFinset, ?_, ?_⟩
    · have hc : ((hfin.toFinset.card : ℕ) : ℕ∞) = ((n : ℕ) : ℕ∞) := by
        rw [← Set.encard_coe_eq_coe_finsetCard, Set.Finite.coe_toFinset]
        exact hte
      have hc' : hfin.toFinset.card = n := by exact_mod_cast hc
      omega
    · intro y hy
      exact mem_cluster_iff.mp (hts ((Set.Finite.mem_toFinset hfin).mp hy))

theorem eq_tailEvent (n : ℕ) :
    clusterCardLarge (0 : M.V) n
      = {ω : Config M.V | (n : ℝ≥0∞) ≤ clusterVol ω (0 : M.V)} :=
  Set.ext fun ω => M.clusterCardLarge_iff_le_clusterVol ω n

/-! ## §4 The uncut mass is the supremum of the cutoff masses -/

/-- Every cutoff mass of an increasing, finitely witnessed event is at most the uncut mass. -/
theorem cutLaw_le_criticalLaw_clusterCardLarge {r : ℝ} (hr : 0 < r) (n : ℕ) :
    M.cutLaw r (clusterCardLarge (0 : M.V) n)
      ≤ M.criticalLaw (clusterCardLarge (0 : M.V) n) :=
  cutLaw_le_criticalLaw M hr (measurableSet_clusterCardLarge (0 : M.V) n)
    (clusterCardLarge_upper (0 : M.V) n)

/-- **The uncut critical cluster-volume tail is the supremum of the cutoff tails over the
radius.**  The cutoff tails are bounded by the uncut one at every radius
(`cutLaw_le_criticalLaw`); the substance is the converse, which decomposes the uncut mass into
finite vertex windows (`edgeMeasure_clusterCardLarge_eq_iSup`), then into finite edge sets
(`edgeMeasure_clusterTail_eq_iSup_finset_edges`), uses the cylinder convergence
`tendsto_clusterEdgeCyl`, and observes that each finite cylinder sits inside `{|K_0| ≥ n}`
(`clusterEdgeCyl_subset`). -/
theorem criticalLaw_le_iSup_cutLaw (n : ℕ) :
    M.criticalLaw (clusterCardLarge (0 : M.V) n)
      ≤ ⨆ r : ℝ, ⨆ (_ : 0 < r), M.cutLaw r (clusterCardLarge (0 : M.V) n) := by
  classical
  rw [SourceModelData.criticalLaw_eq_edgeMeasure,
    edgeMeasure_clusterCardLarge_eq_iSup M.uncutProb (0 : M.V) n]
  refine iSup_le fun Λ => ?_
  rw [edgeMeasure_clusterTail_eq_iSup_finset_edges M.uncutProb (0 : M.V) Λ n]
  refine iSup_le fun E => ?_
  have hlim := M.tendsto_clusterEdgeCyl Λ E n
  have hbound : (edgeMeasure M.uncutProb) {ω : Config M.V |
        n ≤ (cluster (ω ∩ (E : Set (Sym2 M.V))) (0 : M.V) ∩ (Λ : Set M.V)).ncard}
      ≤ ⨆ r : ℝ, ⨆ (_ : 0 < r), M.cutLaw r (clusterCardLarge (0 : M.V) n) := by
    refine le_of_tendsto hlim ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
    refine le_trans (measure_mono (M.clusterEdgeCyl_subset Λ E n)) ?_
    exact le_trans
      (le_iSup (fun _ : 0 < r => M.cutLaw r (clusterCardLarge (0 : M.V) n)) hr)
      (le_iSup (fun r : ℝ => ⨆ (_ : 0 < r), M.cutLaw r (clusterCardLarge (0 : M.V) n)) r)
  exact hbound

/-- **Equality form**: for the cluster-volume tail event, the uncut critical mass *is* the
supremum of the cutoff masses. -/
theorem criticalLaw_eq_iSup_cutLaw (n : ℕ) :
    M.criticalLaw (clusterCardLarge (0 : M.V) n)
      = ⨆ r : ℝ, ⨆ (_ : 0 < r), M.cutLaw r (clusterCardLarge (0 : M.V) n) := by
  refine le_antisymm (M.criticalLaw_le_iSup_cutLaw n) ?_
  refine iSup_le fun r => iSup_le fun hr => ?_
  exact cutLaw_le_criticalLaw_clusterCardLarge M hr n

/-! ## §5 The uniform-in-radius form of the cited leaf -/

/-- **The cited leaf is exactly a uniform-in-radius cutoff bound.**  With
`Analysis.Route3.tailEnvelope C n = C/√n`, the uncut tail envelope `CriticalVolumeTail C` is
equivalent to the same envelope holding for the cutoff law at *every* positive radius with one
and the same constant `C`.

Forward: `cutLaw_tail_le_envelope` (production).  Backward: the uncut mass is the supremum of
the cutoff masses (`criticalLaw_eq_iSup_cutLaw`), so a bound valid at every radius bounds it. -/
theorem criticalVolumeTail_iff_uniform_cutTail {C : ℝ} :
    M.CriticalVolumeTail C ↔
      ∀ r : ℝ, 0 < r → ∀ n : ℕ, 1 ≤ n →
        M.cutLaw r {ω : Config M.V | (n : ℝ≥0∞) ≤ clusterVol ω (0 : M.V)}
          ≤ Analysis.Route3.tailEnvelope C n := by
  constructor
  · intro h r hr n hn
    exact M.cutLaw_tail_le_envelope hr h n hn
  · intro h n hn
    rw [← M.eq_tailEvent n]
    refine le_trans (M.criticalLaw_le_iSup_cutLaw n) ?_
    refine iSup_le fun r => iSup_le fun hr => ?_
    rw [M.eq_tailEvent n]
    exact h r hr n hn

/-- **Consumer form of the Case-3 leaf.**  The p.47 moment gap with the source's own constant
`(4C+1)⁻³`, valid at *every* positive radius with that one constant, follows from the
uniform cutoff tail.  This is the form a Case-3 consumer can use without ever naming the uncut
`CriticalVolumeTail`. -/
theorem momentGap_of_uniform_cutTail {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ r : ℝ, 0 < r → ∀ n : ℕ, 1 ≤ n →
      M.cutLaw r {ω : Config M.V | (n : ℝ≥0∞) ≤ clusterVol ω (0 : M.V)}
        ≤ Analysis.Route3.tailEnvelope C n)
    {r : ℝ} (hr : 0 < r) (h2 : M.cutMoment 2 r ≠ ⊤) :
    (Analysis.Route3.ratioConst C)⁻¹ * (M.cutMassAt r 0).toReal ^ 3
      ≤ (M.cutMoment 2 r).toReal :=
  M.momentGap_of_volumeTail hC
    ((M.criticalVolumeTail_iff_uniform_cutTail (C := C)).mpr h) hr h2

/-! ## §6 The general cutoff-limit identity

The argument of §4 only used that `{|K_0| ≥ n}` is increasing and finitely witnessed.  We record
the general statement, since every event the paper's off-corner analysis raises
(`{Connects ω x y}`, cluster-volume tails, ...) has that form. -/

/-- Cylinder masses converge to the uncut cylinder mass.  A finite set of edges is fixed, so the
mass is a finite product of edge probabilities; those converge by `M.tendsto_cutProb`. -/
theorem tendsto_cutLaw_cyl {s : Finset (Sym2 M.V)} {C : Set (Config M.V)} :
    Tendsto (fun r : ℝ => M.cutLaw r {ω : Config M.V | ω ∩ (s : Set (Sym2 M.V)) ∈ C})
      atTop (𝓝 (M.criticalLaw {ω : Config M.V | ω ∩ (s : Set (Sym2 M.V)) ∈ C})) := by
  have hset : {ω : Config M.V | ω ∩ (s : Set (Sym2 M.V)) ∈ C}
      = {ω : Config M.V |
          (Subtype.val ⁻¹' ω : Set ↥s) ∈ {η : Set ↥s | Subtype.val '' η ∈ C}} := by
    ext ω
    simp only [Set.mem_ofPred_eq]
    rw [image_val_preimage]
  rw [hset]
  have h := PercLib.Probability.tendsto_prodBernoulli_cylinder (p := fun r : ℝ => M.cutProb r)
    (q := M.uncutProb) (fun e => M.tendsto_cutProb e) s {η : Set ↥s | Subtype.val '' η ∈ C}
  simpa [E1Sign.cutLaw_eq, SourceModelData.criticalLaw_eq_edgeMeasure,
    PercLib.CriticalLRP.edgeMeasure, PercLib.Percolation.Bond.law] using h

/-- **The cutoff-limit identity for increasing finitely witnessed events.**  The uncut critical
mass of such an event is the supremum of its cutoff masses over the radius.  Every model field
enters through `M.tendsto_K_atTop_zero`; no estimate on the event is assumed. -/
theorem criticalLaw_eq_iSup_cutLaw_of_finiteWitness {A : Set (Config M.V)}
    (hA : IsUpperSet A) (hfA : Percolation.FiniteWitness A) :
    M.criticalLaw A = ⨆ r : ℝ, ⨆ (_ : 0 < r), M.cutLaw r A := by
  classical
  letI := Encodable.ofCountable (Sym2 M.V)
  have hunion := Percolation.witness_eq_union (E := Sym2 M.V) A hA hfA
  have hmono : Monotone fun n : ℕ => {ω : Config M.V |
      ω ∩ (Percolation.edgeExhaustion (E := Sym2 M.V) n : Set (Sym2 M.V)) ∈ A} := by
    intro m n hmn ω hω
    refine hA (Set.inter_subset_inter (subset_refl (ω : Set (Sym2 M.V)))
      (Finset.coe_subset.mpr (Percolation.edgeExhaustion_mono hmn))) ?_
    change ω ∩ (Percolation.edgeExhaustion (E := Sym2 M.V) m : Set (Sym2 M.V)) ∈ A
    exact hω
  have hstep : M.criticalLaw A
      = ⨆ n : ℕ, M.criticalLaw {ω : Config M.V |
          ω ∩ (Percolation.edgeExhaustion (E := Sym2 M.V) n : Set (Sym2 M.V)) ∈ A} := by
    conv_lhs => rw [hunion]
    exact (iSup_measure_iUnion (μ := M.criticalLaw) hmono).symm
  refine le_antisymm ?_ (iSup_le fun r => iSup_le fun hr => ?_)
  · rw [hstep]
    refine iSup_le fun n => ?_
    have hlim := M.tendsto_cutLaw_cyl (s := Percolation.edgeExhaustion (E := Sym2 M.V) n)
      (C := A)
    refine le_of_tendsto hlim ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
    refine le_trans (measure_mono ?_) (le_trans
      (le_iSup (fun _ : 0 < r => M.cutLaw r A) hr)
      (le_iSup (fun r : ℝ => ⨆ (_ : 0 < r), M.cutLaw r A) r))
    intro ω hω
    exact hA Set.inter_subset_left hω
  · exact cutLaw_le_criticalLaw M hr
      (Percolation.measurableSet_finiteWitness A hA hfA) hA

/-- **Cross-check** with production's `iSup_connects_eq`: the general identity also holds for the
connection event `{x ↔ y}`, there with the supremum restricted to positive radii.  The two
statements are independent proofs of the same limit at a place where production already had a
direct argument, which is the reason to trust the general form above. -/
theorem criticalLaw_eq_iSup_cutLaw_connSet (x y : M.V) :
    M.criticalLaw (connSet x y) = ⨆ r : ℝ, ⨆ (_ : 0 < r), M.cutLaw r (connSet x y) :=
  M.criticalLaw_eq_iSup_cutLaw_of_finiteWitness (isUpper_connSet x y)
    (finiteWitness_connSet x y)

end SourceModelData

end PercLib.CriticalLRP.Orchestration

#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.criticalLaw_eq_edgeMeasure
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.tendsto_cutProb_real
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.tendsto_cutProb
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.clusterEdgeCyl_eq
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.tendsto_clusterEdgeCyl
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.clusterEdgeCyl_subset
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.clusterCardLarge_iff_le_clusterVol
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.eq_tailEvent
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.criticalLaw_le_iSup_cutLaw
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.criticalLaw_eq_iSup_cutLaw
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.criticalVolumeTail_iff_uniform_cutTail
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.momentGap_of_uniform_cutTail
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.tendsto_cutLaw_cyl
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.criticalLaw_eq_iSup_cutLaw_of_finiteWitness
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.criticalLaw_eq_iSup_cutLaw_connSet
