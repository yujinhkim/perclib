/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

# Directed limit from finite fresh sets to the full queried edge set.

Direction 1 (swarm `smwpbvro2`, member m1).  `PoissonBoundStep` bounds the fresh moment of a
*finite* fresh edge set `S σ ⊆ freshEdgeSet σ`.  This file removes that restriction when the
fresh sets come from a directed (monotone, ℕ-indexed) exhaustion `exh σ : ℕ → Finset (Sym2 V)`
of the state's querying set `freshEdgeSet σ`: the extended power
`epow t ((freshEdgeSet σ ∩ ω).encard)` is the pointwise supremum of `t ^ openCount (exh σ j) ω`,
so monotone convergence upgrades the finite estimate to the full (possibly infinite) queried
set, with the *same* deterministic budget `|T_σ| · M`.

Consequences recorded here:
* the exhaustion of the queried set by finite sets is possible without any degree bound because
  the ambient edge set is countable;
* `epow t (|gen|) ≤ epow t ((freshEdgeSet σ ∩ ω).encard)` on a finite state fibre, so the
  extended-power moment of the true generation is bounded by the quantity estimated here.

No finiteness of the generations, of the frontier, or of the cluster is assumed or concluded.
-/
module

public import PercLib.CriticalLRP.Exploration.BFS.Poisson.Fresh.Defs
public import PercLib.CriticalLRP.Exploration.BFS.Limit
public import Mathlib.MeasureTheory.Constructions.Polish.Basic

set_option autoImplicit false

@[expose] public section

noncomputable section

open MeasureTheory Set PercLib.Percolation.Bond Finset
open PercLib.Probability
open PercLib.Probability.AdaptedReveal
open scoped ENNReal BigOperators

namespace PercLib.CriticalLRP.Exploration.BFS

/-- `openCount` is monotone in the finite edge set. -/
theorem openCount_mono {ι : Type*} {S S' : Finset ι} (h : S ⊆ S') (ω : Set ι) :
    openCount S ω ≤ openCount S' ω := by
  classical
  have hsub : S.filter (fun e => e ∈ ω) ⊆ S'.filter (fun e => e ∈ ω) := by
    intro e he
    exact Finset.mem_filter.mpr ⟨h (Finset.mem_filter.mp he).1, (Finset.mem_filter.mp he).2⟩
  exact Finset.card_le_card hsub

/-- The open part of a finite edge set has extended cardinality `openCount`. -/
theorem encard_inter_eq_openCount {ι : Type*} (S : Finset ι) (ω : Set ι) :
    ((S : Set ι) ∩ ω).encard = (openCount S ω : ℕ∞) := by
  classical
  have hset : ((S : Set ι) ∩ ω) = ((S.filter (fun e => e ∈ ω) : Finset ι) : Set ι) := by
    ext e
    simp only [Set.mem_inter_iff, Finset.mem_coe, Finset.mem_filter]
  rw [hset, Set.encard_coe_eq_coe_finsetCard]
  rfl

/-- The extended power of the open count at a finite edge set. -/
theorem epow_encard_inter {ι : Type*} (t : ℝ≥0∞) (ht : 1 ≤ t) (S : Finset ι) (ω : Set ι) :
    epow t (((S : Set ι) ∩ ω).encard) = t ^ openCount S ω := by
  rw [encard_inter_eq_openCount, epow_natCast t ht (openCount S ω), ENNReal.rpow_natCast]

/-- **Directed limit of the extended powers.**  For a monotone ℕ-indexed family of finite edge
sets, the supremum of `epow t` of the open counts is `epow t` of the open count of the union. -/
theorem iSup_epow_encard_inter {ι : Type*} (t : ℝ≥0∞) (ht : 1 ≤ t) (S : ℕ → Finset ι)
    (hmono : Monotone S) (ω : Set ι) :
    (⨆ j, epow t (((S j : Set ι) ∩ ω).encard))
      = epow t (((⋃ j, (S j : Set ι)) ∩ ω).encard) := by
  have hmono' : Monotone fun j => ((S j : Set ι) ∩ ω) := by
    intro i j hij x hx
    exact ⟨hmono hij (by simpa using hx.1), hx.2⟩
  have hunion : ((⋃ j, (S j : Set ι)) ∩ ω) = ⋃ j, ((S j : Set ι) ∩ ω) := Set.iUnion_inter ω _
  rw [hunion]
  rw [encard_iUnion_nat_eq_iSup hmono']
  exact (epow_iSup t ht (fun j => ((S j : Set ι) ∩ ω).encard)).symm

/-- `t ^ openCount S` is measurable for the canonical `σ`-algebra on `Set ι`. -/
theorem measurable_pow_openCount {ι : Type*} (t : ℝ≥0∞) (S : Finset ι) :
    Measurable fun ω : Set ι => t ^ openCount S ω := by
  classical
  have h : (fun ω : Set ι => t ^ openCount S ω) = fun ω => ∏ e ∈ S, powOpen t ω e :=
    funext fun ω => (prod_powOpen_eq_pow_openCount S t ω).symm
  rw [h]
  refine Finset.measurable_prod S (fun e _ => ?_)
  have hpoint : (fun ω : Set ι => powOpen t ω e)
      = fun ω => t * ({ω : Set ι | e ∈ ω}.indicator (1 : Set ι → ℝ≥0∞)) ω
          + ({ω : Set ι | e ∈ ω}ᶜ.indicator (1 : Set ι → ℝ≥0∞)) ω := by
    funext ω
    by_cases hω : e ∈ ω
    · simp [powOpen, powOpenFun, hω]
    · simp [powOpen, powOpenFun, hω]
  rw [hpoint]
  exact ((measurable_const.mul (Measurable.indicator measurable_const (measurableSet_mem e))).add
    (Measurable.indicator measurable_const (measurableSet_mem e).compl))

/-! ### The state level -/

variable {V : Type*}

/-- On a finite state fibre the querying set of the state is exactly the BFS queried set. -/
theorem freshEdgeSet_some_eq_queried [Countable V] {ω : Config V} {o : V} {k : ℕ}
    {Q T : Finset V}
    (h : finState ω o k = some (Q, T)) :
    freshEdgeSet (some (Q, T)) = queried ω o k := by
  obtain ⟨hQ, hT⟩ := finState_eq_some_iff.mp h
  have h1 : edgeSet (T : Set V) ((Q : Set V) ∪ (T : Set V))ᶜ = queried ω o k := by
    rw [queried, U_eq_compl, ← hQ, ← hT]
  have h2 : revealFin (some (Q, T)) = revealed ω o k := by
    ext e
    simp only [revealed, revealFin, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨v, hv, hve⟩
      exact ⟨v, hQ ▸ hv, hve⟩
    · rintro ⟨v, hv, hve⟩
      exact ⟨v, hQ ▸ hv, hve⟩
  rw [freshEdgeSet, h1, h2]
  ext e
  constructor
  · exact fun h => h.1
  · intro he
    exact ⟨he, fun hrev => Set.disjoint_left.mp (disjoint_revealed_queried ω o k) hrev he⟩

/-- On a finite state fibre the true generation is dominated, in extended cardinality, by the
open part of the state's querying set. -/
theorem encard_gen_le_encard_freshEdgeSet_inter [Countable V] {ω : Config V} {o : V} {k : ℕ}
    {Q T : Finset V}
    (h : finState ω o k = some (Q, T)) :
    (gen ω o k).encard ≤ (freshEdgeSet (some (Q, T)) ∩ ω).encard := by
  rw [freshEdgeSet_some_eq_queried h]
  exact gen_encard_le_queried ω o k

/-- **The full directed-limit one-step estimate.**  If the state's querying set
`freshEdgeSet σ` is exhausted by a monotone family of finite edge sets `exh σ j`, then the
extended-power fresh moment `∫ G · epow t (|freshEdgeSet σ ∩ ω|)` is bounded by the history sum
with the deterministic row-sum budget `|T_σ| · M`.

This is the infinite-queried-set form of `Lemma 4.4`: the finite-fresh-set estimate is applied
to each `exh σ j` (all with the *same* budget, so no interchange of `∑'` and `⨆` is needed) and
monotone convergence takes the supremum.  In particular no degree bound and no finiteness of
`A k` or `P k` is assumed. -/
theorem lintegral_bfs_epow_le_rowBound [Countable V] (p : Sym2 V → unitInterval) (o : V) (k : ℕ)
    (G : Config V → ℝ≥0∞)
    (H : (σ : FinState V) → Set (revealFin σ) → ℝ≥0∞)
    (hH : ∀ σ, Measurable (H σ))
    (hG : ∀ ω, G ω = H (finState ω o k) (blockRestrict (revealFin (finState ω o k)) ω))
    (exh : FinState V → ℕ → Finset (Sym2 V))
    (hmono : ∀ σ, Monotone (exh σ))
    (hUnion : ∀ σ, (⋃ j, ((exh σ j : Finset (Sym2 V)) : Set (Sym2 V))) = freshEdgeSet σ)
    (hdisj : ∀ σ j, Disjoint (((exh σ j : Finset (Sym2 V)) : Set (Sym2 V))) (revealFin σ))
    (t : ℝ≥0∞) (ht : 1 ≤ t) (ht_top : t ≠ ⊤) {M : ℝ} (hM : UniformRowBound p M) :
    ∫⁻ ω, G ω * epow t ((freshEdgeSet (finState ω o k) ∩ ω).encard) ∂(prodBernoulli p)
      ≤ ∑' σ : FinState V,
          (∫⁻ ω in {ω | finState ω o k = σ}, G ω ∂(prodBernoulli p))
            * ENNReal.ofReal (Real.exp ((t.toReal - 1) * ((finStateCard σ : ℝ) * M))) := by
  classical
  have hmG : Measurable G := by
    rw [funext hG]
    exact measurable_history (finRevealData o k) H hH
  have hfun : ∀ ω : Config V, epow t ((freshEdgeSet (finState ω o k) ∩ ω).encard)
      = ⨆ j, t ^ openCount (exh (finState ω o k) j) ω := by
    intro ω
    have h := iSup_epow_encard_inter t ht (exh (finState ω o k)) (hmono _) ω
    rw [hUnion (finState ω o k)] at h
    rw [← h]
    exact iSup_congr fun j => epow_encard_inter t ht (exh (finState ω o k) j) ω
  have hsub : ∀ (σ : FinState V) (j : ℕ), ((exh σ j : Finset (Sym2 V)) : Set (Sym2 V))
      ⊆ freshEdgeSet σ := by
    intro σ j
    rw [← hUnion σ]
    exact Set.subset_iUnion (fun j => ((exh σ j : Finset (Sym2 V)) : Set (Sym2 V))) j
  have hstep : ∀ j, ∫⁻ ω, G ω * t ^ openCount (exh (finState ω o k) j) ω
        ∂(prodBernoulli p)
      ≤ ∑' σ : FinState V,
          (∫⁻ ω in {ω | finState ω o k = σ}, G ω ∂(prodBernoulli p))
            * ENNReal.ofReal (Real.exp ((t.toReal - 1) * ((finStateCard σ : ℝ) * M))) := by
    intro j
    refine lintegral_bfs_adapted_pgf_le_rowBound p o k G H hH hG (fun σ => exh σ j)
      (fun σ => hdisj σ j) (fun σ e he => ?_) t ht ht_top hM
    exact hsub σ j (by simpa using he)
  have hcongr : ∫⁻ ω, G ω * epow t ((freshEdgeSet (finState ω o k) ∩ ω).encard)
        ∂(prodBernoulli p)
      = ∫⁻ ω, ⨆ j, G ω * t ^ openCount (exh (finState ω o k) j) ω
        ∂(prodBernoulli p) := by
    refine lintegral_congr fun ω => ?_
    rw [hfun ω, ENNReal.mul_iSup]
  have hmeas_pow : ∀ j, Measurable fun ω : Config V =>
      t ^ openCount (exh (finState ω o k) j) ω := by
    intro j
    have hrep : (fun ω : Config V => t ^ openCount (exh (finState ω o k) j) ω)
        = fun ω => ∑' σ : FinState V,
            ({ω | finState ω o k = σ}.indicator
              (fun ω => t ^ openCount (exh σ j) ω)) ω := by
      funext ω
      rw [tsum_eq_single (finState ω o k)]
      · exact (Set.indicator_of_mem (s := {ω_1 : Config V | finState ω_1 o k = finState ω o k})
          (f := fun ω_1 => t ^ openCount (exh (finState ω o k) j) ω_1) rfl).symm
      · intro σ hσ
        exact Set.indicator_of_notMem (s := {ω_1 : Config V | finState ω_1 o k = σ})
          (f := fun ω_1 => t ^ openCount (exh σ j) ω_1) (Ne.symm hσ)
    rw [hrep]
    exact Measurable.tsum fun σ =>
      (measurable_pow_openCount t (exh σ j)).indicator (measurableSet_finState_eq o k σ)
  have hmeas_f : ∀ j, Measurable fun ω : Config V =>
      G ω * t ^ openCount (exh (finState ω o k) j) ω :=
    fun j => hmG.mul (hmeas_pow j)
  have hmono_f : Monotone fun (j : ℕ) (ω : Config V) =>
      G ω * t ^ openCount (exh (finState ω o k) j) ω := by
    intro i j hij
    exact fun ω => mul_le_mul' le_rfl
      (pow_le_pow_right' ht (openCount_mono (hmono (finState ω o k) hij) ω))
  rw [hcongr, lintegral_iSup hmeas_f hmono_f]
  exact iSup_le hstep

/-! ### Intrinsic existence of the exhaustion and the hypothesis-free form -/

set_option linter.style.haveILetI false in
/-- Every subset of a countable type is the increasing union of an exhaustion by finite sets. -/
theorem exists_monotone_finset_iUnion_eq {α : Type*} [Countable α] (E : Set α) :
    ∃ u : ℕ → Finset α, Monotone u ∧ (⋃ n, ((u n : Finset α) : Set α)) = E := by
  classical
  rcases isEmpty_or_nonempty α with hα | hα
  · haveI := hα
    refine ⟨fun _ => ∅, fun _ _ _ => le_refl _, ?_⟩
    rw [show E = ∅ from Set.eq_empty_iff_forall_notMem.mpr (fun x _ => isEmptyElim x)]
    simp
  · haveI := hα
    obtain ⟨e, he⟩ : ∃ f : ℕ → α, Function.Surjective f := exists_surjective_nat α
    let u : ℕ → Finset α := fun n =>
      Finset.image e (Finset.filter (fun k : ℕ => e k ∈ E) (Finset.range (n + 1)))
    have hu : ∀ n : ℕ, u n
        = Finset.image e (Finset.filter (fun k : ℕ => e k ∈ E) (Finset.range (n + 1))) :=
      fun n => rfl
    refine ⟨u, ?_, ?_⟩
    · intro m n hmn x hx
      rw [hu m] at hx
      rw [hu n]
      obtain ⟨k, hk1, hk2⟩ := Finset.mem_image.mp hx
      have hklt : k < m + 1 := Finset.mem_range.mp (Finset.mem_filter.mp hk1).1
      have hke : e k ∈ E := (Finset.mem_filter.mp hk1).2
      exact Finset.mem_image.mpr ⟨k, Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr (by omega), hke⟩, hk2⟩
    · ext x
      constructor
      · intro hx
        obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx
        rw [hu n] at hn
        obtain ⟨k, hk1, hk2⟩ := Finset.mem_image.mp hn
        rw [← hk2]
        exact (Finset.mem_filter.mp hk1).2
      · intro hx
        obtain ⟨k, hk⟩ := he x
        have hmem : e k ∈ u k := by
          rw [hu k]
          exact Finset.mem_image.mpr ⟨k, Finset.mem_filter.mpr
            ⟨Finset.mem_range.mpr (by omega), hk.symm ▸ hx⟩, rfl⟩
        rw [← hk]
        exact Set.mem_iUnion.mpr ⟨k, hmem⟩

/-- **The hypothesis-free directed-limit one-step estimate.**  Same conclusion as
`lintegral_bfs_epow_le_rowBound`, with the exhaustion of the state's querying set chosen
internally from countability of the edge type.  No finiteness hypothesis on `A k`, `P k`,
`U k`, on the degree, or on the queried set is needed: the fresh moment is the extended power
`epow t (|freshEdgeSet σ ∩ ω|)` with the deterministic budget `|T_σ| · M`. -/
theorem lintegral_bfs_epow_le_rowBound' [Countable V] (p : Sym2 V → unitInterval) (o : V)
    (k : ℕ) (G : Config V → ℝ≥0∞)
    (H : (σ : FinState V) → Set (revealFin σ) → ℝ≥0∞)
    (hH : ∀ σ, Measurable (H σ))
    (hG : ∀ ω, G ω = H (finState ω o k) (blockRestrict (revealFin (finState ω o k)) ω))
    (t : ℝ≥0∞) (ht : 1 ≤ t) (ht_top : t ≠ ⊤) {M : ℝ} (hM : UniformRowBound p M) :
    ∫⁻ ω, G ω * epow t ((freshEdgeSet (finState ω o k) ∩ ω).encard) ∂(prodBernoulli p)
      ≤ ∑' σ : FinState V,
          (∫⁻ ω in {ω | finState ω o k = σ}, G ω ∂(prodBernoulli p))
            * ENNReal.ofReal (Real.exp ((t.toReal - 1) * ((finStateCard σ : ℝ) * M))) := by
  classical
  have hex : ∀ σ : FinState V, ∃ u : ℕ → Finset (Sym2 V), Monotone u ∧
      (⋃ n, ((u n : Finset (Sym2 V)) : Set (Sym2 V))) = freshEdgeSet σ :=
    fun σ => exists_monotone_finset_iUnion_eq (freshEdgeSet σ)
  choose exh hmono hUnion using hex
  refine lintegral_bfs_epow_le_rowBound p o k G H hH hG exh hmono hUnion (fun σ j => ?_)
    t ht ht_top hM
  refine (disjoint_freshEdgeSet_revealFin σ).mono_left ?_
  rw [← hUnion σ]
  exact Set.subset_iUnion (fun n => ((exh σ n : Finset (Sym2 V)) : Set (Sym2 V))) j

end PercLib.CriticalLRP.Exploration.BFS
