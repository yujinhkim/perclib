/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.
New self-avoiding-path estimates using pinned mathlib walks and PercLib Bernoulli
cylinders. No upstream proof copied. Probability products are used only for paths.
-/
module

public import PercLib.Percolation.Bond.RowSum
public import PercLib.Models.Site.Basic
public import Mathlib.Combinatorics.SimpleGraph.Walk.Counting
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section
noncomputable section
open MeasureTheory Set PercLib.Probability
open scoped ENNReal NNReal Classical

namespace PercLib.Percolation.Bond
variable {V : Type*}

/-- A finite list family covers every simple path of length n+1 from x, with
at most Δ(Δ-1)^n members. After the first step, the preceding vertex is excluded. -/
theorem exists_path_list_cover (G : SimpleGraph V) [G.LocallyFinite]
    {Δ : ℕ} (hΔ : ∀ v, G.degree v ≤ Δ) (x : V) (n : ℕ) :
    ∃ S : Finset (List V), S.card ≤ Δ * (Δ - 1)^n ∧
      ∀ l : List V, l.length = n+1 → (x :: l).IsChain G.Adj →
        (x :: l).Nodup → l ∈ S := by
  classical
  let F : ℕ → V → V → Finset (List V) := fun k => Nat.rec
    (fun _ _ => {[]})
    (fun _ rec x v => ((G.neighborFinset x).erase v).biUnion
      (fun y => (rec y x).image (List.cons y))) k
  have hcard : ∀ k x v, G.Adj x v → (F k x v).card ≤ (Δ-1)^k := by
    intro k
    induction k with
    | zero => intro x v _; simp [F]
    | succ k ih =>
      intro x v hv
      change (((G.neighborFinset x).erase v).biUnion
        (fun y => (F k y x).image (List.cons y))).card ≤ _
      calc
        _ ≤ ((G.neighborFinset x).erase v).card * (Δ-1)^k :=
          Finset.card_biUnion_le_card_mul _ _ _ (fun y hy =>
            Finset.card_image_le.trans (ih y x
              ((G.mem_neighborFinset x y).mp (Finset.mem_erase.mp hy).2).symm))
        _ = (G.degree x - 1) * (Δ-1)^k := by
          rw [Finset.card_erase_of_mem ((G.mem_neighborFinset x v).mpr hv)]
          rfl
        _ ≤ (Δ-1) * (Δ-1)^k := Nat.mul_le_mul_right _ (Nat.sub_le_sub_right (hΔ x) 1)
        _ = (Δ-1)^(k+1) := by rw [pow_succ, Nat.mul_comm]
  have hmem : ∀ k x v l, l.length = k → (x::l).IsChain G.Adj →
      (x::l).Nodup → v ∉ l → l ∈ F k x v := by
    intro k
    induction k with
    | zero =>
      intro x v l hl _ _ _
      have : l = [] := List.length_eq_zero_iff.mp hl
      subst l
      simp [F]
    | succ k ih =>
      intro x v l hl hc hn hv
      cases l with
      | nil => simp at hl
      | cons y l =>
        have hlen : l.length = k := by simpa using hl
        have hc' := List.isChain_cons_cons.mp hc
        have hn' := List.nodup_cons.mp hn
        have hyv : y ≠ v := by intro h; subst y; exact hv (by simp)
        change y::l ∈ ((G.neighborFinset x).erase v).biUnion
          (fun y => (F k y x).image (List.cons y))
        apply Finset.mem_biUnion.mpr
        refine ⟨y, Finset.mem_erase.mpr ⟨hyv, (G.mem_neighborFinset x y).mpr hc'.1⟩, ?_⟩
        exact Finset.mem_image.mpr ⟨l, ih y x l hlen hc'.2 hn'.2
          (fun hx => hn'.1 (by simp [hx])), rfl⟩
  refine ⟨(G.neighborFinset x).biUnion (fun y => (F n y x).image (List.cons y)), ?_, ?_⟩
  · calc
      _ ≤ (G.neighborFinset x).card * (Δ-1)^n :=
        Finset.card_biUnion_le_card_mul _ _ _ (fun y hy =>
          Finset.card_image_le.trans (hcard n y x ((G.mem_neighborFinset x y).mp hy).symm))
      _ ≤ Δ * (Δ-1)^n := Nat.mul_le_mul_right _ (hΔ x)
  · intro l hl hc hn
    cases l with
    | nil => simp at hl
    | cons y l =>
      have hc' := List.isChain_cons_cons.mp hc
      have hn' := List.nodup_cons.mp hn
      refine Finset.mem_biUnion.mpr ⟨y, (G.mem_neighborFinset x y).mpr hc'.1, ?_⟩
      exact Finset.mem_image.mpr ⟨l, hmem n y x l (by simpa using hl) hc'.2 hn'.2
        (fun hx => hn'.1 (by simp [hx])), rfl⟩

/-- In any host graph, a simple path and its endpoint are determined by its tail support. -/
theorem path_tail_injective_in_graph (G : SimpleGraph V) (x : V) :
    Function.Injective (fun p : Σ y, G.Path x y => p.2.1.support.tail) := by
  rintro ⟨y, p, hp⟩ ⟨z, r, hr⟩ heq
  change p.support.tail = r.support.tail at heq
  have hs : p.support = r.support := by
    rw [← p.cons_tail_support, ← r.cons_tail_support, heq]
  have hyz : y = z := by
    rw [← p.getLast_support, ← r.getLast_support]
    simp only [hs]
  subst z
  have hpr : p = r := SimpleGraph.Walk.support_injective hs
  subst r
  rfl

/-- Finiteness and the sharp elementary bound for paths with a fixed positive length. -/
theorem finite_card_paths_length (G : SimpleGraph V) [G.LocallyFinite]
    {Δ : ℕ} (hΔ : ∀ v, G.degree v ≤ Δ) (x : V) (n : ℕ) :
    Finite {p : Σ y, G.Path x y // p.2.1.length = n+1} ∧
      Nat.card {p : Σ y, G.Path x y // p.2.1.length = n+1} ≤ Δ * (Δ-1)^n := by
  classical
  obtain ⟨S, hcard, hmem⟩ := exists_path_list_cover G hΔ x n
  let f : {p : Σ y, G.Path x y // p.2.1.length = n+1} → S := fun p =>
    ⟨p.1.2.1.support.tail, hmem _ (by simp [List.length_tail, p.1.2.1.length_support, p.2])
      (by rw [p.1.2.1.cons_tail_support]; exact p.1.2.1.isChain_adj_support)
      (by rw [p.1.2.1.cons_tail_support]; exact p.1.2.2.support_nodup)⟩
  have hf : Function.Injective f := by
    intro a b h
    apply Subtype.ext
    exact path_tail_injective_in_graph G x (congrArg Subtype.val h)
  have hfin := Finite.of_injective f hf
  refine ⟨hfin, ?_⟩
  exact (Nat.card_le_card_of_injective f hf).trans (by simpa using hcard)

/-- All vertices reached by a walk of bounded length form a finite set in a locally
finite graph. -/
theorem finite_bounded_walk_endpoints (G : SimpleGraph V) [G.LocallyFinite] (x : V) (n : ℕ) :
    {y | ∃ p : G.Walk x y, p.length ≤ n}.Finite := by
  induction n generalizing x with
  | zero =>
    apply (Set.finite_singleton x).subset
    rintro y ⟨p, hp⟩
    exact (p.eq_of_length_eq_zero (Nat.eq_zero_of_le_zero hp)).symm
  | succ n ih =>
    apply ((Set.finite_singleton x).union
      ((Set.toFinite (G.neighborSet x)).biUnion (fun y _ => ih y))).subset
    rintro y ⟨p, hp⟩
    cases p with
    | nil => exact Or.inl rfl
    | @cons a b c hab p =>
      refine Or.inr (Set.mem_iUnion₂.mpr ⟨b, hab, p, ?_⟩)
      simpa using hp

/-- Every infinite cluster in a locally finite host contains paths of every finite length. -/
theorem exists_path_length_of_cluster_infinite (G : SimpleGraph V) [G.LocallyFinite]
    {ω : Config V} (hhost : openGraph ω ≤ G) {x : V} (hinf : (cluster ω x).Infinite) (n : ℕ) :
    ∃ y, ∃ p : (openGraph ω).Path x y, p.1.length = n := by
  obtain ⟨y, hy, hny⟩ := hinf.exists_notMem_finite (finite_bounded_walk_endpoints G x n)
  obtain ⟨p, hp⟩ := hy.exists_isPath
  have hn : n ≤ p.length := by
    by_contra h
    apply hny
    exact ⟨p.mapLe hhost, by simpa using (Nat.le_of_lt (Nat.lt_of_not_ge h))⟩
  exact ⟨p.getVert n, ⟨p.take n, hp.take n⟩, by simp [hn]⟩

/-- Union bound for open simple paths of positive length in a bounded-degree host. -/
theorem law_exists_path_length_le (G : SimpleGraph V) [G.LocallyFinite]
    {Δ : ℕ} (hΔ : ∀ v, G.degree v ≤ Δ) (q : Sym2 V → unitInterval) (p : unitInterval)
    (hle : ∀ e ∈ G.edgeSet, q e ≤ p) (x : V) (n : ℕ) :
    law q {ω | ∃ y, ∃ r : G.Path x y, r.1.length = n+1 ∧
      (r.1.edges.toFinset : Set (Sym2 V)) ⊆ ω} ≤
      (Δ * (Δ-1)^n : ℕ) * (unitInterval.toNNReal p : ℝ≥0∞)^(n+1) := by
  classical
  let P := {r : Σ y, G.Path x y // r.2.1.length = n+1}
  have hcard := finite_card_paths_length G hΔ x n
  let : Finite P := hcard.1
  let : Fintype P := Fintype.ofFinite P
  have heq : {ω | ∃ y, ∃ r : G.Path x y, r.1.length = n+1 ∧
      (r.1.edges.toFinset : Set (Sym2 V)) ⊆ ω} =
      ⋃ r : P, {ω : Config V | (r.1.2.1.edges.toFinset : Set (Sym2 V)) ⊆ ω} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    exact ⟨fun ⟨y,r,hn,hr⟩ => ⟨⟨⟨y,r⟩,hn⟩,hr⟩,
      fun ⟨r,hr⟩ => ⟨r.1.1,r.1.2,r.2,hr⟩⟩
  rw [heq]
  calc
    _ ≤ ∑' r : P, law q {ω | (r.1.2.1.edges.toFinset : Set (Sym2 V)) ⊆ ω} := measure_iUnion_le _
    _ = ∑' r : P, ∏ e ∈ r.1.2.1.edges.toFinset, (unitInterval.toNNReal (q e) : ℝ≥0∞) := by
      simp only [law, prodBernoulli_subset]
    _ ≤ ∑' _r : P, (unitInterval.toNNReal p : ℝ≥0∞)^(n+1) := by
      apply ENNReal.tsum_le_tsum
      intro r
      calc
        _ ≤ ∏ _e ∈ r.1.2.1.edges.toFinset, (unitInterval.toNNReal p : ℝ≥0∞) :=
          Finset.prod_le_prod (fun e he => ENNReal.coe_le_coe.mpr
            (hle e (r.1.2.1.edges_subset_edgeSet (List.mem_toFinset.mp he))))
        _ = _ := by
          rw [Finset.prod_const, List.toFinset_card_of_nodup r.1.2.2.isTrail.edges_nodup,
            SimpleGraph.Walk.length_edges, r.2]
    _ = (Nat.card P : ℝ≥0∞) * (unitInterval.toNNReal p : ℝ≥0∞)^(n+1) := by
      simp [tsum_fintype, Nat.card_eq_fintype_card]
    _ ≤ _ := by
      gcongr
      exact_mod_cast hcard.2

/-- Host containment needs zero off-host probabilities only on non-diagonal pairs. -/
theorem ae_openGraph_le_of_zero_off_diagonal [Countable V] (G : SimpleGraph V)
    (q : Sym2 V → unitInterval)
    (hoff : ∀ e, ¬ e.IsDiag → e ∉ G.edgeSet → q e = 0) :
    ∀ᵐ ω ∂law q, openGraph ω ≤ G := by
  have he (e : Sym2 V) : ∀ᵐ ω ∂law q, e ∈ ω → ¬ e.IsDiag → e ∈ G.edgeSet := by
    by_cases hd : e.IsDiag
    · exact Filter.Eventually.of_forall (fun _ _ h => (h hd).elim)
    by_cases hg : e ∈ G.edgeSet
    · exact Filter.Eventually.of_forall (fun _ _ _ => hg)
    have hz := hoff e hd hg
    rw [ae_iff]
    simpa [hd, hg, hz, law] using prodBernoulli_setOf_mem q e
  filter_upwards [ae_all_iff.mpr he] with ω hω
  intro x y hxy
  have hxy' := (openGraph_adj_iff ω x y).mp hxy
  exact hω s(x,y) hxy'.1 (by simpa using hxy'.2)

/-- The self-avoiding-walk criterion, with natural subtraction to include degree zero
and one uniformly. -/
theorem law_cluster_infinite_eq_zero_of_degree_le_ennreal [Countable V]
    (G : SimpleGraph V) [G.LocallyFinite] {Δ : ℕ} (hΔ : ∀ v, G.degree v ≤ Δ)
    (q : Sym2 V → unitInterval) (p : unitInterval)
    (hoff : ∀ e, ¬ e.IsDiag → e ∉ G.edgeSet → q e = 0)
    (hle : ∀ e ∈ G.edgeSet, q e ≤ p)
    (hp : ((Δ-1 : ℕ) : ℝ≥0∞) * unitInterval.toNNReal p < 1) (x : V) :
    law q {ω | (cluster ω x).Infinite} = 0 := by
  apply ENNReal.eq_zero_of_le_mul_pow (ε := (Δ : ℝ≥0) * unitInterval.toNNReal p) hp
  intro n
  calc
    _ ≤ law q {ω | ∃ y, ∃ r : G.Path x y, r.1.length = n+1 ∧
        (r.1.edges.toFinset : Set (Sym2 V)) ⊆ ω} := by
      apply measure_mono_ae
      filter_upwards [ae_openGraph_le_of_zero_off_diagonal G q hoff] with ω hω hi
      obtain ⟨y,r,hr⟩ := exists_path_length_of_cluster_infinite G hω hi (n+1)
      refine ⟨y, ⟨r.1.mapLe hω, r.2.mapLe hω⟩, by simpa using hr, ?_⟩
      intro e he
      have hmem := r.1.edges_subset_edgeSet (by simpa using he)
      exact (show e ∈ ω \ Sym2.diagSet by
        simpa [openGraph, SimpleGraph.edgeSet_fromEdgeSet] using hmem).1
    _ ≤ (Δ * (Δ-1)^n : ℕ) * (unitInterval.toNNReal p : ℝ≥0∞)^(n+1) :=
      law_exists_path_length_le G hΔ q p hle x n
    _ = _ := by
      simp only [Nat.cast_mul, Nat.cast_pow, ENNReal.coe_mul, ENNReal.coe_natCast,
        mul_pow, pow_succ]
      ring

/-- If (Δ−1)p<1, no vertex percolates in a graph of maximum degree Δ.
The real subtraction convention is reconciled with degree zero explicitly. -/
theorem law_cluster_infinite_eq_zero_of_degree_le [Countable V]
    (G : SimpleGraph V) [G.LocallyFinite] {Δ : ℕ} (hΔ : ∀ v, G.degree v ≤ Δ)
    (q : Sym2 V → unitInterval) (p : unitInterval)
    (hoff : ∀ e, ¬ e.IsDiag → e ∉ G.edgeSet → q e = 0)
    (hle : ∀ e ∈ G.edgeSet, q e ≤ p)
    (hp : ((Δ : ℝ)-1) * (p : ℝ) < 1) (x : V) :
    law q {ω | (cluster ω x).Infinite} = 0 := by
  apply law_cluster_infinite_eq_zero_of_degree_le_ennreal G hΔ q p hoff hle _ x
  by_cases hΔ0 : Δ = 0
  · simp [hΔ0]
  · have hΔ1 : 1 ≤ Δ := Nat.one_le_iff_ne_zero.mpr hΔ0
    have hp' : (((Δ-1 : ℕ) : ℝ≥0) * unitInterval.toNNReal p : ℝ≥0) < 1 := by
      change ((Δ-1 : ℕ) : ℝ) * (p : ℝ) < 1
      simpa [Nat.cast_sub hΔ1] using hp
    exact_mod_cast hp'

/-- Countability makes the conclusion simultaneous over every root. -/
theorem ae_all_clusters_finite_of_degree_le [Countable V]
    (G : SimpleGraph V) [G.LocallyFinite] {Δ : ℕ} (hΔ : ∀ v, G.degree v ≤ Δ)
    (q : Sym2 V → unitInterval) (p : unitInterval)
    (hoff : ∀ e, ¬ e.IsDiag → e ∉ G.edgeSet → q e = 0)
    (hle : ∀ e ∈ G.edgeSet, q e ≤ p)
    (hp : ((Δ : ℝ)-1) * (p : ℝ) < 1) :
    ∀ᵐ ω ∂law q, ∀ x, (cluster ω x).Finite := by
  apply ae_all_iff.mpr
  intro x
  rw [ae_iff]
  simpa only [Set.not_finite] using
    law_cluster_infinite_eq_zero_of_degree_le G hΔ q p hoff hle hp x

/-- Nearest-neighbour lattice corollary. The degree estimate is an explicit input,
as permitted by Q-23; this does not assert a separate degree-counting theorem. -/
theorem law_lattice_cluster_infinite_eq_zero_of_degree_bound (d : ℕ) (hd : 1 ≤ d)
    [(PercLib.Models.Site.zdGraph d).LocallyFinite]
    (hdegree : ∀ v, (PercLib.Models.Site.zdGraph d).degree v ≤ 2*d)
    (q : Sym2 (PercLib.Models.Site.LatticeSite d) → unitInterval) (p : unitInterval)
    (hoff : ∀ e, ¬ e.IsDiag → e ∉ (PercLib.Models.Site.zdGraph d).edgeSet → q e = 0)
    (hle : ∀ e ∈ (PercLib.Models.Site.zdGraph d).edgeSet, q e ≤ p)
    (hp : (p : ℝ) < 1 / (2*(d : ℝ)-1)) (x : PercLib.Models.Site.LatticeSite d) :
    law q {ω | (cluster ω x).Infinite} = 0 := by
  apply law_cluster_infinite_eq_zero_of_degree_le (PercLib.Models.Site.zdGraph d)
    hdegree q p hoff hle _ x
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hpos : (0 : ℝ) < 2*d-1 := by linarith
  have hmul := (lt_div_iff₀ hpos).mp hp
  push_cast
  nlinarith

-- Degree zero: arbitrary open loops cannot create an infinite cluster on ℕ.
example :
    let q : Sym2 ℕ → unitInterval := fun e => if e.IsDiag then 1 else 0
    law q {ω | (cluster ω 0).Infinite} = 0 := by
  dsimp
  let : (⊥ : SimpleGraph ℕ).LocallyFinite := fun v =>
    Fintype.ofFinset (∅ : Finset ℕ) (by intro w; simp)
  apply law_cluster_infinite_eq_zero_of_degree_le (⊥ : SimpleGraph ℕ)
    (Δ := 0) (by intro v; simp) _ 1
    (by intro e he _; simp [he]) (by intro e he; simp at he) (by norm_num) 0

-- Degree one permits even probability-one edges; the two-vertex cluster stays finite.
example : law (fun _ : Sym2 Bool => 1) {ω | (cluster ω false).Infinite} = 0 := by
  apply law_cluster_infinite_eq_zero_of_degree_le (⊤ : SimpleGraph Bool)
    (Δ := 1) (by intro v; simp) _ 1
    (by intro e he hn; exact (hn (by simpa using he)).elim)
    (by intro e he; exact le_rfl) (by norm_num) false

-- The requested two-dimensional numerical choice is strictly subcritical for Δ=4.
example : ((2*2 : ℝ)-1) * (1/4) < 1 ∧ (1/4 : ℝ) < 1/(2*2-1) := by norm_num

end PercLib.Percolation.Bond
