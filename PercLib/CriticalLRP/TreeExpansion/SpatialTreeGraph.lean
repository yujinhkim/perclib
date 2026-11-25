/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
Spatially-weighted tree-graph inequalities: the finite-sum weighted moment bounds of
Lemma I.5.9 (`lem:spatial_tree_graph`) of T. Hutchcroft, *Critical long-range
percolation I* (arXiv:2508.18807v1), read against the local source
`.scratch/i52/source/Zd_renormalizationHD.tex` (the lemma is at lines 2865-2930).

The source lemma reads: for `u_1,...,u_n ∈ ℝ^d`, `p_1,...,p_n ≥ 0`, `p = ∑ p_i`,

  `E_{β,r}[∑_{x_1,...,x_n ∈ K} ∏_i |<x_i,u_i>|^{p_i}]`
    `≤ (2n-3)!! n^{max{p,1}} (E_{β,r}|K|)^{2n-2}`
        `· max_i E_{β,r}[|K|^{n-1} ∑_{x ∈ K} |<x,u_i>|^p]`.

Its proof has three steps:

1. (**`eq:spatial_AM_GM`**) weighted AM-GM pointwise on the tuple, giving the reduction to
   `max_i E[|K|^{n-1} ∑_{x∈K} |<x,u_i>|^p]` with *no* constant.  Proved here for arbitrary
   real exponents (`prod_rpow_le_sum_div`, `tuple_prod_rpow_le`,
   `spatial_amgm_expectation`); it is the whole content of the first display of the proof.
2. (**`eq:tree_graph_spatial_explicit`**) apply the tree-graph inequality (I.2.2) and
   decompose `|<x_{i_0},u>|^p` along the tree path `0 = j_0,...,j_ℓ = i_0` using
   `(∑ a_i)^p ≤ ℓ^{max{p-1,0}} ∑ a_i^p`, then evaluate the resulting edge-weighted tree sum
   by transitivity.  The elementary `ℓ^p` inequality of this step is proved here
   (`sum_rpow_le_card_mul`, `abs_addHom_telescope_rpow_le`, with real exponents); the
   evaluation of the tree sum with one weighted leaf is *not* proved here and is isolated as
   the named input `WeightedTreeSum` (its `n = 1` case is verified in §7).
3. Summing the `ℓ ≤ n` terms of the path decomposition gives the constant
   `ℓ · ℓ^{max{p-1,0}} = ℓ^{max{p,1}} ≤ n^{max{p,1}}` and the tree count
   `(2n-3)!! = VolumeMoments.M (n-1)`.

What is closed in this file, with no hypotheses beyond nonnegativity of the data:

* the AM-GM step, finite and in the model (`spatial_amgm_expectation`, and the `max` form
  `spatial_amgm_expectation_le_of_forall_le`);
* the identity turning the expectation of the weighted tuple sum over the cluster into
  `∑_x ∏_i |Φ_i(x_i)|^{p_i} P(o ↔ x_1,...,o ↔ x_n)` (`mem_piFinset_clusterF`,
  `expectReal_tupleSum`, `expectReal_tuple_prod`);
* the elementary `ℓ^p` inequality with real exponents, both regimes (`sum_rpow_le_card_mul`);
* the printed shape of the source (`|K|^{n-1}` inside the max),
  `spatial_tree_graph_printed`, obtained from `spatial_tree_graph_of_inputs`.

What remains: `WeightedTreeSum`, the evaluated tree sum with one weighted leaf (the second and
third displays of the source's proof).  Everything else in the paper's lemma is proved.
-/
module

public import PercLib.CriticalLRP.TreeExpansion.Moment
public import PercLib.CriticalLRP.TreeExpansion.Consistency

set_option autoImplicit true

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section

namespace PercLib.CriticalLRP.TreeExpansion

open Finset

/-! ## 1. Weighted AM-GM with real exponents

The first display of the proof of `lem:spatial_tree_graph`:

  `∏_i |<x_i,u_i>|^{p_i} ≤ ∑_i (p_i/p) |<x_i,u_i>|^p`,  `p = ∑_i p_i`,

which is weighted AM-GM with weights `p_i/p` applied to `a_i^p`. -/

variable {ι : Type*} [Fintype ι]

/-- **Weighted AM-GM with real exponents.** For nonnegative `a` and nonnegative exponents `q`
with `0 < ∑ q`, `∏_i a_i^{q_i} ≤ ∑_i (q_i / ∑_j q_j) a_i^{∑_j q_j}`. -/
theorem prod_rpow_le_sum_div (a q : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (hq : ∀ i, 0 ≤ q i)
    (hP : 0 < ∑ i, q i) :
    ∏ i, a i ^ (q i) ≤ ∑ i, (q i / ∑ j, q j) * a i ^ (∑ j, q j) := by
  classical
  set P : ℝ := ∑ i, q i with hPdef
  have hPpos : 0 < P := by rw [hPdef]; exact hP
  have hw1 : ∑ i, q i / P = 1 := by
    rw [← Finset.sum_div, ← hPdef]
    exact div_self hPpos.ne'
  have hgm := Real.geom_mean_le_arith_mean_weighted (Finset.univ : Finset ι)
    (fun i => q i / P) (fun i => a i ^ P) (fun i _ => div_nonneg (hq i) hPpos.le) hw1
    (fun i _ => Real.rpow_nonneg (ha i) P)
  refine le_trans (le_of_eq ?_) hgm
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← Real.rpow_mul (ha i), mul_div_cancel₀ (q i) hPpos.ne']

/-! ## 2. The `n`-fold sum over tuples from a finite set

`∑_{x_1,...,x_n ∈ K}` is `∑ x ∈ Fintype.piFinset (fun _ : Fin n => K)`; membership in that
finset is exactly "every coordinate lies in `K`" (`Fintype.mem_piFinset`). -/

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The `n`-fold sum over tuples drawn from `K`. -/
noncomputable def tupleSum (K : Finset V) (n : ℕ) (F : (Fin n → V) → ℝ) : ℝ :=
  ∑ x ∈ Fintype.piFinset (fun _ : Fin n => K), F x

theorem tupleSum_def (K : Finset V) (n : ℕ) (F : (Fin n → V) → ℝ) :
    tupleSum K n F = ∑ x ∈ Fintype.piFinset (fun _ : Fin n => K), F x := rfl

/-- Splitting off one coordinate: `∑_{x ∈ K^n} f(x_{i₀}) = |K|^{n-1} ∑_{y ∈ K} f y`. -/
theorem sum_tuple_apply (K : Finset V) {n : ℕ} (i₀ : Fin n) (f : V → ℝ) :
    (∑ x ∈ Fintype.piFinset (fun _ : Fin n => K), f (x i₀))
      = (K.card : ℝ) ^ (n - 1) * ∑ y ∈ K, f y := by
  classical
  have hsingle : ∀ x : Fin n → V,
      (∏ i, (if i = i₀ then f (x i) else (1 : ℝ))) = f (x i₀) := by
    intro x
    rw [Finset.prod_ite_eq']
    simp
  have hrest : ∀ i ∈ (Finset.univ.erase i₀ : Finset (Fin n)),
      (∑ y ∈ K, (if i = i₀ then f y else (1 : ℝ))) = (K.card : ℝ) := by
    intro i hi
    rw [Finset.mem_erase] at hi
    have h0 : ¬ (i = i₀) := hi.1
    simp [h0]
  calc (∑ x ∈ Fintype.piFinset (fun _ : Fin n => K), f (x i₀))
      = ∑ x ∈ Fintype.piFinset (fun _ : Fin n => K),
          ∏ i, (if i = i₀ then f (x i) else (1 : ℝ)) :=
        Finset.sum_congr rfl fun x _ => (hsingle x).symm
    _ = ∏ i : Fin n, ∑ y ∈ K, (if i = i₀ then f y else (1 : ℝ)) :=
        Finset.sum_prod_piFinset K (fun i y => if i = i₀ then f y else (1 : ℝ))
    _ = (K.card : ℝ) ^ (n - 1) * ∑ y ∈ K, f y := by
        rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i₀), Finset.prod_congr rfl hrest,
          Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ i₀), Finset.card_univ,
          Fintype.card_fin]
        simp

/-- **The AM-GM reduction** (`eq:spatial_AM_GM` of the source), finite-set form and with no
constant: for nonnegative weights `A_i` on `V`, nonnegative exponents `q_i` and `0 < ∑ q_i`,

  `∑_{x ∈ K^n} ∏_i A_i(x_i)^{q_i} ≤ |K|^{n-1} ∑_i (q_i/∑_j q_j) ∑_{y ∈ K} A_i(y)^{∑_j q_j}`.

The right-hand side is a convex combination (weights `q_i/∑_j q_j`) of the `n` quantities
`|K|^{n-1} ∑_{y ∈ K} A_i(y)^p`, `p = ∑ q_i`; taking the maximum of those gives the
`max_{1≤i≤n}` of the source. -/
theorem tuple_prod_rpow_le (K : Finset V) {n : ℕ} (_hn : 1 ≤ n)
    (q : Fin n → ℝ) (A : Fin n → V → ℝ)
    (hA : ∀ i y, 0 ≤ A i y) (hq : ∀ i, 0 ≤ q i) (hP : 0 < ∑ i, q i) :
    tupleSum K n (fun x => ∏ i, A i (x i) ^ q i)
      ≤ (K.card : ℝ) ^ (n - 1) *
        ∑ i, (q i / ∑ j, q j) * ∑ y ∈ K, A i y ^ (∑ j, q j) := by
  classical
  have hstep : ∀ x ∈ Fintype.piFinset (fun _ : Fin n => K),
      (∏ i, A i (x i) ^ q i)
        ≤ ∑ i, (q i / ∑ j, q j) * A i (x i) ^ (∑ j, q j) :=
    fun x _ => prod_rpow_le_sum_div (fun i => A i (x i)) q (fun i => hA i (x i)) hq hP
  have hsplit : ∀ i : Fin n,
      (∑ x ∈ Fintype.piFinset (fun _ : Fin n => K), A i (x i) ^ (∑ j, q j))
        = (K.card : ℝ) ^ (n - 1) * ∑ y ∈ K, A i y ^ (∑ j, q j) :=
    fun i => sum_tuple_apply K i (fun y => A i y ^ (∑ j, q j))
  rw [tupleSum_def]
  calc (∑ x ∈ Fintype.piFinset (fun _ : Fin n => K), ∏ i, A i (x i) ^ q i)
      ≤ ∑ x ∈ Fintype.piFinset (fun _ : Fin n => K),
          ∑ i, (q i / ∑ j, q j) * A i (x i) ^ (∑ j, q j) := Finset.sum_le_sum hstep
    _ = ∑ i, (q i / ∑ j, q j) *
          (∑ x ∈ Fintype.piFinset (fun _ : Fin n => K), A i (x i) ^ (∑ j, q j)) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun i _ => (Finset.mul_sum _ _ _).symm
    _ = ∑ i, (q i / ∑ j, q j) *
          ((K.card : ℝ) ^ (n - 1) * ∑ y ∈ K, A i y ^ (∑ j, q j)) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hsplit i]
    _ = (K.card : ℝ) ^ (n - 1) *
          ∑ i, (q i / ∑ j, q j) * ∑ y ∈ K, A i y ^ (∑ j, q j) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring

/-- The same bound with the maximum made explicit: if `M` bounds all the `n` spatial moments
`∑_{y ∈ K} A_i(y)^p`, then the tuple sum is at most `|K|^{n-1} M` — the shape used in the
source after `eq:spatial_AM_GM`.  (`hn` is needed only so that the weights `q_i/∑q` have total
mass one; `hq`, `hP`, `hA` are as above.) -/
theorem tuple_prod_rpow_le_of_forall_le (K : Finset V) {n : ℕ} (hn : 1 ≤ n)
    (q : Fin n → ℝ) (A : Fin n → V → ℝ) (M : ℝ)
    (hA : ∀ i y, 0 ≤ A i y) (hq : ∀ i, 0 ≤ q i) (hP : 0 < ∑ i, q i)
    (hM : ∀ i, ∑ y ∈ K, A i y ^ (∑ j, q j) ≤ M) :
    tupleSum K n (fun x => ∏ i, A i (x i) ^ q i) ≤ (K.card : ℝ) ^ (n - 1) * M := by
  classical
  have hPpos : 0 < ∑ j, q j := hP
  have hw1 : ∑ i, q i / ∑ j, q j = 1 := by
    rw [← Finset.sum_div]
    exact div_self hPpos.ne'
  have hM0 : 0 ≤ M := by
    obtain ⟨i₀⟩ : Nonempty (Fin n) := ⟨⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_one hn⟩⟩
    exact (Finset.sum_nonneg fun y _ => Real.rpow_nonneg (hA i₀ y) _).trans (hM i₀)
  have hcard0 : (0 : ℝ) ≤ (K.card : ℝ) ^ (n - 1) := pow_nonneg (Nat.cast_nonneg K.card) _
  refine (tuple_prod_rpow_le K hn q A hA hq hP).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ hcard0
  calc ∑ i, (q i / ∑ j, q j) * ∑ y ∈ K, A i y ^ (∑ j, q j)
      ≤ ∑ i, (q i / ∑ j, q j) * M :=
        Finset.sum_le_sum fun i _ =>
          mul_le_mul_of_nonneg_left (hM i) (div_nonneg (hq i) hPpos.le)
    _ = (∑ i, q i / ∑ j, q j) * M := (Finset.sum_mul _ _ _).symm
    _ = M := by rw [hw1, one_mul]


/-! ## 3. The canonical finite-edge Bernoulli model

The model is the project's finite-edge Bernoulli bond percolation: `E` is a finite type of
possible edges, `ends : E → Sym2 V` their endpoints, a configuration is a `Finset E`, `pr`
gives the edge probabilities, `Conn ends s x y` is open connectivity in the configuration `s`,
and `clusterF ends s o` is the cluster `K` of the root `o`.  Nothing here uses translation
invariance or BK: these are exact finite-sum identities. -/

variable {E : Type*} [Fintype E] [DecidableEq E]

open PercLib.CriticalLRP.TreeGraph

/-- Expectation is monotone: a pointwise inequality between functionals of the configuration. -/
theorem expectReal_mono (pr : E → ℝ) (hp : ∀ e, 0 ≤ pr e) (hp1 : ∀ e, pr e ≤ 1)
    {F G : Finset E → ℝ} (h : ∀ s, F s ≤ G s) : expectReal pr F ≤ expectReal pr G :=
  Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left (h s) (configurationLaw_nonneg pr hp hp1 s)

/-- Expectation is linear over a finite weighted sum. -/
theorem expectReal_sum (pr : E → ℝ) {ι : Type*} [Fintype ι] (w : ι → ℝ)
    (X : ι → Finset E → ℝ) :
    expectReal pr (fun s => ∑ i, w i * X i s) = ∑ i, w i * expectReal pr (X i) := by
  simp only [expectReal, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun s _ => by ring

/-- The expectation of the indicator of a set of configurations is its probability. -/
theorem expectReal_indicatorR (pr : E → ℝ) (A : Set (Finset E)) :
    expectReal pr (indicatorR A) = prob pr A :=
  (prob_eq_sum_indicator pr A).symm

/-- Membership in the `n`-fold product of the cluster of `o` is exactly "every coordinate is
connected to `o`": the set-theoretic form of `x_1,...,x_n ∈ K`. -/
theorem mem_piFinset_clusterF {ends : E → Sym2 V} (s : Finset E) (o : V) {n : ℕ}
    {x : Fin n → V} :
    x ∈ Fintype.piFinset (fun _ : Fin n => clusterF ends s o)
      ↔ ∀ i : Fin n, Conn ends s o (x i) := by
  rw [Fintype.mem_piFinset]
  exact forall_congr' fun i => mem_clusterF

/-- **Exchange of the tuple sum and the expectation.**  For every function `Φ` of an `n`-tuple,

  `E[∑_{x ∈ K^n} Φ x] = ∑_{x ∈ V^n} Φ x · P(o ↔ x_1, ..., o ↔ x_n)`.

This turns the spatially weighted tuple sum over the cluster into the labelled sum to which
the tree-graph inequality (I.2.2) applies; it is the finite-sum content of the "write the
expectation as a sum over connectivity events" step of the proof of `lem:spatial_tree_graph`
and the `n`-point generalisation of `expectation_clusterVol_sq`. -/
theorem expectReal_tupleSum (pr : E → ℝ) (ends : E → Sym2 V) (o : V) (n : ℕ)
    (Φ : (Fin n → V) → ℝ) :
    expectReal pr (fun s => tupleSum (clusterF ends s o) n Φ)
      = ∑ x : Fin n → V, Φ x * prob pr {s | ∀ i : Fin n, Conn ends s o (x i)} := by
  classical
  have h1 : ∀ s : Finset E, tupleSum (clusterF ends s o) n Φ
      = ∑ x : Fin n → V,
          Φ x * indicatorR {s' : Finset E | ∀ i : Fin n, Conn ends s' o (x i)} s := by
    intro s
    have hf : Fintype.piFinset (fun _ : Fin n => clusterF ends s o)
        = (Finset.univ : Finset (Fin n → V)).filter
            (fun x => ∀ i : Fin n, Conn ends s o (x i)) := by
      ext x
      simp only [Fintype.mem_piFinset, Finset.mem_filter, Finset.mem_univ, true_and]
      exact forall_congr' fun i => mem_clusterF
    rw [tupleSum_def, hf, Finset.sum_filter]
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases hx : ∀ i : Fin n, Conn ends s o (x i) <;> simp [indicatorR, hx]
  simp only [h1]
  rw [expectReal_sum]
  exact Finset.sum_congr rfl fun x _ => by rw [expectReal_indicatorR]

/-- The product-weight form of `expectReal_tupleSum`. -/
theorem expectReal_tuple_prod (pr : E → ℝ) (ends : E → Sym2 V) (o : V) (n : ℕ)
    (q : Fin n → ℝ) (A : Fin n → V → ℝ) :
    expectReal pr (fun s => tupleSum (clusterF ends s o) n (fun x => ∏ i, A i (x i) ^ q i))
      = ∑ x : Fin n → V, (∏ i, A i (x i) ^ q i) *
          prob pr {s | ∀ i : Fin n, Conn ends s o (x i)} :=
  expectReal_tupleSum pr ends o n _

/-- **The AM-GM reduction in the canonical model** (first display of the proof of
`lem:spatial_tree_graph`), with expectations in place of sums over configurations:

  `E[∑_{x ∈ K^n} ∏_i A_i(x_i)^{q_i}]`
    `≤ ∑_i (q_i/p) E[|K|^{n-1} ∑_{y ∈ K} A_i(y)^p]`,  `p = ∑_i q_i`,

hence at most the maximum of the `n` expectations.  The only hypotheses are `0 ≤ pr e ≤ 1`
(for the law to be nonnegative), `A_i ≥ 0` and `q_i ≥ 0` with `0 < p`. -/
theorem spatial_amgm_expectation (pr : E → ℝ) (hp : ∀ e, 0 ≤ pr e) (hp1 : ∀ e, pr e ≤ 1)
    (ends : E → Sym2 V) (o : V) {n : ℕ} (hn : 1 ≤ n) (q : Fin n → ℝ) (A : Fin n → V → ℝ)
    (hA : ∀ i y, 0 ≤ A i y) (hq : ∀ i, 0 ≤ q i) (hP : 0 < ∑ i, q i) :
    expectReal pr (fun s => tupleSum (clusterF ends s o) n (fun x => ∏ i, A i (x i) ^ q i))
      ≤ ∑ i, (q i / ∑ j, q j) *
          expectReal pr (fun s => ((clusterF ends s o).card : ℝ) ^ (n - 1) *
            ∑ y ∈ clusterF ends s o, A i y ^ (∑ j, q j)) := by
  classical
  rw [← expectReal_sum pr (fun i : Fin n => q i / ∑ j, q j)
    (fun i s => ((clusterF ends s o).card : ℝ) ^ (n - 1) *
      ∑ y ∈ clusterF ends s o, A i y ^ (∑ j, q j))]
  refine expectReal_mono pr hp hp1 fun s => ?_
  refine (tuple_prod_rpow_le (clusterF ends s o) hn q A hA hq hP).trans (le_of_eq ?_)
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- **The `max_i` form**, ready for the tree-graph input: if `M` bounds each of the `n`
spatial expectations `E[|K|^{n-1} ∑_{y ∈ K} A_i(y)^p]`, then the weighted tuple sum is at
most `M`.  (In the source, `M` is `(2n-3)!! n^{max{p,1}} (E|K|)^{2n-2}` times the weighted
two-point sum `E ∑_{x ∈ K} |<x,u_i>|^p`.) -/
theorem spatial_amgm_expectation_le_of_forall_le (pr : E → ℝ) (hp : ∀ e, 0 ≤ pr e)
    (hp1 : ∀ e, pr e ≤ 1) (ends : E → Sym2 V) (o : V) {n : ℕ} (hn : 1 ≤ n)
    (q : Fin n → ℝ) (A : Fin n → V → ℝ) (M : ℝ)
    (hA : ∀ i y, 0 ≤ A i y) (hq : ∀ i, 0 ≤ q i) (hP : 0 < ∑ i, q i)
    (hM : ∀ i, expectReal pr (fun s => ((clusterF ends s o).card : ℝ) ^ (n - 1) *
            ∑ y ∈ clusterF ends s o, A i y ^ (∑ j, q j)) ≤ M) :
    expectReal pr (fun s => tupleSum (clusterF ends s o) n (fun x => ∏ i, A i (x i) ^ q i))
      ≤ M := by
  classical
  have hPpos : 0 < ∑ j, q j := hP
  have hw1 : ∑ i, q i / ∑ j, q j = 1 := by
    rw [← Finset.sum_div]
    exact div_self hPpos.ne'
  refine (spatial_amgm_expectation pr hp hp1 ends o hn q A hA hq hP).trans ?_
  calc ∑ i, (q i / ∑ j, q j) *
        expectReal pr (fun s => ((clusterF ends s o).card : ℝ) ^ (n - 1) *
          ∑ y ∈ clusterF ends s o, A i y ^ (∑ j, q j))
      ≤ ∑ i, (q i / ∑ j, q j) * M :=
        Finset.sum_le_sum fun i _ =>
          mul_le_mul_of_nonneg_left (hM i) (div_nonneg (hq i) hPpos.le)
    _ = (∑ i, q i / ∑ j, q j) * M := (Finset.sum_mul _ _ _).symm
    _ = M := by rw [hw1, one_mul]


/-! ## 4. The elementary `ℓ^p` inequality of the path decomposition

The source's second use of the elementary inequality

  `(∑_{m=1}^ℓ a_m)^p ≤ ℓ^{max{p-1,0}} ∑_{m=1}^ℓ a_m^p`,   `a_m ≥ 0`, `p ≥ 0`,

is applied to `a_m = |<x_{j_m}-x_{j_{m-1}},u>|` along the tree path `0 = j_0,...,j_ℓ = i_0`,
where `x_{i_0} = ∑_m (x_{j_m}-x_{j_{m-1}})`.  It is proved here for real exponents: the two
regimes are convexity of `x ↦ x^p` for `p ≥ 1` (Mathlib's weighted power mean
inequality) and subadditivity `(a+b)^p ≤ a^p + b^p` for `0 ≤ p ≤ 1`
(`Real.rpow_add_le_add_rpow`). -/

section Ellp

/-- Subadditivity of `x ↦ x^p` on `[0,∞)` for `0 ≤ p ≤ 1`, finite sums. -/
theorem sum_rpow_le_sum_rpow_of_le_one {ι : Type*} (s : Finset ι) (c : ι → ℝ) {p : ℝ}
    (hc : ∀ i ∈ s, 0 ≤ c i) (hp : 0 ≤ p) (hp1 : p ≤ 1) (hs : s.Nonempty) :
    (∑ i ∈ s, c i) ^ p ≤ ∑ i ∈ s, c i ^ p := by
  classical
  induction s using Finset.induction_on with
  | empty => exact absurd hs (by simp)
  | insert a t ha ih =>
      rw [Finset.sum_insert ha]
      rcases t.eq_empty_or_nonempty with rfl | hne
      · rw [Finset.sum_empty, add_zero]
        simp
      · have ha0 : 0 ≤ c a := hc a (Finset.mem_insert_self a t)
        have ht0 : 0 ≤ ∑ i ∈ t, c i :=
          Finset.sum_nonneg fun i hi => hc i (Finset.mem_insert_of_mem hi)
        have hih := ih (fun i hi => hc i (Finset.mem_insert_of_mem hi)) hne
        have h2 := Real.rpow_add_le_add_rpow ha0 ht0 hp hp1
        calc (c a + ∑ i ∈ t, c i) ^ p
            ≤ c a ^ p + (∑ i ∈ t, c i) ^ p := h2
          _ ≤ c a ^ p + ∑ i ∈ t, c i ^ p := by linarith
          _ = ∑ i ∈ insert a t, c i ^ p := by rw [Finset.sum_insert ha]

/-- The `p ≥ 1` case: the power of a sum is at most `card^{p-1}` times the sum of powers
(Jensen's inequality with uniform weights `1/card`). -/
theorem sum_rpow_le_card_mul_of_one_le {ι : Type*} (s : Finset ι) (c : ι → ℝ) {p : ℝ}
    (hc : ∀ i ∈ s, 0 ≤ c i) (hp : 1 ≤ p) (hs : s.Nonempty) :
    (∑ i ∈ s, c i) ^ p ≤ (s.card : ℝ) ^ (p - 1) * ∑ i ∈ s, c i ^ p := by
  classical
  set N : ℝ := (s.card : ℝ) with hNdef
  have hN : 0 < N := by
    rw [hNdef]
    exact_mod_cast Finset.card_pos.mpr hs
  have hw1 : ∑ _i ∈ s, N⁻¹ = 1 := by
    rw [Finset.sum_const, nsmul_eq_mul, ← hNdef]
    field_simp
  have hmean := Real.rpow_arith_mean_le_arith_mean_rpow s (fun _ => N⁻¹) c
    (fun i _ => by positivity) hw1 hc hp
  have hS : (∑ i ∈ s, N⁻¹ * c i) = N⁻¹ * ∑ i ∈ s, c i := (Finset.mul_sum _ _ _).symm
  have hT : (∑ i ∈ s, N⁻¹ * c i ^ p) = N⁻¹ * ∑ i ∈ s, c i ^ p :=
    (Finset.mul_sum _ _ _).symm
  rw [hS, hT] at hmean
  have hNp : 0 < N ^ p := Real.rpow_pos_of_pos hN p
  have hmul := mul_le_mul_of_nonneg_right hmean hNp.le
  have hS0 : 0 ≤ ∑ i ∈ s, c i := Finset.sum_nonneg fun i hi => hc i hi
  have hL : (N⁻¹ * ∑ i ∈ s, c i) ^ p * N ^ p = (∑ i ∈ s, c i) ^ p := by
    rw [← Real.mul_rpow (mul_nonneg (by positivity) hS0) hN.le]
    congr 1
    field_simp
  have hR : (N⁻¹ * ∑ i ∈ s, c i ^ p) * N ^ p = N ^ (p - 1) * ∑ i ∈ s, c i ^ p := by
    rw [Real.rpow_sub hN, Real.rpow_one, div_eq_mul_inv]
    ring
  rw [hL, hR] at hmul
  exact hmul

/-- **The `ℓ^p` inequality** `(∑ a_i)^p ≤ card^{max{p-1,0}} ∑ a_i^p` for nonnegative reals and
real `p ≥ 0`. -/
theorem sum_rpow_le_card_mul {ι : Type*} (s : Finset ι) (c : ι → ℝ) {p : ℝ}
    (hc : ∀ i ∈ s, 0 ≤ c i) (hp : 0 ≤ p) (hs : s.Nonempty) :
    (∑ i ∈ s, c i) ^ p ≤ (s.card : ℝ) ^ (max (p - 1) 0) * ∑ i ∈ s, c i ^ p := by
  rcases lt_or_ge p 1 with h1 | h1
  · rw [max_eq_right (by linarith : p - 1 ≤ 0), Real.rpow_zero, one_mul]
    exact sum_rpow_le_sum_rpow_of_le_one s c hc hp h1.le hs
  · rw [max_eq_left (by linarith : (0 : ℝ) ≤ p - 1)]
    exact sum_rpow_le_card_mul_of_one_le s c hc h1 hs

/-- **The source's path inequality.**  For an additive functional `φ` (in the source
`φ z = <z,u>`), an index `ℓ ≥ 1` and a path `z 0, z 1, ..., z ℓ`,

  `|φ(z ℓ - z 0)|^p ≤ ℓ^{max{p-1,0}} ∑_{m<ℓ} |φ(z (m+1) - z m)|^p`.

The sum on the right has `ℓ` terms, each of which contributes a factor `ℓ^{max{p-1,0}}` when
the source substitutes the estimate into the tree sum; together they give the factor
`ℓ · ℓ^{max{p-1,0}} = ℓ^{max{p,1}} ≤ n^{max{p,1}}` of the displayed lemma, since the simple
path from the root `0` to a leaf `i_0` of a tree with `n` labelled leaves has `ℓ ≤ n` edges. -/
theorem abs_addHom_telescope_rpow_le {W : Type*} [AddCommGroup W] (φ : W →+ ℝ) (z : ℕ → W)
    {ℓ : ℕ} (hℓ : 1 ≤ ℓ) {p : ℝ} (hp : 0 ≤ p) :
    |φ (z ℓ - z 0)| ^ p
      ≤ (ℓ : ℝ) ^ (max (p - 1) 0) * ∑ m ∈ Finset.range ℓ, |φ (z (m + 1) - z m)| ^ p := by
  classical
  have htel : z ℓ - z 0 = ∑ m ∈ Finset.range ℓ, (z (m + 1) - z m) := by
    rw [Finset.sum_range_sub]
  have hne : (Finset.range ℓ).Nonempty := by
    rw [Finset.nonempty_range_iff]
    omega
  have h1 : |φ (z ℓ - z 0)| ≤ ∑ m ∈ Finset.range ℓ, |φ (z (m + 1) - z m)| := by
    rw [htel, map_sum]
    exact Finset.abs_sum_le_sum_abs _ _
  refine (Real.rpow_le_rpow (abs_nonneg _) h1 hp).trans ?_
  have h := sum_rpow_le_card_mul (Finset.range ℓ) (fun m => |φ (z (m + 1) - z m)|)
    (fun m _ => abs_nonneg _) hp hne
  simpa using h

end Ellp


/-! ## 5. Source fidelity: the printed `|K|^{n-1}` factor

The printed statement of `lem:spatial_tree_graph` carries `|K|^{n-1}` inside the final
expectation, whereas the AM-GM argument (and the tree-graph step of the source's own proof)
produces the same bounds with `|K|^{n-1}` *outside*.  Since `o ∈ K`, `|K| ≥ 1` and so the
printed form is the weaker of the two; this lemma records the passage from the identity proved
here to the printed shape.  Both constants are unaffected, so nothing in the printed lemma
needs the factor. -/

theorem one_le_clusterF_card {ends : E → Sym2 V} (s : Finset E) (o : V) :
    (1 : ℝ) ≤ ((clusterF ends s o).card : ℝ) := by
  have h := Finset.card_pos.mpr ⟨o, self_mem_clusterF ends s o⟩
  exact_mod_cast h

/-- `E[∑_{y ∈ K} A y] ≤ E[|K|^{n-1} ∑_{y ∈ K} A y]` for `n ≥ 1` and `A ≥ 0`: the pass from the
identity to the shape printed in the source. -/
theorem expectReal_cluster_sum_le_pow_mul (pr : E → ℝ) (hp : ∀ e, 0 ≤ pr e)
    (hp1 : ∀ e, pr e ≤ 1) (ends : E → Sym2 V) (o : V) {n : ℕ} (_hn : 1 ≤ n) (A : V → ℝ)
    (hA : ∀ y, 0 ≤ A y) :
    expectReal pr (fun s => ∑ y ∈ clusterF ends s o, A y)
      ≤ expectReal pr (fun s => ((clusterF ends s o).card : ℝ) ^ (n - 1) *
          ∑ y ∈ clusterF ends s o, A y) := by
  refine expectReal_mono pr hp hp1 fun s => ?_
  have hS : 0 ≤ ∑ y ∈ clusterF ends s o, A y := Finset.sum_nonneg fun y _ => hA y
  have h1 : (1 : ℝ) ≤ ((clusterF ends s o).card : ℝ) := one_le_clusterF_card s o
  have h2 : (1 : ℝ) ≤ ((clusterF ends s o).card : ℝ) ^ (n - 1) := one_le_pow₀ h1
  calc ∑ y ∈ clusterF ends s o, A y = 1 * ∑ y ∈ clusterF ends s o, A y := (one_mul _).symm
    _ ≤ ((clusterF ends s o).card : ℝ) ^ (n - 1) * ∑ y ∈ clusterF ends s o, A y :=
        mul_le_mul_of_nonneg_right h2 hS


/-! ## 6. Assembly of `lem:spatial_tree_graph` from two named inputs

* `TreeGraphBound pr ends (twoPoint pr ends)` — the tree-graph inequality (I.2.2).  This is a
  *theorem* in the repository whenever the BK inequality holds: `treeGraphBound_of_bk'` in
  `TreeExpansion/TreeSumRecursionFull.lean` proves it from `BKIncreasing pr`.  It is kept as a
  hypothesis here only to keep this file independent of the BK-development.
* `WeightedTreeSum pr ends o` — the evaluation of the tree sum when one leaf carries the
  weight `A^p`.  This is the arithmetic content of the second and third displays of the
  source's proof (`eq:tree_graph_spatial_explicit`): the path decomposition of
  `|<x_{i_0},u>|^p` (`abs_addHom_telescope_rpow_le`, proved above), transitivity of the
  two-point function along each edge, and the tree count `(2n-3)!!`.  It is **not** proved in
  this file and is the only unproved input besides (I.2.2) itself.

With these two, `spatial_tree_graph_of_inputs` gives exactly the finite-sum weighted moment
bound of `lem:spatial_tree_graph` (in the form produced by the source's proof, i.e. with the
weighted two-point sum on the right, which is the stronger form; `expectReal_cluster_sum_le_pow_mul`
passes to the printed `|K|^{n-1}` shape). -/

section TranslationInvariant

variable [AddCommGroup V]

/-- **The weighted tree-sum input**: the tree sum of (I.2.2) with the weight `|<φ(x_{i₀})>|^p`
on the leaf `i₀`, evaluated.  For `n` labels the evaluation leaves
`(2n−3)!! n^{max{p,1}} (E|K|)^{2n−2}` times the weighted two-point sum
`∑_y |φ y|^p P(o ↔ y)`.  Not proved here.

The weight *must* come from an additive functional `φ` (in the source `φ z = <z,u>`), not from
an arbitrary nonnegative function `A` of the leaf position: for `n ≥ 2` the leaf `i₀` hangs at
an internal vertex `w`, and the generic shape is `∑_{x} A(x_{i₀})^p treeSum = S·∑_x A(x)^p
∑_w T(w)T(x−w)`, which is not bounded by `S² ∑_y A(y)^p T(y)`.  The source's proof handles
this by writing `φ(x_{i₀}) = ∑_m φ(x_{j_m} − x_{j_{m−1}})` along the tree path
(`abs_addHom_telescope_rpow_le`) and then summing each *edge* weight with translation
invariance `twoPoint pr ends a b = T(b − a)`, which is why `hinv` is part of this input. -/
def WeightedTreeSum (pr : E → ℝ) (ends : E → Sym2 V) (o : V) : Prop :=
  ∀ (n : ℕ) (_hn : 1 ≤ n) (i₀ : Fin n) (φ : V →+ ℝ) (p : ℝ), 0 ≤ p →
    (∀ a b : V, twoPoint pr ends a b = twoPoint pr ends o (b - a)) →
    (∑ x : Fin n → V, |φ (x i₀)| ^ p * treeSum (twoPoint pr ends) n o x)
      ≤ (VolumeMoments.M (n - 1) : ℝ) * (n : ℝ) ^ (max p 1) *
          (clusterVolume pr ends o) ^ (2 * n - 2) *
          ∑ y : V, |φ y| ^ p * twoPoint pr ends o y

/-- The tree-graph inequality (I.2.2) applied with the label `o` pinned first. -/
theorem prob_conn_le_treeSum (pr : E → ℝ) (ends : E → Sym2 V) (o : V)
    (hTG : TreeGraphBound pr ends (twoPoint pr ends)) {n : ℕ} (hn : 1 ≤ n) (x : Fin n → V) :
    prob pr {s | ∀ i : Fin n, Conn ends s o (x i)}
      ≤ treeSum (twoPoint pr ends) n o x := by
  classical
  set y : Fin (n + 1) → V := Fin.cases o x with hy
  have hy0 : y 0 = o := rfl
  have hysucc : ∀ j : Fin n, y (Fin.succ j) = x j := by
    intro j
    rw [hy]
    exact Fin.cases_succ j
  have hfun : (fun j => y (Fin.succ j)) = x := funext hysucc
  have hTG' := hTG n hn y
  rw [hfun] at hTG'
  have hset : {s : Finset E | ∀ i : Fin n, Conn ends s o (x i)}
      = {s : Finset E | ∀ i : Fin (n + 1), Conn ends s (y 0) (y i)} := by
    ext s
    constructor
    · intro h' i
      refine Fin.cases ?_ (fun j => ?_) i
      · rw [hy0]
        exact conn_refl ends s o
      · rw [hy0, hysucc j]
        exact h' j
    · intro h' i
      rw [← hysucc i]
      exact h' (Fin.succ i)
  rw [hset, ← hy0]
  exact hTG'

/-- **`lem:spatial_tree_graph`** (finite-sum weighted moment bound) from the tree-graph
inequality and the weighted tree-sum evaluation, in the source's own shape: additive
functionals `Φ_i` (in the source `Φ_i z = <z,u_i>`) and exponents `q_i`,

  `E[∑_{x ∈ K^n} ∏_i |Φ_i(x_i)|^{q_i}]`
    `≤ (2n−3)!! n^{max{p,1}} (E|K|)^{2n−2} · max_i ∑_y |Φ_i y|^p P(o ↔ y)`,  `p = ∑_i q_i`,

with `p > 0` and `q_i ≥ 0`. -/
theorem spatial_tree_graph_of_inputs (pr : E → ℝ) (hp : ∀ e, 0 ≤ pr e) (hp1 : ∀ e, pr e ≤ 1)
    (ends : E → Sym2 V) (o : V) (hTG : TreeGraphBound pr ends (twoPoint pr ends))
    (hW : WeightedTreeSum pr ends o)
    (hinv : ∀ a b : V, twoPoint pr ends a b = twoPoint pr ends o (b - a))
    {n : ℕ} (hn : 1 ≤ n) (q : Fin n → ℝ) (Φ : Fin n → V →+ ℝ) (M : ℝ)
    (hq : ∀ i, 0 ≤ q i) (hP : 0 < ∑ i, q i)
    (hM : ∀ i, ∑ y : V, |Φ i y| ^ (∑ j, q j) * twoPoint pr ends o y ≤ M) :
    expectReal pr (fun s => tupleSum (clusterF ends s o) n (fun x => ∏ i, |Φ i (x i)| ^ q i))
      ≤ (VolumeMoments.M (n - 1) : ℝ) * (n : ℝ) ^ (max (∑ i, q i) 1) *
          (clusterVolume pr ends o) ^ (2 * n - 2) * M := by
  classical
  set P : ℝ := ∑ j, q j with hPdef
  have hPpos : 0 < P := by rw [hPdef]; exact hP
  have hP0 : 0 ≤ P := hPpos.le
  have hS0 : 0 ≤ clusterVolume pr ends o :=
    Finset.sum_nonneg fun y _ => twoPoint_nonneg hp hp1 ends o y
  have hT0 : (0 : ℝ) ≤ (VolumeMoments.M (n - 1) : ℝ) * (n : ℝ) ^ (max P 1) *
      (clusterVolume pr ends o) ^ (2 * n - 2) :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg n) _))
      (pow_nonneg hS0 _)
  have hM' : ∀ i : Fin n, ∑ y : V, |Φ i y| ^ P * twoPoint pr ends o y ≤ M := by
    intro i
    rw [hPdef]
    exact hM i
  have hgm : ∀ x : Fin n → V,
      (∏ i, |Φ i (x i)| ^ q i) ≤ ∑ i, (q i / P) * |Φ i (x i)| ^ P := by
    intro x
    have h := prod_rpow_le_sum_div (fun i => |Φ i (x i)|) q (fun i => abs_nonneg _) hq hP
    rw [← hPdef] at h
    exact h
  have hPx0 : ∀ x : Fin n → V, 0 ≤ prob pr {s | ∀ i : Fin n, Conn ends s o (x i)} :=
    fun x => prob_nonneg hp hp1 _
  have hTGx : ∀ x : Fin n → V, prob pr {s | ∀ i : Fin n, Conn ends s o (x i)}
      ≤ treeSum (twoPoint pr ends) n o x := fun x => prob_conn_le_treeSum pr ends o hTG hn x
  have hstep1 : (∑ x : Fin n → V, (∏ i, |Φ i (x i)| ^ q i) *
        prob pr {s | ∀ i : Fin n, Conn ends s o (x i)})
      ≤ ∑ x : Fin n → V, (∑ i, (q i / P) * |Φ i (x i)| ^ P) *
        prob pr {s | ∀ i : Fin n, Conn ends s o (x i)} :=
    Finset.sum_le_sum fun x _ =>
      mul_le_mul_of_nonneg_right (hgm x) (hPx0 x)
  have hstep2 : (∑ x : Fin n → V, (∑ i, (q i / P) * |Φ i (x i)| ^ P) *
        prob pr {s | ∀ i : Fin n, Conn ends s o (x i)})
      = ∑ i : Fin n, (q i / P) *
        ∑ x : Fin n → V, |Φ i (x i)| ^ P *
          prob pr {s | ∀ i : Fin n, Conn ends s o (x i)} := by
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => by ring
  have hstep3 : (∑ i : Fin n, (q i / P) *
        ∑ x : Fin n → V, |Φ i (x i)| ^ P *
          prob pr {s | ∀ i : Fin n, Conn ends s o (x i)})
      ≤ ∑ i : Fin n, (q i / P) *
        ∑ x : Fin n → V, |Φ i (x i)| ^ P * treeSum (twoPoint pr ends) n o x :=
    Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum fun x _ =>
          mul_le_mul_of_nonneg_left (hTGx x) (Real.rpow_nonneg (abs_nonneg _) P))
        (div_nonneg (hq i) hP0)
  have hstep4 : (∑ i : Fin n, (q i / P) *
        ∑ x : Fin n → V, |Φ i (x i)| ^ P * treeSum (twoPoint pr ends) n o x)
      ≤ ∑ i : Fin n, (q i / P) * ((VolumeMoments.M (n - 1) : ℝ) * (n : ℝ) ^ (max P 1) *
          (clusterVolume pr ends o) ^ (2 * n - 2) *
          ∑ y : V, |Φ i y| ^ P * twoPoint pr ends o y) :=
    Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_left (hW n hn i (Φ i) P hP0 hinv) (div_nonneg (hq i) hP0)
  have hstep5 : (∑ i : Fin n, (q i / P) * ((VolumeMoments.M (n - 1) : ℝ) * (n : ℝ) ^ (max P 1) *
        (clusterVolume pr ends o) ^ (2 * n - 2) *
        ∑ y : V, |Φ i y| ^ P * twoPoint pr ends o y))
      = ((VolumeMoments.M (n - 1) : ℝ) * (n : ℝ) ^ (max P 1) *
          (clusterVolume pr ends o) ^ (2 * n - 2)) *
        ∑ i : Fin n, (q i / P) * ∑ y : V, |Φ i y| ^ P * twoPoint pr ends o y := by
    conv_rhs => rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hstep6 : (∑ i : Fin n, (q i / P) * ∑ y : V, |Φ i y| ^ P * twoPoint pr ends o y) ≤ M := by
    have hw1 : ∑ i : Fin n, q i / P = 1 := by
      rw [← Finset.sum_div, ← hPdef]
      exact div_self hPpos.ne'
    calc ∑ i : Fin n, (q i / P) * ∑ y : V, |Φ i y| ^ P * twoPoint pr ends o y
        ≤ ∑ i : Fin n, (q i / P) * M :=
          Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hM' i) (div_nonneg (hq i) hP0)
      _ = (∑ i : Fin n, q i / P) * M := (Finset.sum_mul _ _ _).symm
      _ = M := by rw [hw1, one_mul]
  have hstep7 : ((VolumeMoments.M (n - 1) : ℝ) * (n : ℝ) ^ (max P 1) *
        (clusterVolume pr ends o) ^ (2 * n - 2)) *
        ∑ i : Fin n, (q i / P) * ∑ y : V, |Φ i y| ^ P * twoPoint pr ends o y
      ≤ ((VolumeMoments.M (n - 1) : ℝ) * (n : ℝ) ^ (max P 1) *
        (clusterVolume pr ends o) ^ (2 * n - 2)) * M :=
    mul_le_mul_of_nonneg_left hstep6 hT0
  rw [expectReal_tupleSum pr ends o n (fun x => ∏ i, |Φ i (x i)| ^ q i)]
  calc ∑ x : Fin n → V, (∏ i, |Φ i (x i)| ^ q i) *
        prob pr {s | ∀ i : Fin n, Conn ends s o (x i)}
      ≤ ∑ x : Fin n → V, (∑ i, (q i / P) * |Φ i (x i)| ^ P) *
          prob pr {s | ∀ i : Fin n, Conn ends s o (x i)} := hstep1
    _ = ∑ i : Fin n, (q i / P) *
          ∑ x : Fin n → V, |Φ i (x i)| ^ P *
            prob pr {s | ∀ i : Fin n, Conn ends s o (x i)} := hstep2
    _ ≤ ∑ i : Fin n, (q i / P) *
          ∑ x : Fin n → V, |Φ i (x i)| ^ P * treeSum (twoPoint pr ends) n o x := hstep3
    _ ≤ ∑ i : Fin n, (q i / P) * ((VolumeMoments.M (n - 1) : ℝ) * (n : ℝ) ^ (max P 1) *
          (clusterVolume pr ends o) ^ (2 * n - 2) *
          ∑ y : V, |Φ i y| ^ P * twoPoint pr ends o y) := hstep4
    _ = ((VolumeMoments.M (n - 1) : ℝ) * (n : ℝ) ^ (max P 1) *
          (clusterVolume pr ends o) ^ (2 * n - 2)) *
        ∑ i : Fin n, (q i / P) * ∑ y : V, |Φ i y| ^ P * twoPoint pr ends o y := hstep5
    _ ≤ ((VolumeMoments.M (n - 1) : ℝ) * (n : ℝ) ^ (max P 1) *
          (clusterVolume pr ends o) ^ (2 * n - 2)) * M := hstep7
    _ = (VolumeMoments.M (n - 1) : ℝ) * (n : ℝ) ^ (max (∑ i, q i) 1) *
          (clusterVolume pr ends o) ^ (2 * n - 2) * M := by rw [← hPdef]

/-- **`lem:spatial_tree_graph` in the printed form.**  With the expectation
`E[|K|^{n-1} ∑_{y ∈ K} |Φ_i y|^p]` on the right — exactly as printed in the source — the bound
is

  `E[∑_{x ∈ K^n} ∏_i |Φ_i(x_i)|^{q_i}]`
    `≤ (2n−3)!! n^{max{p,1}} (E|K|)^{2n−2} max_i E[|K|^{n-1} ∑_{y ∈ K} |Φ_i y|^p]`.

The passage from `spatial_tree_graph_of_inputs` uses `expectation_spatialMoment` (the identity
`E ∑_{y ∈ K} w y = ∑_y w y P(o ↔ y)`) and `|K| ≥ 1` to replace the weighted two-point sum by
the larger printed expression; this is the only place where the printed `|K|^{n-1}` factor is
used, and it costs nothing because the factor is `≥ 1`. -/
theorem spatial_tree_graph_printed (pr : E → ℝ) (hp : ∀ e, 0 ≤ pr e) (hp1 : ∀ e, pr e ≤ 1)
    (ends : E → Sym2 V) (o : V) (hTG : TreeGraphBound pr ends (twoPoint pr ends))
    (hW : WeightedTreeSum pr ends o)
    (hinv : ∀ a b : V, twoPoint pr ends a b = twoPoint pr ends o (b - a))
    {n : ℕ} (hn : 1 ≤ n) (q : Fin n → ℝ) (Φ : Fin n → V →+ ℝ) (M : ℝ)
    (hq : ∀ i, 0 ≤ q i) (hP : 0 < ∑ i, q i)
    (hM : ∀ i, expectReal pr (fun s => ((clusterF ends s o).card : ℝ) ^ (n - 1) *
            ∑ y ∈ clusterF ends s o, |Φ i y| ^ (∑ j, q j)) ≤ M) :
    expectReal pr (fun s => tupleSum (clusterF ends s o) n (fun x => ∏ i, |Φ i (x i)| ^ q i))
      ≤ (VolumeMoments.M (n - 1) : ℝ) * (n : ℝ) ^ (max (∑ i, q i) 1) *
          (clusterVolume pr ends o) ^ (2 * n - 2) * M := by
  refine spatial_tree_graph_of_inputs pr hp hp1 ends o hTG hW hinv hn q Φ M hq hP ?_
  intro i
  have hw : ∀ y : V, 0 ≤ |Φ i y| ^ (∑ j, q j) :=
    fun y => Real.rpow_nonneg (abs_nonneg _) _
  refine le_trans (le_of_eq ?_)
    (le_trans (expectReal_cluster_sum_le_pow_mul pr hp hp1 ends o hn _ hw) (hM i))
  exact (expectation_spatialMoment pr ends o (fun y => |Φ i y| ^ (∑ j, q j))).symm

/-! ## 7. Non-vacuity check: the `n = 1` case of the weighted tree-sum input

For one label the tree sum is just the two-point function, so the `n = 1` instance of
`WeightedTreeSum` is the *identity*
`∑_{x} |φ x|^p · treeSum k 1 o x = ∑_y |φ y|^p P(o ↔ y) = E ∑_{y ∈ K} |φ y|^p`,
with constants `(2·1−3)!! = 1`, `1^{max{p,1}} = 1`, `(E|K|)^0 = 1`.  It needs no translation
invariance and no BK, which pins down the constant bookkeeping at the base case. -/

/-- Non-vacuity of `WeightedTreeSum` at `n = 1`: the inequality holds with no
hypotheses. The path count uses `treeSum_one` from `TreeExpansion.Consistency`. -/
theorem weightedTreeSum_one (pr : E → ℝ) (ends : E → Sym2 V) (o : V) (φ : V →+ ℝ) (p : ℝ)
    (_hp : 0 ≤ p) :
    (∑ x : Fin 1 → V, |φ (x 0)| ^ p * treeSum (twoPoint pr ends) 1 o x)
      ≤ (VolumeMoments.M 0 : ℝ) * (1 : ℝ) ^ (max p 1) *
          (clusterVolume pr ends o) ^ (2 * 1 - 2) *
          ∑ y : V, |φ y| ^ p * twoPoint pr ends o y := by
  classical
  have hL : (∑ x : Fin 1 → V, |φ (x 0)| ^ p * treeSum (twoPoint pr ends) 1 o x)
      = ∑ y : V, |φ y| ^ p * twoPoint pr ends o y := by
    rw [Finset.sum_congr rfl fun x _ => by rw [treeSum_one]]
    refine Fintype.sum_equiv (Equiv.funUnique (Fin 1) V)
      (fun x : Fin 1 → V => |φ (x 0)| ^ p * twoPoint pr ends o (x 0))
      (fun y : V => |φ y| ^ p * twoPoint pr ends o y) ?_
    intro x
    simp [Equiv.funUnique]
  rw [hL]
  simp [VolumeMoments.M_zero]

end TranslationInvariant

/-! ## Axiom audit -/

#print axioms PercLib.CriticalLRP.TreeExpansion.prod_rpow_le_sum_div
#print axioms PercLib.CriticalLRP.TreeExpansion.sum_tuple_apply
#print axioms PercLib.CriticalLRP.TreeExpansion.tuple_prod_rpow_le
#print axioms PercLib.CriticalLRP.TreeExpansion.tuple_prod_rpow_le_of_forall_le
#print axioms PercLib.CriticalLRP.TreeExpansion.expectReal_sum
#print axioms PercLib.CriticalLRP.TreeExpansion.expectReal_mono
#print axioms PercLib.CriticalLRP.TreeExpansion.mem_piFinset_clusterF
#print axioms PercLib.CriticalLRP.TreeExpansion.expectReal_tupleSum
#print axioms PercLib.CriticalLRP.TreeExpansion.expectReal_tuple_prod
#print axioms PercLib.CriticalLRP.TreeExpansion.spatial_amgm_expectation
#print axioms PercLib.CriticalLRP.TreeExpansion.spatial_amgm_expectation_le_of_forall_le
#print axioms PercLib.CriticalLRP.TreeExpansion.sum_rpow_le_sum_rpow_of_le_one
#print axioms PercLib.CriticalLRP.TreeExpansion.sum_rpow_le_card_mul_of_one_le
#print axioms PercLib.CriticalLRP.TreeExpansion.sum_rpow_le_card_mul
#print axioms PercLib.CriticalLRP.TreeExpansion.abs_addHom_telescope_rpow_le
#print axioms PercLib.CriticalLRP.TreeExpansion.expectReal_cluster_sum_le_pow_mul
#print axioms PercLib.CriticalLRP.TreeExpansion.prob_conn_le_treeSum
#print axioms PercLib.CriticalLRP.TreeExpansion.spatial_tree_graph_of_inputs
#print axioms PercLib.CriticalLRP.TreeExpansion.spatial_tree_graph_printed
#print axioms PercLib.CriticalLRP.TreeExpansion.treeSum_one
#print axioms PercLib.CriticalLRP.TreeExpansion.weightedTreeSum_one
