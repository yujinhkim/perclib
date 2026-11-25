/- Integrated from independently rebuilt Ultramath work, base revision 75f8858d8e30ea17b20f9ff1d216bc1508c01ce2.
Scratch source: ../../.ultramath/smwpwq50m/m1/I417A/Expansion.lean ; module path rewritten only.
-/

/-
# Hutchcroft Lemma I.4.17, direction A: labelled-vertex expansion

`cardFun` is the extended cardinality (`⊤` on infinite clusters).  This module expands its
powers over labelled vertex tuples; this is the expansion used in the proof of Lemma I.4.17.
All identities are in `ℝ≥0∞`, so infinite clusters are covered with no finiteness hypothesis.
-/
module

public import PercLib.CriticalLRP.Correlation.I417.Nonnegative.Defs

set_option linter.unusedSectionVars false

@[expose] public section

open MeasureTheory Measure ProbabilityTheory unitInterval
open scoped ENNReal

namespace PercLib.CriticalLRP

namespace I417A

variable {V : Type*} [Countable V]

/-- `cardFun` is the supremum of the cardinalities of the finite subsets of `S`. -/
theorem cardFun_eq_iSup_finset (S : Set V) :
    Percolation.cardFun S =
      ⨆ t : {t : Finset V // (t : Set V) ⊆ S}, (t.1.card : ℝ≥0∞) := by
  classical
  rw [Percolation.cardFun]
  refine le_antisymm (iSup_le fun n => ?_) (iSup_le fun t => ?_)
  · by_cases h : ∃ t : Finset V, n ≤ t.card ∧ (t : Set V) ⊆ S
    · rw [ite_eq_left h, mul_one]
      obtain ⟨t, hcard, hsub⟩ := h
      exact le_trans (by exact_mod_cast hcard)
        (le_iSup (fun t : {t : Finset V // (t : Set V) ⊆ S} => (t.1.card : ℝ≥0∞)) ⟨t, hsub⟩)
    · rw [ite_eq_right h, mul_zero]
      exact bot_le
  · refine le_trans ?_
      (le_iSup (fun n : ℕ =>
        (n : ℝ≥0∞) * ite (∃ t : Finset V, n ≤ t.card ∧ (t : Set V) ⊆ S) 1 0) t.1.card)
    rw [ite_eq_left ⟨t.1, le_rfl, t.2⟩, mul_one]

/-- The extended cardinality is the total mass of the indicator function. -/
theorem tsum_indicator_one (S : Set V) :
    ∑' v : V, S.indicator (fun _ => (1 : ℝ≥0∞)) v = Percolation.cardFun S := by
  classical
  have key : ∀ s : Finset V, ∑ v ∈ s, S.indicator (fun _ => (1 : ℝ≥0∞)) v =
      ((s.filter (fun v => v ∈ S)).card : ℝ≥0∞) := by
    intro s
    simp only [Set.indicator_apply]
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
  have h1 : (∑' v : V, S.indicator (fun _ => (1 : ℝ≥0∞)) v) =
      ⨆ s : Finset V, ((s.filter (fun v => v ∈ S)).card : ℝ≥0∞) := by
    rw [ENNReal.tsum_eq_iSup_sum]
    exact iSup_congr key
  rw [h1, cardFun_eq_iSup_finset]
  refine le_antisymm (iSup_le fun s => ?_) (iSup_le fun t => ?_)
  · exact le_iSup (fun t : {t : Finset V // (t : Set V) ⊆ S} => (t.1.card : ℝ≥0∞))
      ⟨s.filter (fun v => v ∈ S), fun v hv => (Finset.mem_filter.mp hv).2⟩
  · refine le_iSup_of_le t.1 ?_
    rw [Finset.filter_true_of_mem (fun v hv => t.2 hv)]

/-- Powers of an `ℝ≥0∞`-valued sum expand over labelled index tuples. -/
theorem tsum_pow_fin {A : Type*} (a : A → ℝ≥0∞) (n : ℕ) :
    (∑' i : A, a i) ^ n = ∑' f : Fin n → A, ∏ i, a (f i) := by
  classical
  induction n with
  | zero =>
    rw [pow_zero]
    rw [tsum_eq_single (fun i => i.elim0) (by
      intro b hb
      exact absurd (Subsingleton.elim b (fun i => i.elim0)) hb)]
    simp
  | succ n ih =>
    rw [pow_succ, ih]
    have step1 : (∑' f : Fin n → A, ∏ i, a (f i)) * (∑' x : A, a x) =
        ∑' f : Fin n → A, ∑' x : A, (∏ i, a (f i)) * a x := by
      rw [← ENNReal.tsum_mul_right]
      refine tsum_congr fun f => ?_
      rw [ENNReal.tsum_mul_left]
    rw [step1, ← ENNReal.tsum_prod]
    have hswap : (∑' p : (Fin n → A) × A, (∏ i, a (p.1 i)) * a p.2) =
        ∑' q : A × (Fin n → A), (∏ i, a (q.2 i)) * a q.1 := by
      rw [← Equiv.tsum_eq (Equiv.prodComm (Fin n → A) A)
        (fun q : A × (Fin n → A) => (∏ i, a (q.2 i)) * a q.1)]
      exact tsum_congr fun c => rfl
    rw [hswap]
    rw [← Equiv.tsum_eq (Fin.consEquiv (fun _ : Fin (n + 1) => A)).symm
      (fun q : A × (Fin n → A) => (∏ i, a (q.2 i)) * a q.1)]
    refine tsum_congr fun g => ?_
    have hg : (Fin.consEquiv (fun _ : Fin (n + 1) => A)).symm g =
        (g 0, fun i => g i.succ) := by
      rw [Equiv.symm_apply_eq]
      have h1 : (Fin.consEquiv (fun _ : Fin (n + 1) => A)) (g 0, fun i => g i.succ) =
          Fin.cons (g 0) (fun i => g i.succ) := by
        funext i
        rw [Fin.consEquiv_apply]
      rw [h1]
      exact (Fin.cons_self_tail g).symm
    rw [hg, Fin.prod_univ_succ, mul_comm]

/-- **Expansion of cluster-moment powers over labelled vertices.** -/
theorem cardFun_pow_eq_tsum (S : Set V) (n : ℕ) :
    Percolation.cardFun S ^ n =
      ∑' f : Fin n → V, ∏ i, S.indicator (fun _ => (1 : ℝ≥0∞)) (f i) := by
  rw [← tsum_indicator_one (V := V) S]
  exact tsum_pow_fin (fun v => S.indicator (fun _ => (1 : ℝ≥0∞)) v) n

/-! ## The labelled events -/

theorem prod_indicator_eq_indicator (x : V) {p : ℕ} (f : Fin p → V) :
    (fun ω : Config V => ∏ i, (cluster ω x).indicator (fun _ => (1 : ℝ≥0∞)) (f i)) =
      (labelEvent x f).indicator (fun _ => (1 : ℝ≥0∞)) := by
  funext ω
  by_cases h : ∀ i, f i ∈ cluster ω x
  · rw [Set.indicator_of_mem (show ω ∈ labelEvent x f from h)]
    exact Finset.prod_eq_one (fun i _ => Set.indicator_of_mem (h i) _)
  · obtain ⟨i, hi⟩ := not_forall.mp h
    rw [Set.indicator_of_notMem (show ω ∉ labelEvent x f from fun hc => hi (hc i))]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi _)

/-- Product of two `ℝ≥0∞`-valued sums as a sum over the product index type. -/
theorem tsum_mul_tsum_eq_tsum_prod {A B : Type*} (P : A → ℝ≥0∞) (Q : B → ℝ≥0∞) :
    (∑' a, P a) * (∑' b, Q b) = ∑' r : A × B, P r.1 * Q r.2 := by
  rw [← ENNReal.tsum_mul_right]
  rw [show (∑' a : A, P a * ∑' b : B, Q b) = ∑' a : A, ∑' b : B, P a * Q b from
    tsum_congr fun a => (ENNReal.tsum_mul_left (a := P a) (f := Q)).symm]
  rw [← ENNReal.tsum_prod]

theorem tsum_prod_mul_eq_tsum_mul {A B : Type*} (P : A → ℝ≥0∞) (Q : B → ℝ≥0∞) :
    (∑' r : A × B, P r.1 * Q r.2) = (∑' a, P a) * (∑' b, Q b) :=
  (tsum_mul_tsum_eq_tsum_prod P Q).symm

theorem prod_indicator_apply (x : V) {p : ℕ} (f : Fin p → V) (ω : Config V) :
    ∏ i, (cluster ω x).indicator (fun _ => (1 : ℝ≥0∞)) (f i) =
      (labelEvent x f).indicator (fun _ => (1 : ℝ≥0∞)) ω :=
  congrFun (prod_indicator_eq_indicator x f) ω

/-- Powers commute with a supremum of a monotone `ℕ`-indexed family in `ℝ≥0∞`. -/
theorem iSup_nat_pow {f : ℕ → ℝ≥0∞} (hf : Monotone f) (n : ℕ) :
    (⨆ k, f k) ^ n = ⨆ k, (f k) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    show (⨆ k, f k) ^ (n + 1) = ⨆ k, f k ^ (n + 1)
    have hrhs : (⨆ k, f k ^ (n + 1)) = ⨆ k, f k ^ n * f k :=
      iSup_congr fun k => pow_succ (f k) n
    rw [hrhs, pow_succ, ih]
    have step : (⨆ k, (f k) ^ n) * (⨆ k, f k) = ⨆ k, ⨆ l, (f k) ^ n * f l := by
      rw [ENNReal.iSup_mul]
      exact iSup_congr fun k => ENNReal.mul_iSup (f k ^ n) (f := f)
    rw [step]
    refine le_antisymm ?_ (iSup_le fun k => ?_)
    · refine iSup_le fun k => iSup_le fun l => ?_
      exact le_iSup_of_le (max k l)
        (mul_le_mul' (pow_le_pow_left' (hf (le_max_left k l)) n) (hf (le_max_right k l)))
    · exact le_iSup_of_le k (le_iSup (fun l => f k ^ n * f l) k)

/-- Powers of the extended cluster cardinality are continuous from below. -/
theorem cardFun_pow_cont {E : Type*} {G : Percolation.BondGraph V E} (𝓔 : ℕ → Finset E)
    (h𝓔mono : Monotone 𝓔) (h𝓔 : ∀ e : E, ∃ n, e ∈ 𝓔 n) (x : V) (k : ℕ) :
    ∀ (ω : Set E) (s : ℝ≥0∞), s < Percolation.cardFun (Percolation.cluster G ω x) ^ k →
      ∃ n, s < Percolation.cardFun (Percolation.cluster G (ω ∩ (𝓔 n : Set E)) x) ^ k := by
  classical
  intro ω s hs
  set f : ℕ → ℝ≥0∞ := fun n =>
    Percolation.cardFun (Percolation.cluster G (ω ∩ (𝓔 n : Set E)) x) with hfdef
  have hfmono : Monotone f := by
    intro m n hmn
    exact Percolation.cardFun_mono (fun y hy => Percolation.conn_mono G
      (Set.inter_subset_inter_right ω (Finset.coe_subset.mpr (h𝓔mono hmn))) hy)
  have hsup : (⨆ n, f n) = Percolation.cardFun (Percolation.cluster G ω x) := by
    refine le_antisymm (iSup_le fun n => Percolation.cardFun_mono
      (fun y hy => Percolation.conn_mono G (Set.inter_subset_left : _) hy)) ?_
    by_contra hcon
    have hlt : (⨆ n, f n) < Percolation.cardFun (Percolation.cluster G ω x) := not_le.mp hcon
    obtain ⟨n, hn⟩ := Percolation.cardFun_cont 𝓔 h𝓔mono h𝓔 G x ω _ hlt
    exact absurd hn (not_lt.mpr (le_iSup f n))
  rw [← hsup, iSup_nat_pow hfmono k] at hs
  by_contra hcon
  simp only [not_exists, not_lt] at hcon
  exact absurd hs (not_lt.mpr (iSup_le hcon))

end I417A

end PercLib.CriticalLRP
