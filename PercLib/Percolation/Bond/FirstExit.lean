/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.
New first-exit and internal/boundary independence proofs on the canonical bond law.
This is the elementary q-normalized boundary bound of issue 193, not a sharpness
or BK iteration theorem. No upstream proof is copied and no Input is introduced.
-/
module

public import PercLib.Percolation.Bond.LocalConnectivity
public import PercLib.Percolation.Bond.Forest
public import PercLib.Probability.ProdBernoulliIndependence
public import PercLib.Probability.OpenEventHarris

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set PercLib.Probability
open scoped ENNReal NNReal Classical

namespace PercLib.Percolation.Bond
variable {V : Type*}

/-- A connection from inside a domain to outside it has a first exiting edge,
preceded by a connection entirely inside the domain. -/
theorem exists_first_exit (S : Set V) {ω : Config V} {x w : V}
    (hx : x ∈ S) (hw : w ∉ S) (hc : ω ∈ conn x w) :
    ∃ y, ∃ hy : y ∈ S, ∃ z, z ∉ S ∧
      ((openGraph ω).induce S).Reachable ⟨x,hx⟩ ⟨y,hy⟩ ∧ s(y,z) ∈ ω := by
  obtain ⟨p⟩ := hc
  revert hx
  induction p with
  | nil => intro hx; exact (hw hx).elim
  | @cons a b c hab p ih =>
    intro hx
    by_cases hb : b ∈ S
    · obtain ⟨y,hy,z,hz,hlocal,he⟩ := ih hw hb
      have hadj : ((openGraph ω).induce S).Adj ⟨a,hx⟩ ⟨b,hb⟩ := hab
      exact ⟨y,hy,z,hz,hadj.reachable.trans hlocal,he⟩
    · exact ⟨a,hx,b,hb,.refl _,((openGraph_adj_iff ω a b).mp hab).1⟩

/-- Internal connectivity is independent of a boundary pair, even for an infinite
countable domain. No ambient countability is needed for this factorization. -/
theorem law_localConn_inter_boundary (q : Sym2 V → unitInterval) (S : Set V) [Countable S]
    (x y : S) (z : V) (hz : z ∉ S) :
    law q {ω | ((openGraph ω).induce S).Reachable x y ∧ s((y:V),z) ∈ ω} =
      law q {ω | ((openGraph ω).induce S).Reachable x y} *
        (unitInterval.toNNReal (q s((y:V),z)) : ℝ≥0∞) := by
  let R : Set (Sym2 V) := Set.range (Sym2.map (Subtype.val : S → V))
  let e := s((y:V),z)
  have he : e ∉ R := by
    rintro ⟨a,ha⟩
    have hzmem : z ∈ Sym2.map (Subtype.val : S → V) a := by rw [ha]; simp [e]
    obtain ⟨v,_,hv⟩ := Sym2.mem_map.mp hzmem
    exact hz (hv ▸ v.property)
  let A : Set (Set R) := {η | openGraph
    {a : Sym2 S | (⟨Sym2.map Subtype.val a, Set.mem_range_self a⟩ : R) ∈ η} |>.Reachable x y}
  have hA : MeasurableSet A := by
    have hm : Measurable (fun η : Set R =>
        {a : Sym2 S | (⟨Sym2.map Subtype.val a, Set.mem_range_self a⟩ : R) ∈ η}) :=
      Measurable.of_mem (fun a => measurable_set_mem
        (⟨Sym2.map Subtype.val a, Set.mem_range_self a⟩ : R))
    exact (measurableSet_conn x y).preimage hm
  let B : Set (Set ({e} : Set (Sym2 V))) := {η | (⟨e,Set.mem_singleton e⟩ : ({e} : Set (Sym2 V))) ∈ η}
  have hB : MeasurableSet B := measurableSet_mem _
  have h := prodBernoulli_block_inter q R {e} (Set.disjoint_singleton_right.mpr he) A B hA hB
  have hlocal (ω : Config V) : {i : R | (i : Sym2 V) ∈ ω} ∈ A ↔
      ((openGraph ω).induce S).Reachable x y := by
    rw [openGraph_induce]
    rfl
  simp_rw [hlocal] at h
  change law q {ω | ((openGraph ω).induce S).Reachable x y ∧ e ∈ ω} =
    law q {ω | ((openGraph ω).induce S).Reachable x y} * law q {ω | e ∈ ω} at h
  simpa only [law, prodBernoulli_setOf_mem] using h

/-- The first-exit bound, with the finite domain and its complement as index types. -/
theorem law_escape_le_phi_subtype [Countable V] (q : Sym2 V → unitInterval)
    (S : Finset V) (x : (S : Set V)) :
    law q (⋃ w ∈ (S : Set V)ᶜ, conn (x:V) w) ≤
      ∑ y : (S : Set V), ∑' z : ((S : Set V)ᶜ : Set V),
        law q {ω | ((openGraph ω).induce (S : Set V)).Reachable x y} *
          (unitInterval.toNNReal (q s((y:V),(z:V))) : ℝ≥0∞) := by
  let A (y : (S : Set V)) (z : ((S : Set V)ᶜ : Set V)) : Set (Config V) :=
    {ω | ((openGraph ω).induce (S : Set V)).Reachable x y ∧ s((y:V),(z:V)) ∈ ω}
  have hsub : (⋃ w ∈ (S : Set V)ᶜ, conn (x:V) w) ⊆ ⋃ y, ⋃ z, A y z := by
    intro ω hω
    obtain ⟨w,hw,hc⟩ := Set.mem_iUnion₂.mp hω
    obtain ⟨y,hy,z,hz,hlocal,he⟩ := exists_first_exit (S : Set V) x.property hw hc
    exact Set.mem_iUnion₂.mpr ⟨⟨y,hy⟩,⟨z,hz⟩,hlocal,he⟩
  calc
    _ ≤ law q (⋃ y, ⋃ z, A y z) := measure_mono hsub
    _ ≤ ∑' y, law q (⋃ z, A y z) := measure_iUnion_le _
    _ ≤ ∑' y, ∑' z, law q (A y z) := ENNReal.tsum_le_tsum (fun _ => measure_iUnion_le _)
    _ = _ := by
      rw [tsum_fintype]
      apply Finset.sum_congr rfl
      intro y _
      apply tsum_congr
      intro z
      exact law_localConn_inter_boundary q (S : Set V) x y z z.property

/-- The q-normalized boundary functional, written explicitly without introducing a definition. -/
theorem law_escape_le_phi [Countable V] (q : Sym2 V → unitInterval)
    (S : Finset V) {x : V} (hx : x ∈ S) :
    law q (⋃ w ∈ (S : Set V)ᶜ, conn x w) ≤
      ∑ y ∈ S, ∑' z, if z ∈ S then 0 else
        law q {ω | ∃ hy : y ∈ S,
          ((openGraph ω).induce (S : Set V)).Reachable ⟨x,hx⟩ ⟨y,hy⟩} *
            (unitInterval.toNNReal (q s(y,z)) : ℝ≥0∞) := by
  have h := law_escape_le_phi_subtype q S ⟨x,hx⟩
  convert h using 1
  rw [← Finset.sum_coe_sort]
  apply Finset.sum_congr rfl
  intro y _
  have heq : {ω : Config V | ∃ hy : (y:V) ∈ S,
      ((openGraph ω).induce (S : Set V)).Reachable ⟨x,hx⟩ ⟨(y:V),hy⟩} =
      {ω : Config V | ((openGraph ω).induce (S : Set V)).Reachable ⟨x,hx⟩ y} := by
    ext ω
    simp
  rw [heq]
  symm
  simpa only [Set.indicator, Set.mem_compl_iff, Finset.mem_coe, ite_not] using
    (tsum_subtype ((S : Set V)ᶜ) (fun z : V =>
      law q {ω | ((openGraph ω).induce (S : Set V)).Reachable ⟨x,hx⟩ y} *
        (unitInterval.toNNReal (q s((y:V),z)) : ℝ≥0∞)))

/-- An infinite cluster exits every finite set, so the same boundary functional bounds theta. -/
theorem law_cluster_infinite_le_phi [Countable V] (q : Sym2 V → unitInterval)
    (S : Finset V) {x : V} (hx : x ∈ S) :
    law q {ω | (cluster ω x).Infinite} ≤
      ∑ y ∈ S, ∑' z, if z ∈ S then 0 else
        law q {ω | ∃ hy : y ∈ S,
          ((openGraph ω).induce (S : Set V)).Reachable ⟨x,hx⟩ ⟨y,hy⟩} *
            (unitInterval.toNNReal (q s(y,z)) : ℝ≥0∞) := by
  refine (measure_mono ?_).trans (law_escape_le_phi q S hx)
  intro ω hi
  obtain ⟨w,hw,hnot⟩ := hi.exists_notMem_finite S.finite_toSet
  exact Set.mem_iUnion₂.mpr ⟨w,hnot,hw⟩

/-- A singleton domain gives the explicit off-diagonal row sum. -/
theorem law_escape_singleton_le_rowSum [Countable V] (q : Sym2 V → unitInterval) (x : V) :
    law q (⋃ w ∈ ({x} : Set V)ᶜ, conn x w) ≤
      ∑' z, if z = x then 0 else (unitInterval.toNNReal (q s(x,z)) : ℝ≥0∞) := by
  simpa using law_escape_le_phi q {x} (Finset.mem_singleton_self x)

/-- A finite domain with zero boundary profile has zero escape probability. -/
theorem law_escape_eq_zero_of_boundary_zero [Countable V] (q : Sym2 V → unitInterval)
    (S : Finset V) {x : V} (hx : x ∈ S)
    (hz : ∀ y ∈ S, ∀ z ∉ S, q s(y,z) = 0) :
    law q (⋃ w ∈ (S : Set V)ᶜ, conn x w) = 0 := by
  apply le_antisymm _ zero_le
  refine (law_escape_le_phi q S hx).trans_eq ?_
  apply Finset.sum_eq_zero
  intro y hy
  apply ENNReal.tsum_eq_zero.mpr
  intro z
  by_cases h : z ∈ S
  · simp [h]
  · simp [h, hz y hy z h]

/-- On the ray, leaving the initial interval is equivalent almost surely to
reaching its first exterior vertex. -/
theorem law_escape_nat_range (q : Sym2 ℕ → unitInterval) (t : unitInterval)
    (hedge : ∀ n, q s(n,n+1) = t)
    (hz : ∀ m n, m ≠ n → ¬ (m + 1 = n ∨ n + 1 = m) → q s(m,n) = 0)
    (n : ℕ) :
    law q (⋃ w ∈ (Finset.range (n+1) : Set ℕ)ᶜ, conn 0 w) =
      (unitInterval.toNNReal t : ℝ≥0∞) ^ (n+1) := by
  have heq : (⋃ w ∈ (Finset.range (n+1) : Set ℕ)ᶜ, conn 0 w) =ᵐ[law q]
      conn 0 (n+1) := by
    filter_upwards [ae_openGraph_le_hasse_nat q hz] with ω hω
    apply propext
    constructor
    · intro h
      obtain ⟨w,hw,⟨p⟩⟩ := Set.mem_iUnion₂.mp h
      have hle : n + 1 ≤ w := by simpa using hw
      have hm := SimpleGraph.Walk.mem_support_hasse_of_ge_of_le ℕ (p.mapLe hω) (Nat.zero_le (n+1)) hle
      have hm' : n+1 ∈ p.support := by simpa using hm
      exact ⟨p.takeUntil (n+1) hm'⟩
    · intro h
      exact Set.mem_iUnion₂.mpr ⟨n+1,by simp,h⟩
  calc
    _ = tau q 0 (n+1) := measure_congr heq
    _ = _ := by simpa using tau_nat_eq_pow_of_le q t hedge hz (Nat.zero_le (n+1))

/-- The explicit boundary sum is sharp on every finite initial interval of the ray. -/
theorem phi_nat_range (q : Sym2 ℕ → unitInterval) (t : unitInterval)
    (hedge : ∀ n, q s(n,n+1) = t)
    (hz : ∀ m n, m ≠ n → ¬ (m + 1 = n ∨ n + 1 = m) → q s(m,n) = 0)
    (n : ℕ) :
    (∑ y ∈ Finset.range (n+1), ∑' z, if z ∈ Finset.range (n+1) then 0 else
      law q {ω | ∃ hy : y ∈ Finset.range (n+1),
        ((openGraph ω).induce (Finset.range (n+1) : Set ℕ)).Reachable
          ⟨0,by simp⟩ ⟨y,hy⟩} *
        (unitInterval.toNNReal (q s(y,z)) : ℝ≥0∞)) =
      (unitInterval.toNNReal t : ℝ≥0∞) ^ (n+1) := by
  have hzero (y z : ℕ) (hy : y ∈ Finset.range (n+1))
      (hz' : z ∉ Finset.range (n+1)) (hpair : y ≠ n ∨ z ≠ n+1) : q s(y,z) = 0 := by
    have hy' : y < n+1 := Finset.mem_range.mp hy
    have hz'' : n+1 ≤ z := by simpa using hz'
    exact hz y z (by omega) (by omega)
  apply le_antisymm
  · rw [Finset.sum_eq_single n]
    · rw [tsum_eq_single (n+1)]
      · simp only [Finset.mem_range, lt_self_iff_false, ↓reduceIte, hedge]
        rw [pow_succ]
        gcongr
        calc
          _ ≤ tau q 0 n := measure_mono (by
            intro ω h
            obtain ⟨hy,hc⟩ := h
            exact conn_of_localConn ω _ _ _ hc)
          _ = _ := by simpa using tau_nat_eq_pow_of_le q t hedge hz (Nat.zero_le n)
      · intro z hne
        by_cases hz' : z ∈ Finset.range (n+1)
        · simp [hz']
        · simp [hz', hzero n z (by simp) hz' (Or.inr hne)]
    · intro y hy hne
      apply ENNReal.tsum_eq_zero.mpr
      intro z
      by_cases hz' : z ∈ Finset.range (n+1)
      · simp [hz']
      · simp [hz', hzero y z hy hz' (Or.inl hne)]
    · simp
  · rw [← law_escape_nat_range q t hedge hz n]
    simpa only [Finset.mem_range] using
      law_escape_le_phi q (Finset.range (n+1)) (x := 0) (by simp)

-- Non-vacuity: singleton and zero-boundary cases instantiate the public bounds.
example [Countable V] (q : Sym2 V → unitInterval) (x : V) :
    law q (⋃ w ∈ ({x} : Set V)ᶜ, conn x w) ≤
      ∑' z, if z = x then 0 else (unitInterval.toNNReal (q s(x,z)) : ℝ≥0∞) :=
  law_escape_singleton_le_rowSum q x

example (n : ℕ) : law (fun _ : Sym2 ℕ => 0)
    (⋃ w ∈ (Finset.range (n+1) : Set ℕ)ᶜ, conn 0 w) = 0 :=
  law_escape_eq_zero_of_boundary_zero _ _ (by simp) (by simp)

-- Every parameter, including 0 and 1, has a concrete ray profile realizing equality.
example (t : unitInterval) (n : ℕ) : ∃ q : Sym2 ℕ → unitInterval,
    law q (⋃ w ∈ (Finset.range (n+1) : Set ℕ)ᶜ, conn 0 w) =
      (unitInterval.toNNReal t : ℝ≥0∞) ^ (n+1) := by
  let q : Sym2 ℕ → unitInterval := Sym2.lift ⟨fun m k =>
    if m + 1 = k ∨ k + 1 = m then t else 0, by intro m k; simp [or_comm]⟩
  have he (k) : q s(k,k+1) = t := by simp [q]
  have hz (m k) (_ : m ≠ k) (h : ¬ (m + 1 = k ∨ k + 1 = m)) : q s(m,k) = 0 := by
    simp [q,h]
  exact ⟨q, law_escape_nat_range q t he hz n⟩

end PercLib.Percolation.Bond
