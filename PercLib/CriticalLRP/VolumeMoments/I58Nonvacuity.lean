/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
m8, swarm smwhc77id, direction (H).

Non-vacuity analysis of the abstract finite weighted model of
`VolumeMoments/I58Cross.lean` (`T3_bound_global`, `lemma_I_5_8_assembly_global`).

Main finding (Section 3): the model hypotheses `hK : K w ⊆ V` (`V` a `Finset`),
`h0K : 0 ∈ K ω` and `hTI : pairAt` invariant under *all* translations of `ℤ^d`
are jointly unsatisfiable for any non-negative weight that is positive somewhere,
when `d ≥ 1`.  Hence the transport layer, as stated, can only be applied in the
degenerate case `K ω = ∅`, in which every cross term `T0,…,T4` vanishes
identically (Section 4).  Section 6 exhibits the *intended* rooted cluster law
(two sites, one Bernoulli edge) in which `hTI` is simply false, so `hTI` is not a
faithful formalisation of the paper's mass-transport step.  Section 7 records exact
rational arithmetic for the printed `(1/2) G` constant of the source.
-/
module

public import PercLib.CriticalLRP.VolumeMoments.I58Cross

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

set_option autoImplicit true

@[expose] public section

open Finset

set_option maxHeartbeats 800000

namespace PercLib.CriticalLRP.I58

variable {d : ℕ} {Ω : Type*} [Fintype Ω]

/-! ## 1. One-point marginals read off from `pairAt` -/

/-- `pairAt` at four copies of `0` is the one-point marginal `P(0 ∈ K)`. -/
lemma pairAt_zero (w : Ω → ℝ) (K : Ω → Finset (Site d)) :
    pairAt w K 0 0 0 0 = ex w (indIn K 0) := by
  simp only [pairAt, ex]
  refine Finset.sum_congr rfl fun ω _ => ?_
  simp only [indIn]
  split <;> ring

/-- `pairAt` at four copies of `t` is the one-point marginal `P(t ∈ K)`. -/
lemma pairAt_self (w : Ω → ℝ) (K : Ω → Finset (Site d)) (t : Site d) :
    pairAt w K t t t t = ex w (indIn K t) := by
  simp only [pairAt, ex]
  refine Finset.sum_congr rfl fun ω _ => ?_
  simp only [indIn]
  split <;> ring

/-- Translation invariance of the four-point function forces all one-point
marginals `P(t ∈ K)` to be equal. -/
lemma ex_indIn_eq_of_pairAt_shift (w : Ω → ℝ) (K : Ω → Finset (Site d))
    (hTI : ∀ p q r s t : Site d,
      pairAt w K p q r s = pairAt w K (p + t) (q + t) (r + t) (s + t))
    (t : Site d) : ex w (indIn K t) = ex w (indIn K 0) := by
  have h := hTI 0 0 0 0 t
  rw [pairAt_zero] at h
  simpa only [zero_add, pairAt_self] using h.symm

/-! ## 2. No finite set meets every translate in `ℤ^d`, `d ≥ 1` -/

/-- There is a lattice site outside any prescribed finite set, as soon as `d ≥ 1`. -/
lemma exists_site_not_mem (hd : 0 < d) (V : Finset (Site d)) :
    ∃ t : Site d, t ∉ V := by
  have hinj : Function.Injective (fun k : ℕ => (fun _ : Fin d => (k : ℤ)) : ℕ → Site d) := by
    intro k l h
    have h' := congrFun h ⟨0, hd⟩
    simpa using h'
  have hinf : (Set.range (fun k : ℕ => (fun _ : Fin d => (k : ℤ)) : ℕ → Site d)).Infinite :=
    Set.infinite_range_of_injective hinj
  obtain ⟨a, -, ha⟩ := hinf.exists_notMem_finset V
  exact ⟨a, ha⟩

/-- A non-empty finite set of sites is never invariant under a non-zero translation. -/
lemma eq_empty_of_shift_invariant (hd : 0 < d) (V : Finset (Site d)) (t : Site d)
    (ht : t ≠ 0) (hV : ∀ x : Site d, (x ∈ V ↔ x + t ∈ V)) : V = ∅ := by
  ext x
  simp only [Finset.notMem_empty, iff_false]
  intro hx
  obtain ⟨i, hi⟩ : ∃ i : Fin d, t i ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    exact ht (funext h)
  obtain ⟨x₁, hx₁V, hmax⟩ := V.exists_max_image (fun x : Site d => x i) ⟨x, hx⟩
  obtain ⟨x₀, hx₀V, hmin⟩ := V.exists_min_image (fun x : Site d => x i) ⟨x, hx⟩
  have hmem₁ : x₁ + t ∈ V := (hV x₁).mp hx₁V
  have hmem₀ : x₀ + t ∈ V := (hV x₀).mp hx₀V
  have hle := hmax (x₁ + t) hmem₁
  have hge := hmin (x₀ + t) hmem₀
  simp only [Pi.add_apply] at hle hge
  exact hi (by linarith)

/-! ## 3. The hypothesis package of `T3_bound_global` is unsatisfiable -/

/-- **Main theorem.** On the abstract model, translation invariance of the
four-point function together with `K ω ⊆ V` for a *finite* ambient set `V` forces
`K ω = ∅` at every configuration of positive weight. -/
theorem eq_empty_of_pairAt_shift (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω)
    (K : Ω → Finset (Site d)) (V : Finset (Site d)) (hd : 0 < d)
    (hK : ∀ ω, K ω ⊆ V)
    (hTI : ∀ p q r s t : Site d,
      pairAt w K p q r s = pairAt w K (p + t) (q + t) (r + t) (s + t))
    (ω : Ω) (hω : 0 < w ω) : K ω = ∅ := by
  obtain ⟨t, ht⟩ := exists_site_not_mem hd V
  have hind_t : ∀ ω' : Ω, indIn K t ω' = 0 := by
    intro ω'
    simp only [indIn]
    rw [ite_eq_right]
    intro hmem
    exact ht (hK ω' hmem)
  have hzero_t : ex w (indIn K t) = 0 := by
    simp only [ex, hind_t, mul_zero, Finset.sum_const_zero]
  have hzero0 : ex w (indIn K 0) = 0 := by
    rw [← ex_indIn_eq_of_pairAt_shift w K hTI t, hzero_t]
  ext s
  simp only [Finset.notMem_empty, iff_false]
  intro hs
  have hzero_s : ex w (indIn K s) = 0 := by
    rw [ex_indIn_eq_of_pairAt_shift w K hTI s, hzero0]
  have hterm : w ω * indIn K s ω = w ω := by
    simp only [indIn]
    rw [ite_eq_left hs, mul_one]
  have hnn : ∀ ω' ∈ (Finset.univ : Finset Ω), 0 ≤ w ω' * indIn K s ω' := fun ω' _ =>
    mul_nonneg (hw ω') (indIn_nonneg K s ω')
  have hle : w ω * indIn K s ω ≤ ex w (indIn K s) := by
    have := Finset.single_le_sum hnn (Finset.mem_univ ω)
    simpa only [ex] using this
  rw [hterm, hzero_s] at hle
  exact absurd hle (not_le.mpr hω)

/-- Version in "no instance exists" form: a non-negative weight that is positive
somewhere cannot carry a finite ambient set, a cluster containing the origin and a
translation-invariant four-point function at the same time (`d ≥ 1`). -/
theorem false_of_pairAt_shift_and_zero_mem (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω)
    (hne : ∃ ω, 0 < w ω)
    (K : Ω → Finset (Site d)) (V : Finset (Site d)) (hd : 0 < d)
    (hK : ∀ ω, K ω ⊆ V) (h0K : ∀ ω, (0 : Site d) ∈ K ω)
    (hTI : ∀ p q r s t : Site d,
      pairAt w K p q r s = pairAt w K (p + t) (q + t) (r + t) (s + t)) : False := by
  obtain ⟨ω, hω⟩ := hne
  have hempty := eq_empty_of_pairAt_shift w hw K V hd hK hTI ω hω
  have hmem := h0K ω
  rw [hempty] at hmem
  simpa using hmem

/-! ## 4. Consequence: every cross-term observable vanishes identically -/

/-- If `K ω = ∅` wherever `w` is positive, then any observable carrying a factor
`1(x ∈ K)` has zero expectation. -/
lemma ex_mul_indIn_eq_zero (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω)
    (K : Ω → Finset (Site d)) (hKempty : ∀ ω, 0 < w ω → K ω = ∅)
    (F : Ω → ℝ) (x : Site d) :
    ex w (fun ω => F ω * indIn K x ω) = 0 := by
  simp only [ex]
  refine Finset.sum_eq_zero fun ω _ => ?_
  by_cases hw0 : w ω = 0
  · simp [hw0]
  · have hpos : 0 < w ω := lt_of_le_of_ne (hw ω) (Ne.symm hw0)
    have : indIn K x ω = 0 := by
      simp only [indIn]
      rw [ite_eq_right]
      rw [hKempty ω hpos]
      simp
    rw [this, mul_zero, mul_zero]

lemma kcard_eq_zero (K : Ω → Finset (Site d)) (ω : Ω) (h : K ω = ∅) :
    kcard K ω = 0 := by
  simp only [kcard, h, Finset.card_empty, Nat.cast_zero]

lemma kDot_eq_zero (u : Fin d → ℝ) (K : Ω → Finset (Site d)) (ω : Ω) (h : K ω = ∅) :
    kDot u K ω = 0 := by
  simp only [kDot, h, Finset.sum_empty]

lemma kS_eq_zero (u : Fin d → ℝ) (K : Ω → Finset (Site d)) (ω : Ω) (h : K ω = ∅) :
    kS u K ω = 0 := by
  simp only [kS, sMoment, h, Finset.sum_empty]


/-! ## 5. `pairAt`, `pairAll`, `pairDisj` and `T0,…,T4` all vanish on such a model -/

lemma pairAt_eq_zero (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω) (K : Ω → Finset (Site d))
    (hKempty : ∀ ω, 0 < w ω → K ω = ∅) (r x y z : Site d) :
    pairAt w K r x y z = 0 := by
  have h := ex_mul_indIn_eq_zero w hw K hKempty
    (fun ω => indIn K r ω * indIn K x ω * indIn K y ω) z
  simpa only [pairAt] using h

lemma pairAll_eq_zero (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω) (K : Ω → Finset (Site d))
    (hKempty : ∀ ω, 0 < w ω → K ω = ∅) (x y z : Site d) :
    pairAll w K x y z = 0 := by
  have h := ex_mul_indIn_eq_zero w hw K hKempty (fun ω => indIn K x ω * indIn K y ω) z
  simpa only [pairAll] using h

lemma pairDisj_eq_zero (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω) (K : Ω → Finset (Site d))
    (hKempty : ∀ ω, 0 < w ω → K ω = ∅) (Ky : Site d → Ω → Finset (Site d)) (x y z : Site d) :
    pairDisj w K Ky x y z = 0 := by
  have h := ex_mul_indIn_eq_zero w hw K hKempty
    (fun ω => indOut K y ω * indIn (Ky y) z ω) x
  simp only [pairDisj]
  rw [show (fun ω => indOut K y ω * indIn K x ω * indIn (Ky y) z ω)
      = (fun ω => (indOut K y ω * indIn (Ky y) z ω) * indIn K x ω) from by
    funext ω; ring]
  exact h

lemma T0_eq_zero (u : Fin d → ℝ) (K : Ω → Finset (Site d))
    (Ky : Site d → Ω → Finset (Site d)) (y : Site d) (ω : Ω) (h : K ω = ∅) :
    T0 u K Ky y ω = 0 := by
  simp [T0, restW, kcard_eq_zero K ω h]

lemma T2_eq_zero (u : Fin d → ℝ) (K : Ω → Finset (Site d))
    (Ky : Site d → Ω → Finset (Site d)) (y : Site d) (ω : Ω) (h : K ω = ∅) :
    T2 u K Ky y ω = 0 := by
  simp [T2, pairW, kS_eq_zero u K ω h]

lemma T3_eq_zero (u : Fin d → ℝ) (K : Ω → Finset (Site d))
    (Ky : Site d → Ω → Finset (Site d)) (y : Site d) (ω : Ω) (h : K ω = ∅) :
    T3 u K Ky y ω = 0 := by
  simp [T3, kDot_eq_zero u K ω h]

lemma T4_eq_zero (u : Fin d → ℝ) (K : Ω → Finset (Site d))
    (Ky : Site d → Ω → Finset (Site d)) (y : Site d) (ω : Ω) (h : K ω = ∅) :
    T4 u K Ky y ω = 0 := by
  simp [T4, kDot_eq_zero u K ω h]

/-- If `X` vanishes wherever `w` is positive, its expectation vanishes. -/
lemma ex_eq_zero_of_pos_weight (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω) (X : Ω → ℝ)
    (hX : ∀ ω, 0 < w ω → X ω = 0) : ex w X = 0 := by
  simp only [ex]
  refine Finset.sum_eq_zero fun ω _ => ?_
  by_cases hw0 : w ω = 0
  · simp [hw0]
  · have hpos : 0 < w ω := lt_of_le_of_ne (hw ω) (Ne.symm hw0)
    simp [hX ω hpos]

/-- **Every cross term is identically zero.** `T0,…,T4` and all pair weights vanish
in any model satisfying `hK` and `hTI` of `T3_bound_global`. -/
theorem ex_T_eq_zero_of_pairAt_shift (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω)
    (K : Ω → Finset (Site d)) (V : Finset (Site d)) (hd : 0 < d)
    (hK : ∀ ω, K ω ⊆ V)
    (hTI : ∀ p q r s t : Site d,
      pairAt w K p q r s = pairAt w K (p + t) (q + t) (r + t) (s + t))
    (u : Fin d → ℝ) (Ky : Site d → Ω → Finset (Site d)) (B : Finset (Site d)) :
    (∑ y ∈ B, ex w (T0 u K Ky y)) = 0 ∧ (∑ y ∈ B, ex w (T2 u K Ky y)) = 0 ∧
    (∑ y ∈ B, ex w (T3 u K Ky y)) = 0 ∧ (∑ y ∈ B, ex w (T4 u K Ky y)) = 0 ∧
    (∀ x y z : Site d, pairAll w K x y z = 0) := by
  have hKempty : ∀ ω, 0 < w ω → K ω = ∅ := fun ω hω =>
    eq_empty_of_pairAt_shift w hw K V hd hK hTI ω hω
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact Finset.sum_eq_zero fun y _ =>
      ex_eq_zero_of_pos_weight w hw _ fun ω hω => T0_eq_zero u K Ky y ω (hKempty ω hω)
  · exact Finset.sum_eq_zero fun y _ =>
      ex_eq_zero_of_pos_weight w hw _ fun ω hω => T2_eq_zero u K Ky y ω (hKempty ω hω)
  · exact Finset.sum_eq_zero fun y _ =>
      ex_eq_zero_of_pos_weight w hw _ fun ω hω => T3_eq_zero u K Ky y ω (hKempty ω hω)
  · exact Finset.sum_eq_zero fun y _ =>
      ex_eq_zero_of_pos_weight w hw _ fun ω hω => T4_eq_zero u K Ky y ω (hKempty ω hω)
  · exact fun x y z => pairAll_eq_zero w hw K hKempty x y z

/-- Consequently `hgap` of `T3_bound_global` is only satisfiable with `pairProd ≡ 0`. -/
theorem pairProd_eq_zero_of_hgap (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω)
    (K : Ω → Finset (Site d)) (V : Finset (Site d)) (hd : 0 < d)
    (hK : ∀ ω, K ω ⊆ V)
    (hTI : ∀ p q r s t : Site d,
      pairAt w K p q r s = pairAt w K (p + t) (q + t) (r + t) (s + t))
    (Ky : Site d → Ω → Finset (Site d)) (pairProd : Site d → Site d → ℝ)
    (hgap : ∀ x ∈ V, ∀ z ∈ V, ∀ y : Site d,
      |pairDisj w K Ky x y z - pairProd x z| ≤ pairAll w K x y z)
    {x z : Site d} (hx : x ∈ V) (hz : z ∈ V) : pairProd x z = 0 := by
  have hKempty : ∀ ω, 0 < w ω → K ω = ∅ := fun ω hω =>
    eq_empty_of_pairAt_shift w hw K V hd hK hTI ω hω
  have h1 := hgap x hx z hz 0
  rw [pairDisj_eq_zero w hw K hKempty Ky x 0 z,
    pairAll_eq_zero w hw K hKempty x 0 z] at h1
  exact abs_eq_zero.mp (by simpa using h1)

/-! ## 6. The intended rooted-cluster model violates `hTI`

Two sites `0,1`, one edge, open with probability `1/2`; `K = C(0)`.
This is a genuine (if minimal) percolation model: `0 ∈ K` always, `K ⊆ {0,1}`,
the law has total mass `1`, and the four-point function is *not* translation
invariant.  So `hTI` is not merely hard to prove: it is false in the model the
abstraction is meant to describe. -/

/-- The lattice site `n·e₁` in `Site 1`. -/
def site1 (n : ℤ) : Site 1 := fun _ => n

lemma site1_inj : Function.Injective site1 := by
  intro a b h
  have := congrFun h ⟨0, by norm_num⟩
  simpa [site1] using this

lemma site1_zero_ne_one : site1 (0 : ℤ) ≠ site1 1 := by
  intro h
  have := site1_inj h
  norm_num at this

lemma site1_one_ne_zero : site1 (1 : ℤ) ≠ site1 0 := fun h => site1_zero_ne_one h.symm

/-- `C(0)` on the two-site graph `0 — 1`: the edge is open iff the `Bool` is `true`. -/
def Ktwo : Bool → Finset (Site 1) := fun b => if b then {site1 0, site1 1} else {site1 0}

/-- The uniform law on the two edge states, `p = 1/2`. -/
noncomputable def wTwo : Bool → ℝ := fun _ => 1 / 2

lemma wTwo_nonneg (b : Bool) : 0 ≤ wTwo b := by simp [wTwo]

lemma wTwo_sum_one : (∑ b : Bool, wTwo b) = 1 := by
  rw [Fintype.sum_bool]; norm_num [wTwo]

lemma mem_true_zero : site1 0 ∈ Ktwo true := by simp [Ktwo]
lemma mem_false_zero : site1 0 ∈ Ktwo false := by simp [Ktwo]
lemma mem_true_one : site1 1 ∈ Ktwo true := by simp [Ktwo, site1_one_ne_zero]
lemma not_mem_false_one : site1 1 ∉ Ktwo false := by simp [Ktwo, site1_one_ne_zero]

lemma Ktwo_subset (b : Bool) : Ktwo b ⊆ ({site1 0, site1 1} : Finset (Site 1)) := by
  rcases Bool.eq_false_or_eq_true b with rfl | rfl <;> simp [Ktwo]

lemma Ktwo_zero_mem (b : Bool) : site1 0 ∈ Ktwo b := by
  rcases Bool.eq_false_or_eq_true b with rfl | rfl
  · exact mem_true_zero
  · exact mem_false_zero


/-- `P(0 ∈ C(0)) = 1`. -/
theorem pairAt_two_zero :
    pairAt wTwo Ktwo (site1 0) (site1 0) (site1 0) (site1 0) = 1 := by
  rw [pairAt, ex, Fintype.sum_bool]
  norm_num [indIn, wTwo, mem_true_zero, mem_false_zero]

/-- `P(1 ∈ C(0)) = 1/2` in the same model. -/
theorem pairAt_two_one :
    pairAt wTwo Ktwo (site1 1) (site1 1) (site1 1) (site1 1) = 1 / 2 := by
  rw [pairAt, ex, Fintype.sum_bool]
  norm_num [indIn, wTwo, mem_true_one, not_mem_false_one]

/-- **The four-point function of the rooted cluster is not translation invariant.** -/
theorem pairAt_two_not_shift_invariant :
    ¬ ∀ p q r s t : Site 1,
      pairAt wTwo Ktwo p q r s = pairAt wTwo Ktwo (p + t) (q + t) (r + t) (s + t) := by
  intro h
  have hsum : ((site1 0 + site1 1) : Site 1) = site1 1 := by
    funext i; simp [site1]
  have h0 := h (site1 0) (site1 0) (site1 0) (site1 0) (site1 1)
  rw [hsum] at h0
  rw [pairAt_two_zero, pairAt_two_one] at h0
  norm_num at h0

/-- The model has all the *other* hypotheses of `T3_bound_global` (`hK`, `h0K`,
non-negative normalised weight) and a finite ambient set; only `hTI` fails. -/
theorem Ktwo_hK : ∀ b, Ktwo b ⊆ ({site1 0, site1 1} : Finset (Site 1)) := Ktwo_subset

theorem Ktwo_h0K : ∀ b, site1 0 ∈ Ktwo b := Ktwo_zero_mem


/-! ## 7. Exact arithmetic for the two `T3` halves and the printed `(1/2) G`

`A` = first `T3` half `Σ_y E[1(y∈K)|K|S(K)]`, `B` = second half
`Σ_y E[1(y∈K)|K| Σ_{z∈K} q(z−y)]`.  The source splits `|T3| ≤ (1/2)(A + B)`
(AM–GM), identifies `A = B = G` (mass transport) and then prints `(1/2) G`.
The arithmetic below records (i) that `(1/2)(G + G) = G` and that `(1/2) G`
forces `B ≤ 0`, and (ii) exact values in the deterministic all-connected window
`V = B = {0,1,2} ⊂ ℤ`, `u = e₁`, where `G = 45`, `B = 36` and the pair sum is
`24 > 22.5 = (1/2) G`. -/

/-- The two AM–GM halves, each identified with `G` by transport, sum to `G`. -/
theorem amgm_total_eq (G A B : ℝ) (hA : A = G) (hB : B = G) :
    (1 / 2) * (A + B) = G := by
  rw [hA, hB]; ring

/-- The printed constant `(1/2)G` is consistent with the AM–GM split only if the
second half is non-positive. -/
theorem second_half_nonpos_of_printed_constant (G B : ℝ)
    (h : (1 / 2) * (G + B) ≤ (1 / 2) * G) : B ≤ 0 := by linarith

/-! ### The deterministic all-connected window `{0,1,2}` in `ℤ`, `u = e₁` -/

/-- First `T3` half: `G = |K| · |K ∩ B| · S(K) = 3 · 3 · 5 = 45`. -/
theorem window_first_half :
    (3 : ℝ) * 3 * (∑ z ∈ ({0, 1, 2} : Finset ℤ), ((z : ℝ)) ^ 2) = 45 := by
  norm_num [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton]

/-- Second `T3` half: `|K| · Σ_{y∈B} Σ_{z∈K} q(z−y) = 3 · 12 = 36`. -/
theorem window_second_half :
    (3 : ℝ) * (∑ y ∈ ({0, 1, 2} : Finset ℤ),
        ∑ z ∈ ({0, 1, 2} : Finset ℤ), ((z - y : ℤ) : ℝ) ^ 2) = 36 := by
  norm_num [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton]

/-- The pair sum after the BK-gap bound, with the enlarged weight equal to `1`:
`Σ_y Σ_x Σ_z |q(x)|^{1/2} |q(z−y)|^{1/2} = 24`. -/
theorem window_pair_sum :
    (∑ y ∈ ({0, 1, 2} : Finset ℤ), ∑ x ∈ ({0, 1, 2} : Finset ℤ),
        ∑ z ∈ ({0, 1, 2} : Finset ℤ),
          |((x : ℤ) : ℝ)| * |((z - y : ℤ) : ℝ)|) = 24 := by
  norm_num [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton]

/-- The printed constant fails in this window: `24 > 45/2`. -/
theorem window_printed_half_fails :
    (1 / 2 : ℝ) * 45 < 24 := by norm_num

/-- The AM–GM bound `(1/2)(A + B)` holds: `24 ≤ 40.5`. -/
theorem window_amgm_bound_holds :
    (24 : ℝ) ≤ (1 / 2) * (45 + 36) := by norm_num

/-- The transported constant `G` holds: `24 ≤ 45`. -/
theorem window_G_bound_holds : (24 : ℝ) ≤ 45 := by norm_num

/-- **`B = −B` is needed for the summed identity.**  In the same deterministic
window `V = {0,1,2}`, with the *non-symmetric* index set `B = {0,1}`: the first
`T3` half is `|K|·|K∩B|·S(K) = 3·2·5 = 30`, the second half is
`|K|·Σ_{y∈B}Σ_{z∈K} q(z−y) = 3·7 = 21`.  They agree (both `45`) only for the
symmetric `B = V`, which is what `T3_second_half_sum_eq` assumes. -/
theorem nonStd.Symm_B_halves_differ :
    (3 : ℝ) * (2 : ℝ) * (∑ z ∈ ({0, 1, 2} : Finset ℤ), ((z : ℝ)) ^ 2) = 30 ∧
    (3 : ℝ) * (∑ y ∈ ({0, 1} : Finset ℤ),
        ∑ z ∈ ({0, 1, 2} : Finset ℤ), ((z - y : ℤ) : ℝ) ^ 2) = 21 ∧
    (3 : ℝ) * 3 * (∑ z ∈ ({0, 1, 2} : Finset ℤ), ((z : ℝ)) ^ 2) = 45 := by
  refine ⟨by norm_num [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton],
    by norm_num [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton], by norm_num⟩


/-! ## 8. A satisfiable replacement for `hTI`: the summed mass-transport identity

`T3_bound_global` uses `hTI` only through `T3_second_half_sum_eq`, which proves one
summed identity.  Postulating that identity directly (it is the paper's "exchange
the roles of `0` and `y`" step, a two-root mass transport) removes `hTI`, `h0K`,
`hVy` and `hBsym` and leaves a hypothesis package that is *not* forced into the
degenerate case `K = ∅`. -/

theorem T3_bound_MTP (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω) (u : Fin d → ℝ)
    (K : Ω → Finset (Site d)) (Ky : Site d → Ω → Finset (Site d))
    (V B : Finset (Site d)) (hK : ∀ ω, K ω ⊆ V)
    (hKy : ∀ y ∈ B, ∀ ω, Ky y ω ⊆ V)
    (pairProd : Site d → Site d → ℝ)
    (hgap : ∀ y ∈ B, ∀ x ∈ V, ∀ z ∈ V,
      |pairDisj w K Ky x y z - pairProd x z| ≤ pairAll w K x y z)
    (hprod : ∀ y ∈ B,
      (∑ x ∈ V, ∑ z ∈ V, pairProd x z * (dot u x * dot u (z - y))) = 0)
    (hMTP : (∑ y ∈ B, ∑ x ∈ V, ∑ z ∈ V, pairAll w K x y z * q u (z - y))
      = ex w (fun ω => kcard K ω * kap K B ω * kS u K ω)) :
    |∑ y ∈ B, ex w (T3 u K Ky y)|
      ≤ ex w (fun ω => kcard K ω * kap K B ω * kS u K ω) := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have h1 : (∑ y ∈ B, |ex w (T3 u K Ky y)|)
      ≤ ∑ y ∈ B, ((1 / 2) * ex w (fun ω => indIn K y ω * kcard K ω * kS u K ω)
          + (1 / 2) * ex w (fun ω => indIn K y ω * kcard K ω
              * (∑ z ∈ K ω, q u (z - y)))) :=
    Finset.sum_le_sum fun y hy =>
      T3_per_y w hw u K Ky V y hK (hKy y hy) pairProd (hgap y hy) (hprod y hy)
  refine h1.trans ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ex_sum_indIn_kS]
  have heq : (∑ y ∈ B, ex w (fun ω => indIn K y ω * kcard K ω
        * (∑ z ∈ K ω, q u (z - y))))
      = ∑ y ∈ B, ∑ x ∈ V, ∑ z ∈ V, pairAll w K x y z * q u (z - y) :=
    Finset.sum_congr rfl fun y _ => (pairAll_sum_qz w u K V y hK).symm
  rw [heq, hMTP]
  linarith

/-- **Lemma I.5.8 with `T3` and `T4` proved from finite-sum inputs, no translation
invariance of the measure.** Remaining inputs: the covariance-gap bound `hgap`, the
product vanishing `hprod3`/`hprod4` (theorems in `I58Cross` §13 under reflection
symmetry), the two displayed volume/mass remainders `hR0`, `hR2`, and the summed
mass-transport identity `hMTP`. -/
theorem lemma_I_5_8_assembly_MTP
    (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω) (u : Fin d → ℝ)
    (K : Ω → Finset (Site d)) (Ky : Site d → Ω → Finset (Site d))
    (V B : Finset (Site d)) {r : ℝ}
    (hK : ∀ ω, K ω ⊆ V) (hKy : ∀ y ∈ B, ∀ ω, Ky y ω ⊆ V)
    (hB : ∀ y ∈ B, siteNormSq y ≤ r ^ 2)
    (pairProd : Site d → Site d → ℝ)
    (hgap : ∀ y ∈ B, ∀ x ∈ V, ∀ z ∈ V,
      |pairDisj w K Ky x y z - pairProd x z| ≤ pairAll w K x y z)
    (hprod3 : ∀ y ∈ B,
      (∑ x ∈ V, ∑ z ∈ V, pairProd x z * (dot u x * dot u (z - y))) = 0)
    (hprod4 : ∀ y ∈ B,
      (∑ x ∈ V, ∑ z ∈ V, pairProd x z * (dot u x * dot u y)) = 0)
    (hMTP : (∑ y ∈ B, ∑ x ∈ V, ∑ z ∈ V, pairAll w K x y z * q u (z - y))
      = ex w (fun ω => kcard K ω * kap K B ω * kS u K ω))
    (hR0 : |(∑ y ∈ B, ex w (T0 u K Ky y)) -
        (ex w (kcard K)) ^ 2 * (∑ y ∈ B, q u y)|
      ≤ uNormSq u * r ^ 2 * ex w (fun ω => (kcard K ω) ^ 2 * kap K B ω))
    (hR2 : |(∑ y ∈ B, ex w (T2 u K Ky y)) -
        (B.card : ℝ) * (ex w (kcard K)) * (ex w (kS u K))|
      ≤ ex w (fun ω => kcard K ω * kap K B ω * kS u K ω)) :
    |derivTerm w u K Ky B - mainTerm w u K B|
      ≤ 3 * (uNormSq u * r ^ 2 * ex w (fun ω => (kcard K ω) ^ 2 * kap K B ω))
        + 6 * ex w (fun ω => kcard K ω * kap K B ω * kS u K ω) := by
  rw [derivTerm_sub_mainTerm]
  exact abs_assembly_global _ _ _ _ _ _ _
    hR0 hR2
    (T3_bound_MTP w hw u K Ky V B hK hKy pairProd hgap hprod3 hMTP)
    (T4_bound w hw u K Ky V B hK hKy pairProd hgap hprod4)
    (Gq_le_U u K B hw hB)


/-! ## 9. `hMTP` is satisfied by a genuine (non-degenerate) model

The two-site rooted model of Section 6 — where `hTI` is *false* — does satisfy the
summed mass-transport identity `hMTP` of Section 8 with `B = V = {0,1}` and `u = e₁`:
both sides equal `2`.  So the replacement hypothesis is consistent with a real
percolation law, while the hypothesis it replaces is not. -/

/-- `u = e₁` in `Site 1`. -/
def uOne : Fin 1 → ℝ := fun _ => 1

lemma q_site1 (n : ℤ) : q uOne (site1 n) = ((n : ℤ) : ℝ) ^ 2 := by
  simp [q, dot, uOne, site1]

lemma pairAll_two_half (a : ℤ) (ha : a = 0 ∨ a = 1) :
    pairAll wTwo Ktwo (site1 a) (site1 0) (site1 1) = 1 / 2 := by
  rw [pairAll, ex, Fintype.sum_bool]
  have ha0 : site1 a ∈ Ktwo true := by
    rcases ha with rfl | rfl
    · exact mem_true_zero
    · exact mem_true_one
  simp [indIn, wTwo, mem_true_zero, mem_true_one, not_mem_false_one, ha0]

lemma pairAll_two_half' (a : ℤ) (ha : a = 0 ∨ a = 1) :
    pairAll wTwo Ktwo (site1 a) (site1 1) (site1 0) = 1 / 2 := by
  rw [pairAll, ex, Fintype.sum_bool]
  have ha0 : site1 a ∈ Ktwo true := by
    rcases ha with rfl | rfl
    · exact mem_true_zero
    · exact mem_true_one
  simp [indIn, wTwo, mem_true_zero, mem_true_one, not_mem_false_one, ha0]

lemma kS_two_false : kS uOne Ktwo false = 0 := by
  simp [kS, sMoment, Ktwo, q_site1, site1_zero_ne_one]

lemma kS_two_true : kS uOne Ktwo true = 1 := by
  simp [kS, sMoment, Ktwo, q_site1, site1_one_ne_zero]

lemma kcard_two_false : kcard Ktwo false = 1 := by simp [kcard, Ktwo]
lemma kcard_two_true : kcard Ktwo true = 2 := by simp [kcard, Ktwo, site1_zero_ne_one]

lemma kap_two (b : Bool) : kap Ktwo ({site1 0, site1 1} : Finset (Site 1)) b = kcard Ktwo b := by
  rcases Bool.eq_false_or_eq_true b with rfl | rfl <;>
    simp [kap, kcard, Ktwo, site1_zero_ne_one]

/-- Left side of `hMTP`: `Σ_y Σ_x Σ_z P(x,y,z ∈ K) q(z-y) = 2`. -/
theorem MTP_two_lhs :
    (∑ y ∈ ({site1 0, site1 1} : Finset (Site 1)),
      ∑ x ∈ ({site1 0, site1 1} : Finset (Site 1)),
        ∑ z ∈ ({site1 0, site1 1} : Finset (Site 1)),
          pairAll wTwo Ktwo x y z * q uOne (z - y)) = 2 := by
  simp only [Finset.sum_pair site1_zero_ne_one]
  have h0 : ((site1 0 - site1 0 : Site 1)) = site1 0 := by funext i; simp [site1]
  have h1 : ((site1 1 - site1 1 : Site 1)) = site1 0 := by funext i; simp [site1]
  have h2 : ((site1 1 - site1 0 : Site 1)) = site1 1 := by funext i; simp [site1]
  have h3 : ((site1 0 - site1 1 : Site 1)) = site1 (-1) := by funext i; simp [site1]
  simp only [h0, h1, h2, h3, q_site1]
  rw [pairAll_two_half 0 (Or.inl rfl), pairAll_two_half 1 (Or.inr rfl),
    pairAll_two_half' 0 (Or.inl rfl), pairAll_two_half' 1 (Or.inr rfl)]
  norm_num

/-- Right side of `hMTP`: `E[|K| |K ∩ B| S(K)] = 2`. -/
theorem MTP_two_rhs :
    ex wTwo (fun b => kcard Ktwo b * kap Ktwo ({site1 0, site1 1} : Finset (Site 1)) b
      * kS uOne Ktwo b) = 2 := by
  rw [ex, Fintype.sum_bool]
  simp [wTwo, kap_two, kcard_two_false, kcard_two_true, kS_two_false, kS_two_true]

/-- **`hMTP` holds in the rooted two-site percolation model**, i.e. the replacement
hypothesis of `T3_bound_MTP` is satisfiable outside the degenerate case `K = ∅`. -/
theorem twoSite_MTP :
    (∑ y ∈ ({site1 0, site1 1} : Finset (Site 1)),
      ∑ x ∈ ({site1 0, site1 1} : Finset (Site 1)),
        ∑ z ∈ ({site1 0, site1 1} : Finset (Site 1)),
          pairAll wTwo Ktwo x y z * q uOne (z - y))
      = ex wTwo (fun b => kcard Ktwo b
          * kap Ktwo ({site1 0, site1 1} : Finset (Site 1)) b * kS uOne Ktwo b) := by
  rw [MTP_two_lhs, MTP_two_rhs]

#print axioms PercLib.CriticalLRP.I58.pairAll_two_half
#print axioms PercLib.CriticalLRP.I58.MTP_two_lhs
#print axioms PercLib.CriticalLRP.I58.MTP_two_rhs
#print axioms PercLib.CriticalLRP.I58.twoSite_MTP

end PercLib.CriticalLRP.I58

/-! ## 9. Axiom audit -/

#print axioms PercLib.CriticalLRP.I58.pairAt_zero
#print axioms PercLib.CriticalLRP.I58.ex_indIn_eq_of_pairAt_shift
#print axioms PercLib.CriticalLRP.I58.exists_site_not_mem
#print axioms PercLib.CriticalLRP.I58.eq_empty_of_shift_invariant
#print axioms PercLib.CriticalLRP.I58.eq_empty_of_pairAt_shift
#print axioms PercLib.CriticalLRP.I58.false_of_pairAt_shift_and_zero_mem
#print axioms PercLib.CriticalLRP.I58.pairAt_eq_zero
#print axioms PercLib.CriticalLRP.I58.pairAll_eq_zero
#print axioms PercLib.CriticalLRP.I58.pairDisj_eq_zero
#print axioms PercLib.CriticalLRP.I58.ex_T_eq_zero_of_pairAt_shift
#print axioms PercLib.CriticalLRP.I58.pairProd_eq_zero_of_hgap
#print axioms PercLib.CriticalLRP.I58.pairAt_two_zero
#print axioms PercLib.CriticalLRP.I58.pairAt_two_one
#print axioms PercLib.CriticalLRP.I58.pairAt_two_not_shift_invariant
#print axioms PercLib.CriticalLRP.I58.amgm_total_eq
#print axioms PercLib.CriticalLRP.I58.second_half_nonpos_of_printed_constant
#print axioms PercLib.CriticalLRP.I58.window_first_half
#print axioms PercLib.CriticalLRP.I58.window_second_half
#print axioms PercLib.CriticalLRP.I58.window_pair_sum
#print axioms PercLib.CriticalLRP.I58.window_printed_half_fails
#print axioms PercLib.CriticalLRP.I58.nonStd.Symm_B_halves_differ
#print axioms PercLib.CriticalLRP.I58.T3_bound_MTP
#print axioms PercLib.CriticalLRP.I58.lemma_I_5_8_assembly_MTP
