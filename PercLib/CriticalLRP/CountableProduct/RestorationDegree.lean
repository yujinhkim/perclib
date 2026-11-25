/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
# Which restored-degree hypothesis the global ghost inequality needs

The global full-law ghost-restoration inequality

  `ghostHits π h o ≤ ghostHits ρ h o + D * weightedGhostMass ρ h o * G`

consumes a restored-degree bound `D` and a full-law ghost-hit bound `G`.  This file records, for
the countable summation that turns the per-cluster bound `blockSet_measure_le` into that
inequality, exactly what those two constants have to be:

* `D` must dominate the restored row sum at **every** vertex, not only at the origin: the outer
  sum over `x ∈ K` of the restored edge mass is what produces the factor `|K|` that
  `weightedGhostMass = ∫ |K| e^{-h|K|}` carries.  `cluster_restoredMass_le_card_mul` is the
  precise transfer between the per-cluster bound and that factor, and `rowSum_iSup_le_iff` shows
  that the `∀x` form and the `sup_x` form are the same hypothesis.
* The origin-local form (only the row sum at `o` bounded) is **false**: see
  `local_row_form_fails`, a three-vertex kernel-checked counterexample in which the origin is
  incident to no restored edge at all (row sum `0`) while a restored edge *away* from the origin
  still enlarges the origin's cluster, so `ghostHits π h o > ghostHits ρ h o`.
* `G` must dominate `ghostHits π h y` at every `y`, because the off-cluster exploration of
  `blockSet` is a full-law ghost hit at the far endpoint `y` of the restored edge, not at `o`.

No `sorry`, no custom axioms.
-/
module

public import PercLib.CriticalLRP.CountableProduct.GhostMixedBlock
public import PercLib.CriticalLRP.CountableProduct.GhostCutoffCounterexample

set_option autoImplicit true

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1200000

@[expose] public section

open MeasureTheory Measure ProbabilityTheory unitInterval
open scoped ENNReal NNReal

namespace PercLib.CriticalLRP

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Countable V]

/-! ## The `|K|` multiplicity from summing the restored row bound over the cluster -/

/-- **Restored mass over a finite vertex set.**  Summing the per-vertex restored row sums over a
finite set `K` costs `|K| · D` whenever every row sum is at most `D`.  This is where the factor
`|K|` in `weightedGhostMass = ∫ |K| e^{-h|K|}` comes from: the per-cluster bound
`blockSet_measure_le` is stated for each `x ∈ K`, and the outer sum over `x ∈ K` multiplies the
restored mass by `|K|`. -/
theorem cluster_restoredMass_le_card_mul (π ρ : Sym2 V → unitInterval) (D : ℝ≥0∞)
    (hD : ∀ x : V, ∑' y : V,
      ENNReal.ofReal ((shiftProb π ρ (s(x, y)) : unitInterval) : ℝ) ≤ D)
    (K : Finset V) :
    ∑ x ∈ K, ∑' y : V, ENNReal.ofReal ((shiftProb π ρ (s(x, y)) : unitInterval) : ℝ)
      ≤ (K.card : ℝ≥0∞) * D := by
  calc ∑ x ∈ K, ∑' y : V, ENNReal.ofReal ((shiftProb π ρ (s(x, y)) : unitInterval) : ℝ)
      ≤ ∑ _x ∈ K, D := Finset.sum_le_sum fun x _ => hD x
    _ = (K.card : ℝ≥0∞) * D := by rw [Finset.sum_const, nsmul_eq_mul]

/-- The `∀x` row bound and the `sup_x` row bound are the same hypothesis, so a supremum statement
is enough and a statement at a single vertex is not. -/
theorem rowSum_iSup_le_iff (f : V → ℝ≥0∞) (D : ℝ≥0∞) :
    (⨆ x : V, f x) ≤ D ↔ ∀ x : V, f x ≤ D := iSup_le_iff

/-- **The arithmetic core of the summation.**  If cluster shape `i` carries weight `p i`, has
`k i` vertices, ghost avoidance `W ^ k i`, and restored mass `mass i ≤ (k i) * D`, then the total
per-cluster contribution of the exit blocks is at most
`D * G * ∑ i, |K_i| * (p i * W ^ k i)`: exactly `D * G` times the `|K|`-weighted cluster-shape
sum, with the actual `|K|` multiplicity preserved. -/
theorem cluster_sum_arith {ι : Type*} (s : Finset ι) (p : ι → ℝ≥0∞) (k : ι → ℕ)
    (mass : ι → ℝ≥0∞) (W G D : ℝ≥0∞)
    (hmass : ∀ i ∈ s, mass i ≤ (k i : ℝ≥0∞) * D) :
    ∑ i ∈ s, p i * W ^ k i * mass i * G
      ≤ D * G * ∑ i ∈ s, (k i : ℝ≥0∞) * (p i * W ^ k i) := by
  calc ∑ i ∈ s, p i * W ^ k i * mass i * G
      ≤ ∑ i ∈ s, p i * W ^ k i * ((k i : ℝ≥0∞) * D) * G := by
        refine Finset.sum_le_sum fun i hi => ?_
        gcongr
        exact hmass i hi
    _ = D * G * ∑ i ∈ s, (k i : ℝ≥0∞) * (p i * W ^ k i) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        ring

/-- If the two edge laws agree at an edge, nothing is restored there. -/
theorem shiftProb_eq_zero_of_val_eq {π ρ : Sym2 V → unitInterval} {e : Sym2 V}
    (h : (π e : ℝ) = (ρ e : ℝ)) : shiftProb π ρ e = 0 := by
  have hval : ((shiftProb π ρ e : unitInterval) : ℝ) = 0 := by
    rw [shiftProb_val]
    have hzero : ((π e : ℝ) - (ρ e : ℝ)) = 0 := by rw [h]; ring
    rw [hzero, zero_div]
    simp
  exact Subtype.ext (by simpa using hval)

/-! ## The origin-local form of the hypothesis is false

Three vertices `0, 1, 2`; the cut-off law `ρ` opens only the edge `{0,1}`; the full law `π` opens
the whole path `{0,1}, {1,2}`.  No edge incident to the origin `0` is restored, so the origin's
restored row sum is `0`; but the restored edge `{1,2}` joins vertex `2` to the origin's cluster.
At intensity `h = log (4/3)`, so `e^{-h} = 3/4`:

* `ghostHits π h 0 = 1 - (3/4)^3 = 37/64` (the cluster of `0` is all of `Fin 3`);
* `ghostHits ρ h 0 = 1 - (3/4)^2 = 7/16`  (the cluster of `0` is `{0,1}`);
* both laws are point masses, so `G` may be taken to be `1 - (3/4)^3 = 37/64`, the full-law
  ghost-hit probability of every vertex.

Hence with `D = 0` — the origin-local row sum — the claimed right-hand side
`ghostHits ρ h 0 + D * weightedGhostMass ρ h 0 * G` equals `7/16 < 37/64`. -/

/-- The path edges `{0,1}, {1,2}` of `Fin 3`. -/
def pathEdges3 : Finset (Sym2 (Fin 3)) := {s(0, 1), s(1, 2)}

/-- The path configuration on `Fin 3`. -/
def pathConfig3 : Config (Fin 3) := fun e => e ∈ pathEdges3

/-- The full law of the counterexample: both path edges are open. -/
noncomputable def pathPi3 : Sym2 (Fin 3) → unitInterval :=
  fun e => if e ∈ pathEdges3 then 1 else 0

/-- The single edge `{0,1}` of `Fin 3`. -/
def baseEdges3 : Finset (Sym2 (Fin 3)) := {s(0, 1)}

/-- The single-edge configuration on `Fin 3`. -/
def baseConfig3 : Config (Fin 3) := fun e => e ∈ baseEdges3

/-- The cut-off law of the counterexample: only the edge `{0,1}` is open. -/
noncomputable def basePi3 : Sym2 (Fin 3) → unitInterval :=
  fun e => if e ∈ baseEdges3 then 1 else 0

/-- A `0/1` edge law supported on a finite set is the point mass at the indicator configuration. -/
theorem edgeMeasure_of_indicator (S : Finset (Sym2 V)) (q : Sym2 V → unitInterval)
    (h1 : ∀ e ∈ S, q e = 1) (h0 : ∀ e, e ∉ S → q e = 0) :
    edgeMeasure q = dirac (fun e : Sym2 V => e ∈ S) := by
  rw [edgeMeasure_eq_infinitePi q]
  have h : (fun e : Sym2 V => bernoulliMeasure (True : Prop) (False : Prop) (q e)) =
      fun e => dirac ((fun e : Sym2 V => e ∈ S) e) := by
    funext e
    by_cases he : e ∈ S
    · have hq : q e = 1 := h1 e he
      have hpt : ((fun e : Sym2 V => e ∈ S) e) = True := eq_true he
      rw [hq, hpt]; simp [bernoulliMeasure_def]
    · have hq : q e = 0 := h0 e he
      have hpt : ((fun e : Sym2 V => e ∈ S) e) = False := eq_false he
      rw [hq, hpt]; simp [bernoulliMeasure_def]
  rw [h]
  exact Measure.infinitePi_dirac (fun e : Sym2 V => e ∈ S)

theorem pathPi3_eq_one {e : Sym2 (Fin 3)} (he : e ∈ pathEdges3) : pathPi3 e = 1 := by
  simp [pathPi3, he]

theorem pathPi3_eq_zero {e : Sym2 (Fin 3)} (he : e ∉ pathEdges3) : pathPi3 e = 0 := by
  simp [pathPi3, he]

theorem basePi3_eq_one {e : Sym2 (Fin 3)} (he : e ∈ baseEdges3) : basePi3 e = 1 := by
  simp [basePi3, he]

theorem basePi3_eq_zero {e : Sym2 (Fin 3)} (he : e ∉ baseEdges3) : basePi3 e = 0 := by
  simp [basePi3, he]

theorem edgeMeasure_pathPi3 : edgeMeasure pathPi3 = dirac pathConfig3 :=
  edgeMeasure_of_indicator pathEdges3 pathPi3
    (fun _ he => pathPi3_eq_one he) (fun _ he => pathPi3_eq_zero he)

theorem edgeMeasure_basePi3 : edgeMeasure basePi3 = dirac baseConfig3 :=
  edgeMeasure_of_indicator baseEdges3 basePi3
    (fun _ he => basePi3_eq_one he) (fun _ he => basePi3_eq_zero he)

/-- A set that is closed under open edges contains every vertex reachable from it. -/
theorem reflTransGen_mem_of_closed {r : V → V → Prop} {S : Set V} {v : V} (hv : v ∈ S)
    (hclosed : ∀ u ∈ S, ∀ w : V, r u w → w ∈ S) :
    ∀ w : V, Relation.ReflTransGen r v w → w ∈ S := by
  intro w hw
  induction hw with
  | refl => exact hv
  | tail _ hadj ih => exact hclosed _ ih _ hadj

theorem conn_path3_01 : Connects pathConfig3 (0 : Fin 3) 1 := by
  refine connects_of_open (u := (0 : Fin 3)) (v := 1) (by norm_num) ?_
  show pathConfig3 (s(0, 1))
  simp [pathConfig3, pathEdges3]

theorem conn_path3_12 : Connects pathConfig3 (1 : Fin 3) 2 := by
  refine connects_of_open (u := (1 : Fin 3)) (v := 2) (by norm_num) ?_
  show pathConfig3 (s(1, 2))
  simp [pathConfig3, pathEdges3]

theorem conn_path3_02 : Connects pathConfig3 (0 : Fin 3) 2 :=
  connects_trans conn_path3_01 conn_path3_12

/-- In the path configuration every vertex is connected to the origin. -/
theorem conn_path3_to_zero : ∀ v : Fin 3, Connects pathConfig3 v 0 := by
  intro v
  fin_cases v
  · exact connects_refl _ _
  · exact SimpleGraph.Reachable.symm conn_path3_01
  · exact SimpleGraph.Reachable.symm conn_path3_02

/-- The cluster of every vertex of the path configuration is the whole vertex set. -/
theorem cluster_pathConfig3 (y : Fin 3) : cluster pathConfig3 y = Set.univ := by
  refine Set.eq_univ_of_forall fun x => ?_
  rw [mem_cluster_iff]
  exact connects_trans (conn_path3_to_zero y)
    (SimpleGraph.Reachable.symm (conn_path3_to_zero x))

theorem clusterVol_pathConfig3 (y : Fin 3) : clusterVol pathConfig3 y = 3 := by
  rw [clusterVol_eq_encard, cluster_pathConfig3, Set.encard_univ,
    ENat.card_eq_coe_fintype_card, Fintype.card_fin]
  norm_num

theorem ghostMass_pathConfig3 (y : Fin 3) :
    ghostMass refH pathConfig3 y = ENNReal.ofReal ((3 / 4) ^ 3) := by
  have hfin : (cluster pathConfig3 y).Finite := by
    rw [cluster_pathConfig3]; exact Set.finite_univ
  rw [ghostMass_of_finite refH pathConfig3 y hfin, cluster_pathConfig3, Set.ncard_univ,
    Nat.card_eq_fintype_card, Fintype.card_fin, ghostW_refH,
    ← ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 3 / 4) 3]

/-- Under the full law of the counterexample the ghost hits each vertex with probability
`1 - (3/4)^3 = 37/64`. -/
theorem ghostHits_pathPi3 (y : Fin 3) :
    ghostHits pathPi3 refH y = ENNReal.ofReal (37 / 64) := by
  rw [ghostHits_eq_lintegral, edgeMeasure_pathPi3, lintegral_dirac, ghostMass_pathConfig3,
    ← ENNReal.ofReal_one, ← ENNReal.ofReal_sub (p := 1) (q := (3 / 4) ^ 3) (by norm_num)]
  norm_num

/-- In the single-edge configuration the pair `{0,1}` is closed under open edges. -/
theorem base_closed :
    ∀ u ∈ ({0, 1} : Set (Fin 3)), ∀ w : Fin 3,
      (openGraph baseConfig3).Adj u w → w ∈ ({0, 1} : Set (Fin 3)) := by
  intro u _ w hadj
  rw [openGraph_adj] at hadj
  obtain ⟨-, hopen⟩ := hadj
  have hmem : s(u, w) = s(0, 1) := by
    have h' : baseConfig3 (s(u, w)) := hopen
    simpa only [baseConfig3, baseEdges3, Finset.mem_singleton] using h'
  fin_cases u <;> fin_cases w <;> simp_all

/-- The cluster of the origin under the cut-off law is `{0,1}`. -/
theorem cluster_baseConfig3 : cluster baseConfig3 (0 : Fin 3) = {0, 1} := by
  refine Set.Subset.antisymm (fun w hw => ?_) (fun w hw => ?_)
  · refine reflTransGen_mem_of_closed (r := (openGraph baseConfig3).Adj)
      (S := ({0, 1} : Set (Fin 3))) (v := (0 : Fin 3)) (by simp) base_closed w ?_
    rw [mem_cluster_iff] at hw
    rw [Connects, SimpleGraph.reachable_iff_reflTransGen] at hw
    exact hw
  · rw [mem_cluster_iff]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with rfl | rfl
    · exact connects_refl _ _
    · refine connects_of_open (u := (0 : Fin 3)) (v := 1) (by norm_num) ?_
      show baseConfig3 (s(0, 1))
      simp [baseConfig3, baseEdges3]

theorem clusterVol_baseConfig3 : clusterVol baseConfig3 (0 : Fin 3) = 2 := by
  rw [clusterVol_eq_tsum, tsum_fintype, Fin.sum_univ_three]
  simp [cluster_baseConfig3]
  norm_num

theorem ghostMass_baseConfig3 :
    ghostMass refH baseConfig3 (0 : Fin 3) = ENNReal.ofReal ((3 / 4) ^ 2) := by
  have hfin : (cluster baseConfig3 (0 : Fin 3)).Finite := by
    rw [cluster_baseConfig3]; exact Set.toFinite _
  rw [ghostMass_of_finite refH baseConfig3 0 hfin, cluster_baseConfig3,
    Set.ncard_pair (by norm_num : (0 : Fin 3) ≠ 1), ghostW_refH,
    ← ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 3 / 4) 2]

/-- Under the cut-off law the ghost hits the origin with probability `1 - (3/4)^2 = 7/16`. -/
theorem ghostHits_basePi3 :
    ghostHits basePi3 refH (0 : Fin 3) = ENNReal.ofReal (7 / 16) := by
  rw [ghostHits_eq_lintegral, edgeMeasure_basePi3, lintegral_dirac, ghostMass_baseConfig3,
    ← ENNReal.ofReal_one, ← ENNReal.ofReal_sub (p := 1) (q := (3 / 4) ^ 2) (by norm_num)]
  norm_num

/-- The path law opens the single-edge law: `ρ ≤ π`. -/
theorem basePi3_le_pathPi3 (e : Sym2 (Fin 3)) : basePi3 e ≤ pathPi3 e := by
  by_cases he : e ∈ baseEdges3
  · have hsub : baseEdges3 ⊆ pathEdges3 := by
      intro a ha
      simp only [baseEdges3, Finset.mem_singleton] at ha
      subst ha
      simp [pathEdges3]
    simp [basePi3, pathPi3, he, hsub he]
  · simp [basePi3, he]

/-- No edge incident to the origin is restored: the origin's restored row sum vanishes. -/
theorem restoredMass_origin_zero :
    ∑' y : Fin 3,
      ENNReal.ofReal ((shiftProb pathPi3 basePi3 (s((0 : Fin 3), y)) : unitInterval) : ℝ) = 0 := by
  have h0 : shiftProb pathPi3 basePi3 (s((0 : Fin 3), (0 : Fin 3))) = 0 := by
    refine shiftProb_eq_zero_of_val_eq ?_
    simp [basePi3, pathPi3, baseEdges3, pathEdges3]
  have h1 : shiftProb pathPi3 basePi3 (s((0 : Fin 3), (1 : Fin 3))) = 0 := by
    refine shiftProb_eq_zero_of_val_eq ?_
    simp [basePi3, pathPi3, baseEdges3, pathEdges3]
  have h2 : shiftProb pathPi3 basePi3 (s((0 : Fin 3), (2 : Fin 3))) = 0 := by
    refine shiftProb_eq_zero_of_val_eq ?_
    simp [basePi3, pathPi3, baseEdges3, pathEdges3]
  rw [tsum_fintype, Fin.sum_univ_three, h0, h1, h2]
  simp

/-- **The origin-local form of the global ghost inequality is false.**

There are `ρ ≤ π`, `h > 0`, a full-law ghost-hit bound `G`, and a `D` bounding the restored row
sum *at the origin*, for which `ghostHits π h 0` exceeds
`ghostHits ρ h 0 + D * weightedGhostMass ρ h 0 * G`.  Here `D = 0`: the origin is incident to no
restored edge.  So the restored-degree hypothesis has to be imposed at every vertex (or as a
supremum), as the target statement does. -/
theorem local_row_form_fails :
    ∃ (π ρ : Sym2 (Fin 3) → unitInterval) (D G : ℝ≥0∞),
      (∀ e, ρ e ≤ π e) ∧
      (∀ y : Fin 3, ghostHits π refH y ≤ G) ∧
      (∑' y : Fin 3,
          ENNReal.ofReal ((shiftProb π ρ (s((0 : Fin 3), y)) : unitInterval) : ℝ) ≤ D) ∧
      ¬ (ghostHits π refH (0 : Fin 3)
          ≤ ghostHits ρ refH (0 : Fin 3) + D * weightedGhostMass ρ refH (0 : Fin 3) * G) := by
  refine ⟨pathPi3, basePi3, 0, ENNReal.ofReal (37 / 64), basePi3_le_pathPi3,
    fun y => le_of_eq (ghostHits_pathPi3 y), ?_, ?_⟩
  · rw [restoredMass_origin_zero]
  · have hkey : ghostHits basePi3 refH (0 : Fin 3)
        + 0 * weightedGhostMass basePi3 refH (0 : Fin 3) * ENNReal.ofReal (37 / 64)
        < ghostHits pathPi3 refH (0 : Fin 3) := by
      rw [ghostHits_pathPi3, ghostHits_basePi3]
      simp only [zero_mul, add_zero]
      rw [ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0 : ℝ) < 37 / 64)]
      norm_num
    exact not_le.mpr hkey

/-! ## The same model satisfies the target under the `∀x` (here `sup_x`) row bound

The failure above is a failure of the *hypothesis*, not of the target inequality: at the same
`ρ, π, h` the restored row sums are `0` at the origin, `1` at vertices `1` and `2`, so the
supremum form of the hypothesis reads `D = 1`, and then
`ghostHits ρ h 0 + 1 · E_ρ[|K| e^{-h|K|}] · 37/64 = 7/16 + (9/8)(37/64) = 557/512`, which does
dominate `ghostHits π h 0 = 37/64`. -/

theorem weightedGhostMass_basePi3 :
    weightedGhostMass basePi3 refH (0 : Fin 3) = ENNReal.ofReal (9 / 8) := by
  have h2 : (2 : ℝ≥0∞) = ENNReal.ofReal 2 := by norm_num
  rw [weightedGhostMass, edgeMeasure_basePi3, lintegral_dirac, clusterVol_baseConfig3,
    ghostMass_baseConfig3, h2, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
  congr 1
  norm_num

/-- At the same `ρ ≤ π` and `h`, the target inequality with the *supremum* restored row sum
`D = 1` holds: the counterexample above only refutes the origin-local weakening. -/
theorem sup_row_form_holds_in_witness :
    ghostHits pathPi3 refH (0 : Fin 3)
      ≤ ghostHits basePi3 refH (0 : Fin 3)
        + ENNReal.ofReal 1 * weightedGhostMass basePi3 refH (0 : Fin 3)
            * ENNReal.ofReal (37 / 64) := by
  rw [ghostHits_pathPi3, ghostHits_basePi3, weightedGhostMass_basePi3,
    ← ENNReal.ofReal_mul (p := (1 : ℝ)) (q := 9 / 8) (by norm_num),
    ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 * (9 / 8)),
    ← ENNReal.ofReal_add (by norm_num) (by norm_num),
    ENNReal.ofReal_le_ofReal_iff (by norm_num)]
  norm_num

end PercLib.CriticalLRP
