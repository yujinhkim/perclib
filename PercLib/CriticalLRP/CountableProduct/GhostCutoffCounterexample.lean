/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
# Why the cut-off form of (I.3.5) cannot follow from a degree-tail cost

Source: Tom Hutchcroft, *Critical long-range percolation I: High effective dimension*,
arXiv:2508.18807v1, proof of Proposition I.3.1 (p. 29, display (I.3.1)) and of
Proposition I.3.2 (p. 31, display (I.3.5)).

In the notation of `CriticalPercLib.CriticalLRP.CountableProduct.GhostField` the paper's
estimate compares ghost-hit probabilities between a cut-off edge law `π_r` and the full edge
law `π ≥ π_r`:

  `ghostHits π h o ≤ ghostHits π_r h o + ε · E_{π_r}[|K| e^{-h|K|}] · ghostHits π_r h o`,

with `ε` the expected number of restored edges at a vertex (`C r^{-α}` for the long-range
kernel).  This file proves that this *shape* of estimate cannot be a consequence of the product
structure of the edge and ghost laws plus a degree-tail bound on the restored edges.  There is a
machine-checked finite counterexample in which

* `π_r ≤ π` pointwise,
* every vertex carries at most `2` restored edges (so the tight degree-tail constant is `2`),
* and yet `ghostHits π h o` exceeds
  `ghostHits π_r h o + 2 · E_{π_r}[|K|e^{-h|K|}] · ghostHits π_r h o`
  by `15/256`.

The mechanism is structural.  After the cut-off cluster `K` of the origin has been explored, the
edges with both endpoints outside `K` are still i.i.d. with the **full** law `π`: the cut-off
condition constrains only the edges meeting `K`, because `K` is the cut-off cluster.  The ghost is
then hit through the outside region, and the restored edges *inside* the outside region are free
to build a large component there.  Replacing that off-cluster ghost-hit probability by the cut-off
quantity `ghostHits π_r h o` is therefore not a monotonicity step, and the example below shows it
fails outright.  What the exploration does give is the honest product recorded as
`ghostI35_defect_exact`: the defect is the `e^{-h|K|}`-weighted mass of `K` times the ghost-hit
probability of the outside region **in the full law**.  That is consistent with the paper's
display (I.3.1), which carries the *full*-law probability `P_{β_c,∞,h}(0 ↔ G)` on the right-hand
side, and it shows why the cut-off form (I.3.5) as printed needs an additional hypothesis — the
critical balance `E_{β_c,r}|K| ≍ r^α` — before it can hold.

No `sorry`, no custom axioms.
-/
module

public import PercLib.CriticalLRP.CountableProduct.GhostField
public import PercLib.CriticalLRP.CountableProduct.Compatibility

set_option autoImplicit true

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1200000

@[expose] public section

open MeasureTheory Measure ProbabilityTheory unitInterval
open scoped ENNReal NNReal

namespace PercLib.CriticalLRP

variable {V : Type*} [Countable V]

/-! ## The two functionals of (I.3.5) -/

-- The canonical ghost functionals are defined in GhostField.lean.

/-! ## Non-vacuity of the shape of the inequality

With no restored edges the comparison holds for every constant, so the counterexample below
is not hiding a statement that is vacuous for trivial reasons. -/

theorem ghostI35_self (π : Sym2 V → unitInterval) (h : ℝ≥0) (o : V) (ε : ℝ≥0∞) :
    ghostHits π h o ≤ ghostHits π h o + ε * weightedGhostMass π h o * ghostHits π h o :=
  le_add_right le_rfl

/-! ## The degenerate cut-off law -/

/-- The cluster of `o` in the empty configuration is the singleton `{o}`, so its volume is `1`. -/
theorem clusterVol_empty (o : V) : clusterVol (∅ : Config V) o = 1 := by
  rw [clusterVol_eq_encard, cluster_empty, Set.encard_singleton]
  simp

/-- The ghost mass of the empty configuration is the single-vertex weight `e^{-h}`. -/
theorem ghostMass_empty (h : ℝ≥0) (o : V) : ghostMass h (∅ : Config V) o = ghostW h := by
  have hfin : (cluster (∅ : Config V) o).Finite := by
    rw [cluster_empty]; exact Set.finite_singleton o
  rw [ghostMass_of_finite h ∅ o hfin, cluster_empty, Set.ncard_singleton, pow_one]

/-- On a degenerate edge law (`π ≡ 0`, no open edge) the ghost-hit probability is the
single-vertex hitting probability `1 - e^{-h}`. -/
theorem ghostHits_zero_law (h : ℝ≥0) (o : V) :
    ghostHits (fun _ => (0 : unitInterval)) h o = 1 - ghostW h := by
  rw [ghostHits_eq_lintegral, edgeMeasure_zero, lintegral_dirac, ghostMass_empty]

/-- Under `π ≡ 0` the weighted moment is `e^{-h}`: the cluster of `o` is the single vertex `o`. -/
theorem weightedGhostMass_zero_law (h : ℝ≥0) (o : V) :
    weightedGhostMass (fun _ => (0 : unitInterval)) h o = ghostW h := by
  rw [weightedGhostMass, edgeMeasure_zero, lintegral_dirac, clusterVol_empty, ghostMass_empty,
    one_mul]

/-! ## The counterexample

Vertex set `Fin 4 = {0,1,2,3}`; cut-off law `π_r ≡ 0` (no edge open); full law `π` opens exactly
the three path edges `{0,1}`, `{1,2}`, `{2,3}`; ghost intensity `h = log (4/3)`, so that
`e^{-h} = 3/4` exactly; origin `o = 0`.

* `ghostHits π_r h 0 = 1 - 3/4 = 1/4`;
* `E_{π_r}[|K| e^{-h|K|}] = 3/4` (the cut-off cluster is the single vertex `0`);
* `ghostHits π h 0 = 1 - (3/4)^4 = 175/256` (the full cluster is all four vertices);
* the tight degree-tail constant is `2`: `0` and `3` carry one restored edge, `1` and `2` two.

The bound `1/4 + 2 · (3/4) · (1/4) = 5/8 = 160/256` is strictly below `175/256`. -/

/-- The three path edges `{0,1}, {1,2}, {2,3}` of `Fin 4`. -/
def pathEdges : Finset (Sym2 (Fin 4)) := {s(0, 1), s(1, 2), s(2, 3)}

/-- Those three edges, as a configuration. -/
def pathConfig : Config (Fin 4) := fun e => e ∈ pathEdges

/-- The `0/1` edge probability that opens exactly the three path edges. -/
noncomputable def pathPi : Sym2 (Fin 4) → unitInterval :=
  fun e => if e ∈ pathEdges then 1 else 0

/-- The ghost intensity `log (4/3)`, chosen so that `e^{-h} = 3/4` exactly. -/
noncomputable def refH : ℝ≥0 := ⟨Real.log (4 / 3), Real.log_nonneg (by norm_num)⟩

theorem refH_coe : ((refH : ℝ)) = Real.log (4 / 3) := rfl

theorem refH_pos : 0 < refH := by
  rw [← NNReal.coe_pos]
  show (0 : ℝ) < (refH : ℝ)
  rw [refH_coe]
  exact Real.log_pos (by norm_num)

/-- `e^{-h} = 3/4` at the chosen intensity. -/
theorem ghostW_refH : ghostW refH = ENNReal.ofReal (3 / 4) := by
  rw [ghostW, refH_coe, Real.exp_neg,
    Real.exp_log (by norm_num : (0 : ℝ) < 4 / 3)]
  norm_num

/-- The full law of the example is the point mass at the path configuration. -/
theorem edgeMeasure_pathPi : edgeMeasure pathPi = dirac pathConfig := by
  rw [edgeMeasure_eq_infinitePi]
  have h : (fun e : Sym2 (Fin 4) =>
      bernoulliMeasure (True : Prop) (False : Prop) (pathPi e)) = fun e => dirac (pathConfig e) := by
    funext e
    by_cases he : e ∈ pathEdges
    · have h1 : pathPi e = 1 := by simp [pathPi, he]
      have h2 : pathConfig e = True := eq_true he
      rw [h1, h2]
      simp [bernoulliMeasure_def]
    · have h1 : pathPi e = 0 := by simp [pathPi, he]
      have h2 : pathConfig e = False := eq_false he
      rw [h1, h2]
      simp [bernoulliMeasure_def]
  rw [h]
  exact Measure.infinitePi_dirac (fun e => pathConfig e)

/-- A single open edge gives a connection. -/
theorem connects_of_open {ω : Config V} {u v : V} (hne : u ≠ v) (hopen : s(u, v) ∈ ω) :
    Connects ω u v := by
  rw [Connects, SimpleGraph.reachable_iff_reflTransGen]
  exact Relation.ReflTransGen.single (by rw [openGraph_adj]; exact ⟨hne, hopen⟩)

theorem conn_path_01 : Connects pathConfig (0 : Fin 4) 1 := by
  have h : pathConfig (s(0, 1)) := by simp [pathConfig, pathEdges]
  exact connects_of_open (by norm_num) h

theorem conn_path_02 : Connects pathConfig (0 : Fin 4) 2 := by
  have h : pathConfig (s(1, 2)) := by simp [pathConfig, pathEdges]
  exact connects_trans conn_path_01 (connects_of_open (by norm_num) h)

theorem conn_path_03 : Connects pathConfig (0 : Fin 4) 3 := by
  have h : pathConfig (s(2, 3)) := by simp [pathConfig, pathEdges]
  exact connects_trans conn_path_02 (connects_of_open (by norm_num) h)

/-- In the path configuration the cluster of `0` is the whole vertex set. -/
theorem cluster_pathConfig : cluster pathConfig (0 : Fin 4) = Set.univ := by
  refine Set.eq_univ_of_forall fun x => ?_
  rw [mem_cluster_iff]
  fin_cases x
  · exact connects_refl _ _
  · exact conn_path_01
  · exact conn_path_02
  · exact conn_path_03

theorem clusterVol_pathConfig : clusterVol pathConfig (0 : Fin 4) = 4 := by
  rw [clusterVol_eq_encard, cluster_pathConfig, Set.encard_univ,
    ENat.card_eq_coe_fintype_card, Fintype.card_fin]
  norm_num

theorem ghostMass_pathConfig :
    ghostMass refH pathConfig (0 : Fin 4) = ENNReal.ofReal ((3 / 4) ^ 4) := by
  have hfin : (cluster pathConfig (0 : Fin 4)).Finite := by
    rw [cluster_pathConfig]; exact Set.finite_univ
  rw [ghostMass_of_finite refH pathConfig 0 hfin, cluster_pathConfig, Set.ncard_univ,
    Nat.card_eq_fintype_card, Fintype.card_fin, ghostW_refH,
    ← ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 3 / 4) 4]

/-- The ghost-hit probability of the full law of the example: `1 - (3/4)^4 = 175/256`. -/
theorem ghostHits_pathPi : ghostHits pathPi refH (0 : Fin 4) = ENNReal.ofReal (175 / 256) := by
  rw [ghostHits_eq_lintegral, edgeMeasure_pathPi, lintegral_dirac, ghostMass_pathConfig,
    ← ENNReal.ofReal_one, ← ENNReal.ofReal_sub (p := 1) (q := (3 / 4) ^ 4) (by norm_num)]
  norm_num

/-- The ghost-hit probability of the cut-off law of the example: `1 - 3/4 = 1/4`. -/
theorem ghostHits_zero_refH :
    ghostHits (fun _ => (0 : unitInterval)) refH (0 : Fin 4) = ENNReal.ofReal (1 / 4) := by
  rw [ghostHits_zero_law, ghostW_refH, ← ENNReal.ofReal_one,
    ← ENNReal.ofReal_sub (p := 1) (q := 3 / 4) (by norm_num)]
  norm_num

/-- The weighted cluster moment of the cut-off law of the example: `e^{-h} = 3/4`. -/
theorem weightedGhostMass_zero_refH :
    weightedGhostMass (fun _ => (0 : unitInterval)) refH (0 : Fin 4) = ENNReal.ofReal (3 / 4) := by
  rw [weightedGhostMass_zero_law, ghostW_refH]

/-- The density of restored edges at a vertex, summed over the other three vertices. -/
noncomputable def restoredMass (π πr : Sym2 V → unitInterval) (x : V) : ℝ≥0∞ :=
  ∑' y : V, ENNReal.ofReal (((π (s(x, y)) : ℝ) - (πr (s(x, y)) : ℝ)))

/-- The tight degree-tail constant of the example is `2`: in `Fin 4` the vertices `0` and `3`
carry one restored edge and the vertices `1` and `2` carry two, and no vertex carries three. -/
theorem restoredMass_pathPi_le_two (x : Fin 4) :
    restoredMass pathPi (fun _ => (0 : unitInterval)) x ≤ ENNReal.ofReal 2 := by
  rw [restoredMass, tsum_fintype]
  fin_cases x <;> simp [pathPi, pathEdges, Fin.sum_univ_four] <;> norm_num

/-- **The cut-off form of (I.3.5) fails under a degree-tail bound alone.**

With `π_r ≡ 0`, `π` the path indicator on `Fin 4`, `h = log (4/3)`, origin `0`, and the tight
degree-tail constant `2` (every vertex is incident to at most two restored edges), the ghost
hits the origin in the full law with probability `175/256`, while the right-hand side of the
cut-off form is only `5/8 = 160/256`. -/
theorem i35_cutoffForm_fails :
    (∀ e : Sym2 (Fin 4), (fun _ => (0 : unitInterval)) e ≤ pathPi e) ∧
      (∀ x : Fin 4, restoredMass pathPi (fun _ => (0 : unitInterval)) x ≤ ENNReal.ofReal 2) ∧
      ghostHits (fun _ => (0 : unitInterval)) refH (0 : Fin 4)
        + ENNReal.ofReal 2 * weightedGhostMass (fun _ => (0 : unitInterval)) refH (0 : Fin 4)
            * ghostHits (fun _ => (0 : unitInterval)) refH (0 : Fin 4)
        < ghostHits pathPi refH (0 : Fin 4) := by
  refine ⟨fun e => ?_, restoredMass_pathPi_le_two, ?_⟩
  simp
  rw [ghostHits_pathPi, ghostHits_zero_refH, weightedGhostMass_zero_refH]
  have hL : ENNReal.ofReal (1 / 4)
        + ENNReal.ofReal 2 * ENNReal.ofReal (3 / 4) * ENNReal.ofReal (1 / 4)
      = ENNReal.ofReal (5 / 8) := by
    rw [← ENNReal.ofReal_mul (p := 2) (q := 3 / 4) (by norm_num),
      ← ENNReal.ofReal_mul (p := 2 * (3 / 4)) (q := 1 / 4) (by norm_num),
      ← ENNReal.ofReal_add (p := 1 / 4) (q := 2 * (3 / 4) * (1 / 4)) (by norm_num)
        (by norm_num)]
    norm_num
  rw [hL, ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0 : ℝ) < 175 / 256)]
  norm_num

/-- **The exact defect in the example.**

The `15/256` defect is exactly the ghost-free weight `e^{-h}` of the cut-off cluster `{0}` times
the ghost-hit probability `1 - e^{-3h} = 37/64` of the outside region `{1,2,3}` in the full law,
where the two restored edges `{1,2}`, `{2,3}` join the three outside vertices into one component.
This is the honest off-cluster factor of the exploration: it is the *full*-law probability, and it
strictly exceeds the cut-off factor `1 - e^{-h} = 1/4` that `i35_cutoffForm_fails` shows to be
insufficient. -/
theorem ghostI35_defect_exact :
    ghostHits pathPi refH (0 : Fin 4) =
      ghostHits (fun _ => (0 : unitInterval)) refH (0 : Fin 4)
        + ghostW refH * (1 - ghostW refH ^ 3) := by
  rw [ghostHits_pathPi, ghostHits_zero_refH, ghostW_refH,
    ← ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 3 / 4) 3]
  have hsub : (1 : ℝ≥0∞) - ENNReal.ofReal ((3 / 4) ^ 3) = ENNReal.ofReal (37 / 64) := by
    rw [← ENNReal.ofReal_one,
      ← ENNReal.ofReal_sub (p := 1) (q := (3 / 4) ^ 3) (by norm_num)]
    norm_num
  rw [hsub, ← ENNReal.ofReal_mul (p := 3 / 4) (q := 37 / 64) (by norm_num),
    ← ENNReal.ofReal_add (p := 1 / 4) (q := 3 / 4 * (37 / 64)) (by norm_num) (by norm_num)]
  norm_num

/-- **The off-cluster factor strictly exceeds the cut-off ghost-hit probability.**

In the example the outside region `{1,2,3}` is hit by the ghost with probability
`1 - e^{-3h} = 37/64` under the full law, while the cut-off ghost-hit probability at the origin
is only `1 - e^{-h} = 1/4`.  This is exactly the quantitative gap that `i35_cutoffForm_fails`
turns into a failure of the cut-off form of (I.3.5). -/
theorem example_offCluster_exceeds :
    ghostHits (fun _ => (0 : unitInterval)) refH (0 : Fin 4) < ENNReal.ofReal (37 / 64) := by
  rw [ghostHits_zero_refH, ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0 : ℝ) < 37 / 64)]
  norm_num

/-- **The corrected (full-law factor) form holds in the example.**

The paper's display (I.3.1) carries `P_{β_c,∞,h}(0 ↔ G)` — the probability under the *full*
law — as the final factor.  In the example that form reads
`A ≤ B + 2 · E_r[|K| e^{-h|K|}] · A` with `A = 175/256`, `B = 1/4`, `E_r[…] = 3/4`, and it holds
because `2 · E_r[…] = 3/2 ≥ 1`.  So the failure recorded in `i35_cutoffForm_fails` is specific to
replacing the full-law factor `A` by the cut-off factor `B`, not to the exploration itself. -/
theorem i35_fullFactorForm_holds_example :
    ghostHits pathPi refH (0 : Fin 4)
      ≤ ghostHits (fun _ => (0 : unitInterval)) refH (0 : Fin 4)
        + ENNReal.ofReal 2 * weightedGhostMass (fun _ => (0 : unitInterval)) refH (0 : Fin 4)
            * ghostHits pathPi refH (0 : Fin 4) := by
  refine le_trans ?_ (le_add_left le_rfl)
  rw [weightedGhostMass_zero_refH]
  have hmul : ENNReal.ofReal 2 * ENNReal.ofReal (3 / 4) = ENNReal.ofReal (3 / 2) := by
    rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  rw [hmul]
  calc ghostHits pathPi refH (0 : Fin 4) = 1 * ghostHits pathPi refH (0 : Fin 4) :=
        (one_mul _).symm
    _ ≤ ENNReal.ofReal (3 / 2) * ghostHits pathPi refH (0 : Fin 4) := by
        gcongr
        rw [← ENNReal.ofReal_one]
        norm_num

/-- **No degree-tail constant up to `2` repairs the cut-off form.**

The example satisfies the degree-tail bound with constant `2` (and the origin itself carries only
the single restored edge `{0,1}`), so the failure is not an artefact of using the sup over all
vertices: every constant `0 ≤ c ≤ 2` gives a strictly smaller right-hand side than the true
ghost-hit probability.  (The failure threshold is `c < 111/48`.) -/
theorem i35_cutoffForm_fails_cost (c : ℝ) (_hc0 : 0 ≤ c) (hc : c ≤ 2) :
    ghostHits (fun _ => (0 : unitInterval)) refH (0 : Fin 4)
      + ENNReal.ofReal c * weightedGhostMass (fun _ => (0 : unitInterval)) refH (0 : Fin 4)
          * ghostHits (fun _ => (0 : unitInterval)) refH (0 : Fin 4)
      < ghostHits pathPi refH (0 : Fin 4) := by
  have hmono : ENNReal.ofReal c * weightedGhostMass (fun _ => (0 : unitInterval)) refH (0 : Fin 4)
        * ghostHits (fun _ => (0 : unitInterval)) refH (0 : Fin 4)
      ≤ ENNReal.ofReal 2 * weightedGhostMass (fun _ => (0 : unitInterval)) refH (0 : Fin 4)
          * ghostHits (fun _ => (0 : unitInterval)) refH (0 : Fin 4) := by
    gcongr
  exact lt_of_le_of_lt (add_le_add (le_refl _) hmono) i35_cutoffForm_fails.2.2

/-! ## The failure holds for a whole range of ghost intensities -/

/-- The full cluster of the example is all four vertices, so `e^{-h|K|} = (e^{-h})^4`. -/
theorem ghostMass_pathConfig_gen (h : ℝ≥0) :
    ghostMass h pathConfig (0 : Fin 4) = ENNReal.ofReal ((Real.exp (-(h : ℝ))) ^ 4) := by
  have hfin : (cluster pathConfig (0 : Fin 4)).Finite := by
    rw [cluster_pathConfig]; exact Set.finite_univ
  rw [ghostMass_of_finite h pathConfig 0 hfin, cluster_pathConfig, Set.ncard_univ,
    Nat.card_eq_fintype_card, Fintype.card_fin, ghostW,
    ← ENNReal.ofReal_pow (Real.exp_nonneg _) 4]

/-- `ghostHits π h 0 = 1 - (e^{-h})^4` for the full law of the example. -/
theorem ghostHits_pathPi_gen (h : ℝ≥0) :
    ghostHits pathPi h (0 : Fin 4) = 1 - ENNReal.ofReal ((Real.exp (-(h : ℝ))) ^ 4) := by
  rw [ghostHits_eq_lintegral, edgeMeasure_pathPi, lintegral_dirac, ghostMass_pathConfig_gen]

/-- **The cut-off form fails for every intensity with `e^{-h} > (√5-1)/2`.**

This is the general form of `i35_cutoffForm_fails`: as soon as the per-vertex absence weight
`x = e^{-h}` exceeds the golden ratio minus one, the full-law defect `1 - x^4` of the example
strictly exceeds the cut-off bound `(1 - x) + 2x(1 - x)`.  The positive-root threshold
`(√5-1)/2` comes from `x^3 - 2x + 1 = (x-1)(x^2+x-1)`. -/
theorem i35_cutoffForm_fails_of_exp_gt (h : ℝ≥0) (hh : 0 < h)
    (hx : (Real.sqrt 5 - 1) / 2 < Real.exp (-(h : ℝ))) :
    ghostHits (fun _ => (0 : unitInterval)) h (0 : Fin 4)
      + ENNReal.ofReal 2 * weightedGhostMass (fun _ => (0 : unitInterval)) h (0 : Fin 4)
          * ghostHits (fun _ => (0 : unitInterval)) h (0 : Fin 4)
      < ghostHits pathPi h (0 : Fin 4) := by
  set x : ℝ := Real.exp (-(h : ℝ)) with hxdef
  have hxpos : 0 < x := Real.exp_pos _
  have hxone : x ≤ 1 := exp_neg_le_one h
  have hxlt : x < 1 := exp_neg_lt_one hh
  -- the cut-off quantities in terms of `x`
  have hB : ghostHits (fun _ => (0 : unitInterval)) h (0 : Fin 4) = ENNReal.ofReal (1 - x) := by
    rw [ghostHits_zero_law]
    have hgw : ghostW h = ENNReal.ofReal x := rfl
    rw [hgw, ← ENNReal.ofReal_one, ← ENNReal.ofReal_sub (p := 1) (q := x) hxpos.le]
  have hW : weightedGhostMass (fun _ => (0 : unitInterval)) h (0 : Fin 4) = ENNReal.ofReal x := by
    rw [weightedGhostMass_zero_law]
    rfl
  have hA : ghostHits pathPi h (0 : Fin 4) = ENNReal.ofReal (1 - x ^ 4) := by
    rw [ghostHits_pathPi_gen, ← hxdef, ← ENNReal.ofReal_one,
      ← ENNReal.ofReal_sub (p := 1) (q := x ^ 4) (by positivity)]
  rw [hB, hW, hA]
  -- the real inequality behind the failure
  have hsqrt : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hquad : 0 < x ^ 2 + x - 1 := by
    have hr : ((Real.sqrt 5 - 1) / 2) ^ 2 + (Real.sqrt 5 - 1) / 2 = 1 := by nlinarith
    have hpos2 : 0 < x + ((Real.sqrt 5 - 1) / 2) + 1 := by
      have := Real.sqrt_nonneg 5
      linarith
    have hprod := mul_pos (sub_pos.mpr hx) hpos2
    nlinarith [hprod, hr]
  have hreal : (1 - x) + 2 * x * (1 - x) < 1 - x ^ 4 := by
    have hprod : 0 < x * (1 - x) * (x ^ 2 + x - 1) :=
      mul_pos (mul_pos hxpos (sub_pos.mpr hxlt)) hquad
    nlinarith [hprod]
  have hL : ENNReal.ofReal (1 - x) + ENNReal.ofReal 2 * ENNReal.ofReal x * ENNReal.ofReal (1 - x)
      = ENNReal.ofReal ((1 - x) + 2 * x * (1 - x)) := by
    rw [← ENNReal.ofReal_mul (p := 2) (q := x) (by norm_num),
      ← ENNReal.ofReal_mul (p := 2 * x) (q := 1 - x) (by nlinarith),
      ← ENNReal.ofReal_add (p := 1 - x) (q := 2 * x * (1 - x)) (by nlinarith)
        (by nlinarith)]
  rw [hL, ENNReal.ofReal_lt_ofReal_iff (by nlinarith)]
  exact hreal

/-- The general intensity theorem covers the explicit instance `h = log (4/3)`: there
`e^{-h} = 3/4 > (√5-1)/2`. -/
theorem i35_cutoffForm_fails_via_exp :
    ghostHits (fun _ => (0 : unitInterval)) refH (0 : Fin 4)
      + ENNReal.ofReal 2 * weightedGhostMass (fun _ => (0 : unitInterval)) refH (0 : Fin 4)
          * ghostHits (fun _ => (0 : unitInterval)) refH (0 : Fin 4)
      < ghostHits pathPi refH (0 : Fin 4) := by
  refine i35_cutoffForm_fails_of_exp_gt refH refH_pos ?_
  rw [refH_coe, Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 4 / 3)]
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have h0 : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  nlinarith

end PercLib.CriticalLRP
