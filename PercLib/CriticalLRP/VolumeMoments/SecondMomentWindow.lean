/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
-/

/-
# The I.4.7 second-moment premise at the cut-off law: what it really says

Source: T. Hutchcroft, *Critical long-range percolation I*, Definition I.1.5,
Lemma I.4.7 and Corollary I.4.8.  The committed theorem
`PercLib.CriticalLRP.Hvol.lemma_I_4_7_cutoff_of_secondMoment` assumes

  `h2 : ∫⁻ ω, |K_x(ω)|² ∂P_{β,r} ≠ ⊤`   (`P_{β,r}` = `longRangeMeasure J_r β`),

and the paper discharges `h2` from subcriticality of `P_{β,r}` (Definition I.1.5:
`J_r ≤ (1-ε) J`, hence `P_{β,r} ≾ P_{(1-ε)β_c}`).

This file isolates exactly what `h2` *is*, at the source cut-off law, with no
extra hypothesis:

* `box_cofinal` : the lattice boxes are cofinal in the finite subsets of `ℤ^d`;
* `secondMoment_eq_iSup_box` : `∫ |K_x|² = ⨆_n ∫ |K_x ∩ B_n|²`, i.e. the second
  moment is the supremum of the *finite-window* second moments (this is
  `PercLib.Percolation.Bond.lintegral_cluster_sq_eq_iSup` transported to the
  cut-off law; no BK, no subcriticality, no finiteness assumption);
* `secondMoment_ne_top_iff_uniform_window` : consequently `h2` holds **iff** the
  windowed second moments are *uniformly* bounded in the window;
* `window_secondMoment_ne_top` : every single windowed second moment is finite
  (it is at most `|B_n|²`), so the content of `h2` is precisely the uniformity,
  not the finiteness of any one term.
-/

module

public import PercLib.CriticalLRP.VolumeMoments.ErrorBounds
public import PercLib.Percolation.Bond.ClusterMoments

set_option autoImplicit false

@[expose] public section

namespace PercLib.CriticalLRP.Hvol

open MeasureTheory
open scoped ENNReal NNReal
open PercLib.CriticalLRP.FiniteVolume

variable {d : ℕ}

attribute [local instance] Classical.propDecidable

/-- The lattice boxes are cofinal among finite vertex sets. -/
theorem box_cofinal (s : Finset (Fin d → ℤ)) : ∃ n : ℕ, s ⊆ box d n := by
  classical
  refine ⟨s.sup fun y => linfNorm y, ?_⟩
  intro y hy
  rw [mem_box_iff]
  exact Finset.le_sup (f := fun y => linfNorm y) hy

/-- **The second moment is the supremum of its finite-window values**, at an
arbitrary Bernoulli bond law with edge weights `q` (no finiteness assumption). -/
theorem secondMoment_eq_iSup_box (q : Sym2 (Fin d → ℤ) → unitInterval) (x : Fin d → ℤ) :
    (∫⁻ ω, ((cluster ω x).encard : ℝ≥0∞) ^ 2 ∂(edgeMeasure q)) =
      ⨆ n : ℕ, ∫⁻ ω,
        ((cluster ω x ∩ ((box d n : Finset (Fin d → ℤ)) : Set (Fin d → ℤ))).encard :
          ℝ≥0∞) ^ 2 ∂(edgeMeasure q) :=
  PercLib.Percolation.Bond.lintegral_cluster_sq_eq_iSup q x (fun n => box d n) box_cofinal

/-- **`h2` is exactly a uniform-in-window bound.**  The second cluster moment of
the root is finite iff the second moments of the windowed intersection counts
`|K_x ∩ B_n|` admit a bound independent of `n`. -/
theorem secondMoment_ne_top_iff_uniform_window
    (q : Sym2 (Fin d → ℤ) → unitInterval) (x : Fin d → ℤ) :
    (∫⁻ ω, ((cluster ω x).encard : ℝ≥0∞) ^ 2 ∂(edgeMeasure q)) ≠ ⊤ ↔
      ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ n : ℕ,
        (∫⁻ ω, ((cluster ω x ∩ ((box d n : Finset (Fin d → ℤ)) : Set (Fin d → ℤ))).encard :
          ℝ≥0∞) ^ 2 ∂(edgeMeasure q)) ≤ C := by
  rw [secondMoment_eq_iSup_box]
  constructor
  · intro h
    exact ⟨_, h, fun n => le_iSup (fun n : ℕ => ∫⁻ ω,
      ((cluster ω x ∩ ((box d n : Finset (Fin d → ℤ)) : Set (Fin d → ℤ))).encard :
        ℝ≥0∞) ^ 2 ∂(edgeMeasure q)) n⟩
  · rintro ⟨C, hC, hle⟩
    exact ne_top_of_le_ne_top hC (ciSup_le hle)

/-- Each windowed second moment is finite: the window count is bounded by the
window size, so the integral is at most `|B_n|²`.  Hence
`secondMoment_ne_top_iff_uniform_window` is not vacuous in either direction: the
whole content of the second-moment premise is the *uniformity* in `n`. -/
theorem window_secondMoment_ne_top (q : Sym2 (Fin d → ℤ) → unitInterval)
    (x : Fin d → ℤ) (n : ℕ) :
    (∫⁻ ω, ((cluster ω x ∩ ((box d n : Finset (Fin d → ℤ)) : Set (Fin d → ℤ))).encard :
      ℝ≥0∞) ^ 2 ∂(edgeMeasure q)) ≠ ⊤ := by
  have hb : ∀ ω : Config (Fin d → ℤ),
      ((cluster ω x ∩ ((box d n : Finset (Fin d → ℤ)) : Set (Fin d → ℤ))).encard :
        ℝ≥0∞) ≤ (box d n).card := by
    intro ω
    calc ((cluster ω x ∩ ((box d n : Finset (Fin d → ℤ)) : Set (Fin d → ℤ))).encard :
          ℝ≥0∞)
        ≤ (((box d n : Finset (Fin d → ℤ)) : Set (Fin d → ℤ)).encard : ℝ≥0∞) := by
          exact_mod_cast Set.encard_mono
            (Set.inter_subset_right : cluster ω x ∩ ((box d n : Finset (Fin d → ℤ)) :
              Set (Fin d → ℤ)) ⊆ _)
      _ = (box d n).card := by
          rw [Set.encard_coe_eq_coe_finsetCard]
          simp
  have hmono : (∫⁻ ω, ((cluster ω x ∩
        ((box d n : Finset (Fin d → ℤ)) : Set (Fin d → ℤ))).encard : ℝ≥0∞) ^ 2
        ∂(edgeMeasure q)) ≤
      ∫⁻ _ω : Config (Fin d → ℤ), ((box d n).card : ℝ≥0∞) ^ 2 ∂(edgeMeasure q) :=
    lintegral_mono fun ω => pow_le_pow_left' (hb ω) 2
  have htop : (∫⁻ _ω : Config (Fin d → ℤ), ((box d n).card : ℝ≥0∞) ^ 2 ∂(edgeMeasure q)) =
      ((box d n).card : ℝ≥0∞) ^ 2 := by
    rw [lintegral_const]
    simp
  rw [htop] at hmono
  exact ne_top_of_le_ne_top (ENNReal.pow_ne_top (ENNReal.natCast_ne_top _)) hmono

end PercLib.CriticalLRP.Hvol

namespace PercLib.CriticalLRP.Hrest

open MeasureTheory
open scoped ENNReal NNReal

variable {V : Type*} [Countable V]

attribute [local instance] Classical.propDecidable

/-- **A finite third cluster moment implies a finite second one.**  This is the
`cardFun`-product form in which the premise of
`Hvol.lemma_I_4_7_cutoff_of_secondMoment` is stated, so a third-moment input
(such as the tree-graph bound `E|K|³ ≤ 3 (E|K|)⁵` addressed by the `q = 3`
bridge) discharges the second-moment premise.  The converse does not hold. -/
theorem secondMoment_ne_top_of_thirdMoment {q : Sym2 V → unitInterval} (x : V)
    (h3 : (∫⁻ ω, Percolation.cardFun (cluster ω x) ^ 3 ∂(edgeMeasure q)) ≠ ⊤) :
    (∫⁻ ω, Percolation.cardFun (cluster ω x) * Percolation.cardFun (cluster ω x)
      ∂(edgeMeasure q)) ≠ ⊤ := by
  refine ne_top_of_le_ne_top h3 (lintegral_mono fun ω => ?_)
  have h1 : (1 : ℝ≥0∞) ≤ Percolation.cardFun (cluster ω x) :=
    MomentFiniteness.one_le_cardFun x ω
  calc Percolation.cardFun (cluster ω x) * Percolation.cardFun (cluster ω x)
      = Percolation.cardFun (cluster ω x) ^ 2 := (pow_two _).symm
    _ ≤ Percolation.cardFun (cluster ω x) ^ 3 := pow_le_pow_right₀ h1 (by norm_num)

end PercLib.CriticalLRP.Hrest
