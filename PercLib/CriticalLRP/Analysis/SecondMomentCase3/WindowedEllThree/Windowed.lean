/-
The windowed `ℓ = 3` polygon bound at the literal cutoff objects.

Accepted and independently rebuilt from Ultramath `smwzf17v9`, member `m6`, direction `d6`.

## What is proved, and why it is the right repair

`NoGo.lean` shows that the *per-vertex* `ℓ = 3` shape

  `T³_{β_c,r}(0,y) ≤ Cp (∇_{r^c} + r^{-c})`  for every window vertex `y`

of Lemma I.4.18 cannot hold: `T³_{β_c,r}(0,0) ≥ 1` while `∇_{r^c} + r^{-c} → 0`.  The
window summation of the Case-3 numerator, however, only needs the *sum* over the window,
and that sum is controlled by the two bounds that Lemma I.4.18's proof really supplies at
`ℓ = 3`:

* the constant bound `sup_x T³_{β_c,r}(0,x) ≤ ∇_{β_c}` (diagonal maximality; landed as
  `SourceModelData.source_ell_three_le`), and
* the source's own tail `∇_{r^c}`: for `‖y‖ ≥ R` the entry is at most
  `(M.nablaTail R).toReal` (landed as `SourceModelData.source_triTail'` together with
  `SourceModelData.triPoint_le_nablaTail`).

Splitting the window `B_r` at the radius `R = r^{1/2}` into the near part `{‖y‖ < R}` and
the far part `{‖y‖ ≥ R}` therefore gives

  `∑_{y ∈ B_r} T³_{β_c,r}(0,y) ≤ ∇_{β_c} · |B_{r^{1/2}}| + (∇_{r^c}) · |B_r|`,

and since `|B_{r^{1/2}}| ≈ r^{d/2}` while `|B_r| (∇_{r^c} + r^{-c}) ≈ r^{d - c}`, the near
term is absorbed by the driver at every radius — no residual, and in particular no
`χ³/|B_r|` residual as produced by the whole-space column sum `∑_y T³ = χ³`.  This is the
"honest local origin correction": the vertices where `T³` is not small are few, so they
cost a *volume* factor `|B_{r^{1/2}}|` rather than an entry-wise factor `|B_r|`.

The only arithmetic input is the normalized ball count `|B_ρ| ~ ρ^d`
(`SourceModelData.ball_count`), plus `c ≤ 1/2` (the source's `c` is free; the value
`c = α/(4d)` used by the landed `ℓ = 4` manufacturer satisfies it since `α < d`).
Nothing here uses `∑_y T³ = χ³`, no coefficient of the source is changed, and the
conclusion is the windowed hypothesis `WindowedEllThreeGap` of `Defs.lean`, i.e. exactly
what the Case-3 window summation consumes.
-/
module

public import PercLib.CriticalLRP.Analysis.SecondMomentCase3.WindowedEllThree.Defs
public import PercLib.CriticalLRP.Analysis.Polygon.TailConstant
public import PercLib.CriticalLRP.Analysis.Polygon.UncutLink

/-! # The windowed `ℓ = 3` bound -/

set_option linter.style.longLine false

@[expose] public section

noncomputable section

open Filter Topology
open scoped ENNReal NNReal BigOperators

namespace PercLib.CriticalLRP
namespace Orchestration
namespace SourceModelData

variable (M : SourceModelData)

/-! ## The near/far split of the windowed sum -/

/-- **Near/far split of the windowed `ℓ = 3` sum.**  If every entry of the window is at most
`∇_{β_c}` and the entries at distance at least `R` from the origin are at most `trc`, then

  `∑_{y ∈ B_r} T³(0,y) ≤ ∇_{β_c} · #{y ∈ B_r : ‖y‖ < R} + trc · |B_r|`.

This is the finite-sum form of the split carried out in the proof of Lemma I.4.18; the
difference with the printed statement is that the near part is *counted* instead of being
bounded entry by entry, which is exactly what makes the `ℓ = 3` case work. -/
theorem windowPolyKThree_le_split {r R trc : ℝ} (htrc : 0 ≤ trc)
    (hnear : ∀ y : M.V,
      I418C.polyK (M.cutTwoPoint r) 3 (0 : M.V) y ≤ M.triSelf)
    (hfar : ∀ y : M.V, R ≤ M.S.dist (0 : M.V) y →
      I418C.polyK (M.cutTwoPoint r) 3 (0 : M.V) y ≤ trc) :
    M.windowPolyKThree r
      ≤ M.triSelf *
          (((E1Sign.ballF M r).filter (fun y => ¬ R ≤ M.S.dist (0 : M.V) y)).card : ℝ)
        + trc * ((E1Sign.ballF M r).card : ℝ) := by
  have hsplit := Finset.sum_filter_add_sum_filter_not (E1Sign.ballF M r)
    (fun y => R ≤ M.S.dist (0 : M.V) y)
    (fun y => I418C.polyK (M.cutTwoPoint r) 3 (0 : M.V) y)
  have hfar_le :
      ∑ y ∈ (E1Sign.ballF M r).filter (fun y => R ≤ M.S.dist (0 : M.V) y),
        I418C.polyK (M.cutTwoPoint r) 3 (0 : M.V) y
        ≤ trc * ((E1Sign.ballF M r).card : ℝ) := by
    have h1 : ∑ y ∈ (E1Sign.ballF M r).filter (fun y => R ≤ M.S.dist (0 : M.V) y),
        I418C.polyK (M.cutTwoPoint r) 3 (0 : M.V) y
        ≤ ∑ _y ∈ (E1Sign.ballF M r).filter (fun y => R ≤ M.S.dist (0 : M.V) y), trc := by
      refine Finset.sum_le_sum fun y hy => hfar y (Finset.mem_filter.mp hy).2
    have h2 : ∑ _y ∈ (E1Sign.ballF M r).filter (fun y => R ≤ M.S.dist (0 : M.V) y), trc
        = (((E1Sign.ballF M r).filter
            (fun y => R ≤ M.S.dist (0 : M.V) y)).card : ℝ) * trc := by
      rw [Finset.sum_const, nsmul_eq_mul]
    have h3 : (((E1Sign.ballF M r).filter
        (fun y => R ≤ M.S.dist (0 : M.V) y)).card : ℝ) ≤ ((E1Sign.ballF M r).card : ℝ) := by
      exact_mod_cast Finset.card_filter_le (E1Sign.ballF M r) (fun y => R ≤ M.S.dist (0 : M.V) y)
    calc ∑ y ∈ (E1Sign.ballF M r).filter (fun y => R ≤ M.S.dist (0 : M.V) y),
          I418C.polyK (M.cutTwoPoint r) 3 (0 : M.V) y
        ≤ ∑ _y ∈ (E1Sign.ballF M r).filter (fun y => R ≤ M.S.dist (0 : M.V) y), trc := h1
      _ = (((E1Sign.ballF M r).filter
            (fun y => R ≤ M.S.dist (0 : M.V) y)).card : ℝ) * trc := h2
      _ ≤ ((E1Sign.ballF M r).card : ℝ) * trc :=
          mul_le_mul_of_nonneg_right h3 htrc
      _ = trc * ((E1Sign.ballF M r).card : ℝ) := by ring
  have hnear_le :
      ∑ y ∈ (E1Sign.ballF M r).filter (fun y => ¬ R ≤ M.S.dist (0 : M.V) y),
        I418C.polyK (M.cutTwoPoint r) 3 (0 : M.V) y
        ≤ M.triSelf *
          (((E1Sign.ballF M r).filter (fun y => ¬ R ≤ M.S.dist (0 : M.V) y)).card : ℝ) := by
    have h1 : ∑ y ∈ (E1Sign.ballF M r).filter (fun y => ¬ R ≤ M.S.dist (0 : M.V) y),
        I418C.polyK (M.cutTwoPoint r) 3 (0 : M.V) y
        ≤ ∑ _y ∈ (E1Sign.ballF M r).filter (fun y => ¬ R ≤ M.S.dist (0 : M.V) y),
            M.triSelf :=
      Finset.sum_le_sum fun y _ => hnear y
    have h2 : ∑ _y ∈ (E1Sign.ballF M r).filter (fun y => ¬ R ≤ M.S.dist (0 : M.V) y),
        M.triSelf
        = (((E1Sign.ballF M r).filter
            (fun y => ¬ R ≤ M.S.dist (0 : M.V) y)).card : ℝ) * M.triSelf := by
      rw [Finset.sum_const, nsmul_eq_mul]
    calc ∑ y ∈ (E1Sign.ballF M r).filter (fun y => ¬ R ≤ M.S.dist (0 : M.V) y),
          I418C.polyK (M.cutTwoPoint r) 3 (0 : M.V) y
        ≤ _ := h1
      _ = (((E1Sign.ballF M r).filter
            (fun y => ¬ R ≤ M.S.dist (0 : M.V) y)).card : ℝ) * M.triSelf := h2
      _ = M.triSelf * (((E1Sign.ballF M r).filter
            (fun y => ¬ R ≤ M.S.dist (0 : M.V) y)).card : ℝ) := by ring
  calc M.windowPolyKThree r
      = ∑ y ∈ (E1Sign.ballF M r).filter (fun y => R ≤ M.S.dist (0 : M.V) y),
          I418C.polyK (M.cutTwoPoint r) 3 (0 : M.V) y
        + ∑ y ∈ (E1Sign.ballF M r).filter (fun y => ¬ R ≤ M.S.dist (0 : M.V) y),
            I418C.polyK (M.cutTwoPoint r) 3 (0 : M.V) y := hsplit.symm
    _ ≤ M.triSelf *
          (((E1Sign.ballF M r).filter (fun y => ¬ R ≤ M.S.dist (0 : M.V) y)).card : ℝ)
        + trc * ((E1Sign.ballF M r).card : ℝ) := by linarith [hfar_le, hnear_le]

/-- **The near part of the window is contained in the smaller ball.**  This is the counting
step of the repair: the vertices at distance `< R` number at most `|B_R|`. -/
theorem card_near_filter_le {r R : ℝ} :
    (((E1Sign.ballF M r).filter (fun y => ¬ R ≤ M.S.dist (0 : M.V) y)).card
      ≤ (E1Sign.ballF M R).card) := by
  refine Finset.card_le_card ?_
  intro y hy
  obtain ⟨-, hlt⟩ := Finset.mem_filter.mp hy
  rw [E1Sign.mem_ballF] at *
  simp only [ball, Set.mem_ofPred_eq] at *
  rw [CriticalLRPConv.dist_zero_eq_srcNorm M.S y] at hlt
  exact le_of_lt (not_le.mp hlt)

/-! ## The two ball-count bounds -/

/-- **Normalized ball count, lower half.**  `|B_r| ≳ r^d`. -/
theorem eventually_half_card_le (M : SourceModelData) :
    ∀ᶠ r : ℝ in atTop, (1 / 2 : ℝ) * r ^ M.d ≤ ((M.ball r).ncard : ℝ) := by
  have hratio : Tendsto (fun r : ℝ => ((M.ball r).ncard : ℝ) / r ^ M.d) atTop (𝓝 1) := by
    refine (Asymptotics.isEquivalent_iff_tendsto_one ?_).mp M.ball_count
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with r hr
    exact pow_ne_zero _ (ne_of_gt (lt_of_lt_of_le one_pos hr))
  have hmem := hratio (Icc_mem_nhds (show (1 / 2 : ℝ) < 1 by norm_num)
    (show (1 : ℝ) < 3 / 2 by norm_num))
  filter_upwards [hmem, eventually_ge_atTop (1 : ℝ)] with r hr hr1
  simp only [Set.mem_preimage, Set.mem_Icc] at hr
  have hpos : (0 : ℝ) < r ^ M.d := pow_pos (lt_of_lt_of_le one_pos hr1) _
  rw [le_div_iff₀ hpos] at hr
  linarith [hr.1]

/-- **Normalized ball count, upper half at the split radius** `r^{1/2}`. -/
theorem eventually_card_rpow_half_le (M : SourceModelData) :
    ∀ᶠ r : ℝ in atTop,
      ((M.ball (r ^ (1 / 2 : ℝ))).ncard : ℝ) ≤ (3 / 2 : ℝ) * (r ^ (1 / 2 : ℝ)) ^ M.d := by
  have hratio : Tendsto (fun r : ℝ => ((M.ball r).ncard : ℝ) / r ^ M.d) atTop (𝓝 1) := by
    refine (Asymptotics.isEquivalent_iff_tendsto_one ?_).mp M.ball_count
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with r hr
    exact pow_ne_zero _ (ne_of_gt (lt_of_lt_of_le one_pos hr))
  have htop : Tendsto (fun r : ℝ => r ^ (1 / 2 : ℝ)) atTop atTop :=
    tendsto_rpow_atTop (by norm_num)
  have hmem := (hratio.comp htop) (Icc_mem_nhds (show (1 / 2 : ℝ) < 1 by norm_num)
    (show (1 : ℝ) < 3 / 2 by norm_num))
  filter_upwards [hmem, eventually_ge_atTop (1 : ℝ)] with r hr hr1
  simp only [Set.mem_preimage, Set.mem_Icc, Function.comp_apply] at hr
  have hr0 : (0 : ℝ) < r := lt_of_lt_of_le one_pos hr1
  have hpos : (0 : ℝ) < (r ^ (1 / 2 : ℝ)) ^ M.d :=
    pow_pos (Real.rpow_pos_of_pos hr0 _) _
  rw [div_le_iff₀ hpos] at hr
  linarith [hr.2]

/-! ## The arithmetic window -/

/-- **The window arithmetic.**  If the near cost `X` is at most five window-volumes
`S · D`, then `T X + D S ≤ (1 + 5T) S D`. -/
theorem arith_window {T D S X : ℝ} (hT : 0 ≤ T) (hX : X ≤ 5 * (S * D)) :
    T * X + D * S ≤ (1 + 5 * T) * S * D := by
  nlinarith

/-! ## The main theorem: the windowed `ℓ = 3` bound at the Case-3 driver -/

/-- **The windowed `ℓ = 3` polygon bound at the source's Case-3 driver.**

At the literal cutoff two-point matrix `T_{β_c,r} = M.cutTwoPoint r`:

  `∑_{y ∈ B_r} T³_{β_c,r}(0,y) ≤ (1 + 5 ∇_{β_c}) · |B_r| · (∇_{r^c} + r^{-c})` eventually,

for every `0 < c ≤ 1/2`.  This is the `ℓ = 3` term of Lemma I.4.17 at `p = 3`, `q = 0`
summed over the window, bounded in the only way the source's Lemma I.4.18 supports at
`ℓ = 3`, and it is what the window summation of the Case-3 numerator consumes
(`SecondMomentCase3`).  The per-vertex form is refuted in `NoGo.lean`.

Inputs: the triangle condition `∇_{β_c} < ∞` and the finiteness of the truncated first
moment `χ` (used to pass from the `ℝ≥0∞` power to the real iterated sum).  No moment gap,
no polygon estimate and no column-sum identity is used.  (The source's positivity `0 < c`
is recorded but not needed by this estimate: only `c ≤ 1/2` enters.) -/
theorem windowPolyKThree_le_case3Driver_eventually {c : ℝ} (_hc : 0 < c) (hc2 : c ≤ 1 / 2)
    (hTri : TriTail.openTriangleSelf M.kernel M.kernel_nonneg M.betaCrit 0 < ⊤)
    (hχ : ∀ r : ℝ, 1 ≤ r → M.cutMassAt r 0 ≠ ⊤) :
    ∀ᶠ r : ℝ in atTop, M.windowPolyKThree r
      ≤ (1 + 5 * M.triSelf) * ((M.ball r).ncard : ℝ) * M.case3Driver c r := by
  filter_upwards [eventually_ge_atTop (1 : ℝ), eventually_half_card_le M,
    eventually_card_rpow_half_le M] with r hr1 hlow hup
  have hr0 : (0 : ℝ) < r := lt_of_lt_of_le one_pos hr1
  have hne : M.cutMassAt r 0 ≠ ⊤ := hχ r hr1
  set R : ℝ := r ^ (1 / 2 : ℝ) with hR
  set trc : ℝ := (M.nablaTail R).toReal with htrc
  have hsplit := M.windowPolyKThree_le_split (r := r) (R := R) (trc := trc)
    ENNReal.toReal_nonneg
    (fun y => M.source_ell_three_le r hne hTri y)
    (fun y hy => M.source_triTail' r (1 / 2) trc hne hTri
      (fun z hz => M.triPoint_le_nablaTail hTri hz) y (by rw [← hR]; exact hy))
  have hRle : r ^ c ≤ R := by
    rw [hR]
    exact Real.rpow_le_rpow_of_exponent_le hr1 hc2
  have hmono : M.nablaTail R ≤ M.nablaTail (r ^ c) := M.nablaTail_antitone hRle
  have htrc_le : trc ≤ M.case3Driver c r := by
    have h1 : trc ≤ (M.nablaTail (r ^ c)).toReal :=
      ENNReal.toReal_mono (M.nablaTail_ne_top (r ^ c) hTri) hmono
    have h3 : M.case3Driver c r = (M.nablaTail (r ^ c)).toReal + r ^ (-c) := rfl
    rw [h3]
    linarith [h1, (Real.rpow_pos_of_pos hr0 (-c)).le]
  have hnear_card : (((E1Sign.ballF M r).filter
      (fun y => ¬ R ≤ M.S.dist (0 : M.V) y)).card : ℝ)
      ≤ (3 / 2 : ℝ) * R ^ M.d := by
    have h1 : (((E1Sign.ballF M r).filter
        (fun y => ¬ R ≤ M.S.dist (0 : M.V) y)).card : ℝ)
        ≤ ((E1Sign.ballF M R).card : ℝ) := by
      exact_mod_cast M.card_near_filter_le (r := r) (R := R)
    have h2 : ((E1Sign.ballF M R).card : ℝ) = ((M.ball R).ncard : ℝ) := by
      rw [E1Sign.card_ballF]
    rw [h2] at h1
    exact h1.trans hup
  have hS : (0 : ℝ) ≤ ((M.ball r).ncard : ℝ) := by positivity
  have hX : R ^ M.d ≤ 3 * (((M.ball r).ncard : ℝ) * M.case3Driver c r) := by
    have hd1 : (1 : ℝ) ≤ (M.d : ℝ) := by exact_mod_cast M.hd
    have hcd : c ≤ (M.d : ℝ) / 2 := by linarith
    have hexp_eq : (1 / 2 : ℝ) * (M.d : ℝ) = (M.d : ℝ) / 2 := by ring
    have hRd : R ^ M.d = r ^ ((M.d : ℝ) / 2) := by
      rw [hR, ← Real.rpow_natCast, ← Real.rpow_mul hr0.le, hexp_eq]
    have hexp : (M.d : ℝ) / 2 ≤ (M.d : ℝ) - c := by linarith
    have hstep1 : r ^ ((M.d : ℝ) / 2) ≤ r ^ ((M.d : ℝ) - c) :=
      Real.rpow_le_rpow_of_exponent_le hr1 hexp
    have hstep2 : r ^ ((M.d : ℝ) - c) = r ^ (M.d : ℝ) * r ^ (-c) := by
      rw [sub_eq_add_neg, Real.rpow_add hr0]
    have hlow' : (1 / 2 : ℝ) * r ^ (M.d : ℝ) ≤ ((M.ball r).ncard : ℝ) := by
      rw [Real.rpow_natCast]
      exact hlow
    have hrc : (0 : ℝ) ≤ r ^ (-c) := (Real.rpow_pos_of_pos hr0 _).le
    have hprod : (1 / 2 : ℝ) * r ^ (M.d : ℝ) * r ^ (-c)
        ≤ ((M.ball r).ncard : ℝ) * M.case3Driver c r := by
      refine mul_le_mul hlow' ?_ hrc (by positivity)
      have h3 : M.case3Driver c r = (M.nablaTail (r ^ c)).toReal + r ^ (-c) := rfl
      rw [h3]
      exact le_add_of_nonneg_left ENNReal.toReal_nonneg
    calc R ^ M.d = r ^ ((M.d : ℝ) / 2) := hRd
      _ ≤ r ^ ((M.d : ℝ) - c) := hstep1
      _ = r ^ (M.d : ℝ) * r ^ (-c) := hstep2
      _ ≤ 3 * (((M.ball r).ncard : ℝ) * M.case3Driver c r) := by nlinarith [hprod]
  have hT : (0 : ℝ) ≤ M.triSelf := ENNReal.toReal_nonneg
  have h1 : M.triSelf * (((E1Sign.ballF M r).filter
      (fun y => ¬ R ≤ M.S.dist (0 : M.V) y)).card : ℝ)
      ≤ M.triSelf * ((3 / 2 : ℝ) * R ^ M.d) :=
    mul_le_mul_of_nonneg_left hnear_card hT
  have h2 : trc * ((E1Sign.ballF M r).card : ℝ)
      ≤ M.case3Driver c r * ((M.ball r).ncard : ℝ) := by
    have hc' : ((E1Sign.ballF M r).card : ℝ) = ((M.ball r).ncard : ℝ) := by
      rw [E1Sign.card_ballF]
    rw [hc']
    exact mul_le_mul_of_nonneg_right htrc_le hS
  set S : ℝ := ((M.ball r).ncard : ℝ) with hSdef
  set D : ℝ := M.case3Driver c r with hDdef
  have hD : (0 : ℝ) ≤ D := M.case3Driver_nonneg_of_one_le hr1
  have habs : M.triSelf * ((3 / 2 : ℝ) * R ^ M.d) + D * S
      ≤ (1 + 5 * M.triSelf) * S * D :=
    arith_window hT (by linarith [hX])
  calc M.windowPolyKThree r
      ≤ M.triSelf * (((E1Sign.ballF M r).filter
            (fun y => ¬ R ≤ M.S.dist (0 : M.V) y)).card : ℝ)
        + trc * ((E1Sign.ballF M r).card : ℝ) := hsplit
    _ ≤ M.triSelf * ((3 / 2 : ℝ) * R ^ M.d) + D * S := by linarith [h1, h2]
    _ ≤ (1 + 5 * M.triSelf) * S * D := habs

/-! ## The source-shaped windowed input `WindowedEllThreeGap` -/

/-- **The windowed `ℓ = 3` input in the source's `∀ r ≥ 1` shape.**

The eventual bound `windowPolyKThree_le_case3Driver_eventually` holds from some radius `R₁`
on; below `R₁` the driver is bounded below by `R₁ ^ (-c) > 0`, so a finite enlargement of
the constant covers the remaining finite range.  The conclusion is exactly
`Defs.WindowedEllThreeGap`, i.e. the hypothesis the Case-3 window summation consumes in
place of the refuted per-vertex `hT3`. -/
theorem exists_windowedEllThreeGap {c : ℝ} (hc : 0 < c) (hc2 : c ≤ 1 / 2)
    (hTri : TriTail.openTriangleSelf M.kernel M.kernel_nonneg M.betaCrit 0 < ⊤)
    (hχ : ∀ r : ℝ, 1 ≤ r → M.cutMassAt r 0 ≠ ⊤) :
    ∃ Cp : ℝ, 0 ≤ Cp ∧ M.WindowedEllThreeGap c Cp := by
  obtain ⟨R₁, hR₁⟩ := eventually_atTop.mp
    (M.windowPolyKThree_le_case3Driver_eventually hc hc2 hTri hχ)
  have hT : (0 : ℝ) ≤ M.triSelf := ENNReal.toReal_nonneg
  refine ⟨(1 + 5 * M.triSelf) * max 1 (R₁ ^ c), ?_, ?_⟩
  · have hA : (0 : ℝ) ≤ 1 + 5 * M.triSelf := by linarith
    have hmax : (0 : ℝ) ≤ max 1 (R₁ ^ c) := le_trans zero_le_one (le_max_left _ _)
    positivity
  · intro r hr1
    have hr0 : (0 : ℝ) < r := lt_of_lt_of_le one_pos hr1
    have hS : (0 : ℝ) ≤ ((M.ball r).ncard : ℝ) := by positivity
    have hD : (0 : ℝ) ≤ M.case3Driver c r := M.case3Driver_nonneg_of_one_le hr1
    by_cases hbig : R₁ ≤ r
    · have hstep : M.windowPolyKThree r
          ≤ (1 + 5 * M.triSelf) * ((M.ball r).ncard : ℝ) * M.case3Driver c r := hR₁ r hbig
      have hA : (0 : ℝ) ≤ 1 + 5 * M.triSelf := by linarith
      have hmax : (1 : ℝ) ≤ max 1 (R₁ ^ c) := le_max_left _ _
      have hcoef : (1 + 5 * M.triSelf)
          ≤ (1 + 5 * M.triSelf) * max 1 (R₁ ^ c) := by nlinarith
      have hbase : (0 : ℝ) ≤ (1 + 5 * M.triSelf) * ((M.ball r).ncard : ℝ) * M.case3Driver c r :=
        by positivity
      calc M.windowPolyKThree r
          ≤ (1 + 5 * M.triSelf) * ((M.ball r).ncard : ℝ) * M.case3Driver c r := hstep
        _ ≤ ((1 + 5 * M.triSelf) * ((M.ball r).ncard : ℝ) * M.case3Driver c r)
              * max 1 (R₁ ^ c) := by nlinarith [hmax, hbase]
        _ = ((1 + 5 * M.triSelf) * max 1 (R₁ ^ c)) * ((M.ball r).ncard : ℝ)
              * M.case3Driver c r := by ring
    · have hrle : r ≤ R₁ := le_of_lt (lt_of_not_ge hbig)
      have hR1pos : (0 : ℝ) < R₁ := lt_of_lt_of_le hr0 hrle
      have hnear : M.windowPolyKThree r ≤ M.triSelf * ((M.ball r).ncard : ℝ) := by
        have h1 : M.windowPolyKThree r
            ≤ ∑ _y ∈ E1Sign.ballF M r, M.triSelf :=
          Finset.sum_le_sum fun y _ => M.source_ell_three_le r (hχ r hr1) hTri y
        have h2 : ∑ _y ∈ E1Sign.ballF M r, M.triSelf
            = ((E1Sign.ballF M r).card : ℝ) * M.triSelf := by
          rw [Finset.sum_const, nsmul_eq_mul]
        have h3 : ((E1Sign.ballF M r).card : ℝ) * M.triSelf
            = M.triSelf * ((M.ball r).ncard : ℝ) := by
          rw [E1Sign.card_ballF]; ring
        linarith [h1, le_of_eq h2, le_of_eq h3]
      -- the driver is bounded below on the finite range
      have hrc : R₁ ^ (-c) ≤ r ^ (-c) :=
        Real.rpow_le_rpow_of_nonpos hr0 hrle (by linarith)
      have hdrv : R₁ ^ (-c) ≤ M.case3Driver c r := by
        have h3 : M.case3Driver c r = (M.nablaTail (r ^ c)).toReal + r ^ (-c) := rfl
        rw [h3]
        linarith [ENNReal.toReal_nonneg (a := M.nablaTail (r ^ c))]
      -- the enlarged constant dominates `∇_{β_c}` on the finite range
      have hmaxge : R₁ ^ c ≤ max 1 (R₁ ^ c) := le_max_right _ _
      have hposc : (0 : ℝ) < R₁ ^ c := Real.rpow_pos_of_pos hR1pos _
      have hone : (1 : ℝ) ≤ max 1 (R₁ ^ c) * R₁ ^ (-c) := by
        have h4 : R₁ ^ c * R₁ ^ (-c) = 1 := by
          rw [← Real.rpow_add hR1pos]
          simp
        nlinarith [hmaxge, h4, hposc]
      have hA : (0 : ℝ) ≤ 1 + 5 * M.triSelf := by linarith
      have hTle : M.triSelf ≤ (1 + 5 * M.triSelf) * max 1 (R₁ ^ c) * M.case3Driver c r := by
        have h5 : (1 + 5 * M.triSelf) ≤ (1 + 5 * M.triSelf) * (max 1 (R₁ ^ c) * R₁ ^ (-c)) := by
          nlinarith
        have h6 : (1 + 5 * M.triSelf) * (max 1 (R₁ ^ c) * R₁ ^ (-c))
            ≤ (1 + 5 * M.triSelf) * max 1 (R₁ ^ c) * M.case3Driver c r := by
          have := mul_le_mul_of_nonneg_left hdrv hA
          nlinarith
        linarith
      calc M.windowPolyKThree r ≤ M.triSelf * ((M.ball r).ncard : ℝ) := hnear
        _ ≤ ((1 + 5 * M.triSelf) * max 1 (R₁ ^ c) * M.case3Driver c r)
              * ((M.ball r).ncard : ℝ) := mul_le_mul_of_nonneg_right hTle hS
        _ = (1 + 5 * M.triSelf) * max 1 (R₁ ^ c) * ((M.ball r).ncard : ℝ)
              * M.case3Driver c r := by ring

end SourceModelData
end Orchestration
end PercLib.CriticalLRP
