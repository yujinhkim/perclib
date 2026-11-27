/- Integrated from independently rebuilt and accepted
`.ultramath/smwypth8o/m1/Main.lean` at production base
`d2b527c1acf9fb8db8ca24854405020a6b3de061`. -/

/-
Swarm `smwypth8o`, member `m1`, direction d1.

# Regular variation and moment measurability for the cutoff packet of I.4.20

Read-only base: `.scratch/critical-lrp-orchestration` at commit
`e8c25f3936540fbe66322454ff596091b18b7436` (plus on-disk accepted files).

All hypotheses are explicit; nothing is invented.  See `REPORT.md`.
-/

module

public import PercLib.CriticalLRP.VolumeMoments.HigherMoments.RVData
public import PercLib.CriticalLRP.MomentMonotonicity.SourceModelCutoffLimit
public import PercLib.CriticalLRP.VolumeMoments.HigherMoments.I420Case3.SplitPolygon.TailLower
public import PercLib.CriticalLRP.Analysis.Cutoff.OffCorner.SourceCutoffAllMoments
public import PercLib.CriticalLRP.Analysis.Cutoff.OffCorner.AeDerivativeHandoff

/-! # Regular variation and its cutoff-model interfaces -/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal

set_option autoImplicit false
set_option linter.hashCommand false
set_option linter.unusedSectionVars false

namespace PercLib.CriticalLRP

namespace Analysis

set_option linter.unusedVariables false

/-! ## From a normalised asymptotic to regular variation -/

/-- A normalised asymptotic `f r / (c * r ^ a) → 1` forces `f` to be
eventually non-vanishing.  Nothing is assumed about `f` itself. -/
theorem eventually_ne_zero_of_tendsto_div {f : ℝ → ℝ} {c a : ℝ}
    (h : Tendsto (fun r : ℝ => f r / (c * r ^ a)) atTop (𝓝 1)) :
    ∀ᶠ r : ℝ in atTop, f r ≠ 0 := by
  have h2 : ∀ᶠ r : ℝ in atTop, (1 / 2 : ℝ) < f r / (c * r ^ a) :=
    h.eventually (Ioi_mem_nhds (by norm_num))
  filter_upwards [h2, eventually_gt_atTop (0 : ℝ)] with r hr hr0 hf
  rw [hf, zero_div] at hr
  linarith

/-- **A normalised asymptotic gives regular variation.**  If
`f r / (c * r ^ a) → 1` with `c ≠ 0`, then `f` is regularly varying of index
`a` at infinity.  Both conjuncts of the definition are derived: eventual
non-vanishing comes from the ratio being eventually positive, and the scaling
limit from `f (l x) / f x = (ratio (l x) / ratio x) * l ^ a`. -/
theorem regularlyVaryingAtTop_of_tendsto_div {f : ℝ → ℝ} {c a : ℝ} (hc : c ≠ 0)
    (h : Tendsto (fun r : ℝ => f r / (c * r ^ a)) atTop (𝓝 1)) :
    RegularlyVaryingAtTop f a := by
  have hne := eventually_ne_zero_of_tendsto_div h
  refine ⟨hne, fun l hl => ?_⟩
  have hcomp : Tendsto (fun x : ℝ => f (l * x) / (c * (l * x) ^ a)) atTop (𝓝 1) :=
    h.comp (Tendsto.const_mul_atTop hl tendsto_id)
  have hdiv : Tendsto (fun x : ℝ =>
      (f (l * x) / (c * (l * x) ^ a)) / (f x / (c * x ^ a))) atTop (𝓝 (1 / 1)) :=
    hcomp.div h one_ne_zero
  rw [div_one] at hdiv
  have hmul : Tendsto (fun x : ℝ =>
      ((f (l * x) / (c * (l * x) ^ a)) / (f x / (c * x ^ a))) * l ^ a) atTop (𝓝 (l ^ a)) := by
    simpa using hdiv.mul_const (l ^ a)
  refine hmul.congr' ?_
  filter_upwards [hne, eventually_gt_atTop (0 : ℝ)] with x hx hx0
  have hx0' : x ≠ 0 := ne_of_gt hx0
  have hxa : x ^ a ≠ 0 := (Real.rpow_pos_of_pos hx0 a).ne'
  have hla : l ^ a ≠ 0 := (Real.rpow_pos_of_pos hl a).ne'
  have hlxa : (l * x) ^ a = l ^ a * x ^ a := Real.mul_rpow hl.le hx0.le
  rw [hlxa]
  field_simp

/-- A function converging to a nonzero limit is regularly varying of index `0`. -/
theorem regularlyVaryingAtTop_of_tendsto_const {f : ℝ → ℝ} {c : ℝ} (hc : c ≠ 0)
    (h : Tendsto f atTop (𝓝 c)) : RegularlyVaryingAtTop f 0 := by
  refine ⟨h.eventually_ne hc, fun l hl => ?_⟩
  have hcomp : Tendsto (fun x : ℝ => f (l * x)) atTop (𝓝 c) :=
    h.comp (Tendsto.const_mul_atTop hl tendsto_id)
  have hdiv : Tendsto (fun x : ℝ => f (l * x) / f x) atTop (𝓝 (c / c)) :=
    hcomp.div h hc
  rw [div_self hc] at hdiv
  simpa using hdiv

/-- **A squeezed regular variation.**  If `G` is regularly varying and
eventually positive, `h` is bounded below by `a G` for a positive constant and
the ratio `h / G` tends to one, then `h` carries `G`'s index.  The ratio-one
premise is exactly the part that a two-sided comparison with different
constants cannot supply; it is stated here, not derived. -/
theorem regularlyVaryingAtTop_of_squeeze {G h : ℝ → ℝ} {σ a : ℝ}
    (hG : RegularlyVaryingAtTop G σ) (hGpos : ∀ᶠ x : ℝ in atTop, 0 < G x)
    (hratio : Tendsto (fun x : ℝ => h x / G x) atTop (𝓝 1))
    (hlo : ∀ᶠ x : ℝ in atTop, a * G x ≤ h x) (ha : 0 < a) :
    RegularlyVaryingAtTop h σ := by
  have hne : ∀ᶠ x : ℝ in atTop, h x ≠ 0 :=
    (hlo.and hGpos).mono (fun x hx => by
      have hpos : 0 < a * G x := mul_pos ha hx.2
      exact ne_of_gt (lt_of_lt_of_le hpos hx.1))
  refine ⟨hne, fun l hl => ?_⟩
  have hcomp : Tendsto (fun x : ℝ => h (l * x) / G (l * x)) atTop (𝓝 1) :=
    hratio.comp (Tendsto.const_mul_atTop hl tendsto_id)
  have hprod : Tendsto (fun x : ℝ =>
      (h (l * x) / G (l * x)) * (G (l * x) / G x) / (h x / G x)) atTop (𝓝 (1 * l ^ σ / 1)) :=
    (hcomp.mul (hG.2 l hl)).div hratio one_ne_zero
  simp only [one_mul, div_one] at hprod
  refine hprod.congr' ?_
  have hGne : ∀ᶠ x : ℝ in atTop, G x ≠ 0 := hG.1
  have hne_l : ∀ᶠ x : ℝ in atTop, h (l * x) ≠ 0 :=
    (Tendsto.const_mul_atTop hl tendsto_id).eventually hne
  have hGne_l : ∀ᶠ x : ℝ in atTop, G (l * x) ≠ 0 :=
    (Tendsto.const_mul_atTop hl tendsto_id).eventually hGne
  filter_upwards [hne, hGne, hne_l, hGne_l] with x hx hxG hxl hGxl
  field_simp

end Analysis

namespace Orchestration

open PercLib.CriticalLRP.Analysis
open PercLib.CriticalLRP.Analysis.Route3
open PercLib.CriticalLRP.I420Case3

/-! ## The cutoff moments as a `mom : ℕ → ℝ → ℝ` packet -/


/-- Every cutoff moment is at least one, because the root lies in its own
cluster.  This is the "cluster root positivity" used instead of monotonicity of
`toReal` (which fails at `⊤`). -/
theorem SourceModelData.one_le_cutMoment (M : SourceModelData) (m : ℕ) (r : ℝ) :
    (1 : ℝ≥0∞) ≤ M.cutMoment m r := by
  have hbase : (1 : ℝ≥0∞) ≤ ∫⁻ ω : Config M.V, clusterVol ω (0 : M.V) ^ m
      ∂(M.cutLaw r) :=
    calc (1 : ℝ≥0∞) = ∫⁻ _ω : Config M.V, (1 : ℝ≥0∞) ∂(M.cutLaw r) := by
          simp
      _ ≤ ∫⁻ ω : Config M.V, clusterVol ω (0 : M.V) ^ m ∂(M.cutLaw r) :=
          lintegral_mono (fun ω => one_le_clusterVol_pow ω (0 : M.V) m)
  simpa [SourceModelData.cutMoment] using hbase

/-- `hP` forces the first cutoff moment to be finite at *every* radius.
Eventual finiteness is read off `hP`; monotonicity of the cutoff moment in the
radius propagates it to the small radii.  No sharpness or finiteness is assumed:
`hP` is the standard input already carried by the Case-3 chain. -/
theorem SourceModelData.cutMoment_one_ne_top_of_asymptotic (M : SourceModelData) {c : ℝ}
    (hP : Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal / (c * r ^ M.α)) atTop (𝓝 1)) :
    ∀ r : ℝ, M.cutMoment 1 r ≠ ⊤ := by
  have h2 : ∀ᶠ r : ℝ in atTop, (1 / 2 : ℝ) < (M.cutMassAt r 0).toReal / (c * r ^ M.α) :=
    hP.eventually (Ioi_mem_nhds (by norm_num))
  have h3 : ∀ᶠ r : ℝ in atTop, (0 < r ∧ (M.cutMassAt r 0).toReal ≠ 0) := by
    filter_upwards [h2, eventually_gt_atTop (0 : ℝ)] with r hr hr0
    refine ⟨hr0, ?_⟩
    intro h0
    rw [h0, zero_div] at hr
    linarith
  obtain ⟨R, hR⟩ := eventually_atTop.1 h3
  intro r
  rcases lt_or_ge r R with hlt | hge
  · have hle : M.cutMoment 1 r ≤ M.cutMoment 1 R := M.cutMoment_monotone 1 hlt.le
    intro htop
    have htopR : M.cutMassAt R 0 = ⊤ := by
      rw [M.cutMassAt_zero_eq_cutMoment]
      exact top_le_iff.mp (by rw [← htop]; exact hle)
    exact (hR R le_rfl).2 (by rw [htopR]; rfl)
  · rw [← M.cutMassAt_zero_eq_cutMoment r]
    intro htop
    exact (hR r hge).2 (by rw [htop]; rfl)

/-- The real shadow of a cutoff moment that is finite everywhere is globally
measurable: it is monotone, `r ↦ M.cutMoment p r` being monotone and `toReal`
monotone on finite values.  This is *global* `Measurable` on all of `ℝ`; no
radius value below zero is interpreted. -/
theorem SourceModelData.measurable_cutMoment_toReal (M : SourceModelData) (p : ℕ)
    (hfin : ∀ r : ℝ, M.cutMoment p r ≠ ⊤) :
    Measurable (fun r : ℝ => (M.cutMoment p r).toReal) :=
  Monotone.measurable (f := fun r : ℝ => (M.cutMoment p r).toReal) (fun _a b hab =>
    ENNReal.toReal_mono (hfin b) (M.cutMoment_monotone p hab))

/-- `hP` gives regular variation of index `M.α` of the real first cutoff mass. -/
theorem SourceModelData.cutMassReal_regularlyVarying (M : SourceModelData)
    (hα : 0 < M.α) (hβ : (M.betaCrit : ℝ) ≠ 0)
    (hP : Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal
      / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) atTop (𝓝 1)) :
    RegularlyVaryingAtTop (fun r : ℝ => (M.cutMassAt r 0).toReal) M.α :=
  Analysis.regularlyVaryingAtTop_of_tendsto_div (c := M.α / (M.betaCrit : ℝ))
    (div_ne_zero hα.ne' hβ) hP

/-- **`h1` of the higher-moment packet**, for the actual real cutoff moment:
`hP` alone gives `RegularlyVaryingAtTop (mom 1) M.α`. -/
theorem SourceModelData.momOf_one_regularlyVarying (M : SourceModelData)
    (hα : 0 < M.α) (hβ : (M.betaCrit : ℝ) ≠ 0)
    (hP : Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal
      / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) atTop (𝓝 1)) :
    RegularlyVaryingAtTop (fun r : ℝ => momOf (fun r => M.cutProb r) (0 : M.V) 1 r) M.α := by
  have h := M.cutMassReal_regularlyVarying hα hβ hP
  have hfun : (fun r : ℝ => (M.cutMassAt r 0).toReal)
      = fun r : ℝ => momOf (fun r => M.cutProb r) (0 : M.V) 1 r := by
    funext r
    rw [momOf_cutProb_eq_toReal_cutMoment M r 1, M.cutMassAt_zero_eq_cutMoment r]
  rwa [hfun] at h

/-- **Positivity of every real cutoff moment** from cluster-root positivity
(`0` lies in its own cluster, so `|K| ≥ 1`) together with finiteness. -/
theorem SourceModelData.momOf_pos (M : SourceModelData) (m : ℕ) (r : ℝ)
    (hfin : M.cutMoment m r ≠ ⊤) :
    0 < momOf (fun r => M.cutProb r) (0 : M.V) m r := by
  rw [momOf_cutProb_eq_toReal_cutMoment M r m]
  exact ENNReal.toReal_pos
    (ne_of_gt (lt_of_lt_of_le one_pos (M.one_le_cutMoment m r))) hfin

/-- Positivity of every real cutoff moment at a radius with finite first cutoff
moment: all higher moments are then finite by the ordinary atlas bound
`cutMoment_le_dfactorial`. -/
theorem SourceModelData.momOf_pos_all (M : SourceModelData) (r : ℝ)
    (h1 : M.cutMoment 1 r ≠ ⊤) (m : ℕ) :
    0 < momOf (fun r => M.cutProb r) (0 : M.V) m r := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    rw [momOf_cutProb_eq_toReal_cutMoment M r 0, M.cutMoment_zero]
    norm_num
  · exact M.momOf_pos m r (cutMoment_ne_top_of_one M r h1 m)

/-- **`hmom` of the higher-moment packet**: every real cutoff moment is
strictly positive at every radius, from `hP` alone. -/
theorem SourceModelData.momOf_pos_of_hP (M : SourceModelData) {c : ℝ}
    (hP : Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal / (c * r ^ M.α)) atTop (𝓝 1)) :
    ∀ m : ℕ, ∀ r : ℝ, 0 < r → 0 < momOf (fun r => M.cutProb r) (0 : M.V) m r := by
  have h1 : ∀ r : ℝ, M.cutMoment 1 r ≠ ⊤ := M.cutMoment_one_ne_top_of_asymptotic hP
  exact fun m r _hr => M.momOf_pos_all r (h1 r) m

/-- **`hmommeas1` and `hmommeas2` of the higher-moment packet**, from `hP`
alone: both real cutoff moments are globally measurable on `ℝ`. -/
theorem SourceModelData.momOf_measurable_one_two (M : SourceModelData) {c : ℝ}
    (hP : Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal / (c * r ^ M.α)) atTop (𝓝 1)) :
    Measurable (fun r : ℝ => momOf (fun r => M.cutProb r) (0 : M.V) 1 r) ∧
      Measurable (fun r : ℝ => momOf (fun r => M.cutProb r) (0 : M.V) 2 r) := by
  have h1 : ∀ r : ℝ, M.cutMoment 1 r ≠ ⊤ := M.cutMoment_one_ne_top_of_asymptotic hP
  have h2 : ∀ r : ℝ, M.cutMoment 2 r ≠ ⊤ := fun r =>
    cutMoment_ne_top_of_one M r (h1 r) 2
  have hm1 := M.measurable_cutMoment_toReal 1 h1
  have hm2 := M.measurable_cutMoment_toReal 2 h2
  constructor
  · have hfun : (fun r : ℝ => momOf (fun r => M.cutProb r) (0 : M.V) 1 r)
        = fun r : ℝ => (M.cutMoment 1 r).toReal := by
      funext r; exact momOf_cutProb_eq_toReal_cutMoment M r 1
    rw [hfun]; exact hm1
  · have hfun : (fun r : ℝ => momOf (fun r => M.cutProb r) (0 : M.V) 2 r)
        = fun r : ℝ => (M.cutMoment 2 r).toReal := by
      funext r; exact momOf_cutProb_eq_toReal_cutMoment M r 2
    rw [hfun]; exact hm2

/-- The ordinary atlas bound `E|K|² ≤ 3 (E|K|)³` at a radius with finite first
cutoff moment, in reals. -/
theorem SourceModelData.cutMoment_two_toReal_le (M : SourceModelData) (r : ℝ)
    (h1 : M.cutMoment 1 r ≠ ⊤) :
    (M.cutMoment 2 r).toReal ≤ (VolumeMoments.M 1 : ℝ) * (M.cutMoment 1 r).toReal ^ 3 := by
  have h := cutMoment_le_dfactorial M r (q := 2) (by norm_num)
  have h3 : 2 * 2 - 1 = 3 := by norm_num
  rw [h3] at h
  have hR : ((VolumeMoments.M 1 : ℝ≥0∞) * M.cutMoment 1 r ^ 3) ≠ ⊤ :=
    ENNReal.mul_ne_top (by simp) (ENNReal.pow_ne_top h1)
  have hle := ENNReal.toReal_mono hR h
  rwa [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_natCast] at hle

/-- **The two-sided second-moment comparison available at HEAD**: the ordinary
atlas bound from above and `case3_hgm_of_tail` from below.  A bounded
comparison only — *not* a ratio asymptotic. -/
theorem SourceModelData.momOf_two_squeeze (M : SourceModelData) {C : ℝ} (hC : 0 ≤ C)
    (hTail : ∀ n : ℕ, 1 ≤ n →
      M.criticalLaw {ω : Config M.V | (n : ℝ≥0∞) ≤ clusterVol ω (0 : M.V)} ≤
        tailEnvelope C n)
    (h1fin : ∀ r : ℝ, M.cutMoment 1 r ≠ ⊤) :
    (∃ a : ℝ, 0 < a ∧ ∀ᶠ r : ℝ in atTop,
        a * momOf (fun r => M.cutProb r) (0 : M.V) 1 r ^ (3 : ℕ)
          ≤ momOf (fun r => M.cutProb r) (0 : M.V) 2 r) ∧
      (∃ b : ℝ, 0 < b ∧ ∀ᶠ r : ℝ in atTop,
        momOf (fun r => M.cutProb r) (0 : M.V) 2 r
          ≤ b * momOf (fun r => M.cutProb r) (0 : M.V) 1 r ^ (3 : ℕ)) := by
  constructor
  · obtain ⟨c3, hc3, hgm⟩ := case3_hgm_of_tail M hC hTail
      (fun r _hr => cutMoment_ne_top_of_one M r (h1fin r) 2)
    exact ⟨c3, hc3, hgm⟩
  · refine ⟨(VolumeMoments.M 1 : ℝ), ?_, ?_⟩
    · exact_mod_cast VolumeMoments.M_pos 1
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with r _hr
      rw [momOf_cutProb_eq_toReal_cutMoment M r 2,
        momOf_cutProb_eq_toReal_cutMoment M r 1]
      exact M.cutMoment_two_toReal_le r (h1fin r)

end Orchestration

namespace Analysis

/-- Regular variation transports along an eventual equality. -/
theorem RegularlyVaryingAtTop.congr' {f g : ℝ → ℝ} {a : ℝ} (h : f =ᶠ[atTop] g)
    (hf : RegularlyVaryingAtTop f a) : RegularlyVaryingAtTop g a := by
  have hne : ∀ᶠ x : ℝ in atTop, g x ≠ 0 := by
    filter_upwards [h, hf.1] with x hx hx0
    rw [← hx]
    exact hx0
  refine ⟨hne, fun l hl => ?_⟩
  have hl_ev : ∀ᶠ x : ℝ in atTop, f (l * x) = g (l * x) :=
    (Tendsto.const_mul_atTop hl tendsto_id).eventually h
  have hratio : ∀ᶠ x : ℝ in atTop, f (l * x) / f x = g (l * x) / g x := by
    filter_upwards [hl_ev, h, hf.1, hne] with x h1 h2 hf0 hg0
    rw [h1, h2]
  exact (hf.2 l hl).congr' hratio

/-- The cube of a regularly varying function is regularly varying of three
times the index. -/
theorem regularlyVaryingAtTop_pow_three {g : ℝ → ℝ} {ρ : ℝ}
    (hg : RegularlyVaryingAtTop g ρ) :
    RegularlyVaryingAtTop (fun x : ℝ => g x ^ (3 : ℕ)) (3 * ρ) := by
  refine ⟨?_, fun l hl => ?_⟩
  · filter_upwards [hg.1] with x hx
    exact pow_ne_zero 3 hx
  · have hp : Tendsto (fun x : ℝ => (g (l * x) / g x) ^ (3 : ℕ)) atTop
        (𝓝 ((l ^ ρ) ^ (3 : ℕ))) :=
      (hg.2 l hl).pow 3
    have hidx : (l ^ ρ) ^ (3 : ℕ) = l ^ (3 * ρ) := by
      have h1 : (l ^ ρ) ^ (3 : ℕ) = (l ^ ρ) ^ (3 : ℝ) :=
        (Real.rpow_natCast (l ^ ρ) 3).symm
      rw [h1, ← Real.rpow_mul hl.le ρ 3]
      congr 1
      ring
    rw [hidx] at hp
    refine hp.congr' ?_
    filter_upwards with x
    rw [div_pow]

end Analysis

namespace Orchestration

open PercLib.CriticalLRP.Analysis
open PercLib.CriticalLRP.I420Case3
open PercLib.CriticalLRP.VolumeMoments.HigherMoments

/-- **The exact remaining freedom in the second-moment comparison.**  Given the
first-moment regular variation, the second-moment regular variation of index
`3α` is *equivalent* to the comparison factor `mom 2 / (mom 1) ^ 3` being
slowly varying.  A bounded two-sided comparison of that factor is weaker than
this and is not used as a substitute. -/
theorem SourceModelData.momTwo_regularlyVarying_iff_slowly (M : SourceModelData) {α : ℝ}
    (h1 : RegularlyVaryingAtTop (fun r : ℝ => momOf (fun r => M.cutProb r) (0 : M.V) 1 r) α)
    (h1pos : ∀ᶠ r : ℝ in atTop, 0 < momOf (fun r => M.cutProb r) (0 : M.V) 1 r) :
    RegularlyVaryingAtTop (fun r : ℝ => momOf (fun r => M.cutProb r) (0 : M.V) 2 r) (3 * α) ↔
      RegularlyVaryingAtTop
        (fun r : ℝ => momOf (fun r => M.cutProb r) (0 : M.V) 2 r
          / momOf (fun r => M.cutProb r) (0 : M.V) 1 r ^ (3 : ℕ)) 0 := by
  have hcube := Analysis.regularlyVaryingAtTop_pow_three h1
  constructor
  · intro h2
    have h := h2.mul hcube.inv
    rw [show 3 * α + -(3 * α) = 0 by ring] at h
    refine h.congr' ?_
    filter_upwards with r
    rw [div_eq_mul_inv]
  · intro hs
    have h := hs.mul hcube
    rw [show 0 + 3 * α = 3 * α by ring] at h
    refine h.congr' ?_
    filter_upwards [h1pos] with r hr
    field_simp

/-- **A sufficient form of the second-moment regular variation**: convergence of
the comparison factor to a nonzero limit.  This is strictly stronger than the
bounded comparison `case3_hgm_of_tail` + the ordinary atlas bound provide, and
it is stated as an input rather than derived. -/
theorem SourceModelData.momTwo_regularlyVarying_of_tendsto_ratio (M : SourceModelData) {α c : ℝ}
    (h1 : RegularlyVaryingAtTop (fun r : ℝ => momOf (fun r => M.cutProb r) (0 : M.V) 1 r) α)
    (h1pos : ∀ᶠ r : ℝ in atTop, 0 < momOf (fun r => M.cutProb r) (0 : M.V) 1 r)
    (hratio : Tendsto
      (fun r : ℝ => momOf (fun r => M.cutProb r) (0 : M.V) 2 r
        / momOf (fun r => M.cutProb r) (0 : M.V) 1 r ^ (3 : ℕ)) atTop (𝓝 c))
    (hc : c ≠ 0) :
    RegularlyVaryingAtTop (fun r : ℝ => momOf (fun r => M.cutProb r) (0 : M.V) 2 r) (3 * α) :=
  (M.momTwo_regularlyVarying_iff_slowly h1 h1pos).2
    (Analysis.regularlyVaryingAtTop_of_tendsto_const hc hratio)

/-- **The full side-premise packet of the higher-moment machinery for the
actual cutoff moments.**  `hmom` (positivity), `hmommeas1`, `hmommeas2` and
`h1` (first-moment regular variation) are all derived from `hP`; the
second-moment regular variation `h2` is the one genuinely independent input,
matching Proposition I.4.15 / gap WS002. -/
theorem SourceModelData.momOf_packet (M : SourceModelData) (hα : 0 < M.α)
    (hβ : (M.betaCrit : ℝ) ≠ 0)
    (hP : Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal
      / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) atTop (𝓝 1))
    (h2 : RegularlyVaryingAtTop (fun r : ℝ => momOf (fun r => M.cutProb r) (0 : M.V) 2 r)
      (3 * M.α)) :
    (∀ m : ℕ, ∀ r : ℝ, 0 < r → 0 < momOf (fun r => M.cutProb r) (0 : M.V) m r) ∧
      Measurable (fun r : ℝ => momOf (fun r => M.cutProb r) (0 : M.V) 1 r) ∧
      Measurable (fun r : ℝ => momOf (fun r => M.cutProb r) (0 : M.V) 2 r) ∧
      RegularlyVaryingAtTop (fun r : ℝ => momOf (fun r => M.cutProb r) (0 : M.V) 1 r) M.α ∧
      RegularlyVaryingAtTop (fun r : ℝ => momOf (fun r => M.cutProb r) (0 : M.V) 2 r)
        (3 * M.α) :=
  ⟨M.momOf_pos_of_hP hP, (M.momOf_measurable_one_two hP).1,
    (M.momOf_measurable_one_two hP).2, M.momOf_one_regularlyVarying hα hβ hP, h2⟩

/-- **The `RVPosData` of the driving term, instantiated at the actual cutoff
moments.**  This is the consumer of the packet: the `RegularlyVaryingAtTop`
and measurability data required by `drivingTerm_RVPosData` are supplied from
`hP` and `h2`. -/
theorem SourceModelData.drivingTerm_RVPosData_of_hP (M : SourceModelData) (p : ℕ) (hp : 3 ≤ p)
    (hα : 0 < M.α) (hβ : (M.betaCrit : ℝ) ≠ 0)
    (hP : Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal
      / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) atTop (𝓝 1))
    (h2 : RegularlyVaryingAtTop (fun r : ℝ => momOf (fun r => M.cutProb r) (0 : M.V) 2 r)
      (3 * M.α)) :
    Nonempty (RVPosData
      (drivingTerm p M.α (fun m r => momOf (fun r => M.cutProb r) (0 : M.V) m r))
      ((2 * (p : ℝ) - 1) * M.α)) :=
  drivingTerm_RVPosData (α := M.α) hp hα (M.momOf_pos_of_hP hP)
    (M.momOf_measurable_one_two hP).1 (M.momOf_measurable_one_two hP).2
    (M.momOf_one_regularlyVarying hα hβ hP) h2

/-- **`h1` of the packet from the repo's actual first-moment asymptotic.**  The
conclusion of `SourceModelData.first_moment_asymptotic_ae_of_critical_divergence`
(`Analysis/Cutoff/OffCorner/AeDerivativeHandoff.lean`) is literally the `hP` shape
consumed by `momOf_one_regularlyVarying`, so the regular variation of the real
first cutoff moment follows with no further input.  Note `0 < M.α` is a field of
`SourceModelData`. -/
theorem SourceModelData.momOf_one_regularlyVarying_of_critical_divergence
    (M : SourceModelData) (T : ℕ → Finset M.V) (hTmono : Monotone T) (hT : ∀ y : M.V, ∃ n, y ∈ T n)
    (Se : ℕ → Finset (Sym2 M.V)) (hSmono : Monotone Se) (hS : ∀ e : Sym2 M.V, ∃ n, e ∈ Se n)
    {R a₀ r₀ C : ℝ} (hRpos : 0 < R) (hRa₀ : R < a₀) (ha₀r₀ : a₀ < r₀)
    (hβ : (0 : ℝ) < (M.betaCrit : ℝ))
    (hlowenv : ∀ s : ℝ, R < s → (1 / 2) * s ^ (-(M.d : ℝ) - M.α - 1) ≤ |deriv M.K s|)
    (huppenv : ∀ s : ℝ, R < s → |deriv M.K s| ≤ 2 * s ^ (-(M.d : ℝ) - M.α - 1))
    (h2 : ∀ t : ℝ, a₀ ≤ t → M.cutMoment 2 t ≠ ⊤)
    (hcontinf : ∀ y : M.V, ∀ r : ℝ, a₀ ≤ r → ContinuousAt
      (sMomentInfFlux (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv) r)
    (hK : ∀ r : ℝ, a₀ ≤ r → ContinuousAt (fun r' => deriv M.K r') r)
    (hex : ∀ r : ℝ, a₀ ≤ r → ContinuousAt M.exclScalar r)
    (htop : M.uncutMean M.betaCrit = ⊤)
    (hfin : ∀ᶠ r : ℝ in atTop, M.cutMassAt r 0 ≠ ⊤)
    (hC : ∀ t : ℝ, r₀ ≤ t → |I420Case3.cutError M t| ≤ C)
    (h0 : Tendsto (I420Case3.cutError M) atTop (𝓝 0)) :
    RegularlyVaryingAtTop (fun r : ℝ => momOf (fun r => M.cutProb r) (0 : M.V) 1 r) M.α :=
  M.momOf_one_regularlyVarying M.hα (ne_of_gt hβ)
    (M.first_moment_asymptotic_ae_of_critical_divergence T hTmono hT Se hSmono hS hRpos hRa₀
      ha₀r₀ hβ hlowenv huppenv h2 hcontinf hK hex htop hfin hC h0)

end Orchestration

end PercLib.CriticalLRP

/-! ## Axiom audit

Only the standard axioms `propext`, `Classical.choice` and `Quot.sound` are
permitted.  Every declaration of this file is listed below. -/

set_option linter.style.longLine false

#print axioms PercLib.CriticalLRP.Analysis.eventually_ne_zero_of_tendsto_div
#print axioms PercLib.CriticalLRP.Analysis.regularlyVaryingAtTop_of_tendsto_div
#print axioms PercLib.CriticalLRP.Analysis.regularlyVaryingAtTop_of_tendsto_const
#print axioms PercLib.CriticalLRP.Analysis.regularlyVaryingAtTop_of_squeeze
#print axioms PercLib.CriticalLRP.Analysis.RegularlyVaryingAtTop.congr'
#print axioms PercLib.CriticalLRP.Analysis.regularlyVaryingAtTop_pow_three
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.one_le_cutMoment
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.cutMoment_one_ne_top_of_asymptotic
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.measurable_cutMoment_toReal
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.cutMassReal_regularlyVarying
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.momOf_one_regularlyVarying
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.momOf_pos
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.momOf_pos_all
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.momOf_pos_of_hP
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.momOf_measurable_one_two
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.cutMoment_two_toReal_le
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.momOf_two_squeeze
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.momTwo_regularlyVarying_iff_slowly
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.momTwo_regularlyVarying_of_tendsto_ratio
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.momOf_packet
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.momOf_one_regularlyVarying_of_critical_divergence
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.drivingTerm_RVPosData_of_hP
