/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
Lemma I.5.8 of T. Hutchcroft, *Critical long-range percolation I*
(arXiv:2508.18807v1): proof of the two expectation-level comparisons

    (BC)  ex (Bfun) = ex (Cfun)          (DF)  ex (Dfun) = - ex (Ffun)

that `VolumeMoments/I58Collapse.lean` isolates as the exact residue
`B - C + 2D + 2F` of the paper's six-to-four term collapse ((I.5.3)).

## Source reading

The paper's proof of `lem:gyration_derivative2` expands `⟨z-x,u⟩²` with
`z - x = (z-y) + (y-0) + (0-x)` into six terms and then says

> "Using the mass-transport principle again to exchange the roles of `0` and `y`
>  we see that some of these terms are equal"

leaving four terms.  This file shows what that sentence must mean, and proves it.

## The mechanism: the point reflection `x ↦ y - x`

"Exchanging the roles of `0` and `y`" is *not* a translation and *not* a global
mass transport: it is the **reflection of the whole configuration in the
mid-point of `0` and `y`**, i.e. the lattice involution

    ρ_y : x ↦ y - x,      ρ_y(0) = y,  ρ_y(y) = 0,  ρ_y ∘ ρ_y = id.

For a radial (hence inversion-invariant) edge law every `ρ_y` preserves the
law, and it exchanges the cluster of `0` with the cluster of `y`.  This is a
*per-site* symmetry, and its consequences are therefore per-site too:

* `q_u ∘ (ρ_y · - y) = q_u`, so on the reflected configuration the term
  `|K_0| Σ_{z ∈ K_y} q_u(z - y)` becomes exactly `|K_y| Σ_{x ∈ K_0} q_u(x)`.
  This is the exact `q_u(y)`-cancellation: everything that would carry a
  `q_u(y)` (or a `⟪y,u⟫` factor multiplying the quadratic weight) is destroyed
  by the evenness of `q_u`, so `(BC)` needs no `q_u(y)` bookkeeping at all.
* `⟪ρ_y z - y, u⟫ = -⟪z,u⟫`, so the *linear* moment is odd: writing
  `d_y := 1(y∉K_0)·⟪y,u⟫·|K_0|·Σ_{z∈K_y}⟪z-y,u⟫` and
  `f_y := 1(y∉K_0)·⟪y,u⟫·|K_y|·Σ_{x∈K_0}⟪x,u⟫`, one gets
  `d_y ∘ ρ_y = - f_y` and `f_y ∘ ρ_y = - d_y`, hence `d_y + f_y` is odd
  under `ρ_y` and has mean zero.  That is `(DF)`; the dot signs are exactly the
  two minus signs (`⟪ρ_y x - y, u⟫ = -⟪x,u⟫` and `⟪ρ_y z, u⟫ = ⟪y,u⟫ - ⟪z,u⟫`)
  appearing on the two cross-terms.

Both identities therefore hold for **every** `Finset B` of sites — no symmetry
of `B` is needed, and no "enlargement" of `B` is involved.

## What is hypothesised, and what is proved

The lattice involution `ρ_y` and its effect on `q_u`, `⟪·,u⟫` are *theorems*
here (`rho_*`, `q_rho_sub`, `dot_rho_sub`).  The single model hypothesis is
`PRefl u K Ky w y`, a bundle of

  `R` (the configuration-space involution), `R ∘ R = id`, `w ∘ R = w`,
  `K (R ω) = ρ_y '' K_y ω`, `K_y (R ω) = ρ_y '' K_0 ω`,
  `y ∈ K_0 ↔ 0 ∈ K_y`.

These are *not* restated expectation identities: they are pointwise structural
facts (a symmetry of the weight and the equivariance of the two cluster maps),
exactly the "exchange the roles of `0` and `y`" input of the source.  They are
satisfied by every radial edge law; `I58ReflectWitness.lean` verifies them, and
evaluates both comparisons non-trivially, in an explicit finite model whose
clusters are connected components of a three-edge graph.

## Model

*Abstract finite weighted model*: `Ω` is a `Fintype` (the configuration space,
with no product structure assumed) and `w : Ω → ℝ` an arbitrary weight meant to
be nonnegative and normalised.  Neither the canonical Bernoulli algebra
`configurationLaw p` nor the torus geometry enters; the expectation `ex w` is
`I58Remainder`'s finite sum `∑ ω, w ω * X ω`.

No `sorry`, no `admit`, no custom axioms, no `native_decide`.
-/
module

public import PercLib.CriticalLRP.VolumeMoments.I58Collapse

set_option autoImplicit true

@[expose] public section

open Finset

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace PercLib.CriticalLRP.I58

variable {d : ℕ}

/-! ## 1. The lattice involution `x ↦ y - x` -/

/-- The reflection of `Z^d` in the mid-point of `0` and `y`: `x ↦ y - x`.
This is the source's "exchange the roles of `0` and `y`" at the level of sites. -/
def rho (y x : Site d) : Site d := y - x

@[simp] theorem rho_apply (y x : Site d) : rho y x = y - x := rfl

@[simp] theorem rho_y (y : Site d) : rho y y = 0 := by simp [rho]

@[simp] theorem rho_zero (y : Site d) : rho y 0 = y := by simp [rho]

theorem rho_involutive (y : Site d) : Function.Involutive (rho y) := by
  intro x
  simp [rho]

theorem rho_injective (y : Site d) : Function.Injective (rho y) := by
  intro a b h
  have := congrArg (rho y) h
  simpa using this

/-- `ρ_y` is a bijection of the lattice. -/
theorem rho_bijective (y : Site d) : Function.Bijective (rho y) :=
  (rho_involutive y).bijective

/-- The reflection sends the site `y - x` to `x`: the vector `z - y` becomes `-x`. -/
theorem rho_eq_self_iff {y z : Site d} (h : rho y z = y) : z = 0 := by
  rw [rho_apply] at h
  have h2 : y + -z = y + -0 := by
    rw [neg_zero, add_zero, ← sub_eq_add_neg]
    exact h
  have h3 : -z = -0 := add_left_cancel h2
  simpa using h3

/-- **The projection is odd**: `⟪ρ_y z - y, u⟫ = -⟪z,u⟫`. -/
theorem dot_rho_sub (u : Fin d → ℝ) (y x : Site d) :
    dot u (rho y x - y) = - dot u x := by
  have h : rho y x - y = -x := by rw [rho_apply]; abel
  rw [h, dot_neg]

/-- **The quadratic weight is even**: `q_u(ρ_y x - y) = q_u(x)`.
This is the exact `q_u(y)`-cancellation behind `(BC)`. -/
theorem q_rho_sub (u : Fin d → ℝ) (y x : Site d) :
    q u (rho y x - y) = q u x := by
  simp only [q, dot_rho_sub]
  ring

/-- Cardinality of the reflected cluster. -/
theorem card_image_rho (y : Site d) (s : Finset (Site d)) :
    (s.image (rho y)).card = s.card :=
  Finset.card_image_of_injective s (rho_injective y)

/-! ## 2. The model hypothesis: a point-reflection symmetry at `0`/`y` -/

variable {Ω : Type*} [Fintype Ω]

/-- **The point-reflection symmetry at the mid-point of `0` and `y`.**

The source's "exchange the roles of `0` and `y`" for a stationary (radial) law:
the configuration-space involution `R` preserves the weight and exchanges the
cluster of `0` with the cluster of `y` through the lattice reflection `ρ_y`,
and the two sites `0`, `y` are joined or not simultaneously.

`K` is the cluster of `0` and `Ky y` the (restored) cluster of `y`, exactly as
in `I58Remainder`.  Nothing about the size of the clusters, about `B`, or about
independence is assumed. -/
structure PRefl (u : Fin d → ℝ) (K : Ω → Finset (Site d))
    (Ky : Site d → Ω → Finset (Site d)) (w : Ω → ℝ) (y : Site d) where
  /-- the configuration-space involution realising the reflection `ρ_y` -/
  R : Ω → Ω
  /-- it is an involution -/
  invol : Function.Involutive R
  /-- it preserves the weight -/
  weight : ∀ ω, w (R ω) = w ω
  /-- it exchanges the cluster of `0` with the cluster of `y` -/
  cluster0 : ∀ ω, K (R ω) = (Ky y ω).image (rho y)
  /-- and conversely -/
  clusterY : ∀ ω, Ky y (R ω) = (K ω).image (rho y)
  /-- `0` and `y` are joined simultaneously -/
  sep : ∀ ω, (y ∈ K ω ↔ 0 ∈ Ky y ω)

variable {u : Fin d → ℝ} {K : Ω → Finset (Site d)}
  {Ky : Site d → Ω → Finset (Site d)} {w : Ω → ℝ} {y : Site d}

/-- Change of variables in the finite expectation along an involution that
preserves the weight. -/
theorem ex_comp_invol {R : Ω → Ω} (hinv : Function.Involutive R)
    (hw : ∀ ω, w (R ω) = w ω) (X : Ω → ℝ) :
    ex w (fun ω => X (R ω)) = ex w X := by
  simp only [ex]
  have h1 : (∑ ω, w ω * X (R ω)) = ∑ ω, w (R ω) * X (R ω) :=
    Finset.sum_congr rfl fun ω _ => by rw [hw ω]
  rw [h1]
  exact Equiv.sum_comp (Equiv.ofBijective R hinv.bijective) (fun ω => w ω * X ω)

/-- The reflection preserves the restoring indicator `1(y ∉ K_0)`. -/
theorem indOut_comp (P : PRefl u K Ky w y) (ω : Ω) :
    indOut K y (P.R ω) = indOut K y ω := by
  have hiff : (y ∈ K (P.R ω)) ↔ (y ∈ K ω) := by
    rw [P.cluster0 ω, Finset.mem_image, P.sep ω]
    constructor
    · rintro ⟨z, hz, hzy⟩
      have hzx : z = 0 := rho_eq_self_iff hzy
      simpa [hzx] using hz
    · intro h0
      exact ⟨0, h0, by simp [rho]⟩
  simp only [indOut, hiff]

/-- **`(BC)` at a single site.**  Under the point reflection, the first
comparison term of the paper, `|K_0| Σ_{z∈K_y} q_u(z-y)`, becomes the second,
`|K_y| Σ_{x∈K_0} q_u(x)`. -/
theorem bSite_comp (P : PRefl u K Ky w y) (ω : Ω) :
    indOut K y (P.R ω) * (kcard K (P.R ω) * (∑ z ∈ Ky y (P.R ω), qrel u y z))
      = indOut K y ω * (kcard (Ky y) ω * kS u K ω) := by
  have hcard : kcard K (P.R ω) = kcard (Ky y) ω := by
    simp only [kcard]
    rw [P.cluster0 ω, card_image_rho]
  have hsum : (∑ z ∈ Ky y (P.R ω), qrel u y z) = kS u K ω := by
    have h1 : (∑ z ∈ (K ω).image (rho y), qrel u y z)
        = ∑ x ∈ K ω, qrel u y (rho y x) :=
      Finset.sum_image (fun a _ b _ hab => rho_injective y hab)
    rw [P.clusterY ω, h1]
    simp only [kS, sMoment]
    exact Finset.sum_congr rfl fun x _ => by
      simp only [qrel_apply]
      exact q_rho_sub u y x
  rw [indOut_comp P ω, hcard, hsum]

/-- **`(DF)`, first half.**  On the reflected configuration the `D`-integrand
becomes minus the `F`-integrand at `ω`. -/
theorem dSite_comp (P : PRefl u K Ky w y) (ω : Ω) :
    indOut K y (P.R ω) *
        (kcard K (P.R ω) * (dot u y * (∑ z ∈ Ky y (P.R ω), drel u y z)))
      = - (indOut K y ω * (kcard (Ky y) ω * (dot u y * kDot u K ω))) := by
  have hcard : kcard K (P.R ω) = kcard (Ky y) ω := by
    simp only [kcard]
    rw [P.cluster0 ω, card_image_rho]
  have hsum : (∑ z ∈ Ky y (P.R ω), drel u y z) = -kDot u K ω := by
    have h1 : (∑ z ∈ (K ω).image (rho y), drel u y z)
        = ∑ x ∈ K ω, drel u y (rho y x) :=
      Finset.sum_image (fun a _ b _ hab => rho_injective y hab)
    rw [P.clusterY ω, h1]
    simp only [drel_apply, kDot]
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun x _ => dot_rho_sub u y x
  rw [indOut_comp P ω, hcard, hsum]
  ring

/-- **`(DF)`, second half.**  On the reflected configuration the `F`-integrand
becomes minus the `D`-integrand at `ω`. -/
theorem fSite_comp (P : PRefl u K Ky w y) (ω : Ω) :
    indOut K y (P.R ω) *
        (kcard (Ky y) (P.R ω) * (dot u y * kDot u K (P.R ω)))
      = - (indOut K y ω * (kcard K ω * (dot u y * (∑ z ∈ Ky y ω, drel u y z)))) := by
  have hcard : kcard (Ky y) (P.R ω) = kcard K ω := by
    simp only [kcard]
    rw [P.clusterY ω, card_image_rho]
  have hsum : kDot u K (P.R ω) = -(∑ z ∈ Ky y ω, drel u y z) := by
    have h1 : (∑ z ∈ (Ky y ω).image (rho y), dot u z)
        = ∑ x ∈ Ky y ω, dot u (rho y x) :=
      Finset.sum_image (fun a _ b _ hab => rho_injective y hab)
    simp only [kDot]
    rw [P.cluster0 ω, h1]
    simp only [drel_apply]
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun z _ => by
      have h' : rho y z = -(z - y) := by rw [rho_apply]; abel
      rw [h', dot_neg]
  rw [indOut_comp P ω, hcard, hsum]
  ring

/-- **The linear two-point moment is odd under the point reflection.** -/
theorem dSite_add_fSite_comp (P : PRefl u K Ky w y) (ω : Ω) :
    (indOut K y (P.R ω) *
          (kcard K (P.R ω) * (dot u y * (∑ z ∈ Ky y (P.R ω), drel u y z)))
        + indOut K y (P.R ω) *
            (kcard (Ky y) (P.R ω) * (dot u y * kDot u K (P.R ω))))
      = - (indOut K y ω * (kcard K ω * (dot u y * (∑ z ∈ Ky y ω, drel u y z)))
        + indOut K y ω * (kcard (Ky y) ω * (dot u y * kDot u K ω))) := by
  rw [dSite_comp P ω, fSite_comp P ω]
  ring

/-- **`(DF)` at a single site**, hence its expectation vanishes. -/
theorem ex_site_D_add_F_eq_zero (P : PRefl u K Ky w y) :
    ex w (fun ω => indOut K y ω * (kcard K ω * (dot u y * (∑ z ∈ Ky y ω, drel u y z)))
        + indOut K y ω * (kcard (Ky y) ω * (dot u y * kDot u K ω))) = 0 := by
  set X : Ω → ℝ := fun ω =>
    indOut K y ω * (kcard K ω * (dot u y * (∑ z ∈ Ky y ω, drel u y z)))
      + indOut K y ω * (kcard (Ky y) ω * (dot u y * kDot u K ω)) with hX
  have h1 : ex w (fun ω => X (P.R ω)) = ex w X := ex_comp_invol P.invol P.weight X
  have h2 : (fun ω => X (P.R ω)) = fun ω => -X ω := by
    funext ω
    exact dSite_add_fSite_comp P ω
  rw [h2, ex_neg] at h1
  linarith

/-! ## 3. The two comparisons, summed over an arbitrary set of sites -/

/-- **`(BC)`: `ex Bfun = ex Cfun`**, for an arbitrary finite set `B` of sites. -/
theorem ex_Bfun_eq_ex_Cfun (B : Finset (Site d))
    (hR : ∀ y ∈ B, PRefl u K Ky w y) :
    ex w (Bfun u K Ky B) = ex w (Cfun u K Ky B) := by
  have h1 : ex w (Bfun u K Ky B)
      = ∑ y ∈ B, ex w (fun ω =>
          indOut K y ω * (kcard K ω * (∑ z ∈ Ky y ω, qrel u y z))) := by
    rw [show Bfun u K Ky B = fun ω =>
        ∑ y ∈ B, indOut K y ω * (kcard K ω * (∑ z ∈ Ky y ω, qrel u y z)) from rfl]
    exact ex_sum B _
  have h2 : ex w (Cfun u K Ky B)
      = ∑ y ∈ B, ex w (fun ω =>
          indOut K y ω * (kcard (Ky y) ω * kS u K ω)) := by
    rw [show Cfun u K Ky B = fun ω =>
        ∑ y ∈ B, indOut K y ω * (kcard (Ky y) ω * kS u K ω) from rfl]
    exact ex_sum B _
  rw [h1, h2]
  refine Finset.sum_congr rfl fun y hy => ?_
  set X : Ω → ℝ := fun ω => indOut K y ω * (kcard K ω * (∑ z ∈ Ky y ω, qrel u y z))
    with hX
  have h := ex_comp_invol (hR y hy).invol (hR y hy).weight X
  have h2 : (fun ω => X ((hR y hy).R ω))
      = fun ω => indOut K y ω * (kcard (Ky y) ω * kS u K ω) := by
    funext ω
    rw [hX]
    exact bSite_comp (hR y hy) ω
  rw [← h, h2]

/-- **`(DF)`: `ex Dfun = - ex Ffun`**, for an arbitrary finite set `B` of sites.
This is the genuine two-point linear-moment transport: `⟪y,u⟫⟪z-y,u⟫` and
`⟪y,u⟫⟪x,u⟫` are exchanged with a sign by the reflection `ρ_y`. -/
theorem ex_Dfun_eq_neg_ex_Ffun (B : Finset (Site d))
    (hR : ∀ y ∈ B, PRefl u K Ky w y) :
    ex w (Dfun u K Ky B) = -ex w (Ffun u K Ky B) := by
  have hD : ex w (Dfun u K Ky B)
      = ∑ y ∈ B, ex w (fun ω =>
          indOut K y ω * (kcard K ω * (dot u y * (∑ z ∈ Ky y ω, drel u y z)))) := by
    rw [show Dfun u K Ky B = fun ω =>
        ∑ y ∈ B, indOut K y ω *
          (kcard K ω * (dot u y * (∑ z ∈ Ky y ω, drel u y z))) from rfl]
    exact ex_sum B _
  have hF : ex w (Ffun u K Ky B)
      = ∑ y ∈ B, ex w (fun ω =>
          indOut K y ω * (kcard (Ky y) ω * (dot u y * kDot u K ω))) := by
    rw [show Ffun u K Ky B = fun ω =>
        ∑ y ∈ B, indOut K y ω *
          (kcard (Ky y) ω * (dot u y * kDot u K ω)) from rfl]
    exact ex_sum B _
  have hsum : ex w (Dfun u K Ky B) + ex w (Ffun u K Ky B) = 0 := by
    rw [hD, hF, ← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun y hy => ?_
    have h := ex_site_D_add_F_eq_zero (hR y hy)
    rw [ex_add] at h
    exact h
  linarith

/-! ## 4. The collapse -/

/-- **The six-to-four term collapse of `(I.5.3)`, discharged by the point
reflection.**  Both comparisons hold outright, so the paper's residue
`B - C + 2D + 2F` vanishes and `ex rawRusso = derivTerm`. -/
theorem collapse_of_reflection (B : Finset (Site d))
    (hR : ∀ y ∈ B, PRefl u K Ky w y) :
    ex w (rawRusso u K Ky B) = derivTerm w u K Ky B :=
  collapse_of_comparisons u K Ky B (ex_Bfun_eq_ex_Cfun B hR) (ex_Dfun_eq_neg_ex_Ffun B hR)

/-- The same, in the `collapse_iff_comparisons` form: the residue is zero. -/
theorem residue_eq_zero_of_reflection (B : Finset (Site d))
    (hR : ∀ y ∈ B, PRefl u K Ky w y) :
    ex w (Bfun u K Ky B) - ex w (Cfun u K Ky B)
      + 2 * ex w (Dfun u K Ky B) + 2 * ex w (Ffun u K Ky B) = 0 := by
  rw [ex_Bfun_eq_ex_Cfun B hR, ex_Dfun_eq_neg_ex_Ffun B hR]
  ring

end PercLib.CriticalLRP.I58

#print axioms PercLib.CriticalLRP.I58.rho_involutive
#print axioms PercLib.CriticalLRP.I58.dot_rho_sub
#print axioms PercLib.CriticalLRP.I58.q_rho_sub
#print axioms PercLib.CriticalLRP.I58.ex_comp_invol
#print axioms PercLib.CriticalLRP.I58.indOut_comp
#print axioms PercLib.CriticalLRP.I58.bSite_comp
#print axioms PercLib.CriticalLRP.I58.dSite_comp
#print axioms PercLib.CriticalLRP.I58.fSite_comp
#print axioms PercLib.CriticalLRP.I58.dSite_add_fSite_comp
#print axioms PercLib.CriticalLRP.I58.ex_site_D_add_F_eq_zero
#print axioms PercLib.CriticalLRP.I58.ex_Bfun_eq_ex_Cfun
#print axioms PercLib.CriticalLRP.I58.ex_Dfun_eq_neg_ex_Ffun
#print axioms PercLib.CriticalLRP.I58.collapse_of_reflection
#print axioms PercLib.CriticalLRP.I58.residue_eq_zero_of_reflection
