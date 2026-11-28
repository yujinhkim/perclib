/-
Ultramath swarm `smwzt36y2`, member `m6`, direction `d2`.

# The single-branch-vertex (`p = 6`, `k = 2`) shape

Hutchcroft, *Critical long-range percolation I*, arXiv:2508.18807v1, Lemma I.4.16 at
`p = 6`, `k = 2`:

  `E|K|^6 ≤ 945 (E|K|^2)^2 (E|K|)^5`.

Production's packet `Correlation/SixPoint/MixedK2/SixthMoment` reduces this to `HubK2.SixCover`,
a cover of the sixfold joint connection probability by `945` **two-hub** slot diagrams, and
`HubK2SixCounterexample.sixCover_false256` refutes that cover for *every* labelling family, at
the collapsed tuple `(0,3,3,3,3,3)` of the vertex-transitive six-cycle at `θ = 1/256`: the event
has probability at least `θ^3` there, while all `945` two-hub slots together are `O(θ^6)`.

The two-hub slot is not the shape that the source's `k = 2` regrouping produces.  At `p = 4`,
`k = 2` the *landed unconditional* theorem `FivePoint.fourth_moment_mixed_k2_le` uses a
**single** branch vertex `c` carrying both joint pairs and the residual two-point links
(`FivePoint.starK2 = jointP i₀ i₁ c * (tau i₂ c * jointP i₃ i₄ c)`).  The `p = 6`
analogue is `hubOne` below: one branch vertex, two joint pairs, and two residual two-point
links, one of which is the link to the root `o`.

This is a computational candidate, not a certified source decomposition. The new
`SixCoverOne` premise is explicit and unproved, and the root-first degenerate tuple is
not decided by this file. Its useful mathematical content is the exact leaf/branch-sum
evaluation, conditional assembly and fully collapsed algebra below:

* its exact leaf-and-branch sum is `(E|K|^2)^2 (E|K|)^3` (`tsum_slotOne_six`), i.e. *two*
  susceptibility powers below the `(E|K|^2)^2 (E|K|)^5` that the moment bound allows, whereas
  the two-hub shape reaches only `(E|K|^2)^2 (E|K|)^4`
  (`tsum_slotK2Six_six` in production);
* the branch sum is finite only because of the root link, which is exactly the structure of the
  landed `p = 4` shape, and it stays finite without any non-degeneracy hypothesis;
* at the *fully collapsed* tuple `(x,x,x,x,x,x)`, where all six terminals coincide and the root
  is not among them, one term of the single-branch slot is already `tau π o x`, the event
  probability itself (section 5 below).  The two-hub slot is only `(tau π o x)^2` there, so the
  fully collapsed tuple is a real obstruction for the two-hub family and none for this one.

Scope warning, stated here rather than discovered later: production's refutation
`sixCover_false256` uses the tuple `(0,3,3,3,3,3)` whose *first leaf is the root*, not the fully
collapsed tuple.  Section 5 proves the fully collapsed case only.  At `(0,3,3,3,3,3)` one slot of
every diagram has to carry the root as a leaf, and the root link contributes a second `tau 0 3`
factor; with the branch vertex at a neighbour-class vertex `c` the five `3`-leaves contribute
exponent `0`, so a single-branch slot is expected to be of order `theta^6` against an event of
order `theta^3`.  That counting is **not** formalized here (it needs the cyclic-distance exponent
bookkeeping of `tau_le_gen`/`jointP_le_gen` plus an allocation case split), so no refutation of
`SixCoverOne` at `(0,3,3,3,3,3)` is claimed.  The reader should assume the single-branch family
probably fails there, exactly as the two-hub family does.

Nothing here asserts the cover: `SixCoverOne` is retained as an explicit hypothesis, exactly as
`SixCover` is in production.  What is proved here is (i) the exact evaluation of the shape, (ii)
the sharp-constant `945` assembly from a cover by this shape, both abstractly and at the literal
cutoff law of `SourceModelData`, and (iii) the immunity of the collapsed tuple.
-/
module

public import PercLib.CriticalLRP.Correlation.SixPoint.MixedK2.SixthMoment.Model
public import PercLib.CriticalLRP.Correlation.SixPoint.MixedK2.SixthMoment.Obstruction
public import PercLib.CriticalLRP.Analysis.SecondMomentCase2.Source.Defs

/-! ## 1. The shape, its slot diagram, and its cover -/

@[expose] public section

noncomputable section

open Set MeasureTheory
open scoped ENNReal NNReal BigOperators
open PercLib.Percolation.Bond
open PercLib.Probability

namespace PercLib.CriticalLRP.TreeExpansion.HubK2

open PercLib.CriticalLRP.TreeExpansion.FivePoint

variable {V : Type*}

/-- **Single-branch-vertex `p = 6`, `k = 2` integrand.**  One branch vertex `c` carrying two
joint pairs `a b` and `d e` (each summing to the native second moment `E|K|^2` at `c`), the
residual two-point links `f` and `g`, and the link to the root `o`.  This is the `p = 6`
companion of the landed `FivePoint.starK2`. -/
noncomputable def hubOne (π : Sym2 V → unitInterval) (o a b d e f g c : V) : ℝ≥0∞ :=
  (jointP π a b c * jointP π d e c) * ((tau π f c * tau π g c) * tau π o c)

/-- **The `p = 6` single-branch integrand is the landed `p = 4`, `k = 2` comb integrand
`FivePoint.starK2` on five of its slots, times the two extra two-point links.**  This records
that the shape is not a new invention: it is the shape of the unconditional `p = 4` theorem with
the two extra terminals of `p = 6` attached as two-point links, one of them to the root. -/
theorem hubOne_eq_starK2 (π : Sym2 V → unitInterval) (o a b d e f g c : V) :
    hubOne π o a b d e f g c = starK2 π a b f d e c * (tau π g c * tau π o c) := by
  simp only [hubOne, starK2]
  ring

/-- **The single-branch-vertex slot diagram.**  Only the branch vertex `c` is summed; the six
free leaves are read through the labelling `σ`.  `tsum_slotOne` shows the leaf sum does not
depend on `σ`, so the event side may choose its own labelling family. -/
noncomputable def slotOne (π : Sym2 V → unitInterval) (σ : Equiv.Perm (Fin 6)) (o : V)
    (L : Fin 6 → V) : ℝ≥0∞ :=
  ∑' c, hubOne π o (L (σ 0)) (L (σ 1)) (L (σ 2)) (L (σ 3)) (L (σ 4)) (L (σ 5)) c

/-- **The `p = 6`, `k = 2` cover by single-branch-vertex diagrams.**

For every six-tuple of terminals, the probability that the root is connected to all of them is at
most the sum of the `945 = (2 * 6 - 3)!!` labelled single-branch diagrams.  This is the
deterministic union bound of the source's proof of Lemma I.4.16 followed by the BK inequality; it
is retained as an explicit hypothesis here, exactly as `SixCover` is in the two-hub packet. -/
def SixCoverOne (π : Sym2 V → unitInterval) (o : V) (pat : Fin 945 → Equiv.Perm (Fin 6)) :
    Prop :=
  ∀ y z w q r s : V,
    law π (sixConnSet o y z w q r s) ≤
      ∑' t : Fin 945, slotOne π (pat t) o ![y, z, w, q, r, s]

/-! ## 2. Exact evaluation of the shape -/

/-- **Leaf factorization at a fixed branch vertex.**  With the branch vertex held fixed, the six
free leaves separate into two joint double sums, two residual two-point sums and the root link. -/
theorem hubOne_tsum [Countable V] [AddCommGroup V] (π : Sym2 V → unitInterval) (o c : V) :
    (∑' a, ∑' b, ∑' d, ∑' e, ∑' f, ∑' g, hubOne π o a b d e f g c)
      = secondMoment π c * (secondMoment π c *
          (((∑' f, tau π f c) * (∑' g, tau π g c)) * tau π o c)) := by
  have hshape : (∑' a, ∑' b, ∑' d, ∑' e, ∑' f, ∑' g, hubOne π o a b d e f g c)
      = ∑' a, ∑' b, ∑' d, ∑' e, ∑' f, ∑' g,
          jointP π a b c * jointP π d e c * tau π f c * (tau π g c * tau π o c) :=
    tsum_congr fun a => tsum_congr fun b => tsum_congr fun d => tsum_congr fun e =>
      tsum_congr fun f => tsum_congr fun g => by simp only [hubOne]; ring
  rw [hshape, tsum_six_split (A := fun a b => jointP π a b c)
    (B := fun d e => jointP π d e c) (C := fun f => tau π f c)
    (D := fun g => tau π g c * tau π o c)]
  rw [← secondMoment_eq π c, ENNReal.tsum_mul_right]
  ring

/-- **Leaf factorization at a fixed branch vertex, on `Fin 6 → V`.** -/
theorem hubOne_tsum_fin [Countable V] [AddCommGroup V] (π : Sym2 V → unitInterval) (o c : V) :
    (∑' L : Fin 6 → V, hubOne π o (L 0) (L 1) (L 2) (L 3) (L 4) (L 5) c)
      = secondMoment π c * (secondMoment π c *
          (((∑' f, tau π f c) * (∑' g, tau π g c)) * tau π o c)) := by
  rw [tsum_fin6 (G := fun L => hubOne π o (L 0) (L 1) (L 2) (L 3) (L 4) (L 5) c)]
  exact hubOne_tsum π o c

/-- **Single-branch-vertex evaluation at `p = 6`.**  Summing the six free leaves and the branch
vertex gives the square of the native second moment times the cube of the susceptibility. -/
theorem tsum_hubOne [Countable V] [AddCommGroup V] (π : Sym2 V → unitInterval)
    (hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y)) (o : V) :
    (∑' c, ∑' L : Fin 6 → V, hubOne π o (L 0) (L 1) (L 2) (L 3) (L 4) (L 5) c)
      = secondMoment π o ^ 2 * (∑' x, tau π o x) ^ 3 := by
  have hS : ∀ c : V, secondMoment π c = secondMoment π o := fun c =>
    (secondMoment_root_independent π hq c).trans
      (secondMoment_root_independent π hq o).symm
  have hT : ∀ c : V, (∑' f, tau π f c) = ∑' x, tau π o x := fun c =>
    (tau_col π hq c).trans (tau_row π hq o).symm
  calc (∑' c, ∑' L : Fin 6 → V, hubOne π o (L 0) (L 1) (L 2) (L 3) (L 4) (L 5) c)
      = ∑' c, secondMoment π c * (secondMoment π c *
          (((∑' f, tau π f c) * (∑' g, tau π g c)) * tau π o c)) :=
        tsum_congr fun c => hubOne_tsum_fin π o c
    _ = ∑' c, secondMoment π o * (secondMoment π o *
          (((∑' x, tau π o x) * (∑' x, tau π o x)) * tau π o c)) :=
        tsum_congr fun c => by rw [hS c, hT c]
    _ = secondMoment π o ^ 2 * (∑' x, tau π o x) ^ 3 := by
        have hfac : ∀ c : V,
            secondMoment π o * (secondMoment π o *
              (((∑' x, tau π o x) * (∑' x, tau π o x)) * tau π o c))
              = (secondMoment π o * secondMoment π o * (∑' x, tau π o x)
                  * (∑' x, tau π o x)) * tau π o c := by
          intro c; ring
        rw [tsum_congr hfac, ENNReal.tsum_mul_left]
        ring

/-- **Pattern independence for the single-branch family.**  Every labelling of the six leaf slots
gives the same value, so the event side is free to choose its own family. -/
theorem tsum_slotOne [Countable V] [AddCommGroup V] (π : Sym2 V → unitInterval)
    (hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y)) (σ : Equiv.Perm (Fin 6)) (o : V) :
    (∑' L : Fin 6 → V, slotOne π σ o L)
      = secondMoment π o ^ 2 * (∑' x, tau π o x) ^ 3 := by
  have hperm : (∑' L : Fin 6 → V, slotOne π σ o L)
      = ∑' L : Fin 6 → V, slotOne π (Equiv.refl (Fin 6)) o L := by
    have h := tsum_fin6_perm σ (G := fun L => slotOne π (Equiv.refl (Fin 6)) o L)
    refine (tsum_congr fun L => ?_).trans h
    simp only [slotOne, Equiv.refl_apply]
  rw [hperm]
  have hswap : (∑' L : Fin 6 → V, slotOne π (Equiv.refl (Fin 6)) o L)
      = ∑' c, ∑' L : Fin 6 → V, hubOne π o (L 0) (L 1) (L 2) (L 3) (L 4) (L 5) c := by
    simp only [slotOne, Equiv.refl_apply]
    exact ENNReal.tsum_comm
  rw [hswap, tsum_hubOne π hq o]

/-- The six-nested-sum form used by the moment assembly. -/
theorem tsum_slotOne_six [Countable V] [AddCommGroup V] (π : Sym2 V → unitInterval)
    (hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y)) (σ : Equiv.Perm (Fin 6)) (o : V) :
    (∑' y, ∑' z, ∑' w, ∑' q, ∑' r, ∑' s, slotOne π σ o ![y, z, w, q, r, s])
      = secondMoment π o ^ 2 * (∑' x, tau π o x) ^ 3 := by
  rw [← tsum_fin6 (G := fun L => slotOne π σ o L)]
  exact tsum_slotOne π hq σ o

/-- **The single-branch mass has two susceptibility powers to spare.** -/
theorem tsum_slotOne_six_le [Countable V] [AddCommGroup V] (π : Sym2 V → unitInterval)
    (hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y)) (σ : Equiv.Perm (Fin 6)) (o : V) :
    (∑' y, ∑' z, ∑' w, ∑' q, ∑' r, ∑' s, slotOne π σ o ![y, z, w, q, r, s])
      ≤ secondMoment π o ^ 2 * (∑' x, tau π o x) ^ 5 := by
  rw [tsum_slotOne_six π hq σ o]
  exact mul_le_mul' le_rfl
    (pow_le_pow_right₀ (one_le_susceptibility π o) (by norm_num : 3 ≤ 5))

end PercLib.CriticalLRP.TreeExpansion.HubK2

/-! ## 3. The sharp-constant assembly from a single-branch cover -/

namespace PercLib.CriticalLRP.TreeExpansion.HubK2

open PercLib.CriticalLRP.TreeExpansion.FivePoint

variable {V : Type*}

/-- **`p = 6`, `k = 2` from a single-branch cover.**  A pointwise bound of the sixfold joint
connection probability by the `945` single-branch slot diagrams implies
`E|K|^6 ≤ 945 (E|K|^2)^2 (E|K|)^5`.

The only other inputs are the exact sixfold moment identity `lintegral_cardFun_six_eq`
(Tonelli) and the exact diagram evaluation `tsum_slotOne_six_le`, both proved. -/
theorem sixth_moment_of_sixCoverOne [Countable V] [AddCommGroup V]
    (π : Sym2 V → unitInterval) (o : V) (pat : Fin 945 → Equiv.Perm (Fin 6))
    (hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y))
    (hcover : SixCoverOne π o pat) : SixthMomentLe π o := by
  have hmass : ∀ t : Fin 945,
      (∑' y, ∑' z, ∑' w, ∑' q, ∑' r, ∑' s, slotOne π (pat t) o ![y, z, w, q, r, s])
        ≤ secondMoment π o ^ 2 * (∑' x, tau π o x) ^ 5 :=
    fun t => tsum_slotOne_six_le π hq (pat t) o
  have hmain :
      ∫⁻ ω, (PercLib.CriticalLRP.Percolation.cardFun (cluster ω o)) ^ 6 ∂(law π)
        ≤ 945 * (secondMoment π o ^ 2 * (∑' x, tau π o x) ^ 5) := by
    rw [PercLib.CriticalLRP.TreeExpansion.SixFold.lintegral_cardFun_six_eq π o]
    calc ∑' y, ∑' z, ∑' w, ∑' q, ∑' r, ∑' s,
          law π (conn o y ∩ conn o z ∩ conn o w ∩ conn o q ∩ conn o r ∩ conn o s)
        ≤ ∑' y, ∑' z, ∑' w, ∑' q, ∑' r, ∑' s, ∑' t : Fin 945,
            slotOne π (pat t) o ![y, z, w, q, r, s] :=
          ENNReal.tsum_le_tsum fun y => ENNReal.tsum_le_tsum fun z =>
            ENNReal.tsum_le_tsum fun w => ENNReal.tsum_le_tsum fun q =>
              ENNReal.tsum_le_tsum fun r => ENNReal.tsum_le_tsum fun s =>
                hcover y z w q r s
      _ = ∑' t : Fin 945, ∑' y, ∑' z, ∑' w, ∑' q, ∑' r, ∑' s,
            slotOne π (pat t) o ![y, z, w, q, r, s] :=
          tsum_six_fin945_swap (fun y z w q r s t => slotOne π (pat t) o ![y, z, w, q, r, s])
      _ ≤ ∑' _t : Fin 945, secondMoment π o ^ 2 * (∑' x, tau π o x) ^ 5 :=
          ENNReal.tsum_le_tsum hmass
      _ = 945 * (secondMoment π o ^ 2 * (∑' x, tau π o x) ^ 5) := tsum_fin945_const _
  simpa only [SixthMomentLe, secondMoment, firstMoment, ← firstMoment_eq, mul_assoc]
    using hmain

end PercLib.CriticalLRP.TreeExpansion.HubK2

/-! ## 4. The assembly at the literal cutoff law -/

namespace PercLib.CriticalLRP.SixthMoment

open PercLib.CriticalLRP.Orchestration
open PercLib.CriticalLRP.TreeExpansion.HubK2

variable (M : SourceModelData)

/-- **`CaseTwo.SixthMomentMixed M` from a single-branch `945`-shape cover.**

The single hypothesis is `HubK2.SixCoverOne` at every radius.  Everything else — the sixfold
moment identity, the shape evaluation, the exponent bookkeeping and the passage to the cutoff
law — is proved.  Compare production's `sixthMomentMixed_of_sixCover`, which has the refuted
two-hub cover `SixCover` in the same place. -/
theorem sixthMomentMixed_of_sixCoverOne (pat : Fin 945 → Equiv.Perm (Fin 6))
    (hcover : ∀ (r : ℝ), 0 ≤ r → SixCoverOne (M.cutProb r) (0 : M.V) pat) :
    PercLib.CriticalLRP.CaseTwo.SixthMomentMixed M := by
  intro r hr
  have habs : SixthMomentLe (M.cutProb r) (0 : M.V) :=
    sixth_moment_of_sixCoverOne (M.cutProb r) (0 : M.V) pat (cutProb_translate M r)
      (hcover r hr)
  rw [M.cutMoment_eq_lintegral_cardFun r 6 0, M.cutMoment_eq_lintegral_cardFun r 2 0,
    M.cutMoment_eq_lintegral_cardFun r 1 0]
  simp only [pow_one]
  exact habs

end PercLib.CriticalLRP.SixthMoment

/-! ## 5. The fully collapsed tuple

At the *fully* collapsed tuple `(x,x,x,x,x,x)` — all six terminals equal, root not among them —
one term of the branch sum already dominates the event, because a jointly-summed pair with both
endpoints equal to the branch vertex contributes `tau π x x = 1` rather than a small power, and
the branch sum at `c = x` reduces to the root link `tau π o x`.

This is *not* production's refuting tuple: `sixCover_false256` uses `(0,3,3,3,3,3)`, whose first
leaf is the root, and at that tuple one slot has to carry the root as a leaf, so the same argument
only gives `(tau π o x)^2`.  Nothing in this section decides the cover at `(0,3,3,3,3,3)`. -/

namespace PercLib.CriticalLRP.TreeExpansion.HubK2

open PercLib.CriticalLRP.TreeExpansion.FivePoint

variable {V : Type*}

/-- The collapsed six-tuple as a constant vector. -/
theorem sixVec_const (x : V) : ![x, x, x, x, x, x] = fun _ : Fin 6 => x := by
  funext i
  fin_cases i <;> rfl

/-- At a collapsed tuple the sixfold joint connection event is the single connection event. -/
theorem sixConnSet_collapsed [Countable V] (o x : V) :
    sixConnSet (V := V) o x x x x x x = conn o x := by
  simp only [sixConnSet, Set.inter_self]

/-- A joint pair with both endpoints at its centre is a single two-point event. -/
theorem jointP_self [Countable V] (π : Sym2 V → unitInterval) (a c : V) :
    jointP π a a c = tau π a c := by
  simp only [jointP, tau, Set.inter_self]

/-- **The single-branch slot at a collapsed tuple.**  Every leaf equals `x`, so the slot is the
branch sum of `(tau π x c)^4 * tau π o x`. -/
theorem slotOne_collapsed [Countable V] (π : Sym2 V → unitInterval) (σ : Equiv.Perm (Fin 6))
    (o x : V) :
    slotOne π σ o ![x, x, x, x, x, x]
      = ∑' c, (tau π x c * tau π x c) * ((tau π x c * tau π x c) * tau π o c) := by
  rw [sixVec_const]
  refine tsum_congr fun c => ?_
  simp only [hubOne, jointP_self]

/-- **A single term of the branch sum already dominates the collapsed event.**  The term `c = x`
of the branch sum is `tau π o x` because `tau π x x = 1`. -/
theorem tau_le_slotOne_collapsed [Countable V] (π : Sym2 V → unitInterval)
    (σ : Equiv.Perm (Fin 6)) (o x : V) :
    tau π o x ≤ slotOne π σ o ![x, x, x, x, x, x] := by
  rw [slotOne_collapsed]
  have hxx : tau π x x = 1 := by
    rw [tau, conn_self, measure_univ]
  have hsingle : (tau π x x * tau π x x) * ((tau π x x * tau π x x) * tau π o x)
      = tau π o x := by
    rw [hxx]; simp
  refine hsingle ▸ ENNReal.le_tsum
    (f := fun c => (tau π x c * tau π x c) * ((tau π x c * tau π x c) * tau π o c)) x

/-- **The fully collapsed tuple satisfies the single-branch cover for every labelling family.** -/
theorem sixCoverOne_collapsed [Countable V] (π : Sym2 V → unitInterval) (o x : V)
    (pat : Fin 945 → Equiv.Perm (Fin 6)) :
    law π (sixConnSet o x x x x x x) ≤
      ∑' t : Fin 945, slotOne π (pat t) o ![x, x, x, x, x, x] := by
  rw [sixConnSet_collapsed]
  refine (tau_le_slotOne_collapsed π (pat 0) o x).trans (ENNReal.le_tsum
    (f := fun t : Fin 945 => slotOne π (pat t) o ![x, x, x, x, x, x]) 0)

end PercLib.CriticalLRP.TreeExpansion.HubK2

/-! ## 6. The same tuple in the packet's own counterexample model -/

namespace PercLib.CriticalLRP.TreeExpansion.HubK2

open PercLib.CriticalLRP.TreeExpansion.FivePoint

open PercLib.CriticalLRP.Counterexample.Cycle6
open PercLib.CriticalLRP.TreeExpansion.HubK2SixCounterexample

/-- **At the fully collapsed tuple `(3,3,3,3,3,3)` of the six-cycle at `θ = 1/256`, the
single-branch slot already dominates the sixfold event**, with no hypothesis.  With the root
as the first leaf — production's refuting tuple `(0,3,3,3,3,3)` — one slot has to carry the
root as a leaf and the root link adds a second `tau 0 3` factor, so this argument does not
extend: the cover at that tuple is not addressed anywhere in this file. -/
theorem slotOne_counterexample_collapsed (σ : Equiv.Perm (Fin 6)) :
    law (stepProfile theta256) (sixConnSet (0 : ZMod 6) 3 3 3 3 3 3)
      ≤ slotOne (stepProfile theta256) σ 0 ![3, 3, 3, 3, 3, 3] := by
  rw [sixConnSet_collapsed]
  exact tau_le_slotOne_collapsed _ σ 0 3

end PercLib.CriticalLRP.TreeExpansion.HubK2

namespace PercLib.CriticalLRP.SixthMoment

open Filter Topology
open PercLib.CriticalLRP.Orchestration
open PercLib.CriticalLRP.TreeExpansion.HubK2

variable (M : SourceModelData)

/-- **Case 2 of Proposition I.4.15 with a single-branch `945`-shape cover as the only remaining
input.**

Combining `sixthMomentMixed_of_sixCoverOne` with production's
`CaseTwo.p2ExclError_tendsto_zero_of_caseTwo'` (which already discharges universal tightness via
Corollary I.2.5): under `d = 3α`, (Hydro), the first-moment asymptotic `hP` and eventual
finiteness of the second cutoff moment, the excluded-error term `E_{2,r}` of (I.4.14) vanishes.

This is *not* an unconditional model theorem: `SixCoverOne` is retained explicitly, and it is not
claimed true.  It is strictly better placed than the two-hub cover at the fully collapsed tuple
(`sixCoverOne_collapsed`), where the two-hub family fails. -/
theorem p2ExclError_tendsto_zero_of_sixCoverOne (pat : Fin 945 → Equiv.Perm (Fin 6))
    (hcover : ∀ (r : ℝ), 0 ≤ r → SixCoverOne (M.cutProb r) (0 : M.V) pat)
    (hd : (M.d : ℝ) = 3 * M.α)
    (hκ : 0 < M.α / (M.betaCrit : ℝ))
    (hP : Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal
      / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) atTop (𝓝 1))
    (hH : Hydro M)
    (h2 : ∀ᶠ r : ℝ in atTop, M.cutMoment 2 r ≠ ⊤) :
    Tendsto M.p2ExclError atTop (𝓝 0) := by
  refine PercLib.CriticalLRP.CaseTwo.p2ExclError_tendsto_zero_of_caseTwo' M hd hκ hP hH h2 ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with r hr
  exact sixthMomentMixed_of_sixCoverOne M pat hcover r hr

end PercLib.CriticalLRP.SixthMoment

/-! ## 7. Axiom audit -/

set_option linter.hashCommand false

#print axioms PercLib.CriticalLRP.TreeExpansion.HubK2.hubOne_eq_starK2
#print axioms PercLib.CriticalLRP.TreeExpansion.HubK2.hubOne_tsum
#print axioms PercLib.CriticalLRP.TreeExpansion.HubK2.tsum_hubOne
#print axioms PercLib.CriticalLRP.TreeExpansion.HubK2.tsum_slotOne
#print axioms PercLib.CriticalLRP.TreeExpansion.HubK2.tsum_slotOne_six
#print axioms PercLib.CriticalLRP.TreeExpansion.HubK2.tsum_slotOne_six_le
#print axioms PercLib.CriticalLRP.TreeExpansion.HubK2.sixth_moment_of_sixCoverOne
#print axioms PercLib.CriticalLRP.SixthMoment.sixthMomentMixed_of_sixCoverOne
#print axioms PercLib.CriticalLRP.SixthMoment.p2ExclError_tendsto_zero_of_sixCoverOne
#print axioms PercLib.CriticalLRP.TreeExpansion.HubK2.sixConnSet_collapsed
#print axioms PercLib.CriticalLRP.TreeExpansion.HubK2.slotOne_collapsed
#print axioms PercLib.CriticalLRP.TreeExpansion.HubK2.tau_le_slotOne_collapsed
#print axioms PercLib.CriticalLRP.TreeExpansion.HubK2.sixCoverOne_collapsed
#print axioms PercLib.CriticalLRP.TreeExpansion.HubK2.slotOne_counterexample_collapsed
