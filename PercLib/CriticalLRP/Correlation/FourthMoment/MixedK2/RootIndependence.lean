/-
Direction A of Ultramath swarm `smwpq441z`: root independence of the native second
cluster moment `E |K_v|²`, derived from the **full** translation invariance

  `hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y)`

of the edge profile.  No `h2` (second-moment finiteness) hypothesis is used or
needed: everything here is an identity between extended nonnegative integrals.

The reusable content is

* `lintegral_cardFun_pow_root_indep` : for **any** power `n`, a measure-preserving
  self-map `T` of `Config V` and a vertex map `e` with cluster covariance
  `cluster (T ω) (e v) = e '' cluster ω v`, the moment `∫⁻ |K_{e v}|^n` equals
  `∫⁻ |K_v|^n`.  (Generalises `Hvol.lintegral_cardFun_root_indep`, which is `n = 1`.)
* `secondMoment_translate`, `secondMoment_root_independent_of_hq` : the `n = 2` instance for
  the translation action on `law π`, with `hq` discharged.
* `tau_add_eq`, `tau_eq_root_sub` : translation invariance of the two-point function,
  i.e. the hypothesis `hinv` of the `p = 4`, `k = 1` theorem, derived from `hq`.
* `chi_root_independent`, `joinSum_root_independent` : the same for the first moment
  and for the joint star-pair sum `∑_a ∑_c law (conn x c ∩ conn a c)`.

No `sorry`, no `admit`, no `native_decide`, no custom axioms.
-/
module

public import PercLib.CriticalLRP.Correlation.FourthMoment.MixedK2.Defs
public import PercLib.Percolation.Bond.Transport
public import PercLib.Percolation.Bond.Ergodic
public import PercLib.CriticalLRP.Correlation.HvolPermutation

open MeasureTheory Set
open scoped ENNReal
open PercLib.Percolation.Bond

@[expose] public section

namespace PercLib.CriticalLRP.TreeExpansion.FivePoint

variable {V : Type*}

/-- The native first cluster moment is the susceptibility. -/
theorem firstMoment_eq_chi (π : Sym2 V → unitInterval) (v : V) :
    firstMoment π v = chi π v := by
  rw [firstMoment, chi]
  exact lintegral_congr fun ω => PercLib.CriticalLRP.Percolation.cardFun_eq_encard _

set_option linter.unusedSectionVars false

/-! ## 1. Generic moment invariance under a measure-preserving relabelling -/

/-- **Moment invariance at every power.**  If `T` preserves `μ`, `e` is injective, and
clusters are carried along `(T, e)`, then `∫⁻ |K_{e v}|^n = ∫⁻ |K_v|^n`.

The proof is the `n = 1` argument of `Hvol.lintegral_cardFun_root_indep` with
`cardFun` replaced by its `n`-th power; measurability of the power is
`Hrest.measurable_cardFun_cluster_canonical` followed by `Measurable.pow`. -/
theorem lintegral_cardFun_pow_root_indep [Countable V] (μ : Measure (Config V))
    {T : Config V → Config V} (hT : Measurable T) (hinv : μ.map T = μ)
    {e : V → V} (he : Function.Injective e)
    (hcov : ∀ ω v, cluster (T ω) (e v) = e '' cluster ω v) (n : ℕ) (v : V) :
    ∫⁻ ω, (PercLib.CriticalLRP.Percolation.cardFun (cluster ω (e v))) ^ n ∂μ
      = ∫⁻ ω, (PercLib.CriticalLRP.Percolation.cardFun (cluster ω v)) ^ n ∂μ := by
  have hmeas : Measurable fun ω => (PercLib.CriticalLRP.Percolation.cardFun
      (cluster ω (e v))) ^ n :=
    (Hrest.measurable_cardFun_cluster_canonical (e v)).pow_const n
  have h1 : ∫⁻ ω, (PercLib.CriticalLRP.Percolation.cardFun (cluster (T ω) (e v))) ^ n ∂μ
      = ∫⁻ ω, (PercLib.CriticalLRP.Percolation.cardFun (cluster ω (e v))) ^ n ∂μ :=
    Hvol.lintegral_comp_of_map_eq hT hinv hmeas
  rw [← h1]
  refine lintegral_congr fun ω => ?_
  rw [hcov ω v, Hvol.cardFun_image_of_injective he]

/-- The `n = 1` instance, matching `Hvol.lintegral_cardFun_root_indep` (kept here so that
the `p = 4`, `k = 2` files do not have to import the whole translation theory). -/
theorem lintegral_cardFun_root_indep' [Countable V] (μ : Measure (Config V))
    {T : Config V → Config V} (hT : Measurable T) (hinv : μ.map T = μ)
    {e : V → V} (he : Function.Injective e)
    (hcov : ∀ ω v, cluster (T ω) (e v) = e '' cluster ω v) (v : V) :
    ∫⁻ ω, PercLib.CriticalLRP.Percolation.cardFun (cluster ω (e v)) ∂μ
      = ∫⁻ ω, PercLib.CriticalLRP.Percolation.cardFun (cluster ω v) ∂μ :=
  by simpa using lintegral_cardFun_pow_root_indep μ hT hinv he hcov 1 v

/-- The `n = 2` instance: the second cluster moment is invariant. -/
theorem lintegral_cardFun_sq_root_indep [Countable V] (μ : Measure (Config V))
    {T : Config V → Config V} (hT : Measurable T) (hinv : μ.map T = μ)
    {e : V → V} (he : Function.Injective e)
    (hcov : ∀ ω v, cluster (T ω) (e v) = e '' cluster ω v) (v : V) :
    ∫⁻ ω, (PercLib.CriticalLRP.Percolation.cardFun (cluster ω (e v))) ^ 2 ∂μ
      = ∫⁻ ω, (PercLib.CriticalLRP.Percolation.cardFun (cluster ω v)) ^ 2 ∂μ :=
  lintegral_cardFun_pow_root_indep μ hT hinv he hcov 2 v

/-! ## 2. The translation action on `Config V`, for a translation-invariant profile -/

variable [Countable V] [AddCommGroup V]

/-- Cluster covariance under the translation `ω ↦ Sym2.map (· + a) '' ω`, obtained from
`PercLib.Percolation.Bond.cluster_image` with the vertex permutation `Equiv.addRight a`. -/
theorem cluster_image_add (a : V) (ω : Config V) (v : V) :
    cluster (Sym2.map (· + a) '' ω) (v + a) = (fun u => u + a) '' cluster ω v :=
  cluster_image (Equiv.addRight a) ω v

/-- **Root independence of the `n`-th cluster moment** for the translation-invariant law
`law π`: translating the root by `a` does not change `E |K|^n`. -/
theorem lintegral_cardFun_pow_translate (π : Sym2 V → unitInterval)
    (hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y)) (n : ℕ) (x a : V) :
    ∫⁻ ω, (PercLib.CriticalLRP.Percolation.cardFun (cluster ω (x + a))) ^ n ∂(law π)
      = ∫⁻ ω, (PercLib.CriticalLRP.Percolation.cardFun (cluster ω x)) ^ n ∂(law π) :=
  lintegral_cardFun_pow_root_indep (law π) (measurable_image_sym2Map_add a)
    (measurePreserving_image_sym2Map_add π hq a).map_eq (e := fun u => u + a)
    (fun _ _ h => by simpa using h) (cluster_image_add a) n x

/-- **The second moment at a translated root.** -/
theorem secondMoment_translate (π : Sym2 V → unitInterval)
    (hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y)) (x a : V) :
    secondMoment π (x + a) = secondMoment π x :=
  lintegral_cardFun_pow_translate π hq 2 x a

/-- **`E |K_v|²` does not depend on the root**, from full translation invariance of `π`
and nothing else.  This is the missing input (in place of a bare `h2` or a
second-moment root-invariance premise) of the `p = 4`, `k = 2` assembly. -/
theorem secondMoment_root_independent_of_hq (π : Sym2 V → unitInterval)
    (hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y)) (x y : V) :
    secondMoment π x = secondMoment π y := by
  have h := secondMoment_translate π hq x (y - x)
  rw [add_sub_cancel] at h
  exact h.symm

/-- **The first moment at a translated root.** -/
theorem firstMoment_translate (π : Sym2 V → unitInterval)
    (hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y)) (x a : V) :
    firstMoment π (x + a) = firstMoment π x :=
  by simpa [firstMoment] using lintegral_cardFun_pow_translate π hq 1 x a

/-- **`E |K_v|` does not depend on the root** (`hvol`), in the `firstMoment` shape. -/
theorem firstMoment_root_independent (π : Sym2 V → unitInterval)
    (hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y)) (x y : V) :
    firstMoment π x = firstMoment π y := by
  have h := firstMoment_translate π hq x (y - x)
  rw [add_sub_cancel] at h
  exact h.symm

/-- **`hvol` in the susceptibility shape.** -/
theorem chi_root_independent (π : Sym2 V → unitInterval)
    (hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y)) (x y : V) :
    chi π x = chi π y := by
  rw [← firstMoment_eq_chi, ← firstMoment_eq_chi]
  exact firstMoment_root_independent π hq x y

/-! ## 3. Translation invariance of the two-point function (the `hinv` hypothesis) -/

/-- **`tau` is invariant under a common translation of its two arguments.** -/
theorem tau_add_eq (π : Sym2 V → unitInterval)
    (hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y)) (x y g : V) :
    tau π (x + g) (y + g) = tau π x y := by
  have h := tau_apply_eq_of_map_law_eq (p := π) (Equiv.addRight g)
    (measurePreserving_image_sym2Map_add π hq g).map_eq x y
  simpa using h

/-- **The `hinv` hypothesis of the `p = 4`, `k = 1` theorem, derived from `hq`.**
`tau π a b` depends only on the difference `b - a`. -/
theorem tau_eq_root_sub (π : Sym2 V → unitInterval)
    (hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y)) (a b : V) :
    tau π a b = tau π 0 (b - a) := by
  have h := tau_add_eq π hq 0 (b - a) a
  simpa using h

/-- Root-independence form of `tau_eq_root_sub`. -/
theorem tau_root_independent (π : Sym2 V → unitInterval)
    (hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y)) (a b c d : V) :
    tau π a b = tau π c d ↔ tau π 0 (b - a) = tau π 0 (d - c) := by
  rw [tau_eq_root_sub π hq a b, tau_eq_root_sub π hq c d]

/-- **Two-point row and column sums are root-free.**  Every `tau` row sum equals
`E |K_0| = chi π 0`. -/
theorem tsum_tau_row_eq_chi (π : Sym2 V → unitInterval)
    (hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y)) (a : V) :
    (∑' b, tau π a b) = chi π 0 := by
  rw [show (∑' b, tau π a b) = ∑' b, tau π 0 (b - a) from
    tsum_congr fun b => tau_eq_root_sub π hq a b]
  have hre : (∑' b : V, tau π 0 (b - a)) = ∑' b, tau π 0 b := by
    simpa only [Equiv.subRight_apply] using
      (Equiv.tsum_eq (Equiv.subRight a) (fun b : V => tau π 0 b))
  rw [hre]
  exact (chi_eq_tsum_tau π 0).symm

/-! ## 4. The joint star-pair sum is root-free -/

/-- **Root independence of the joint star-pair double sum**
`Z_x = ∑_a ∑_c law π (conn x c ∩ conn a c)`, which is exactly `E |K_x|²`. -/
theorem joinSum_root_independent (π : Sym2 V → unitInterval)
    (hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y)) (x y : V) :
    (∑' a, ∑' c, law π (conn x c ∩ conn a c))
      = ∑' a, ∑' c, law π (conn y c ∩ conn a c) := by
  rw [joinSum_eq_cardFun_sq π x, joinSum_eq_cardFun_sq π y]
  exact secondMoment_root_independent_of_hq π hq x y

/-- **The first moment is the sum of the two-point function.**  This is the conversion
between `firstMoment` and `tau` that the slot summation needs when it evaluates the factor
`∑_b τ(b,v)`. -/
theorem firstMoment_eq_tsum_tau (π : Sym2 V → unitInterval) (v : V) :
    firstMoment π v = ∑' x, tau π v x := by
  rw [firstMoment_eq_chi, chi_eq_tsum_tau]

/-- **Column sums of `tau` are root-free.**  Every column sum equals `E |K_0| = chi π 0`.
For the `p = 4`, `k = 2` assembly this is the statement `∑_b τ(b,v) = χ`. -/
theorem tsum_tau_col_eq_chi (π : Sym2 V → unitInterval)
    (hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y)) (b : V) :
    (∑' a, tau π a b) = chi π 0 := by
  rw [show (∑' a, tau π a b) = ∑' a, tau π b a from
    tsum_congr fun a => tau_comm π a b]
  exact tsum_tau_row_eq_chi π hq b

/-! ## 5. The two atomic double-star moment identities

Both are needed by the `p = 4`, `k = 2` slot summation: the *shallow* joint event is
`conn root c ∩ conn a c` (root first, common centre `c` last) and the *deep* joint event is
`conn c v ∩ conn d v` (common centre `v` last, both leaves first). -/

/-- **Shallow double star.**  `∑_a ∑_c law (conn root c ∩ conn a c) = E |K_root|²`. -/
theorem shallowDoubleSum_eq_secondMoment (π : Sym2 V → unitInterval) (root : V) :
    (∑' a, ∑' c, law π (conn root c ∩ conn a c)) = secondMoment π root :=
  joinSum_eq_cardFun_sq π root

/-- **Deep double star.**  `∑_c ∑_d law (conn c v ∩ conn d v) = E |K_v|²`.

The two difference from `shallowDoubleSum_eq_secondMoment` is only the order of the two
vertices in each `conn`: the *centre* `v` is the second argument, so that both remaining
leaves `c, d` are summed.  The identification is `lintegral_cardFun_sq_eq` composed with
`conn_symm` at both vertices. -/
theorem deepDoubleSum_eq_secondMoment (π : Sym2 V → unitInterval) (v : V) :
    (∑' c, ∑' d, law π (conn c v ∩ conn d v)) = secondMoment π v := by
  have h : (∑' c, ∑' d, law π (conn c v ∩ conn d v))
      = ∑' c, ∑' d, law π (conn v c ∩ conn v d) :=
    tsum_congr fun c => tsum_congr fun d => by rw [conn_symm c v, conn_symm d v]
  rw [h, secondMoment]
  exact (lintegral_cardFun_sq_eq π v).symm

/-- **The deep double star is root-free** (this is what the deep joint event of the
`p = 4`, `k = 2` slot diagram contributes, at any centre). -/
theorem deepDoubleSum_root_independent (π : Sym2 V → unitInterval)
    (hq : ∀ x y g : V, π s(x + g, y + g) = π s(x, y)) (x y : V) :
    (∑' c, ∑' d, law π (conn c x ∩ conn d x))
      = ∑' c, ∑' d, law π (conn c y ∩ conn d y) := by
  rw [deepDoubleSum_eq_secondMoment, deepDoubleSum_eq_secondMoment]
  exact secondMoment_root_independent_of_hq π hq x y

#print axioms PercLib.CriticalLRP.TreeExpansion.FivePoint.lintegral_cardFun_pow_root_indep
#print axioms PercLib.CriticalLRP.TreeExpansion.FivePoint.secondMoment_root_independent_of_hq
#print axioms PercLib.CriticalLRP.TreeExpansion.FivePoint.chi_root_independent
#print axioms PercLib.CriticalLRP.TreeExpansion.FivePoint.tau_eq_root_sub
#print axioms PercLib.CriticalLRP.TreeExpansion.FivePoint.tsum_tau_row_eq_chi
#print axioms PercLib.CriticalLRP.TreeExpansion.FivePoint.joinSum_root_independent
#print axioms PercLib.CriticalLRP.TreeExpansion.FivePoint.firstMoment_eq_tsum_tau
#print axioms PercLib.CriticalLRP.TreeExpansion.FivePoint.tsum_tau_col_eq_chi
#print axioms PercLib.CriticalLRP.TreeExpansion.FivePoint.deepDoubleSum_eq_secondMoment
#print axioms PercLib.CriticalLRP.TreeExpansion.FivePoint.deepDoubleSum_root_independent

end PercLib.CriticalLRP.TreeExpansion.FivePoint
