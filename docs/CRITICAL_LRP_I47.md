# Continuation: Lemma I.4.7 covariance and finite-moment bounds

Source: supplied PDF, Lemma I.4.7 on page 36. This unit follows the completed
I.4.6 proof described in `docs/CRITICAL_LRP_CONTINUATION.md`. I.4.7 remains
PARTIAL in the coverage ledger; the reason is made precise below.

## Unconditional covariance in extended nonnegative reals

`VolumeMoments/ErrorBounds.lean` proves
`Hrest.joint_cardFun_sum_covariance` for a canonical independent-edge product
law. Let `A` be the common extended mean cluster volume at the root and at all
sites of a finite window `B`, let `J_y` be the full joint expectation of
`|K_x| |K_y|`, and let `C_y` be its connected-component expectation
`E[1(x ↔ y) |K_x|²]`. The theorem proves, entirely in `ℝ≥0∞`,

`B.card * A² ≤ ∑ y∈B J_y ≤ B.card * A² + ∑ y∈B C_y`.

There is no real subtraction and no finite-moment hypothesis in this theorem.
Consequently, it remains meaningful when the critical mean is infinite.

The proof uses:

- Harris–FKG, `A² ≤ J_y`, for the lower bound;
- two-cluster BK on the disconnected part `D_y`, `D_y ≤ A²`;
- cluster equality on `{x ↔ y}` and the exact decomposition `J_y = C_y + D_y`.

These are not replaced by an absolute per-site estimate with the wrong sign.
Finite-sum interchange (`lintegral_joint_cardFun_sum`) identifies the first sum
with the expectation of `|K_x| ∑_{y∈B}|K_y|`.
`connected_cardFun_sum_eq` and `lintegral_connected_cardFun_sum` identify the
second sum with the expectation of `|K_x|² #(B ∩ K_x)`, represented by a finite
`Finset.filter` cardinal.

`one_le_lintegral_cardFun` also proves that every expected cluster volume is at
least one, because the root is always in its own cluster.

## Real `cE1` bound when the denominator is finite

The paper's error is the existing definition

`cE1 A S T b = (b*A² - S + T) / (b*A²)`.

`VolumeMoments.cE1_bounds_of_covariance` proves the finite-denominator algebra:
if `0 < A`, `0 < b`, `b*A² ≤ S` and `S - b*A² ≤ T`, then

`0 ≤ cE1 A S T b ≤ T / (b*A²)`.

`Hrest.lemma_I_4_7_of_finite` applies this to the canonical product law. A
nonempty window, finite mean `A`, and finite aggregated connected moment imply
all other positivity and finiteness conditions. In particular, the upper
`ℝ≥0∞` covariance bound proves finiteness of the joint moment, so no separate
joint-finiteness premise is needed.

Model instantiations are proved:

- `Hvol.lemma_I_4_7_shift_of_finite`: stationary edge probabilities on `Z^d`,
  with equal mean supplied by `Hvol.hvol_cardFun`;
- `Hvol.lemma_I_4_7_latticeLongRange_of_finite`: the *uncut* stationary
  `latticeLongRangeMeasure`, an auxiliary instance using its
  translation-invariant kernel and the canonical `edgeExhaustion`. It is not
  the source's range-truncated `E_{β,r}` model and should not be confused with
  the cutoff export below.
- `Hvol.lemma_I_4_7_cutoff_of_finite` and
  `Hvol.lemma_I_4_7_cutoff_of_secondMoment`: the intended `P_{β,r}` from
  Definition I.1.5, instantiated at `CutoffKernel.cutoffSymKernel`. Translation
  invariance and edge probability bounds are discharged internally.

`Hrest.MomentFiniteness` proves `|K| ≤ |K|²`, finiteness of the first moment
from the second, and finiteness of the connected-window moment from the second
using `|K ∩ B| ≤ |B|`. Thus the intended cutoff theorem initially needed only
one finite premise: `E|K|² < ∞`. The newer countable-lattice tree bound proves
`E|K|² ≤ (E|K|)³` with explicit homogeneity, discharged by shift invariance.
The unrestricted tree-graph variant is not used: an exact rational enumeration
checks an inhomogeneous two-level star with first moment `8/5`, second moment
`121/20`, and `121/20 > (8/5)³ = 512/125`, so homogeneity is essential.

`Hvol.cutoffSecondMoment_ne_top_of_firstMoment` now derives the second-moment
premise from `E|K| < ∞`; `cutoffJointSecondMoment_ne_top_of_firstMoment`
furthermore gives finiteness of the joint window moment using the pointwise
pairwise-square comparison. Hence the remaining first-moment sine qua non is
**finite first moment via sharpness**, not a separately supplied second moment.
Independent review also checked the underlying per-site covariance against the
source and identified the need to instantiate `CutoffKernel` rather than only
the uncut law; the wrappers above address that model requirement while
preserving its remaining first-moment hypothesis.

These express `S` and `T` as the literal expectations above, not as uninterpreted
scalar parameters.

`VolumeMoments/SecondMomentFirstMoment.lean` adds transport-only wrappers: a
finite first moment gives a finite second moment at every root by shift
invariance, and `lemma_I_4_7_shift_of_firstMoment`,
`lemma_I_4_7_latticeLongRange_of_firstMoment`, and
`lemma_I_4_7_cutoff_of_firstMoment` remove redundant higher-moment inputs.
`lemma_I_4_11_of_firstMoment` removes only the joint-window premise `hJfin`;
it retains `hDfin`, which is a different averaged triangle-shaped finiteness
input, not a cluster moment. These wrappers preserve the original providers
and require the finite first moment. They do not supply sharpness, higher
moments, or either paper root theorem.

## Third-moment reduction used in (I.4.8)

`Hrest.connected_window_mul_sq_le` proves the pointwise estimate
`|K ∩ B| |K|² ≤ |K|³` for every finite window `B`.
`Hrest.cE1_le_three_mul_cube_div_of_finite` combines it with the exact finite
`cE1` bound and an explicitly supplied tree-graph estimate
`E|K|³ ≤ 3 A^5`. It concludes, for finite `A`,

`0 ≤ cE1 ≤ 3 A³ / B.card`.

This also proves the connected moment is finite from the third-moment estimate,
so that separate side condition disappears in this regime. The native
third-moment reduction in `CRITICAL_LRP_THIRD_MOMENT.md` is now unconditional:
`ThirdMoment/ArmDecomposition.lean` proves the three-shape binary-arm
construction for an arbitrary simple graph, including star and coincident-
terminal cases. `Native.third_moment_cutoff` instantiates the resulting bound
at the loop-safe source cutoff law. Thus the former `harm` premise is no longer
a model gap. `Hvol.cE1_le_three_mul_cube_div_cutoff` instantiates the consumer
directly: for a nonempty finite window, its sole moment premise is finite first
moment. Finite first moment via sharpness remains a separate gap for the
critical real-valued applications, and this does not complete I.4.9.

`Correlation/CutoffThirdMomentFinite.lean` finishes the corresponding conditional
third-moment transfer: finite first moment at the loop-safe cutoff implies
`E|K|³ ≤ 3(E|K|)⁵`, hence finite third moment. The source-profile specialization
in `Correlation/CutoffThirdMomentHighTemp.lean` proves the same conclusion when
`β M < 1`, for `M` the power-law profile mass at exponent `d+α`. It uses `J_r ≤ J`
and the existing finite first-moment bound directly, not an unproved cutoff
sharpness premise. Both results are only for `p = 3`: finiteness of all cutoff
moments, the critical-parameter finite-first-moment input, and the source roots
remain open. The `β = 0` specialization is compiled as a non-vacuity witness.
There is no assertion that every cutoff cluster belongs deterministically to a
finite ball; bounded-range percolation can still have infinite clusters.

`Analysis/ErrorFunctions.lean` supplies the small exact error-algebra steps needed
for `i.4.g9`: `isLogErrorFunction_neg`, the proof that a measurable term bounded
by `c / r` is logarithmically integrable and tends to zero, and subtraction of an
arbitrary logarithmic error. This says that if `E_{0,r} = q_r - δ_r`, with
`|q_r| ≤ c r⁻¹` and δ already a logarithmic error, then `E_{0,r}` is also a
logarithmic error. The source-specific product expansion and normalization used
to discharge the `q_r` bound remain separate work; the helper is not used as
completion of Lemma I.4.9 or of the whole `i.4.g9` modelling obligation. A
compiled `q = 0`, `δ(r) = r⁻¹` instantiation in
`.scratch/verified-gaps/ErrorFunctionWitness.lean` checks the exact case
`E(r) = -r⁻¹`. These declarations use only the three standard axioms.

## Windowed second moments and the finite third-moment example

`VolumeMoments/SecondMomentWindow.lean` now proves that finite second moment is
exactly a **uniform-in-window** bound. The lattice boxes are cofinal, the second
moment is the supremum of the moments of `|K ∩ B_n|`, and every individual
windowed moment is finite. This characterizes the remaining estimate; it does
not establish uniformity for the intended critical cutoff law.

`Percolation.cardFun_eq_encard` identifies the extended finite-subset cardinality
with `Set.encard` in `ℝ≥0∞`, for both finite and infinite clusters.
`Hrest.secondMoment_ne_top_of_thirdMoment` also reduces finite second moment to
finite third moment.

`TreeExpansion/SymmetricGroup/` proves translation invariance for the constant
complete-graph model on a finite abelian group and deduces
`E|K|³ ≤ 3 (E|K|)⁵`, including on the torus `(ZMod n)^d`. Its finite alignment
module identifies the finite tree-expansion graph and atoms with the native
complete bond graph. The newer `SymmetricGroup/Expectation/Basic.lean` then sums
those atoms to identify arbitrary finite real expectations with native
Lebesgue integrals, and identifies the native first, second and third cluster
moments. It proves the native second- and third-moment bounds for every
translation-invariant edge weight on a finite abelian group, including even
nonnegative kernels with `π(x,y) = 1 - exp (-(β J(y-x)))`.
These remain real non-vacuous native-model examples. They predate the general
infinite-native arm decomposition above and do not depend on it; no finite-volume
uniformity step is claimed.
Furthermore, `torus_cE1_le_three_mul_cube_div` discharges the entire
third-moment `cE1` consumer on a finite torus, including root independence and
finiteness of its first moment. It obtains `0 ≤ cE1 ≤ 3(E|K|)^3 / |B|` without
any remaining moment hypothesis. This is a non-vacuity witness for the
conditional consumer, not a source-theorem upgrade on the infinite lattice.

## Why the classification remains PARTIAL

At criticality the paper can have `E|K| = ∞`. A real-valued fraction containing
both `|B_r| (E|K|)²` and an infinite joint expectation is not a well-defined
ordinary real subtraction. The new extended covariance handles that case without
inventing an `∞ - ∞` value. The real `cE1` identity and quotient are proved only
under finite first/connected moment premises. The ledger therefore does not
claim that every occurrence of the paper's informal infinite ratio has an
unconditional real-valued formalization, nor does finite-moment `cE1` alone
complete the unrestricted source assertion. Interpreting that case entirely
through the extended covariance may permit a future classification upgrade after
a separate statement-fidelity decision.

## Validation

On the exact pre-commit working tree:

- `lake build --wfail PercLib` passes with 9,466 jobs;
- `python3 scripts/check_import_closure.py PercLib` reports all 419 modules;
- `.scratch/LemmaI47Audit.lean`, `.scratch/ThirdMomentAudit.lean` and
  `.scratch/CutoffI47Audit.lean` audit seventeen new declarations; every
  `#print axioms` report contains only `propext`, `Classical.choice`, and
  `Quot.sound`;
- the comment-aware placeholder scan and `git diff --check` pass.

These are local checks, not upstream CI. The finite-expectation condition is
explicit in theorem names and documentation rather than hidden in the proof or
omitted from the statement.


A later package validation used 9,474 jobs and 427 imported modules. The new
window, finite third-moment and alignment declarations have focused axiom checks
containing only the three standard axioms. This was local compilation, not CI.
