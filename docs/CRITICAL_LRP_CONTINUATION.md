# Formalization continuation: Lemma I.4.6

This note records the integer-cell counting proof of Lemma I.4.6 on the
continuation branch. It does not assert completion of the rest of the paper.
The source statement is the supplied PDF, page 36, with the unit-volume
convention from Definition I.1.3 on page 6.

## Complete result

`LatticeGeometry.Cell.Asymptotic` exports `lemma_I_4_6`. For a subadditive,
even, continuous and absolutely homogeneous `rho` whose real unit ball has
Lebesgue volume one, it proves

```text
(fun r : ℝ => ({z : Fin d → ℤ | rho (fun j => (z j : ℝ)) ≤ r}.ncard : ℝ)
  - r ^ d) =O[atTop] (fun r => r ^ (d - 1)).
```

This is the source expansion `|B_r| = r^d ± O(r^(d-1))`. It applies to the
integer `Set.ncard`, not to the Lebesgue measure of a real ball. The only
analytical premise is the source's unit-volume normalization. The other
hypotheses are the defining properties of a norm used by the proof;
`lemma_I_4_6_norm` discharges them through Lean's norm API. No positive lower
bound on the dimension is needed: in dimension zero the remainder is zero.
In positive dimension, `lemma_I_4_6_isEquivalent` derives the standing
normalization `|B_r| ~[atTop] (fun r => r^d)` from the same error estimate.
`Cell/Example.lean` supplies an explicit non-vacuous model in every dimension:
for `rho x = 2 * ‖x‖`, its unit ball is `[-1/2,1/2]^d` with volume one, and
`lemma_I_4_6_two_mul_norm` proves the expansion with no normalization premise.

## Proof structure

The `LatticeGeometry.Cell` package separates the argument into the following
steps.

- `integerCell` is the half-open cell `z + [0,1)^d`. The cells cover real
  coordinate space and are pairwise disjoint (`exists_mem_integerCell`,
  `integerCell_unique`, and `integerCell_disjoint_of_ne`).
- `integerCells_bounded_cubes` proves the two inclusions
  `{rho x <= r-C} ⊆ ⋃ cell z ⊆ {rho x <= r+C}` for centres with
  `rho z <= r`. A subadditivity, evenness and half-open unit-cube bound supply
  the fractional-displacement estimates. `exists_unitCube_upper_bound`
  obtains the latter bound for a continuous function, and
  `integerCells_bounded_cubes_l1` gives an explicit l1 witness.
- `volume_integerCell` gives every cell Lebesgue volume one, and
  `volume_biUnion_integerCell` converts a finite disjoint cell union to its
  cardinality. `card_le_volume_of_centers_le` and `counting_sandwich` package
  the resulting volume comparisons.
- `integer_centers_finite_of_volume_ne_top` proves finiteness of the complete
  admissible centre set. `ncard_integer_centers_sandwich` identifies its
  `Set.ncard` with the corresponding finite-set cardinality and proves the
  exact inner/outer measure sandwich. This does not rely on an arbitrary
  existential cover being the complete centre set.
- `rhoBall_pos_eq_smul` identifies a positive-radius rho-ball with the
  corresponding scalar multiple of the unit ball. `volume_rhoBall` then uses
  `Measure.addHaar_smul_of_nonneg` and
  `Module.finrank_fintype_fun_eq_card`: if the unit ball has volume one, its
  radius-`r` ball has volume `ENNReal.ofReal (r ^ d)`.
- `ncard_integer_centers_sandwich_real` yields, for `0 ≤ C < r`,
  `(r-C)^d ≤ |B_r| ≤ (r+C)^d`.
  `abs_ncard_integer_centers_sub_pow_le` consequently bounds
  `||B_r| - r^d|` by `(r+C)^d - (r-C)^d`.
- `abs_add_sub_pow_le` applies `abs_pow_sub_pow_le` and
  `(r+C)^(d-1) ≤ (2r)^(d-1)` for `0 ≤ C ≤ r`. The resulting explicit
  remainder estimate is
  `|(r+C)^d - (r-C)^d| ≤ 2*C*d*2^(d-1)*r^(d-1)`.
  `isBigO_add_sub_pow` converts it to the required `IsBigO`, and
  `ncard_integer_centers_sub_pow_isBigO` performs the final assembly.

The modular helper `ncard_integer_centers_sub_pow_isBigO_of_remainder` keeps
its power-difference premise visible. The unconditional `lemma_I_4_6` uses
the proved remainder theorem, not that helper premise as an assumption.

## Source correspondence

The paper's closed centred cells and the formalization's translated half-open
cells are two tilings of the same real coordinate space. Half-openness permits
exact disjointness; translation preserves unit volume and the norm bounds,
with evenness controlling the negative fractional displacement. Any finite
upper bound on the cube is sufficient, so an actual diameter need not be
computed. The condition `C < r` is used only in a finite-radius helper and is
valid eventually, while the exported source claim is asymptotic.

The normalization `volume {x | rho x <= 1} = 1` is intentional and is retained
in both final statements. This is neither a claim that every norm is already
normalized nor a replacement of the lattice count by real-ball volume. The
canonical sup norm's unit ball has volume `2^d`, not one in positive dimension;
`Cell/Example.lean` uses the correctly rescaled rho `2 * ‖x‖` instead. Haar
volume scaling is proved, not asserted.

## Arbitrary-norm normalization

`Cell/Normalization.lean` proves the source's normalization step rather than
merely carrying `hunit` through the theorem. For a positive-definite
norm-like `rho`,

- `exists_pos_mul_norm_le_of_pos_def` obtains a positive lower comparison
  `m * ‖x‖ ≤ rho x` by minimizing `rho` on the compact unit sphere;
- `volume_rhoBall_ne_top_of_pos_def` consequently makes every rho-ball have
  finite volume;
- `volume_rhoBall_one_pos_of_pos_def` uses a small positive dilation of a
  nonzero vector and continuity to make the unit ball's volume positive;
- `exists_normalized_smul` performs the explicit reciprocal-root rescaling,
  using `volume (r • rhoBall rho 1) = ofReal (r^d) * volume (rhoBall rho 1)`.

The export `exists_normalized_unitBall` therefore returns a positive scalar
`a` with `volume (rhoBall (fun x => a * rho x) 1) = 1`. Its direct consequence
`lemma_I_4_6_after_normalization` returns that `a` together with the complete
lattice error estimate for the norm `a * rho`. The rescaling and the remainder
are proved, not asserted. Positive definiteness and positive dimension are
explicit inputs, as is continuity (a standard property supplied by a norm's
API); the unit-volume hypothesis in the resulting rescaled theorem is proved.

This addresses the norm part of Definition I.1.3's WLOG normalization. It does
not package the separate derivative-kernel normalization or every logarithmic
error condition, so Definition I.1.3 as a whole remains PARTIAL.

## Validation

On the exact pre-commit working tree:

- `lake build --wfail PercLib` passes with 9,466 jobs;
- `python3 scripts/check_import_closure.py PercLib` reports all 419 modules;
- `.scratch/LemmaI46Audit.lean` and `.scratch/NormalizationAudit.lean` check
  24 normalization, count, remainder, equivalence and example declarations.
  Every `#print axioms` report contains
  only `propext`,
  `Classical.choice`, and `Quot.sound`;
- the comment-aware placeholder scan and `git diff --check` are clean.

These are local compilation and axiom checks, not upstream CI. Source fidelity
was checked separately against the supplied passages. The 75-item coverage
ledger now records I.4.6 as FULL; the other source obligations are unchanged.
